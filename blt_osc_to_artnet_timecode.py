import json
import queue
import socket
import struct
import threading
import time
from collections import deque
from dataclasses import dataclass, asdict
from difflib import SequenceMatcher
from typing import Optional, List, Dict, Any, Tuple

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

try:
    from pythonosc.dispatcher import Dispatcher
    from pythonosc.osc_server import ThreadingOSCUDPServer
    from pythonosc.udp_client import SimpleUDPClient
except ImportError:
    Dispatcher = None
    ThreadingOSCUDPServer = None
    SimpleUDPClient = None

try:
    import sounddevice as sd
    import soundfile as sf
    import librosa
    import numpy as np
except ImportError:
    sd = None
    sf = None
    librosa = None
    np = None


# ----------------------------
# Art-Net (ArtTimeCode) helpers
# ----------------------------

ARTNET_PORT = 6454
ARTNET_ID = b"Art-Net\x00"
OP_TIMECODE = 0x9700  # ArtTimeCode (little-endian on the wire)
PROT_VER_HI = 0
PROT_VER_LO = 14

TC_FILM_24 = 0
TC_EBU_25 = 1
TC_DF_29_97 = 2
TC_SMPTE_30 = 3  # 30 fps non-drop


def ms_to_timecode_fields(ms: int, fps: int) -> Tuple[int, int, int, int]:
    """Convert milliseconds into HH:MM:SS:FF at integer fps (non-drop)."""
    if ms < 0:
        ms = 0
    total_frames = int(round(ms * fps / 1000.0))
    frames = total_frames % fps
    total_seconds = total_frames // fps
    seconds = total_seconds % 60
    total_minutes = total_seconds // 60
    minutes = total_minutes % 60
    hours = (total_minutes // 60) % 24
    return hours, minutes, seconds, frames


def build_arttimecode_packet(hours: int, minutes: int, seconds: int, frames: int,
                             tc_type: int = TC_SMPTE_30,
                             stream_id: int = 0) -> bytes:
    """
    Build an ArtTimeCode packet.
    Format (Art-Net 4):
      ID[8], OpCode[2], ProtVerHi, ProtVerLo, Filler1, StreamId,
      Frames, Seconds, Minutes, Hours, Type
    """
    filler1 = 0
    return struct.pack(
        "<8sHBBBBBBBBB",
        ARTNET_ID,
        OP_TIMECODE,
        PROT_VER_HI,
        PROT_VER_LO,
        filler1,
        stream_id & 0xFF,
        frames & 0xFF,
        seconds & 0xFF,
        minutes & 0xFF,
        hours & 0xFF,
        tc_type & 0xFF,
    )


# ----------------------------
# Config + offsets model
# ----------------------------

@dataclass
class OffsetEntry:
    entry_id: int = 0          # unique identifier for this entry
    rekordbox_id: str = ""     # store as string for easy matching
    title: str = ""
    offset_ms: int = 0


@dataclass
class AppConfig:
    # OSC listen (HARDCODED - not UI configurable)
    osc_listen_ip: str = "0.0.0.0"
    osc_listen_port: int = 9000
    osc_path: str = "/blt/player"

    # Art-Net send
    artnet_target_ip: str = "127.0.0.1"  # common Art-Net broadcast
    artnet_use_broadcast: bool = False
    artnet_port: int = 6454
    artnet_stream_id: int = 0
    artnet_fps: int = 30
    artnet_type: int = TC_SMPTE_30
    send_rate_hz: int = 30

    # OSC output (speed master commands)
    osc_output_ip: str = "127.0.0.1"
    osc_output_port: int = 8000
    speed_master_1: str = "3.1"
    speed_master_2: str = "3.2"

    # Outbound interface selection
    bind_local_ip: str = "0.0.0.0"  # bind to chosen interface IP for sending

    # Time adjustments
    global_shift_ms: int = 0

    # Matching
    fuzzy_threshold: float = 0.90

    # Behavior
    extrapolate_timeout_s: float = 1.0  # if OSC stops, freeze after this many seconds
    stop_sending_when_no_signal: bool = False

    # Offsets database
    offsets: List[OffsetEntry] = None
    next_entry_id: int = 1  # Counter for unique entry IDs

    def __post_init__(self):
        if self.offsets is None:
            self.offsets = []


def config_to_json(cfg: AppConfig) -> Dict[str, Any]:
    d = asdict(cfg)
    d["offsets"] = [asdict(x) for x in cfg.offsets]
    d["next_entry_id"] = cfg.next_entry_id
    return d


def config_from_json(d: Dict[str, Any]) -> AppConfig:
    cfg = AppConfig()
    for k, v in d.items():
        if k == "offsets":
            cfg.offsets = [OffsetEntry(**e) for e in v]
        elif k == "next_entry_id":
            cfg.next_entry_id = v
        elif hasattr(cfg, k):
            setattr(cfg, k, v)
    return cfg


# ----------------------------
# Core state (updated by OSC)
# ----------------------------

@dataclass
class TrackState:
    device_id: str = ""
    is_on_air: bool = False
    track_time_ms: int = 0
    rekordbox_id: str = ""
    title: str = ""
    bpm: float = 0.0
    last_recv_monotonic: float = 0.0
    last_recv_time_ms: int = 0


class SharedState:
    def __init__(self):
        self._lock = threading.Lock()
        self.track = TrackState()
        self.matched_offset_ms = 0
        self.matched_label = "(none)"
        self.signal_ok = False
        self.last_bpm = 0.0  # Track BPM changes
        self.simulation_mode = False  # True when playback simulation is active

        # Multi-player tracking
        self.players = {}  # type: Dict[str, TrackState]  # device_id -> TrackState
        self.active_player_id = None  # type: Optional[str]  # currently selected player
        self.last_on_air_time = {}  # type: Dict[str, float]  # device_id -> last time went on air

        # For OSC updates/sec:
        # store monotonic timestamps of recent updates
        self._osc_times = deque()  # type: deque[float]

    def update_from_osc(self, device_id: str, is_on_air: bool, track_time_ms: int, rekordbox_id: str, title: str, bpm: float = 0.0):
        nowm = time.monotonic()
        bpm_changed = False
        player_list_changed = False
        active_changed = False
        
        with self._lock:
            # Update or create player state
            if device_id not in self.players:
                self.players[device_id] = TrackState()
                player_list_changed = True
            
            player = self.players[device_id]
            player.device_id = str(device_id)
            player.is_on_air = bool(is_on_air)
            player.track_time_ms = int(track_time_ms)
            player.rekordbox_id = str(rekordbox_id or "")
            player.title = str(title or "")
            player.bpm = float(bpm)
            player.last_recv_monotonic = nowm
            player.last_recv_time_ms = int(track_time_ms)
            
            # Track when player went on air
            if is_on_air:
                if device_id not in self.last_on_air_time:
                    self.last_on_air_time[device_id] = nowm
                    # Auto-select this player as it went on air
                    if self.active_player_id != device_id:
                        self.active_player_id = device_id
                        active_changed = True
                else:
                    # Check if this is more recent than current active player
                    if self.active_player_id:
                        current_on_air_time = self.last_on_air_time.get(self.active_player_id, 0)
                        if nowm > current_on_air_time and self.active_player_id != device_id:
                            self.last_on_air_time[device_id] = nowm
                            self.active_player_id = device_id
                            active_changed = True
            else:
                # Remove from on_air tracking if no longer on air
                if device_id in self.last_on_air_time:
                    del self.last_on_air_time[device_id]
            
            # If no active player is set, auto-select the first one
            if self.active_player_id is None and device_id:
                self.active_player_id = device_id
                active_changed = True
            
            # Update main track state with active player's data
            if self.active_player_id and self.active_player_id in self.players:
                active_player = self.players[self.active_player_id]
                self.track = TrackState(**asdict(active_player))
                self.signal_ok = True
                
                # Check if BPM changed
                if abs(self.track.bpm - self.last_bpm) > 0.01:
                    self.last_bpm = self.track.bpm
                    bpm_changed = True
            
            # record timestamp for rate calculation
            self._osc_times.append(nowm)
            # prune old values beyond a few seconds to keep deque small
            cutoff = nowm - 5.0
            while self._osc_times and self._osc_times[0] < cutoff:
                self._osc_times.popleft()
        
        return bpm_changed, player_list_changed, active_changed

    def snapshot(self) -> Tuple[TrackState, int, str, bool]:
        with self._lock:
            return (TrackState(**asdict(self.track)),
                    int(self.matched_offset_ms),
                    str(self.matched_label),
                    bool(self.signal_ok))

    def set_match(self, offset_ms: int, label: str):
        with self._lock:
            self.matched_offset_ms = int(offset_ms)
            self.matched_label = str(label)

    def osc_updates_per_sec(self, window_s: float = 1.0) -> float:
        """Return number of OSC updates received in the last window_s seconds."""
        nowm = time.monotonic()
        with self._lock:
            cutoff = nowm - float(window_s)
            # prune older than 5s (already done, but cheap)
            cutoff5 = nowm - 5.0
            while self._osc_times and self._osc_times[0] < cutoff5:
                self._osc_times.popleft()
            # count in last window
            # (deque is small; linear scan is fine)
            count = 0
            for t in reversed(self._osc_times):
                if t >= cutoff:
                    count += 1
                else:
                    break
            return float(count) / float(window_s)

    def set_simulation_mode(self, active: bool):
        with self._lock:
            self.simulation_mode = active

    def is_simulation_mode(self) -> bool:
        with self._lock:
            return self.simulation_mode
    
    def get_players(self) -> Dict[str, TrackState]:
        """Return a snapshot of all players."""
        with self._lock:
            return {k: TrackState(**asdict(v)) for k, v in self.players.items()}
    
    def get_active_player_id(self) -> Optional[str]:
        """Return the currently active player ID."""
        with self._lock:
            return self.active_player_id
    
    def set_active_player(self, device_id: str) -> bool:
        """Manually set the active player. Returns True if changed."""
        with self._lock:
            if device_id in self.players and self.active_player_id != device_id:
                self.active_player_id = device_id
                # Update main track state
                active_player = self.players[device_id]
                self.track = TrackState(**asdict(active_player))
                return True
            return False


# ----------------------------
# Matching logic
# ----------------------------

def normalize_title(s: str) -> str:
    return " ".join((s or "").strip().lower().split())


def best_offset_for_track(cfg: AppConfig, rekordbox_id: str, title: str) -> Tuple[int, str]:
    """
    Priority:
      1) Exact rekordbox_id match (string compare)
      2) Fuzzy title match >= threshold
    """
    rb = str(rekordbox_id or "").strip()
    tnorm = normalize_title(title)

    # 1) Exact ID match
    if rb:
        for e in cfg.offsets:
            if e.rekordbox_id and str(e.rekordbox_id).strip() == rb:
                label = f"ID match: {rb} → offset {e.offset_ms} ms"
                return int(e.offset_ms), label

    # 2) Fuzzy title match
    if tnorm:
        best = (0, "(none)", 0.0)  # offset, label, score
        for e in cfg.offsets:
            if not e.title:
                continue
            score = SequenceMatcher(None, tnorm, normalize_title(e.title)).ratio()
            if score > best[2]:
                best = (int(e.offset_ms),
                        f"Title match ({score:.2f}): '{e.title}' → offset {e.offset_ms} ms",
                        score)
        if best[2] >= float(cfg.fuzzy_threshold):
            return best[0], best[1]

    return 0, "(none)"


# ----------------------------
# OSC Receiver Thread
# ----------------------------

class OscReceiver:
    def __init__(self, cfg: AppConfig, state: SharedState, ui_queue: "queue.Queue[Tuple[str, Any]]"):
        self.cfg = cfg
        self.state = state
        self.ui_queue = ui_queue
        self.server = None
        self.thread = None

    def _handler(self, address: str, *args):
        """
        Accept shapes:
          /blt/player device_id is_on_air track_time_ms rekordbox_id title bpm
        Expected: device_id (str), is_on_air (bool/int), track_time_ms (int), 
                  rekordbox_id (int/str), title (str), bpm (float)
        """

        print("OSC received:", address, args)

        # Ignore OSC data when in simulation mode
        if self.state.is_simulation_mode():
            return

        if not args:
            return

        # Expected format: device_id, is_on_air, track_time_ms, rekordbox_id, title, bpm
        device_id = ""
        is_on_air = False
        track_time_ms = None
        rekordbox_id = ""
        title = ""
        bpm = 0.0

        # Extract parameters based on expected positions
        if len(args) >= 1:
            device_id = str(args[0])
        if len(args) >= 2:
            # Handle is_on_air as bool or int (0/1)
            is_on_air = bool(args[1]) if isinstance(args[1], (bool, int)) else False
        if len(args) >= 3 and isinstance(args[2], (int, float)):
            track_time_ms = int(args[2])
        if len(args) >= 4:
            rekordbox_id = str(args[3])
        if len(args) >= 5:
            title = str(args[4])
        if len(args) >= 6 and isinstance(args[5], (int, float)):
            bpm = float(args[5])

        if track_time_ms is None or not device_id:
            return

        bpm_changed, player_list_changed, active_changed = self.state.update_from_osc(
            device_id, is_on_air, track_time_ms, rekordbox_id, title, bpm
        )
        self.ui_queue.put(("osc_update", (bpm_changed, player_list_changed, active_changed)))

    def start(self):
        if Dispatcher is None or ThreadingOSCUDPServer is None:
            raise RuntimeError("python-osc is not installed. Run: pip install python-osc")

        disp = Dispatcher()
        disp.map(self.cfg.osc_path, self._handler)

        self.server = ThreadingOSCUDPServer((self.cfg.osc_listen_ip, int(self.cfg.osc_listen_port)), disp)

        def run():
            try:
                self.server.serve_forever()
            except Exception as e:
                self.ui_queue.put(("error", f"OSC server error: {e!r}"))

        self.thread = threading.Thread(target=run, daemon=True)
        self.thread.start()

    def stop(self):
        if self.server:
            try:
                self.server.shutdown()
            except Exception:
                pass
            self.server = None


# ----------------------------
# Art-Net Sender Thread
# ----------------------------

class ArtnetSender:
    def __init__(self, cfg: AppConfig, state: SharedState, ui_queue: "queue.Queue[Tuple[str, Any]]"):
        self.cfg = cfg
        self.state = state
        self.ui_queue = ui_queue
        self.thread = None
        self._stop = threading.Event()
        self.sock = None

    def _make_socket(self):
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        if self.cfg.artnet_use_broadcast:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        # Bind for interface selection (best-effort)
        try:
            bind_ip = self.cfg.bind_local_ip.strip()
            if bind_ip and bind_ip != "0.0.0.0":
                s.bind((bind_ip, 0))
        except Exception as e:
            self.ui_queue.put(("error", f"Could not bind to local IP {self.cfg.bind_local_ip}: {e}"))
        return s

    def start(self):
        self._stop.clear()
        self.sock = self._make_socket()

        def run():
            fps = int(self.cfg.artnet_fps)
            send_rate = max(1, int(self.cfg.send_rate_hz))
            period = 1.0 / float(send_rate)
            next_send = time.monotonic()

            while not self._stop.is_set():
                track, matched_offset_ms, matched_label, signal_ok = self.state.snapshot()

                # Update matching
                offset_ms, label = best_offset_for_track(self.cfg, track.rekordbox_id, track.title)
                if offset_ms != matched_offset_ms or label != matched_label:
                    self.state.set_match(offset_ms, label)
                    self.ui_queue.put(("match_update", None))

                nowm = time.monotonic()
                age = nowm - float(track.last_recv_monotonic or 0.0)

                if (not signal_ok) or (track.last_recv_monotonic <= 0):
                    if not self.cfg.stop_sending_when_no_signal:
                        pkt = build_arttimecode_packet(0, 0, 0, 0, self.cfg.artnet_type, self.cfg.artnet_stream_id)
                        try:
                            self.sock.sendto(pkt, (self.cfg.artnet_target_ip, int(self.cfg.artnet_port)))
                        except Exception as e:
                            self.ui_queue.put(("error", f"Art-Net send error: {e}"))

                    next_send += period
                    dt = next_send - time.monotonic()
                    if dt > 0:
                        time.sleep(dt)
                    else:
                        next_send = time.monotonic()
                    continue

                # Extrapolate between OSC updates
                if age <= float(self.cfg.extrapolate_timeout_s):
                    effective_ms = track.last_recv_time_ms + int(age * 1000.0)
                else:
                    effective_ms = track.last_recv_time_ms

                effective_ms += int(offset_ms) + int(self.cfg.global_shift_ms)

                h, m, s, f = ms_to_timecode_fields(effective_ms, fps=fps)
                pkt = build_arttimecode_packet(h, m, s, f, self.cfg.artnet_type, self.cfg.artnet_stream_id)

                try:
                    self.sock.sendto(pkt, (self.cfg.artnet_target_ip, int(self.cfg.artnet_port)))
                except Exception as e:
                    self.ui_queue.put(("error", f"Art-Net send error: {e}"))

                self.ui_queue.put(("tick", (h, m, s, f)))

                next_send += period
                dt = next_send - time.monotonic()
                if dt > 0:
                    time.sleep(dt)
                else:
                    next_send = time.monotonic()

        self.thread = threading.Thread(target=run, daemon=True)
        self.thread.start()

    def stop(self):
        self._stop.set()
        if self.sock:
            try:
                self.sock.close()
            except Exception:
                pass
            self.sock = None


# ----------------------------
# OSC Sender (Speed Master Commands)
# ----------------------------

class OscSender:
    def __init__(self, cfg: AppConfig, state: SharedState, ui_queue: "queue.Queue[Tuple[str, Any]]"):
        self.cfg = cfg
        self.state = state
        self.ui_queue = ui_queue
        self.client = None
        self.last_sent_bpm = 0.0

    def start(self):
        if SimpleUDPClient is None:
            raise RuntimeError("python-osc is not installed. Run: pip install python-osc")
        
        try:
            self.client = SimpleUDPClient(self.cfg.osc_output_ip, int(self.cfg.osc_output_port))
        except Exception as e:
            raise RuntimeError(f"Could not create OSC client: {e}")

    def send_bpm_update(self, bpm: float):
        if self.client is None or abs(bpm - self.last_sent_bpm) < 0.01:
            return
        
        try:
            # Send to speed master 1
            msg1 = f"Master {self.cfg.speed_master_1} At BPM {bpm:.2f}"
            self.client.send_message("/cmd", msg1)
            
            # Send to speed master 2 with double BPM
            bpm2 = bpm * 2.0
            msg2 = f"Master {self.cfg.speed_master_2} At BPM {bpm2:.2f}"
            self.client.send_message("/cmd", msg2)
            
            self.last_sent_bpm = bpm
            self.ui_queue.put(("osc_sent", (bpm, bpm2)))
        except Exception as e:
            self.ui_queue.put(("error", f"OSC send error: {e}"))

    def stop(self):
        self.client = None


# ----------------------------
# Tkinter UI
# ----------------------------

def discover_local_ips() -> List[str]:
    ips = ["0.0.0.0"]
    try:
        hostname = socket.gethostname()
        for info in socket.getaddrinfo(hostname, None, family=socket.AF_INET):
            ip = info[4][0]
            if ip not in ips:
                ips.append(ip)
    except Exception:
        pass
    for extra in ["127.0.0.1"]:
        if extra not in ips:
            ips.append(extra)
    return ips


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("BLT OSC → Python → Art-Net Timecode")
        self.geometry("865x650")

        self.cfg = AppConfig()
        self.state = SharedState()
        self.ui_queue: "queue.Queue[Tuple[str, Any]]" = queue.Queue()

        self.osc = None
        self.artnet = None
        self.osc_sender = None
        self._flash_state = False  # For flashing red when no signal

        # Playback simulation state
        self.playback_audio_file = None
        self.playback_audio_data = None
        self.playback_samplerate = None
        self.playback_duration = 0.0
        self.playback_bpm = 0.0
        self.playback_selected_entry = None
        self.playback_is_playing = False
        self.playback_paused = False
        self.playback_start_sample = 0  # Where playback started from
        self.playback_start_time = 0.0  # When playback started (time.time())
        self.playback_pause_time = 0.0  # Time when paused
        self.playback_thread = None
        self.playback_stop_event = threading.Event()
        self.playback_audio_thread = None  # Track audio thread
        self.playback_audio_lock = threading.Lock()  # Prevent concurrent audio starts
        self.playback_slider_updating = False  # Prevent seek during slider updates
        self.playback_was_playing_before_seek = False  # Track if playing before slider grab

        self._build_ui()
        self._refresh_status()
        self.after(50, self._poll_ui_queue)

    def _build_ui(self):
        notebook = ttk.Notebook(self)
        notebook.pack(fill="both", expand=True, padx=10, pady=10)

        self.tab_network = ttk.Frame(notebook)
        self.tab_offsets = ttk.Frame(notebook)
        self.tab_playback = ttk.Frame(notebook)
        self.tab_status = ttk.Frame(notebook)
        self.tab_help = ttk.Frame(notebook)

        notebook.add(self.tab_network, text="Network")
        notebook.add(self.tab_offsets, text="Offsets")
        notebook.add(self.tab_playback, text="Playback")
        notebook.add(self.tab_status, text="Status")
        notebook.add(self.tab_help, text="Help")

        self._build_network_tab()
        self._build_offsets_tab()
        self._build_playback_tab()
        self._build_status_tab()
        self._build_help_tab()

        bottom = ttk.Frame(self)
        bottom.pack(fill="x", padx=10, pady=(0, 10))

        ttk.Button(bottom, text="Load Config…", command=self.load_config).pack(side="left")
        ttk.Button(bottom, text="Save Config…", command=self.save_config).pack(side="left", padx=(6, 0))

        self.btn_start = ttk.Button(bottom, text="Start", command=self.start_services)
        self.btn_start.pack(side="right")
        self.btn_stop = ttk.Button(bottom, text="Stop", command=self.stop_services, state="disabled")
        self.btn_stop.pack(side="right", padx=(0, 6))

    def _build_network_tab(self):
        f = self.tab_network

        art_box = ttk.LabelFrame(f, text="Art-Net Output (Timecode)")
        art_box.pack(fill="x", padx=10, pady=10)

        self.var_use_bcast = tk.BooleanVar(value=self.cfg.artnet_use_broadcast)
        self.var_target_ip = tk.StringVar(value=self.cfg.artnet_target_ip)
        self.var_art_port = tk.IntVar(value=self.cfg.artnet_port)
        self.var_bind_ip = tk.StringVar(value=self.cfg.bind_local_ip)

        self.var_send_rate = tk.IntVar(value=self.cfg.send_rate_hz)
        self.var_stream_id = tk.IntVar(value=self.cfg.artnet_stream_id)
        self.var_global_shift = tk.IntVar(value=self.cfg.global_shift_ms)
        self.var_fuzzy = tk.DoubleVar(value=self.cfg.fuzzy_threshold)

        ips = discover_local_ips()

        ttk.Checkbutton(art_box, text="Use broadcast", variable=self.var_use_bcast).grid(
            row=0, column=0, sticky="w", padx=8, pady=6
        )
        ttk.Label(art_box, text="Target IP:").grid(row=0, column=1, sticky="w", padx=8, pady=6)
        ttk.Entry(art_box, textvariable=self.var_target_ip, width=18).grid(row=0, column=2, sticky="w", padx=8, pady=6)

        ttk.Label(art_box, text="Port:").grid(row=0, column=3, sticky="w", padx=8, pady=6)
        ttk.Entry(art_box, textvariable=self.var_art_port, width=10).grid(row=0, column=4, sticky="w", padx=8, pady=6)

        ttk.Label(art_box, text="Bind local IP:").grid(row=1, column=0, sticky="w", padx=8, pady=6)
        self.combo_bind = ttk.Combobox(art_box, textvariable=self.var_bind_ip, values=ips, width=16)
        self.combo_bind.grid(row=1, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(art_box, text="(choose NIC IP)").grid(row=1, column=2, sticky="w", padx=8, pady=6)

        ttk.Label(art_box, text="Send rate (Hz):").grid(row=2, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(art_box, textvariable=self.var_send_rate, width=10).grid(row=2, column=1, sticky="w", padx=8, pady=6)

        ttk.Label(art_box, text="Stream ID:").grid(row=2, column=2, sticky="w", padx=8, pady=6)
        ttk.Entry(art_box, textvariable=self.var_stream_id, width=10).grid(row=2, column=3, sticky="w", padx=8, pady=6)

        ttk.Label(art_box, text="Global shift (ms):").grid(row=3, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(art_box, textvariable=self.var_global_shift, width=10).grid(row=3, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(art_box, text="(negative = earlier, positive = later)").grid(row=3, column=2, columnspan=3, sticky="w", padx=8, pady=6)

        ttk.Label(art_box, text="Title match threshold:").grid(row=4, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(art_box, textvariable=self.var_fuzzy, width=10).grid(row=4, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(art_box, text="(e.g. 0.90)").grid(row=4, column=2, sticky="w", padx=8, pady=6)

        osc_out_box = ttk.LabelFrame(f, text="OSC Output (Speed Master Commands)")
        osc_out_box.pack(fill="x", padx=10, pady=10)

        self.var_osc_out_ip = tk.StringVar(value=self.cfg.osc_output_ip)
        self.var_osc_out_port = tk.IntVar(value=self.cfg.osc_output_port)
        self.var_speed_master_1 = tk.StringVar(value=self.cfg.speed_master_1)
        self.var_speed_master_2 = tk.StringVar(value=self.cfg.speed_master_2)

        ttk.Label(osc_out_box, text="Target IP:").grid(row=0, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(osc_out_box, textvariable=self.var_osc_out_ip, width=18).grid(row=0, column=1, sticky="w", padx=8, pady=6)

        ttk.Label(osc_out_box, text="Port:").grid(row=0, column=2, sticky="w", padx=8, pady=6)
        ttk.Entry(osc_out_box, textvariable=self.var_osc_out_port, width=10).grid(row=0, column=3, sticky="w", padx=8, pady=6)

        ttk.Label(osc_out_box, text="Speed Master 1:").grid(row=1, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(osc_out_box, textvariable=self.var_speed_master_1, width=10).grid(row=1, column=1, sticky="w", padx=8, pady=6)

        ttk.Label(osc_out_box, text="Speed Master 2:").grid(row=1, column=2, sticky="w", padx=8, pady=6)
        ttk.Entry(osc_out_box, textvariable=self.var_speed_master_2, width=10).grid(row=1, column=3, sticky="w", padx=8, pady=6)

        ttk.Label(osc_out_box, text="Sends: /cmd \"Master <id> At BPM <value>\" on BPM change (SM2 = 2x BPM)").grid(
            row=2, column=0, columnspan=5, sticky="w", padx=8, pady=6
        )

    def _build_offsets_tab(self):
        f = self.tab_offsets

        top = ttk.Frame(f)
        top.pack(fill="x", padx=10, pady=10)
        ttk.Label(top, text="Offsets database (ms): exact Rekordbox ID match first, else fuzzy title match.").pack(anchor="w")

        mid = ttk.Frame(f)
        mid.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        cols = ("entry_id", "rekordbox_id", "title", "offset_ms")
        self.tree = ttk.Treeview(mid, columns=cols, show="headings", selectmode="browse")
        self.tree.heading("entry_id", text="ID")
        self.tree.heading("rekordbox_id", text="Rekordbox ID")
        self.tree.heading("title", text="Title")
        self.tree.heading("offset_ms", text="Offset")
        self.tree.column("entry_id", width=50, anchor="w")
        self.tree.column("rekordbox_id", width=120, anchor="w")
        self.tree.column("title", width=480, anchor="w")
        self.tree.column("offset_ms", width=120, anchor="e")
        self.tree.pack(side="left", fill="both", expand=True)

        scroll = ttk.Scrollbar(mid, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscroll=scroll.set)
        scroll.pack(side="right", fill="y")

        edit = ttk.LabelFrame(f, text="Add / Edit entry")
        edit.pack(fill="x", padx=10, pady=(0, 10))

        self.var_edit_entry_id = tk.IntVar(value=0)
        self.var_edit_id = tk.StringVar()
        self.var_edit_title = tk.StringVar()
        self.var_edit_minutes = tk.IntVar(value=0)
        self.var_edit_seconds = tk.IntVar(value=0)

        # Row 0: Entry ID (hidden, just for tracking)
        ttk.Label(edit, text="Entry ID:").grid(row=0, column=0, sticky="w", padx=8, pady=6)
        ttk.Label(edit, textvariable=self.var_edit_entry_id).grid(row=0, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(edit, text="(auto-assigned)").grid(row=0, column=2, sticky="w", padx=8, pady=6)

        # Row 1: Rekordbox ID
        ttk.Label(edit, text="Rekordbox ID (optional):").grid(row=1, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(edit, textvariable=self.var_edit_id, width=30).grid(row=1, column=1, columnspan=2, sticky="w", padx=8, pady=6)

        # Row 2: Title
        ttk.Label(edit, text="Title (optional):").grid(row=2, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(edit, textvariable=self.var_edit_title, width=60).grid(row=2, column=1, columnspan=2, sticky="w", padx=8, pady=6)

        # Row 3: Offset - Minutes
        ttk.Label(edit, text="Offset Minutes:").grid(row=3, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(edit, textvariable=self.var_edit_minutes, width=10).grid(row=3, column=1, sticky="w", padx=8, pady=6)

        # Row 4: Offset - Seconds
        ttk.Label(edit, text="Offset Seconds:").grid(row=4, column=0, sticky="w", padx=8, pady=6)
        ttk.Entry(edit, textvariable=self.var_edit_seconds, width=10).grid(row=4, column=1, sticky="w", padx=8, pady=6)

        # Row 5: Buttons
        btns = ttk.Frame(edit)
        btns.grid(row=5, column=0, columnspan=3, sticky="w", padx=8, pady=(10, 8))
        ttk.Button(btns, text="Add / Update", command=self.add_or_update_entry).pack(side="left")
        ttk.Button(btns, text="Load selected", command=self.load_selected_entry).pack(side="left", padx=(6, 0))
        ttk.Button(btns, text="Grab Current", command=self.grab_current_track).pack(side="left", padx=(6, 0))
        ttk.Button(btns, text="Delete selected", command=self.delete_selected_entry).pack(side="left", padx=(6, 0))
        ttk.Button(btns, text="Clear fields", command=self.clear_entry_fields).pack(side="left", padx=(6, 0))

        self._refresh_offsets_tree()

    def _build_playback_tab(self):
        f = self.tab_playback

        if not sd or not librosa:
            ttk.Label(f, text="Playback requires sounddevice, soundfile, and librosa. Install with: pip install sounddevice soundfile librosa", 
                     foreground="red", font=("TkDefaultFont", 12, "bold")).pack(padx=20, pady=20)
            return

        # Mode indicator
        mode_frame = ttk.Frame(f)
        mode_frame.pack(fill="x", padx=10, pady=10)
        ttk.Label(mode_frame, text="Mode:").pack(side="left", padx=(0, 5))
        self.lbl_playback_mode = ttk.Label(mode_frame, text="LIVE OSC", foreground="green", 
                                          font=("TkDefaultFont", 11, "bold"))
        self.lbl_playback_mode.pack(side="left")

        # Offset selection
        offset_box = ttk.LabelFrame(f, text="Available Offsets (Read-Only)")
        offset_box.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        cols = ("entry_id", "rekordbox_id", "title", "offset")
        self.playback_tree = ttk.Treeview(offset_box, columns=cols, show="headings", selectmode="browse", height=6)
        self.playback_tree.heading("entry_id", text="ID")
        self.playback_tree.heading("rekordbox_id", text="Rekordbox ID")
        self.playback_tree.heading("title", text="Title")
        self.playback_tree.heading("offset", text="Offset")
        self.playback_tree.column("entry_id", width=50, anchor="w")
        self.playback_tree.column("rekordbox_id", width=120, anchor="w")
        self.playback_tree.column("title", width=400, anchor="w")
        self.playback_tree.column("offset", width=100, anchor="e")
        
        scroll = ttk.Scrollbar(offset_box, orient="vertical", command=self.playback_tree.yview)
        self.playback_tree.configure(yscroll=scroll.set)
        self.playback_tree.pack(side="left", fill="both", expand=True, padx=5, pady=5)
        scroll.pack(side="right", fill="y", pady=5)

        # Audio file selection
        file_box = ttk.LabelFrame(f, text="Audio File")
        file_box.pack(fill="x", padx=10, pady=(0, 10))

        file_info = ttk.Frame(file_box)
        file_info.pack(fill="x", padx=8, pady=8)
        
        ttk.Button(file_info, text="Load Audio File...", command=self.playback_load_file).pack(side="left")
        self.lbl_playback_file = ttk.Label(file_info, text="No file loaded")
        self.lbl_playback_file.pack(side="left", padx=(10, 0))

        # Playback controls
        control_box = ttk.LabelFrame(f, text="Playback Controls")
        control_box.pack(fill="x", padx=10, pady=(0, 10))

        btn_frame = ttk.Frame(control_box)
        btn_frame.pack(fill="x", padx=8, pady=8)

        self.btn_playback_play = ttk.Button(btn_frame, text="Play", command=self.playback_play, state="disabled")
        self.btn_playback_play.pack(side="left", padx=(0, 5))

        self.btn_playback_pause = ttk.Button(btn_frame, text="Pause", command=self.playback_pause, state="disabled")
        self.btn_playback_pause.pack(side="left", padx=(0, 5))

        self.btn_playback_stop = ttk.Button(btn_frame, text="Stop", command=self.playback_stop, state="disabled")
        self.btn_playback_stop.pack(side="left")

        # Position display and scrubber
        pos_frame = ttk.Frame(control_box)
        pos_frame.pack(fill="x", padx=8, pady=(0, 8))

        self.lbl_playback_pos = ttk.Label(pos_frame, text="00:00 / 00:00")
        self.lbl_playback_pos.pack(anchor="w")

        self.playback_slider = ttk.Scale(pos_frame, from_=0, to=100, orient="horizontal", 
                                        command=self.playback_seek)
        self.playback_slider.pack(fill="x", pady=(5, 0))
        self.playback_slider.config(state="disabled")
        
        # Bind slider events to pause during drag
        self.playback_slider.bind("<ButtonPress-1>", self.playback_slider_press)
        self.playback_slider.bind("<ButtonRelease-1>", self.playback_slider_release)

        # Info
        info_frame = ttk.Frame(control_box)
        info_frame.pack(fill="x", padx=8, pady=(0, 8))
        self.lbl_playback_info = ttk.Label(info_frame, text="")
        self.lbl_playback_info.pack(anchor="w")

        self._refresh_playback_offsets()

    def _build_status_tab(self):
        f = self.tab_status

        # Mode indicator at top
        mode_frame = ttk.Frame(f)
        mode_frame.pack(fill="x", padx=10, pady=(10, 0))
        ttk.Label(mode_frame, text="Mode:").pack(side="left", padx=(0, 5))
        self.lbl_status_mode = ttk.Label(mode_frame, text="LIVE OSC", foreground="green", 
                                        font=("TkDefaultFont", 12, "bold"))
        self.lbl_status_mode.pack(side="left")

        box = ttk.LabelFrame(f, text="Live status")
        box.pack(fill="both", expand=False, padx=10, pady=10)

        self.lbl_signal = ttk.Label(box, text="Signal: (waiting)")
        self.lbl_signal.pack(anchor="w", padx=8, pady=(8, 4))

        self.lbl_osc_rate = ttk.Label(box, text="OSC updates/sec: 0.0")
        self.lbl_osc_rate.pack(anchor="w", padx=8, pady=4)

        self.lbl_track = ttk.Label(box, text="Track: -")
        self.lbl_track.pack(anchor="w", padx=8, pady=4)

        self.lbl_bpm = ttk.Label(box, text="BPM: -")
        self.lbl_bpm.pack(anchor="w", padx=8, pady=4)

        self.lbl_match = ttk.Label(box, text="Offset match: (none)")
        self.lbl_match.pack(anchor="w", padx=8, pady=4)

        self.lbl_tc = ttk.Label(box, text="Timecode: 00:00:00:00")
        self.lbl_tc.pack(anchor="w", padx=8, pady=4)

        self.lbl_osc_out = ttk.Label(box, text="OSC Output: -")
        self.lbl_osc_out.pack(anchor="w", padx=8, pady=4)

        self.lbl_err = ttk.Label(box, text="", foreground="red")
        self.lbl_err.pack(anchor="w", padx=8, pady=(10, 4))

        # Player selector section
        player_box = ttk.LabelFrame(f, text="Player Selection")
        player_box.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        # Scrollable frame for players
        canvas = tk.Canvas(player_box, height=150)
        scrollbar = ttk.Scrollbar(player_box, orient="vertical", command=canvas.yview)
        self.player_selector_frame = ttk.Frame(canvas)

        self.player_selector_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )

        canvas.create_window((0, 0), window=self.player_selector_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True, padx=5, pady=5)
        scrollbar.pack(side="right", fill="y")

        # Dictionary to track player buttons
        self.player_buttons = {}  # device_id -> (button, label_frame)

    def _build_help_tab(self):
        f = self.tab_help

        # Create scrollable text area
        text_frame = ttk.Frame(f)
        text_frame.pack(fill="both", expand=True, padx=10, pady=10)

        scrollbar = ttk.Scrollbar(text_frame)
        scrollbar.pack(side="right", fill="y")

        help_text = tk.Text(text_frame, wrap="word", yscrollcommand=scrollbar.set, font=("TkDefaultFont", 10))
        help_text.pack(side="left", fill="both", expand=True)
        scrollbar.config(command=help_text.yview)

        # Help content
        content = """OSC TO ART-NET & OSC TRANSCEIVER - HELP

━━━━━━━━━━━━━━━━━━━━━━━━━━━━

OSC INPUT (FIXED CONFIGURATION)

This application listens for OSC messages on:
  • IP: 0.0.0.0 (all network interfaces)
  • Port: 9000
  • Path: /blt/player

Expected OSC Message Format:
  /blt/player <device_id> <is_on_air> <track_time_ms> <rekordbox_id> <title> <bpm>

  Parameters:
    • device_id (str)        - Player/device identifier (e.g., "CDJ1", "CDJ2")
    • is_on_air (bool/int)   - Whether this player is currently on air (1/0 or true/false)
    • track_time_ms (int)    - Current position in track (milliseconds)
    • rekordbox_id (str)     - Rekordbox track ID
    • title (str)            - Track title
    • bpm (float)            - Current track BPM

  Example:
    /blt/player "CDJ1" 1 123456 987654 "My Track" 128.0

Multi-Player Behavior:
  • The application tracks all players that send data
  • Players can be manually selected via the Status tab
  • When a player goes "on air", it automatically becomes the active player
  • If multiple players are on air, the most recently activated one is selected
  • Manual selection is available when mixer data is unavailable (is_on_air always false)

Configure Beat Link Trigger to send OSC messages in this format to port 9000.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━

ART-NET OUTPUT

Sends ArtTimeCode packets for timecode synchronization.

Configuration:
  • Target IP: Set to your lighting console's IP (or broadcast address)
  • Port: 6454 (Art-Net standard)
  • Stream ID: Identifies this timecode stream
  • Send Rate: How often to send updates (Hz)
  • Global Shift: Add/subtract milliseconds from all timecode

━━━━━━━━━━━━━━━━━━━━━━━━━━━━

OSC OUTPUT (SPEED MASTER COMMANDS)

Sends BPM updates to control speed masters (e.g., MA Lighting GrandMA3).

Configuration:
  • Target IP: IP address of your lighting console
  • Port: OSC port configured on your console
  • Speed Master 1: Identifier for first speed master (e.g., "3.1")
  • Speed Master 2: Identifier for second speed master (e.g., "3.2")

Behavior:
  • When BPM changes, sends OSC messages to /cmd path
  • Speed Master 1 receives actual BPM value
  • Speed Master 2 receives double BPM value

  Message Format:
    /cmd "Master <speed_master_id> At BPM <bpm_value>"

  Example:
    /cmd "Master 3.1 At BPM 128.00"
    /cmd "Master 3.2 At BPM 256.00"

━━━━━━━━━━━━━━━━━━━━━━━━━━━━

GRANDMA3 CONFIGURATION

OSC Input Setup:
1. Enable OSC Input:
   • Go to: Menu → In & Out → OSC
   • Set correct Network Interface
   • Add new OSC Data
   • Set UDP Port to match "OSC Output Port" in this application (e.g., 8000)
   • Enable "Receive" and "Receive Command"
   • Enable "Enable Input"
   • Note your console's IP address

2. Network Configuration:
   • In this application's "OSC Output" section:
     - Set "Target IP" to your GrandMA3 console's IP
     - Set "Port" to match the UDP port from step 1
     - Set "Speed Master 1" to your first executor (e.g., "3.1")
     - Set "Speed Master 2" to your second executor (e.g., "3.2")

3. Art-Net Timecode Setup:
   • Go to: Menu → DMX Protocols → Art-Net
   • Set correct Network Interface
   • Add new Art-Net Data
   • Enable and set Mode to "Input"
   • Select preferred Timecode Slot (usually Slot 1, is default)
   • Link timecode to desired objects

4. Testing:
   • Start this application
   • Play a track in your DJ software with Beat Link Trigger or simulated playback
   • Check Status tab for BPM updates
   • Verify speed masters and Timecodes on console receive BPM values

━━━━━━━━━━━━━━━━━━━━━━━━━━━━

OFFSETS DATABASE

Use the Offsets tab to create track-specific timing adjustments.

Matching Priority:
  1. Exact Rekordbox ID match (highest priority)
  2. Fuzzy title match (if threshold exceeded)
  3. No match = 0 offset

Title Match Threshold:
  • Set in Network tab (e.g., 0.90 = 90% similarity required)
  • Higher values = stricter matching

━━━━━━━━━━━━━━━━━━━━━━━━━━━━

TROUBLESHOOTING

No OSC Signal:
  • Check Beat Link Trigger is running and configured
  • Verify OSC messages are sent to port 9000
  • Check firewall settings

No Art-Net Output:
  • Verify target IP is correct
  • Check network connectivity
  • Ensure Art-Net port 6454 is not blocked

No OSC Output (Speed Masters):
  • Verify GrandMA3 OSC input is enabled
  • Check target IP and port match console settings
  • Verify speed master IDs exist on console
  • Check console network settings and firewall

BPM Not Updating:
  • Ensure BLT sends BPM parameter (4th parameter)
  • Check Status tab shows BPM value
  • Look for errors in Status tab

━━━━━━━━━━━━━━━━━━━━━━━━━━━━
"""

        help_text.insert("1.0", content)
        help_text.config(state="disabled")  # Make read-only

    # ---- Config apply/save/load ----

    def apply_ui_to_config(self):
        # OSC input is hardcoded, no UI to read from
        self.cfg.osc_listen_ip = "0.0.0.0"
        self.cfg.osc_listen_port = 9000
        self.cfg.osc_path = "/blt/track"

        self.cfg.artnet_use_broadcast = bool(self.var_use_bcast.get())
        self.cfg.artnet_target_ip = self.var_target_ip.get().strip() or ("2.255.255.255" if self.cfg.artnet_use_broadcast else "127.0.0.1")
        self.cfg.artnet_port = int(self.var_art_port.get())
        self.cfg.bind_local_ip = self.var_bind_ip.get().strip() or "0.0.0.0"

        self.cfg.send_rate_hz = int(self.var_send_rate.get())
        self.cfg.artnet_stream_id = int(self.var_stream_id.get())
        self.cfg.global_shift_ms = int(self.var_global_shift.get())
        self.cfg.fuzzy_threshold = float(self.var_fuzzy.get())

        # OSC output settings
        self.cfg.osc_output_ip = self.var_osc_out_ip.get().strip() or "127.0.0.1"
        self.cfg.osc_output_port = int(self.var_osc_out_port.get())
        self.cfg.speed_master_1 = self.var_speed_master_1.get().strip() or "3.1"
        self.cfg.speed_master_2 = self.var_speed_master_2.get().strip() or "3.2"

        # fixed for your request
        self.cfg.artnet_fps = 30
        self.cfg.artnet_type = TC_SMPTE_30

    def save_config(self):
        self.apply_ui_to_config()
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json")],
            title="Save config"
        )
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            json.dump(config_to_json(self.cfg), f, indent=2)
        messagebox.showinfo("Saved", f"Saved config to:\n{path}")

    def load_config(self):
        path = filedialog.askopenfilename(
            filetypes=[("JSON", "*.json")],
            title="Load config"
        )
        if not path:
            return
        with open(path, "r", encoding="utf-8") as f:
            d = json.load(f)
        self.cfg = config_from_json(d)

        # Push into UI (OSC input is hardcoded, no UI to update)
        self.var_use_bcast.set(self.cfg.artnet_use_broadcast)
        self.var_target_ip.set(self.cfg.artnet_target_ip)
        self.var_art_port.set(self.cfg.artnet_port)
        self.var_bind_ip.set(self.cfg.bind_local_ip)

        self.var_send_rate.set(self.cfg.send_rate_hz)
        self.var_stream_id.set(self.cfg.artnet_stream_id)
        self.var_global_shift.set(self.cfg.global_shift_ms)
        self.var_fuzzy.set(self.cfg.fuzzy_threshold)

        # OSC output settings
        self.var_osc_out_ip.set(self.cfg.osc_output_ip)
        self.var_osc_out_port.set(self.cfg.osc_output_port)
        self.var_speed_master_1.set(self.cfg.speed_master_1)
        self.var_speed_master_2.set(self.cfg.speed_master_2)

        self._refresh_offsets_tree()
        self._refresh_playback_offsets()  # Update playback tab too
        messagebox.showinfo("Loaded", f"Loaded config from:\n{path}")

    # ---- Offsets DB actions ----

    def _refresh_offsets_tree(self):
        for row in self.tree.get_children():
            self.tree.delete(row)
        for e in self.cfg.offsets:
            # Format offset as XXm XXs
            total_seconds = e.offset_ms // 1000
            minutes = total_seconds // 60
            seconds = total_seconds % 60
            offset_display = f"{minutes}m {seconds}s"
            self.tree.insert("", "end", iid=str(e.entry_id), values=(e.entry_id, e.rekordbox_id, e.title, offset_display))

    def clear_entry_fields(self):
        self.var_edit_entry_id.set(0)
        self.var_edit_id.set("")
        self.var_edit_title.set("")
        self.var_edit_minutes.set(0)
        self.var_edit_seconds.set(0)

    def load_selected_entry(self):
        sel = self.tree.selection()
        if not sel:
            return
        entry_id = int(sel[0])
        # Find entry by entry_id
        e = None
        for entry in self.cfg.offsets:
            if entry.entry_id == entry_id:
                e = entry
                break
        if not e:
            return
        
        self.var_edit_entry_id.set(e.entry_id)
        self.var_edit_id.set(e.rekordbox_id)
        self.var_edit_title.set(e.title)
        
        # Convert ms to minutes and seconds
        total_seconds = e.offset_ms // 1000
        minutes = total_seconds // 60
        seconds = total_seconds % 60
        self.var_edit_minutes.set(minutes)
        self.var_edit_seconds.set(seconds)

    def grab_current_track(self):
        """Grab the currently playing track's ID and title."""
        track, _, _, _ = self.state.snapshot()
        if track.rekordbox_id or track.title:
            self.var_edit_id.set(track.rekordbox_id)
            self.var_edit_title.set(track.title)
        else:
            messagebox.showinfo("No track", "No track is currently playing.")

    def add_or_update_entry(self):
        rid = self.var_edit_id.get().strip()
        title = self.var_edit_title.get().strip()
        minutes = int(self.var_edit_minutes.get())
        seconds = int(self.var_edit_seconds.get())
        offset_ms = (minutes * 60 + seconds) * 1000
        entry_id = int(self.var_edit_entry_id.get())

        if not rid and not title:
            messagebox.showwarning("Missing", "Provide at least Rekordbox ID or Title.")
            return

        # Check if we're updating an existing entry
        if entry_id > 0:
            for e in self.cfg.offsets:
                if e.entry_id == entry_id:
                    e.rekordbox_id = rid
                    e.title = title
                    e.offset_ms = offset_ms
                    self._refresh_offsets_tree()
                    self.clear_entry_fields()
                    return

        # Otherwise, create new entry
        new_entry = OffsetEntry(
            entry_id=self.cfg.next_entry_id,
            rekordbox_id=rid,
            title=title,
            offset_ms=offset_ms
        )
        self.cfg.offsets.append(new_entry)
        self.cfg.next_entry_id += 1

        self._refresh_offsets_tree()
        self._refresh_playback_offsets()  # Update playback tab too
        self.clear_entry_fields()

    def delete_selected_entry(self):
        sel = self.tree.selection()
        if not sel:
            return
        entry_id = int(sel[0])
        # Find and delete entry by entry_id
        self.cfg.offsets = [e for e in self.cfg.offsets if e.entry_id != entry_id]
        self._refresh_offsets_tree()
        self._refresh_playback_offsets()  # Update playback tab too

    # ---- Playback simulation methods ----

    def _refresh_playback_offsets(self):
        """Refresh the read-only offset list in playback tab."""
        if not hasattr(self, 'playback_tree'):
            return
        for row in self.playback_tree.get_children():
            self.playback_tree.delete(row)
        for e in self.cfg.offsets:
            total_seconds = e.offset_ms // 1000
            minutes = total_seconds // 60
            seconds = total_seconds % 60
            offset_display = f"{minutes}m {seconds}s"
            self.playback_tree.insert("", "end", iid=str(e.entry_id), 
                                     values=(e.entry_id, e.rekordbox_id, e.title, offset_display))

    def playback_load_file(self):
        path = filedialog.askopenfilename(
            filetypes=[("Audio Files", "*.mp3 *.wav *.flac *.ogg *.m4a"), ("All Files", "*.*")],
            title="Load Audio File"
        )
        if not path:
            return

        try:
            # Analyze BPM with librosa (this takes a moment)
            self.lbl_playback_info.configure(text="Analyzing BPM...")
            self.update()
            
            # Load audio and analyze BPM
            y, sr = librosa.load(path, sr=None)
            tempo, _ = librosa.beat.beat_track(y=y, sr=sr)
            self.playback_bpm = float(tempo)
            self.playback_duration = librosa.get_duration(y=y, sr=sr)
            
            # Load audio data for playback with soundfile (don't force 2D)
            audio_data, samplerate = sf.read(path, dtype='float32')
            
            # Ensure we have the right shape (samples, channels) for sounddevice
            if audio_data.ndim == 1:
                # Mono audio - reshape to (samples, 1)
                audio_data = audio_data.reshape(-1, 1)
            
            # Ensure data is C-contiguous for sounddevice compatibility
            if not audio_data.flags['C_CONTIGUOUS']:
                audio_data = np.ascontiguousarray(audio_data)
            
            print(f"Audio loaded: shape={audio_data.shape}, dtype={audio_data.dtype}, sr={samplerate}, contiguous={audio_data.flags['C_CONTIGUOUS']}")
            
            self.playback_audio_data = audio_data
            self.playback_samplerate = int(samplerate)
            self.playback_audio_file = path
            self.playback_start_sample = 0
            
            # Update UI
            filename = path.split("/")[-1]
            self.lbl_playback_file.configure(text=f"{filename} ({self.playback_duration:.1f}s, {self.playback_bpm:.1f} BPM)")
            self.lbl_playback_info.configure(text=f"BPM: {self.playback_bpm:.1f}, Duration: {int(self.playback_duration//60)}:{int(self.playback_duration%60):02d}")
            
            # Enable controls
            self.btn_playback_play.config(state="normal")
            self.playback_slider.config(state="normal", to=self.playback_duration)
            
        except Exception as e:
            messagebox.showerror("Error", f"Could not load audio file:\n{e}")
            self.lbl_playback_info.configure(text="Error loading file")

    def playback_play(self):
        if not self.playback_audio_file:
            return
        
        # If resuming from pause
        if self.playback_paused:
            self.playback_paused = False
            self.playback_is_playing = True
            self.playback_start_time = time.time()
            self.btn_playback_play.config(state="disabled")
            self.btn_playback_pause.config(state="normal")

            # Restart audio thread from current position
            slider_pos = self.playback_slider.get()
            self.playback_start_sample = int(slider_pos * self.playback_samplerate)
            
            self.playback_audio_thread = threading.Thread(target=self._audio_playback_thread, daemon=True)
            self.playback_audio_thread.start()
            return
        
        # Get selected offset entry
        sel = self.playback_tree.selection()
        if not sel:
            messagebox.showwarning("No Selection", "Please select an offset entry first.")
            return
        
        entry_id = int(sel[0])
        for e in self.cfg.offsets:
            if e.entry_id == entry_id:
                self.playback_selected_entry = e
                break
        
        if not self.playback_selected_entry:
            return
        
        # Enter simulation mode
        self.state.set_simulation_mode(True)
        self._update_mode_indicators()
        
        # Get playback position from slider
        slider_pos = self.playback_slider.get()
        self.playback_start_sample = int(slider_pos * self.playback_samplerate)
        self.playback_start_time = time.time()
        
        self.playback_is_playing = True
        self.playback_paused = False
        self.btn_playback_play.config(state="disabled")
        self.btn_playback_pause.config(state="normal")
        self.btn_playback_stop.config(state="normal")
        
        # Update info with offset being used
        offset_secs = self.playback_selected_entry.offset_ms // 1000
        offset_mins = offset_secs // 60
        offset_sec = offset_secs % 60
        self.lbl_playback_info.configure(
            text=f"BPM: {self.playback_bpm:.1f}, Duration: {int(self.playback_duration//60)}:{int(self.playback_duration%60):02d}, Offset: {offset_mins}m {offset_sec}s"
        )
        
        # Stop any existing audio first
        sd.stop()
        time.sleep(0.1)  # Give time for audio to stop
        
        # Start audio playback in background thread
        self.playback_stop_event.clear()
        self.playback_audio_thread = threading.Thread(target=self._audio_playback_thread, daemon=True)
        self.playback_audio_thread.start()
        
        # Start simulation thread for OSC updates
        self.playback_thread = threading.Thread(target=self._playback_simulation_loop, daemon=True)
        self.playback_thread.start()

    def playback_pause(self):
        self.playback_is_playing = False
        self.playback_paused = True
        self.playback_pause_time = time.time()
        # Don't need to stop sd here - the audio thread will handle it
        self.btn_playback_play.config(state="normal")
        self.btn_playback_pause.config(state="disabled")

    def playback_stop(self):
        self.playback_is_playing = False
        self.playback_paused = False
        self.playback_stop_event.set()
        
        # Stop audio and wait for threads to finish
        with self.playback_audio_lock:
            sd.stop()
            time.sleep(0.1)  # Give audio time to fully stop
        
        # Wait for audio thread to finish
        if self.playback_audio_thread and self.playback_audio_thread.is_alive():
            self.playback_audio_thread.join(timeout=0.5)
        
        # Exit simulation mode
        self.state.set_simulation_mode(False)
        self._update_mode_indicators()
        
        # Reset controls
        self.btn_playback_play.config(state="normal")
        self.btn_playback_pause.config(state="disabled")
        self.btn_playback_stop.config(state="disabled")
        self.playback_slider.set(0)
        self.playback_start_sample = 0
        self.lbl_playback_pos.configure(text="00:00 / 00:00")

    def playback_slider_press(self, event):
        """Handle slider grab - pause if playing."""
        if self.playback_is_playing and not self.playback_paused:
            self.playback_was_playing_before_seek = True
            self.playback_pause()
        else:
            self.playback_was_playing_before_seek = False
    
    def playback_slider_release(self, event):
        """Handle slider release - resume if was playing before."""
        if self.playback_was_playing_before_seek:
            self.playback_was_playing_before_seek = False
            # use self.playback_pause_time to pause at least 0.2 seconds
            elapsed = time.time() - self.playback_pause_time
            min_pause = 0.5
            if elapsed < min_pause:
                time.sleep(min_pause - elapsed)
            self.playback_play()
    
    def playback_seek(self, value):
        # Ignore if we're just updating the slider during playback
        if self.playback_slider_updating:
            return
            
        if not self.playback_audio_file:
            return
        
        # Only update position if paused (slider press/release handles play/pause)
        pos = float(value)
        self.playback_start_sample = int(pos * self.playback_samplerate)

    def _audio_playback_thread(self):
        """Audio playback thread using sounddevice.OutputStream for better macOS compatibility."""
        stream = None
        try:
            with self.playback_audio_lock:
                # Double-check we should still be playing
                if not self.playback_is_playing or self.playback_paused:
                    return
                
                # Get audio chunk from start position to end
                audio_chunk = self.playback_audio_data[self.playback_start_sample:]
                
                # Ensure audio chunk is valid
                if len(audio_chunk) == 0:
                    return
                
                # Ensure chunk is C-contiguous
                if not audio_chunk.flags['C_CONTIGUOUS']:
                    audio_chunk = np.ascontiguousarray(audio_chunk)
                
                num_channels = audio_chunk.shape[1] if audio_chunk.ndim > 1 else 1
                print(f"Playing audio: chunk shape={audio_chunk.shape}, dtype={audio_chunk.dtype}, sr={self.playback_samplerate}, channels={num_channels}")
                
                # Create stream with explicit parameters for macOS compatibility
                stream = sd.OutputStream(
                    samplerate=self.playback_samplerate,
                    channels=num_channels,
                    dtype='float32',
                    blocksize=2048  # Smaller blocksize for lower latency
                )
                
                # Start the stream
                stream.start()
            
            # Write audio data in chunks (outside lock)
            chunk_size = 4096
            position = 0
            
            while position < len(audio_chunk):
                # Check if we should stop
                if not self.playback_is_playing or self.playback_paused or self.playback_stop_event.is_set():
                    break
                    
                end_pos = min(position + chunk_size, len(audio_chunk))
                chunk = audio_chunk[position:end_pos]
                
                try:
                    stream.write(chunk)
                    position = end_pos
                except Exception as e:
                    print(f"Stream write error: {e}")
                    break
            
            # Clean up stream
            if stream:
                stream.stop()
                stream.close()
            
            # Playback finished naturally (not paused or stopped)
            if self.playback_is_playing and not self.playback_paused and not self.playback_stop_event.is_set():
                self.after(0, self.playback_stop)
                
        except Exception as e:
            print(f"Audio playback error: {e}")
            import traceback
            traceback.print_exc()
            if stream:
                try:
                    stream.stop()
                    stream.close()
                except:
                    pass
    
    def _playback_simulation_loop(self):
        """Background thread that sends simulated OSC data and updates UI."""
        last_ui_update = 0
        while not self.playback_stop_event.is_set():
            if not self.playback_is_playing or self.playback_paused:
                time.sleep(0.1)
                continue
            
            # Calculate current position based on time elapsed
            elapsed = time.time() - self.playback_start_time
            pos = (self.playback_start_sample / self.playback_samplerate) + elapsed
            
            # Check if we've reached the end
            if pos >= self.playback_duration:
                self.after(0, self.playback_stop)
                break
            
            track_time_ms = int(pos * 1000)
            
            # Send simulated OSC data (use a simulated device_id for playback)
            bpm_changed, player_list_changed, active_changed = self.state.update_from_osc(
                "SIM1",  # simulated device ID
                False,  # is_on_air = False for simulation
                track_time_ms,
                self.playback_selected_entry.rekordbox_id,
                self.playback_selected_entry.title,
                self.playback_bpm
            )
            
            if bpm_changed and self.osc_sender:
                self.after(0, lambda: self.osc_sender.send_bpm_update(self.playback_bpm))
            
            # Update UI less frequently (2Hz) to avoid overhead
            now = time.time()
            if now - last_ui_update >= 0.5:
                last_ui_update = now
                mins = int(pos // 60)
                secs = int(pos % 60)
                total_mins = int(self.playback_duration // 60)
                total_secs = int(self.playback_duration % 60)
            
                def update_ui():
                    self.lbl_playback_pos.configure(text=f"{mins:02d}:{secs:02d} / {total_mins:02d}:{total_secs:02d}")
                    self.playback_slider_updating = True
                    self.playback_slider.set(pos)
                    self.playback_slider_updating = False
                
                self.after(0, update_ui)
            
            time.sleep(0.05)  # 20Hz loop for smooth OSC data

    def _update_mode_indicators(self):
        """Update mode indicator labels in both tabs."""
        is_sim = self.state.is_simulation_mode()
        mode_text = "SIMULATION MODE" if is_sim else "LIVE OSC"
        mode_color = "red" if is_sim else "green"
        
        self.lbl_playback_mode.configure(text=mode_text, foreground=mode_color)
        self.lbl_status_mode.configure(text=mode_text, foreground=mode_color)

    # ---- Start/stop services ----

    def start_services(self):
        self.apply_ui_to_config()

        if self.osc or self.artnet or self.osc_sender:
            messagebox.showinfo("Already running", "Services are already running.")
            return

        try:
            self.osc = OscReceiver(self.cfg, self.state, self.ui_queue)
            self.osc.start()
        except Exception as e:
            self.osc = None
            messagebox.showerror("OSC error", f"Could not start OSC server:\n{e}")
            return

        try:
            self.artnet = ArtnetSender(self.cfg, self.state, self.ui_queue)
            self.artnet.start()
        except Exception as e:
            self.artnet = None
            messagebox.showerror("Art-Net error", f"Could not start Art-Net sender:\n{e}")
            if self.osc:
                self.osc.stop()
                self.osc = None
            return

        try:
            self.osc_sender = OscSender(self.cfg, self.state, self.ui_queue)
            self.osc_sender.start()
        except Exception as e:
            self.osc_sender = None
            messagebox.showerror("OSC Sender error", f"Could not start OSC sender:\n{e}")
            if self.osc:
                self.osc.stop()
                self.osc = None
            if self.artnet:
                self.artnet.stop()
                self.artnet = None
            return

        self.btn_start.configure(state="disabled")
        self.btn_stop.configure(state="normal")
        self.ui_queue.put(("info", "Started OSC + Art-Net + OSC Output"))

    def stop_services(self):
        if self.osc:
            self.osc.stop()
            self.osc = None
        if self.artnet:
            self.artnet.stop()
            self.artnet = None
        if self.osc_sender:
            self.osc_sender.stop()
            self.osc_sender = None
        self.btn_start.configure(state="normal")
        self.btn_stop.configure(state="disabled")
        self.ui_queue.put(("info", "Stopped"))

    # ---- UI updates ----

    def _poll_ui_queue(self):
        try:
            while True:
                kind, payload = self.ui_queue.get_nowait()
                if kind == "error":
                    self.lbl_err.configure(text=str(payload))
                elif kind == "osc_update":
                    # payload is (bpm_changed, player_list_changed, active_changed)
                    bpm_changed, player_list_changed, active_changed = payload
                    if bpm_changed and self.osc_sender:
                        track, _, _, _ = self.state.snapshot()
                        self.osc_sender.send_bpm_update(track.bpm)
                    if player_list_changed:
                        self._update_player_buttons()
                    if active_changed:
                        self._update_player_selection()
                    self._refresh_status()
                elif kind == "osc_sent":
                    # payload is (bpm1, bpm2)
                    bpm1, bpm2 = payload
                    self.lbl_osc_out.configure(text=f"OSC Output: Sent BPM {bpm1:.2f} / {bpm2:.2f}")
                elif kind in ("match_update", "tick", "info"):
                    self._refresh_status()
                self.ui_queue.task_done()
        except queue.Empty:
            pass
        self.after(50, self._poll_ui_queue)

    def _update_player_buttons(self):
        """Update the player selector buttons based on current players."""
        players = self.state.get_players()
        
        # Add buttons for new players
        for device_id, player in players.items():
            if device_id not in self.player_buttons:
                # Create frame for this player
                player_frame = ttk.Frame(self.player_selector_frame)
                player_frame.pack(fill="x", padx=5, pady=2)
                
                # Create toggle button
                btn = ttk.Button(
                    player_frame,
                    text=f"Device {device_id}",
                    command=lambda did=device_id: self._select_player(did),
                    width=15
                )
                btn.pack(side="left", padx=(0, 10))
                
                # Create label for track title
                lbl = ttk.Label(player_frame, text="-")
                lbl.pack(side="left", fill="x", expand=True)
                
                self.player_buttons[device_id] = (btn, lbl, player_frame)
        
        # Update labels with current track info
        for device_id, player in players.items():
            if device_id in self.player_buttons:
                _, lbl, _ = self.player_buttons[device_id]
                title = player.title or "(no title)"
                on_air_marker = " [ON AIR]" if player.is_on_air else ""
                lbl.configure(text=f"{title}{on_air_marker}")
        
        # Update button states
        self._update_player_selection()
    
    def _update_player_selection(self):
        """Update button states to reflect active player."""
        active_id = self.state.get_active_player_id()
        
        for device_id, (btn, lbl, frame) in self.player_buttons.items():
            if device_id == active_id:
                # Highlight active player button
                btn.state(['pressed'])
            else:
                btn.state(['!pressed'])
    
    def _select_player(self, device_id: str):
        """Manually select a player."""
        changed = self.state.set_active_player(device_id)
        if changed:
            self._update_player_selection()
            self._refresh_status()
            # Send BPM update if needed
            if self.osc_sender:
                track, _, _, _ = self.state.snapshot()
                if track.bpm > 0:
                    self.osc_sender.send_bpm_update(track.bpm)

    def _refresh_status(self):
        track, matched_offset_ms, matched_label, signal_ok = self.state.snapshot()

        nowm = time.monotonic()
        age = nowm - float(track.last_recv_monotonic or 0.0)

        # Flash signal label red if no signal for > 1 seconds, green when OK
        if signal_ok and track.last_recv_monotonic > 0:
            if age > 1.0:
                # Flash red/orange when signal is old
                self._flash_state = not self._flash_state
                flash_color = "red" if self._flash_state else "orange"
                self.lbl_signal.configure(text=f"Signal: OK (last OSC {age:.2f}s ago)", foreground=flash_color)
            else:
                # Green when signal is recent
                self._flash_state = False
                self.lbl_signal.configure(text=f"Signal: OK (last OSC {age:.2f}s ago)", foreground="green")
        else:
            self._flash_state = False
            self.lbl_signal.configure(text="Signal: (waiting for OSC)", foreground="black")

        rate = self.state.osc_updates_per_sec(window_s=1.0)
        self.lbl_osc_rate.configure(text=f"OSC updates/sec: {rate:.1f}")

        rid = track.rekordbox_id or "-"
        title = track.title or "-"
        self.lbl_track.configure(text=f"Track: ID={rid} | Title={title} | track-time-reached={track.track_time_ms} ms")

        self.lbl_bpm.configure(text=f"BPM: {track.bpm:.2f}" if track.bpm > 0 else "BPM: -")

        self.lbl_match.configure(text=f"Offset match: {matched_label} | Global shift: {self.cfg.global_shift_ms} ms")

        if signal_ok and track.last_recv_monotonic > 0:
            if age <= float(self.cfg.extrapolate_timeout_s):
                effective_ms = track.last_recv_time_ms + int(age * 1000.0)
            else:
                effective_ms = track.last_recv_time_ms
            effective_ms += int(matched_offset_ms) + int(self.cfg.global_shift_ms)
        else:
            effective_ms = 0

        h, m, s, f = ms_to_timecode_fields(effective_ms, fps=int(self.cfg.artnet_fps))
        self.lbl_tc.configure(text=f"Timecode: {h:02d}:{m:02d}:{s:02d}:{f:02d}  (Type=30 ND)")

    def on_close(self):
        # Stop playback if active
        if hasattr(self, 'playback_is_playing') and self.playback_is_playing:
            self.playback_stop()
        
        # Ensure all audio is stopped
        sd.stop()
        
        self.stop_services()
        self.destroy()


def main():
    if Dispatcher is None or ThreadingOSCUDPServer is None:
        print("Missing dependency: python-osc")
        print("Install with: pip install python-osc")
        return

    app = App()
    app.protocol("WM_DELETE_WINDOW", app.on_close)
    app.mainloop()


if __name__ == "__main__":
    main()
