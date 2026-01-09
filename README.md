[![License: NCPUL](https://img.shields.io/badge/license-NCPUL-blue.svg)](./LICENSE.md)

# CDJ to GrandMA3 - Beat Link Trigger to Art-Net Timecode Bridge

Quick and dirty solution to sync Pioneer CDJ timecode to GrandMA3 lighting consoles via Art-Net timecode.

## What it does

This project bridges [Beat Link Trigger](https://github.com/Deep-Symmetry/beat-link-trigger) with lighting consoles that support Art-Net timecode (like GrandMA3). It receives track playback information from Beat Link Trigger via OSC and converts it to Art-Net timecode packets.

**Features:**
- Receives track time, title, and BPM from Beat Link Trigger via OSC
- Sends Art-Net timecode (ArtTimeCode) to lighting consoles
- Per-track time offset configuration (for cueing specific moments)
- Fuzzy track matching by title or Rekordbox ID
- GUI for managing offsets and configuration
- Optional audio playback simulation for testing without CDJs
- OSC output for speed master control

## Quick Start

1. Install system dependencies (macOS):
```bash
brew install portaudio
```

2. Install Python dependencies:
```bash
pip install -r requirements.txt
```

2. Import the Beat Link Trigger configuration:
   - Open [Beat Link Trigger](https://github.com/Deep-Symmetry/beat-link-trigger)
   - Import the `python_export_trigger.bltx` file
   - This configures BLT to send OSC messages to localhost:9000

3. Run the Python bridge:
```bash
python blt_osc_to_artnet_timecode.py
```

4. Configure your Art-Net target IP in the GUI (usually your lighting console's IP)

5. Play tracks on your CDJs - timecode should now be sent to your console

## Misc info
- BLT Trigger script is made to be used on the same machine as this Python app (localhost)

## How it works

1. Beat Link Trigger tracks CDJ playback and sends track time + metadata via OSC (`/blt/track`)
2. Python app receives OSC, applies configured offsets, and sends Art-Net timecode packets
3. Lighting console receives timecode and can trigger cues accordingly

## Configuration

- **Art-Net Settings:** Target IP, broadcast mode, FPS (24/25/29.97/30)
- **Track Offsets:** Add per-track time offsets by Rekordbox ID or title
- **Global Shift:** Apply a global time offset to all tracks
- **Speed Masters:** Optional OSC output for tempo-based speed control

## License

See [LICENSE.md](./LICENSE.md)
