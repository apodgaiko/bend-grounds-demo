#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.bun/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"
bash scripts/setup.sh
if ! python3 scripts/build_manifest.py check build/server build/cli; then
  bash scripts/build.sh
fi
if ! bash scripts/start.sh; then
  printf '\nNo existing server was adopted or stopped.\n' >&2
  printf 'If the port is occupied, inspect and stop that server yourself, or choose another port:\n' >&2
  printf '  BG_PORT=8766 bash scripts/start.sh --fg\n' >&2
  printf 'Then open http://127.0.0.1:8766 in your browser.\n' >&2
  read -r -p 'Press Enter to close this launcher. ' _ || true
  exit 1
fi
open "http://127.0.0.1:${BG_PORT:-8765}"
printf '\nBend Grounds — local server started. See build/server.log.\n'
printf 'Inspect the server process before stopping it; PID files are informational only.\n'
