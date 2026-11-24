#!/bin/bash
# Start a provenance-checked local server. Foreground mode is recommended.
set -euo pipefail
cd "$(dirname "$0")/.."
PORT="${BG_PORT:-8765}"
[[ "$PORT" =~ ^[0-9]{1,5}$ ]] && [ "$PORT" -ge 1 ] && [ "$PORT" -le 65535 ] || { echo 'BG_PORT must be 1..65535' >&2; exit 1; }
URL="http://127.0.0.1:$PORT"
case "${1:-}" in
  --stop)
    echo 'Automatic PID-file stopping is disabled: a stale PID can belong to another process.' >&2
    echo 'Use Ctrl-C for a foreground server; otherwise inspect the process before stopping it.' >&2
    exit 1 ;;
  ''|--fg) ;;
  *) echo 'usage: bash scripts/start.sh [--fg]' >&2; exit 2 ;;
esac
mkdir -p build
[ -x build/server ] || bash scripts/build.sh
python3 scripts/build_manifest.py check build/server
if curl -fsS --max-time 2 "$URL/api/health" >/dev/null 2>&1; then
  echo "A server already answers at $URL; refusing to adopt an unverified running process." >&2
  echo 'Stop it explicitly, or select another BG_PORT.' >&2
  exit 1
fi
if [ "${1:-}" = '--fg' ]; then exec ./build/server serve "$PORT"; fi
nohup ./build/server serve "$PORT" >>build/server.log 2>&1 &
PID=$!
echo "$PID" >build/server.pid
for _ in $(seq 1 50); do
  kill -0 "$PID" 2>/dev/null || { echo 'Server exited; see build/server.log' >&2; exit 1; }
  if curl -fsS --max-time 2 "$URL/api/health" >/dev/null 2>&1; then
    echo "Serving $URL (pid $PID; log build/server.log)"
    echo 'For simple lifecycle control use: bash scripts/start.sh --fg'
    exit 0
  fi
  sleep 0.1
done
echo 'Server readiness timed out; inspect build/server.log and the process before restarting.' >&2
exit 1
