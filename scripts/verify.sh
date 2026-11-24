#!/bin/bash
# Source-based local release gate; no archived binaries or research fixtures.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$HOME/.bun/bin:$PATH"
unset BG_CLI BG_URL BG_PROTO_URL BG_RUNNER BG_ORACLE BG_BACKEND V4_BUILD_DIR BENDTT BG_PROOFS BG_STRICT BG_RUNNER_BUILD
mkdir -p evidence build
bash scripts/build.sh
python3 scripts/build_manifest.py check build/server build/cli
node --check web/app.js
python3 tests/release_regression_test.py
node tests/web_regression_test.js
python3 tests/strategy_test.py --backend fast --seeds 1-3 --json evidence/public-strategy.json
python3 tests/fast_runner_test.py --quick --no-http
PORT="${BG_VERIFY_PORT:-18965}"
[[ "$PORT" =~ ^[0-9]{1,5}$ ]] && [ "$PORT" -ge 1 ] && [ "$PORT" -le 65535 ] || { echo 'BG_VERIFY_PORT must be 1..65535' >&2; exit 1; }
# Refuse occupied ports before launching, and never adopt an existing server.
python3 - "$PORT" <<'PY'
import socket, sys
with socket.socket() as s:
    s.bind(('127.0.0.1', int(sys.argv[1])))
PY
./build/server serve "$PORT" >build/public-http.log 2>&1 &
SERVER_PID=$!
cleanup() { kill "$SERVER_PID" 2>/dev/null || true; wait "$SERVER_PID" 2>/dev/null || true; }
trap cleanup EXIT
export BG_URL="http://127.0.0.1:$PORT" BG_PROTO_URL="http://127.0.0.1:$PORT" BG_BACKEND=http
READY=0
for _ in $(seq 1 50); do
  kill -0 "$SERVER_PID" 2>/dev/null || { echo 'Test server exited' >&2; exit 1; }
  if curl -fsS --max-time 2 "$BG_URL/api/health" >/dev/null; then READY=1; break; fi
  sleep 0.1
done
[ "$READY" = 1 ] || { echo 'Test server readiness timed out' >&2; exit 1; }
for suite in api_test http_security_test protocol_v3_test v4_protocol_plumbing_test card_interactions_test; do
  python3 "tests/$suite.py" 2>&1 | tee "evidence/public-$suite.log"
  if grep -qiE '\.\.\. skipped|skipped=[0-9]|^SKIP' "evidence/public-$suite.log"; then
    echo "Unexpected skipped HTTP case in $suite" >&2; exit 1
  fi
done
cleanup
trap - EXIT
unset BG_URL BG_PROTO_URL BG_BACKEND
for file in PROOF.bend engine/game.bend tests/engine_invariants.bend tests/action_laws.bend \
  tests/damage_laws.bend tests/v4_golden_laws.bend tests/v3_growth_laws.bend tests/card_interactions.bend; do
  bun vendor/bend/bend2/main.ts "$file" --verdict
done
printf '\nSource-based verification complete. No full-game correctness or bot-strength claim.\n'
