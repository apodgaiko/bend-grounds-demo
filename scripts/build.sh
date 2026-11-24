#!/bin/bash
# Build the native Bend 2 server: build/server (from engine/main.bend).
# Uses only the pinned, unmodified compiler in vendor/bend.
#   bash scripts/build.sh            build; report proof status if PROOF.bend exists
#   BG_STRICT=1 bash scripts/build.sh   also fail unless PROOF.bend prints ALL PROOFS CHECK
#   BG_PROOFS=0 bash scripts/build.sh   skip the proof report (faster)
#   BG_RUNNER_BUILD=0 bash scripts/build.sh   skip build/runner (simulations then refuse --backend fast)
# Outputs: build/server (HTTP), build/cli (replay oracle), build/runner (fast backend).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.bun/bin:$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"
PIN=52637f747b1f7e08263b7853ffd7204262d8e41e
BEND=(bun vendor/bend/bend2/main.ts)
mkdir -p build evidence

[ -f vendor/bend/bend2/main.ts ] || { echo "missing toolchain: run bash scripts/setup.sh" >&2; exit 1; }
HEAD=$(git -C vendor/bend rev-parse HEAD)
[ "$HEAD" = "$PIN" ] || { echo "vendor/bend is at $HEAD, expected pin $PIN" >&2; exit 1; }
# clean means: no unstaged or staged edits against HEAD, and no untracked files
git -C vendor/bend diff HEAD --quiet || { echo "vendor/bend has local edits; refusing to build" >&2; exit 1; }
[ -z "$(git -C vendor/bend status --porcelain --untracked-files=all)" ] || { echo "vendor/bend is not clean (git status); refusing to build" >&2; exit 1; }

# 1. The pure engine must check on its own (no @unsafe, no foreign code).
echo "== check engine/game.bend"
"${BEND[@]}" engine/game.bend --check-only

# 2. The server. A check of main.bend always reports SOME PROOFS FAIL,
#    naming the accept loop (@unsafe) and the defs that call it; any other
#    error is fatal.
echo "== check engine/main.bend"
OUT=$("${BEND[@]}" engine/main.bend --check-only 2>&1 || true)
echo "$OUT"
EXPECTED_UNSAFE="defs that depend on @unsafe: serve, serve_on, cli_port, cli_serve, cli_cmd, cli, cli_args, main"
echo "$OUT" | grep -Fxq "$EXPECTED_UNSAFE" || { echo "unexpected server unsafe dependencies" >&2; exit 1; }
if echo "$OUT" | grep -q "^- message"; then echo "engine/main.bend has errors" >&2; exit 1; fi

SERVER_SRC=(engine/main.bend engine/game.bend engine/econ.bend)
CLI_SRC=(engine/cli.bend engine/game.bend engine/econ.bend)
echo "== build build/server"
rm -f build/server.manifest.json
python3 scripts/build_manifest.py snapshot --out build/server.sources.json "${SERVER_SRC[@]}"
"${BEND[@]}" engine/main.bend -o build/server.tmp
mv build/server.tmp build/server
./build/server health >/dev/null || { echo "build/server does not run" >&2; exit 1; }
python3 scripts/build_manifest.py write --binary build/server --snapshot build/server.sources.json

# The replay CLI is the differential oracle for the fast runner and the
# offline transport of agent.py/tests; rebuild it with the server so it can
# never lag behind the engine.
echo "== build build/cli"
rm -f build/cli.manifest.json
python3 scripts/build_manifest.py snapshot --out build/cli.sources.json "${CLI_SRC[@]}"
"${BEND[@]}" engine/cli.bend -o build/cli.tmp
mv build/cli.tmp build/cli
./build/cli rules | grep -q '"protocolVersion":3' || { echo "build/cli does not speak protocol 3" >&2; exit 1; }
python3 scripts/build_manifest.py write --binary build/cli --snapshot build/cli.sources.json

# The accelerated runner (default backend of simulations, scripts/bg_engine.py).
if [ "${BG_RUNNER_BUILD:-1}" != "0" ]; then
  [ -f scripts/build_runner.sh ] || { echo "scripts/build_runner.sh missing: the fast runner is required (BG_RUNNER_BUILD=0 skips it explicitly)" >&2; exit 1; }
  echo "== build build/runner"
  bash scripts/build_runner.sh
fi
# Provenance: build/server and build/cli have BINARY.manifest.json (source,
# compiler and binary hashes, scripts/build_manifest.py); build/runner has the
# runner manifest that scripts/fast_runner.py validates before every spawn.
python3 scripts/build_manifest.py check build/server build/cli

# 3. Proofs: REPORT ONLY by default, so a proof in progress never blocks
#    the server build; BG_STRICT=1 makes a failure fatal. The hard proof
#    gate is scripts/verify.sh, which runs PROOF.bend --verdict (Lean kernel).
if [ "${BG_PROOFS:-1}" != "0" ] && [ -f PROOF.bend ]; then
  echo "== check PROOF.bend"
  P=$("${BEND[@]}" PROOF.bend 2>&1 || true)
  echo "$P" | tail -5
  if echo "$P" | grep -q "ALL PROOFS CHECK"; then
    echo "proofs: ALL PROOFS CHECK (bend2 checker; --verdict kernel run is in scripts/verify.sh)"
  else
    echo "proofs: NOT passing" >&2
    [ "${BG_STRICT:-0}" = "1" ] && exit 1
  fi
fi
echo "built build/server ($(wc -c < build/server | tr -d ' ') bytes)"
