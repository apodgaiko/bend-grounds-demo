#!/bin/bash
# Build the fast simulation runner (engine/runner.bend) against an engine
# tree, with the pinned, unmodified compiler in vendor/bend, and write a
# provenance manifest next to the binary.
#
#   bash scripts/build_runner.sh                       engine/ -> build/runner
#   bash scripts/build_runner.sh ENGINE_DIR [OUT]      e.g.
#   bash scripts/build_runner.sh build/candidate/engine build/candidate/runner
#
# ENGINE_DIR must hold game.bend and econ.bend. The runner source is always
# engine/runner.bend: it is copied next to that tree's rules into a scratch
# directory, so no rule is duplicated or edited.
# Output: OUT and OUT.manifest.json (validated by scripts/fast_runner.py).
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$(pwd)
export PATH="$HOME/.bun/bin:$HOME/.elan/bin:$HOME/.local/bin:/opt/homebrew/bin:$PATH"
PIN=52637f747b1f7e08263b7853ffd7204262d8e41e
BEND=(bun "$ROOT/vendor/bend/bend2/main.ts")
ENGINE_DIR=${1:-engine}
OUT=${2:-build/runner}

die() { echo "build_runner: $*" >&2; exit 1; }
[ -f vendor/bend/bend2/main.ts ] || die "missing toolchain: run bash scripts/setup.sh"
HEAD=$(git -C vendor/bend rev-parse HEAD)
[ "$HEAD" = "$PIN" ] || die "vendor/bend is at $HEAD, expected pin $PIN"
git -C vendor/bend diff HEAD --quiet || die "vendor/bend has local edits; refusing to build"
[ -z "$(git -C vendor/bend status --porcelain --untracked-files=all)" ] || die "vendor/bend is not clean; refusing to build"
[ -f "$ENGINE_DIR/game.bend" ] || die "$ENGINE_DIR/game.bend not found"
[ -f "$ENGINE_DIR/econ.bend" ] || die "$ENGINE_DIR/econ.bend not found"
[ -f engine/runner.bend ] || die "engine/runner.bend not found"
# the rules may import only Base and ./econ.bend (so the scratch copy is complete)
BAD=$(grep -h '^import' "$ENGINE_DIR/game.bend" "$ENGINE_DIR/econ.bend" | grep -v -e '^import Base$' -e '^import ./econ.bend as Econ$' || true)
[ -z "$BAD" ] || die "unexpected imports in $ENGINE_DIR: $BAD"

ENGINE_ABS=$(cd "$ENGINE_DIR" && pwd)
case "$ENGINE_ABS" in "$ROOT"/*) ENGINE_REL=${ENGINE_ABS#"$ROOT"/} ;; *) ENGINE_REL=$ENGINE_ABS ;; esac
mkdir -p "$(dirname "$OUT")"
SRC=$(mktemp -d "$ROOT/build/.runner-src.XXXXXX")
trap 'rm -rf "$SRC"' EXIT
cp "$ENGINE_DIR/game.bend" "$ENGINE_DIR/econ.bend" engine/runner.bend "$SRC/"
sha() { shasum -a 256 "$1" | cut -d' ' -f1; }
SG=$(sha "$SRC/game.bend"); SE=$(sha "$SRC/econ.bend"); SR=$(sha "$SRC/runner.bend")

# The check must name exactly the read loop as @unsafe; any error is fatal.
echo "== check runner.bend against $ENGINE_REL"
CHK=$("${BEND[@]}" "$SRC/runner.bend" --check-only 2>&1 || true)
echo "$CHK"
echo "$CHK" | grep -qx "defs that depend on @unsafe: loop, next, main" || die "runner.bend check failed"
! echo "$CHK" | grep -q "^- message" || die "runner.bend has errors"

OUT_ABS="$(cd "$(dirname "$OUT")" && pwd)/$(basename "$OUT")"
case "$OUT_ABS" in "$ROOT"/*) OUT_REL=${OUT_ABS#"$ROOT"/} ;; *) OUT_REL=$OUT_ABS ;; esac
echo "== compile $OUT_REL"
"${BEND[@]}" "$SRC/runner.bend" -o "$OUT_ABS.tmp"
H=$(printf 'health\n' | "$OUT_ABS.tmp")
case "$H" in '200 {"ok":true,"runner":"fast-runner/1"'*) ;; *) rm -f "$OUT_ABS.tmp"; die "runner smoke failed: $H" ;; esac
RULES_LINE=$(printf 'rules\n' | "$OUT_ABS.tmp")
case "$RULES_LINE" in '200 {'*) ;; *) rm -f "$OUT_ABS.tmp"; die "runner rules failed" ;; esac
# sha256 of the rules body bytes (the line after "200 ", without its newline)
RULES_SHA=$(printf '%s' "${RULES_LINE#200 }" | shasum -a 256 | cut -d' ' -f1)
# The binary was compiled from the scratch copies hashed above. Refuse to
# publish if the tree sources or the compiler changed meanwhile.
[ "$(sha "$ENGINE_DIR/game.bend")" = "$SG" ] || { rm -f "$OUT_ABS.tmp"; die "$ENGINE_DIR/game.bend changed during the build"; }
[ "$(sha "$ENGINE_DIR/econ.bend")" = "$SE" ] || { rm -f "$OUT_ABS.tmp"; die "$ENGINE_DIR/econ.bend changed during the build"; }
[ "$(sha engine/runner.bend)" = "$SR" ] || { rm -f "$OUT_ABS.tmp"; die "engine/runner.bend changed during the build"; }
[ "$(git -C vendor/bend rev-parse HEAD)" = "$PIN" ] && git -C vendor/bend diff HEAD --quiet \
  && [ -z "$(git -C vendor/bend status --porcelain --untracked-files=all)" ] || { rm -f "$OUT_ABS.tmp"; die "vendor/bend changed during the build"; }
BIN_SHA=$(sha "$OUT_ABS.tmp"); BIN_BYTES=$(wc -c < "$OUT_ABS.tmp" | tr -d ' ')
BUNV=$(bun --version)
NOW=$(date -u +%Y-%m-%dT%H:%M:%SZ)
cat > "$OUT_ABS.manifest.json.tmp" <<EOF
{"kind":"bend-grounds-runner","manifestVersion":1,"protocol":"fast-runner/1","engineDir":"$ENGINE_REL","sources":{"game.bend":"$SG","econ.bend":"$SE","runner.bend":"$SR"},"compiler":{"repo":"vendor/bend","commit":"$PIN","clean":true,"bun":"$BUNV"},"binary":{"path":"$OUT_REL","sha256":"$BIN_SHA","bytes":$BIN_BYTES},"rulesSha256":"$RULES_SHA","builtAt":"$NOW"}
EOF
# publish: binary first, then its manifest (a reader in between sees a
# sha mismatch and fails loudly, never a blessed stale binary)
mv "$OUT_ABS.tmp" "$OUT_ABS"
mv "$OUT_ABS.manifest.json.tmp" "$OUT_ABS.manifest.json"
echo "built $OUT ($BIN_BYTES bytes, sha256 $BIN_SHA)"
echo "manifest $OUT.manifest.json (game $SG, econ $SE, runner $SR)"
