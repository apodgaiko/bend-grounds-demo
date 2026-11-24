#!/bin/bash
# Reconstruct the pinned Bend 2 toolchain on another machine.
set -eu
cd "$(dirname "$0")/.."
PIN=52637f747b1f7e08263b7853ffd7204262d8e41e
command -v bun >/dev/null || { echo 'Install Bun first: https://bun.sh'; exit 1; }
command -v cc >/dev/null || { echo 'A C compiler is required (macOS: xcode-select --install).'; exit 1; }
if [ ! -d vendor/bend/.git ]; then
  mkdir -p vendor
  git clone https://github.com/bendlang/bend.git vendor/bend
  git -C vendor/bend checkout "$PIN"
fi
ACTUAL=$(git -C vendor/bend rev-parse HEAD)
if [ "$ACTUAL" != "$PIN" ]; then
  echo "Unexpected Bend revision: $ACTUAL (expected $PIN)."
  echo 'Preserving the existing checkout. Restore the pinned revision yourself.'
  exit 1
fi
bun vendor/bend/bend2/main.ts --help | head -1
printf '\nToolchain ready. Run bash scripts/build.sh.\n'
