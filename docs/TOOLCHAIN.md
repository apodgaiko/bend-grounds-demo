# Toolchain and native runtime

## Which Bend?

This project targets the **Bend 2** implementation at [bendlang/bend](https://github.com/bendlang/bend), pinned to:

```text
52637f747b1f7e08263b7853ffd7204262d8e41e
```

The upstream compiler is licensed under **Apache-2.0**; its license identifies **Copyright 2026 HigherOrderCO**. `setup.sh` fetches that compiler from the repository above at the exact pinned commit. The compiler checkout is a local build dependency, not redistributed as part of this source release; its license is available in the fetched `vendor/bend/LICENSE`.

The original Bend Grounds game code and documentation are licensed under the [MIT License](../LICENSE), copyright 2026 Aleksandr Podgaiko. The Bend compiler remains separately licensed under Apache-2.0; the project's MIT license does not replace the compiler's license or notices.

It is not a project targeting the original Bend implementation commonly associated with HVM. Compiler capabilities are not application benchmarks: Bend Grounds makes no GPU-execution, automatic-parallelism or current speed claim.

## Prerequisites

For setup, building and play:

- Git and Bun;
- a Clang toolchain accepted by the pinned compiler;
- Python 3 (standard library only for game clients and build helpers);
- `shasum` and `curl` for build/start helpers.

The development baseline is macOS. Other platforms are not claimed supported by these instructions. The optional `Play.command` launcher uses macOS `open`; the foreground server command does not open a browser.

Kernel proof checks additionally require **Lean v4.34.0**, including `lean` and `leanc`, normally installed through elan:

```sh
elan toolchain install leanprover/lean4:v4.34.0
```

The canonical release gate, `bash scripts/verify.sh`, requires both the Lean toolchain above and Node.js. Node.js is used for the browser JavaScript syntax check; browser-helper tests also need it. The gate uses its own isolated HTTP server on `BG_VERIFY_PORT` (default 18965) and refuses an occupied port; see [Verification](VERIFICATION.md) for its eight `--verdict` files and finite-test scope.

## Setup and build

From the repository root:

```sh
bash scripts/setup.sh
bash scripts/build.sh
```

`setup.sh` clones the upstream compiler into `vendor/bend` when absent and checks out the pin. An existing checkout at a different revision is refused rather than overwritten. `build.sh` also requires a clean compiler checkout; do not modify the compiler or standard library to bypass a failed check.

The compiler command is:

```sh
bun vendor/bend/bend2/main.ts
```

The native build path emits C and invokes Clang. Bun executes the compiler; the resulting game executables do not require a JavaScript server process.

| Output | Entry point | Purpose |
| --- | --- | --- |
| `build/server` | `engine/main.bend` | Native HTTP/static-file server and command-line entry points. |
| `build/cli` | `engine/cli.bend` | Full-transcript replay oracle. |
| `build/runner` | `engine/runner.bend` | Persistent process with incremental game steps. |

The entry points share `engine/game.bend` and `engine/econ.bend`. Builds record source/compiler/binary provenance in manifests. Native agent transports refuse missing or stale builds; there is no silent fallback.

Run the HTTP server from the repository root so it can serve `web/`:

```sh
bash scripts/start.sh --fg
```

Open `http://127.0.0.1:8765`. Set `BG_PORT` to choose another local port, for example `BG_PORT=8766 bash scripts/start.sh --fg`, then open `http://127.0.0.1:8766`. The server binds loopback, not a public network interface. Stop a foreground server with Ctrl+C.

`bash scripts/start.sh` starts in the background; `./Play.command` uses that mode and opens the browser on macOS. There is no automatic stop command. Inspect a background server's process before stopping it; PID files are informational only, since a stale PID could identify an unrelated process.

Rebuild after changing engine sources. The helper checks binary provenance and refuses a launch if a server already answers on the selected port, rather than adopting an unverified running process. Identify and stop that process explicitly, or select another `BG_PORT`.

## Build checks versus proof checks

The normal build checks the engine and reports an economy-proof checker result. That report is not the complete proof suite and is not a `--verdict` kernel run. A successful native build therefore does not establish that all laws or HTTP/UI tests passed.

`--verdict` rechecks proof output with **BendTT, a kernel written in Lean**, provided by the pinned compiler. This is distinct from ordinary Bend type checking and from testing concrete game scenarios. See [Verification](VERIFICATION.md) for focused commands and boundaries.
