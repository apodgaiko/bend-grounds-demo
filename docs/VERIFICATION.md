# Verification: what the checks establish

Bend Grounds combines executable rules, explicit laws and finite regression tests. These are different kinds of evidence. This document describes their scope and how to invoke them; it is not a claim that the current checkout has passed every command.

For change-specific check selection, use the [development task map](DEVELOPMENT.md) after the [coding-agent entrypoint](../AGENTS.md). This document remains the reference for verification commands and their evidence boundaries.

## Canonical release gate

After setup, run from the repository root:

```sh
bash scripts/verify.sh
# Choose another unused local port if necessary:
BG_VERIFY_PORT=18966 bash scripts/verify.sh
```

The gate requires the build prerequisites, **Node.js** and **Lean v4.34.0**, including `lean` and `leanc` (normally installed through elan; see [Toolchain](TOOLCHAIN.md)). It rebuilds native artifacts, checks server/CLI provenance, checks browser JavaScript syntax, runs finite strategy and runner checks, then starts its own HTTP server on loopback. It uses `BG_VERIFY_PORT` (default 18965), refuses an occupied port instead of adopting a running server, and cleans up the server process it launched.

The HTTP suites cover API, security, protocol 3, protocol plumbing and card interactions, rejecting reported skipped cases. The gate then invokes `--verdict` on these eight files:

1. `PROOF.bend`
2. `engine/game.bend`
3. `tests/engine_invariants.bend`
4. `tests/action_laws.bend`
5. `tests/damage_laws.bend`
6. `tests/v4_golden_laws.bend`
7. `tests/v3_growth_laws.bend`
8. `tests/card_interactions.bend`

`scripts/verify.sh` uses a fixed file list, not automatic discovery. When adding a new proof file, add it to the verdict loop in that script and the list above; a gate PASS alone does not cover an unlisted file. Run and report a focused verdict for the affected file as well.

These files contain different kinds of checks; eight verdict invocations do not mean eight universal full-game proofs. The gate does not automate a complete browser playthrough. The description above follows `scripts/verify.sh`; no current execution result is claimed here.

## 1. Compiler and build checks

```sh
bash scripts/setup.sh
bash scripts/build.sh
python3 scripts/build_manifest.py check build/server build/cli
node --check web/app.js
```

The build checks the pure engine, compiles the native entry points and records provenance. Compiler acceptance is not a proof of every intended game rule. The server includes an explicitly `@unsafe` accept loop (`serve` in `engine/main.bend`); the complete HTTP application is not a total verified program.

## 2. Explicit laws and dependent proof results

With the Lean toolchain in [Toolchain](TOOLCHAIN.md) installed, run from the repository root:

```sh
bun vendor/bend/bend2/main.ts PROOF.bend --verdict
bun vendor/bend/bend2/main.ts tests/engine_invariants.bend --verdict
bun vendor/bend/bend2/main.ts tests/action_laws.bend --verdict
bun vendor/bend/bend2/main.ts tests/damage_laws.bend --verdict
bun vendor/bend/bend2/main.ts tests/v4_golden_laws.bend --verdict
```

For any affected Bend proof file, the general focused command is (replace `<file>` with its repository-relative path):

```sh
bun vendor/bend/bend2/main.ts <file> --verdict
```

The focused run checks only that file and its dependencies; it does not replace the release gate.

These files import the actual economy/engine functions. Representative statements:

| Source / symbol | Scope |
| --- | --- |
| `LAWS.bend` / `spend_pays`; `PROOF.bend` / `Laws.spend_pays` | For all natural-number costs and remainders, an affordable payment succeeds and returns exactly the remainder. |
| `tests/action_laws.bend` / `spend_some` | Payment success is equivalent to sufficient funds, for every natural-number purse and cost. |
| `tests/engine_invariants.bend` / `g_apply_zone_cap` | Given a game satisfying the zone bounds, an action result preserves them. |
| `tests/engine_invariants.bend` / `replay_zone_cap` | Every seed, mode and list of move strings produces a replay state with boards of at most 5 and hands of at most 7. |
| `tests/action_laws.bend` / `legal_sound` | Typed `Act` values retained by `legal_filter` are accepted by `p_apply`; the filter itself tests that acceptance. |

For example, `ZOk(p)` is a proof result indexed by an actual player value, combining evidence of that player's board and hand bounds. This is a dependent-type use, not merely a Boolean assertion checked on a few fixtures. Conversely, the ordinary `Player` record does not itself store a bounded-vector type that makes all invalid states unrepresentable.

### Boundaries

- A finite card scenario remains a finite scenario even if its equality is kernel-checked. Do not count it as a universally quantified invariant.
- Legal-action soundness concerns typed `Act` values, not the JSON `legalActions` strings. It does not prove completeness of the action list or the `act_str` / `parse_move` roundtrip.
- Damage-cap laws bound recorded fight damage; they do not by themselves prove all resulting game-level HP and ranking behavior.
- Golden-assembly laws do not establish every merged-stat or timing property universally.
- There is no proof here of the entire game, strategic balance, HTTP routing, JSON serialization, browser behavior or all combat traces.

## 3. Finite tests and real surfaces

For focused development diagnostics after building, you can run:

```sh
python3 tests/api_test.py
```

This standalone test may reuse an unrelated server already answering at `BG_URL` or the default port, and can start a server if none answers. Its success alone therefore does not establish acceptance of the freshly built sources or binary provenance. Use `bash scripts/verify.sh` for the canonical release gate with its owned isolated server. A native-runner test or CLI replay does not substitute for HTTP routing/security tests.

Other included test files cover protocol handling, card interactions, combat events, runner parity and browser rendering helpers. Run their documented commands against the surfaces they exercise; retain failures and skipped cases as such. A syntax check or a source-level UI test is not a completed browser game.

A small real-surface release check should include:

1. Build from the sanitized checkout with the pinned compiler.
2. Start the resulting native server and inspect health/rules over HTTP.
3. Complete a browser game against bots, including buy, deploy and combat playback.
4. Exercise bot autoplay and copy/reopen a replay link.
5. Run the example agent and verify a saved replay through the CLI client.
6. Run `bash scripts/verify.sh`, recording the actual outcomes rather than substituting individual standalone tests for the gate.

No historical gate count, archived binary checksum or old PASS substitutes for those checks on the release being reviewed. The project makes no current throughput or GPU-performance claim.
