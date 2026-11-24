# Bend Grounds

**A small autobattler with its authoritative game engine and native HTTP backend written in Bend 2.** Play in the browser, watch built-in bots, or bring your own agent.

Four players recruit units, build a warband and fight automatic battles. Spend gold on immediate power or invest in later rounds; combine three copies into a golden unit and scout your next opponent. There are 44 cards, three tribes plus Neutral units, five tiers and up to 14 rounds.

## Why Bend?

Bend is not a wrapper around a JavaScript game here. It owns the game:

- **State and rules:** [game.bend](engine/game.bend) defines players, actions, recruiting, seeded randomness, combat, round transitions and built-in bot policies. [econ.bend](engine/econ.bend) supplies the economy functions those rules use.
- **The interface to the rules:** legal actions, private/public observations, generated card text and JSON encoding also live in Bend. Humans and agents act through the same engine.
- **The native HTTP backend:** [main.bend](engine/main.bend) handles HTTP parsing, routing, static-file responses and TCP serving. There is no Python or JavaScript application server behind it.
- **Executable rules alongside explicit laws:** the proof files import the real engine. They do not prove a separate simplified model and assume it matches the game.

For example, this statement from [LAWS.bend](LAWS.bend) says an affordable payment leaves exactly the remainder, for **every** natural-number cost and remainder:

```bend
law spend_pays:
  for cost: Nat
  for rest: Nat
  {Econ.spend(Nat.add(cost, rest), cost) == Some{rest} : Maybe<&2, Nat>}
```

The corresponding recursive proof is `Laws.spend_pays` in [PROOF.bend](PROOF.bend). This is an equality type referring directly to the `spend` function used by the engine—not a few example balances passing a test.

Other dependent proof results include `g_apply_zone_cap` and `replay_zone_cap` in [engine_invariants.bend](tests/engine_invariants.bend), which express preservation of board and hand bounds through real transitions and transcript replay. `legal_sound` in [action_laws.bend](tests/action_laws.bend) shows that typed `Act` values retained by `legal_filter` are accepted by `p_apply`: the filter itself tests that acceptance. This does not establish that JSON action strings survive the `act_str` / `parse_move` roundtrip, or that the action list is complete.

**Scope matters:** these are selected properties, not full-game correctness or balance. The HTTP server, serialization and complete combat/HP/ranking behavior are not universally verified. The server's unbounded accept loop is explicitly `@unsafe`. See [Verification](docs/VERIFICATION.md).

### What is not Bend?

The browser is vanilla HTML, CSS and JavaScript: it renders observations, submits actions and animates combat events supplied by Bend. Python provides policy plugins, clients, build helpers and tests. Policies choose actions; they do not implement authoritative legality or game transitions.

```text
Browser UI ── HTTP ──> Bend HTTP server ──> Bend rules engine
Agent client ────────> HTTP / native CLI / native runner
                                             └─ same rules engine
```

This targets the pinned **Bend 2** implementation in `bendlang/bend`, not the original Bend implementation commonly associated with HVM. It demonstrates neither GPU execution nor automatic parallel speedups, and makes no current performance claim.

## Build and play locally

Requirements: Git, [Bun](https://bun.sh), a compatible Clang toolchain, Python 3, `curl` and `shasum`. Python game clients use only the standard library. The existing development baseline is macOS; portability is not claimed. See [Toolchain](docs/TOOLCHAIN.md) for the compiler pin and proof prerequisites.

From the repository root:

```sh
bash scripts/setup.sh
bash scripts/build.sh
bash scripts/start.sh --fg
```

Open **http://127.0.0.1:8765** in your browser. Choose **Versus bots** to play one seat against three built-in Bend bots. Stop a foreground server with Ctrl+C.

On macOS, `./Play.command` checks the toolchain and native build provenance, rebuilds if needed, starts a background server and opens the browser. You can also start a background server directly:

```sh
bash scripts/start.sh
```

Foreground mode is recommended for simple lifecycle control. There is no automatic stop command: for a background server, inspect the process before stopping it; PID files are informational only. A second launch refuses to adopt a server already answering on the selected port. Stop that process explicitly after identifying it, or choose another port, for example `BG_PORT=8766 bash scripts/start.sh --fg`.

The build invokes the pinned Bend compiler with Bun and produces three native executables: `build/server`, `build/cli` and `build/runner`, plus provenance manifests. Bun runs the compiler, not the game server. Rebuild after changing Bend sources; the agent transports reject missing or stale native builds rather than silently selecting another backend.

## How to play

Start with 40 HP. Each round brings fresh gold; unspent gold does not carry over.

| Action | What it does |
| --- | --- |
| Buy | Spend 3 gold to put a shop unit in your private hand, up to 7 cards. |
| Deploy | Play a hand card onto your board, up to 5 units. Only the board fights. |
| Sell | Remove a board unit for gold. Hand cards cannot be sold. |
| Reorder | Change board order; the leftmost unit attacks first. |
| Roll / freeze | Pay 1 gold for a new shop, or preserve unsold offers for next round. |
| Upgrade | Unlock higher-tier shop units. Waiting discounts the next upgrade to its floor. |
| Invest | Pay 2 gold for +1 income in later rounds, up to 3 investments. |
| End turn | Resolve end-of-turn effects, bot turns and automatic combat in versus-bots mode. |

Three regular copies across hand and board assemble into one golden card in your hand. Merges can change indexes: agents should read the new observation after each action. The in-game **Rules** panel and `/api/rules` provide the card list, costs and detailed mechanics directly from Bend.

**Watch bots:** open the **Commands** tab and choose **Autoplay to the end**. **Autopilot turn** delegates only the current turn. **Manual control** lets you act for each seat in turn. The **Transcript** tab can copy a replay link.

## Bring an agent

No model service or API key is required. Start with the included Python policy:

```sh
python3 scripts/agent.py rules
python3 scripts/agent.py play --seed 42 --policy scripts/example_policy.py:policy
python3 scripts/agent.py selfplay --seed 42 --policies tempo,econ,random,bot
python3 scripts/agent.py human --seat 0 --policies scripts/example_policy.py:policy,bot,bot
```

These use the persistent native Bend runner by default; a web server is not needed. A custom policy receives the acting seat's observation and returns one string from `legalActions`. Only load trusted policy files: plugins execute local Python code.

To use the same HTTP surface as the browser, with the server running:

```sh
python3 scripts/agent.py --backend http --url http://127.0.0.1:8765 play --seed 42 --policy tempo
curl 'http://127.0.0.1:8765/api/game?seed=42&mode=bots&v=3&moves=buy:0,play:0,end'
```

Save and verify a replay:

```sh
python3 scripts/agent.py play --seed 42 --policy tempo --save build/replay.json
python3 scripts/agent.py replay build/replay.json
```

See [Agent API](docs/AGENTS-API.md) for modes, protocol 3, observations and the plugin contract. This is an interface for writing agents, not a bundled trained language-model opponent.

## Verification and limitations

The canonical source-based release gate is:

```sh
bash scripts/verify.sh
```

In addition to build prerequisites, it requires Node.js and Lean v4.34.0 (`lean` and `leanc`, normally via elan). It rebuilds, checks provenance, exercises native and HTTP regressions against its own isolated server, and runs eight `--verdict` files. The default isolated port is 18965; override it with `BG_VERIFY_PORT`. An occupied port is refused rather than reused.

[Verification](docs/VERIFICATION.md) details the gate, focused checks and their limits. Building the game is not evidence that all proof and integration checks passed; even the gate does not replace a browser playthrough. No current gate PASS or historical acceptance count is claimed here.

The HTTP API replays `(seed, mode, moves)` without server-side game sessions. This makes branching and reproduction straightforward, but permits undo and lookahead. Manual-mode recruiting is sequential, so later seats see earlier seats' updated boards. This is a local game and agent playground—not authenticated multiplayer, secure ranked play, or a claim of balanced strategies.

## License and attribution

Bend Grounds' original game code and documentation are licensed under the [MIT License](LICENSE), copyright 2026 Aleksandr Podgaiko.

The [Bend compiler](https://github.com/bendlang/bend) is a separate **Apache-2.0** dependency, copyright 2026 HigherOrderCO, pinned to commit `52637f747b1f7e08263b7853ffd7204262d8e41e`. Setup fetches the compiler; this source release does not redistribute its checkout. Its license and notices remain applicable independently of this project's MIT license. See [Toolchain](docs/TOOLCHAIN.md).
