# Working on Bend Grounds

This file is the entry point for **coding agents** working in this repository.
For agents that **play the game**, use [the game-agent interface](docs/AGENTS-API.md).
Read the relevant route below, not every document by default. Linked documents
are on-demand references; this file does not make a client load them automatically.

## Always preserve

- **Bend 2 is authoritative.** Rules, legal actions, observations, bots and replay
  live in `engine/game.bend` and `engine/econ.bend`. Python clients and browser
  code must not grow a competing rules implementation.
- Keep the compiler pin and provenance checks intact. Do not edit `vendor/bend`
  or bypass stale-build refusals. Rebuild after engine changes.
- Be precise about evidence: a build, finite test, kernel-checked law and browser
  playthrough establish different things. No full-game verification, bot-strength,
  GPU or performance claim follows from this repository's existing checks.
- Custom Python policies execute trusted local code, **not sandboxed code**.
  Do not turn the policy loader into a public upload/execution endpoint.
- The server defaults to loopback. Public deployment needs explicit operator
  authorization and target/security validation; these docs grant neither.
- Keep public documentation in English. Never add credentials, private research
  artifacts, raw agent conversations or machine-specific access details.

## Choose one task route

| Task | Read next | Primary source |
| --- | --- | --- |
| Set up, build or start locally | [Toolchain](docs/TOOLCHAIN.md) | `scripts/setup.sh`, `scripts/build.sh`, `scripts/start.sh` |
| Change browser UI or combat presentation | [Development: browser UI](docs/DEVELOPMENT.md#browser-ui) | `web/app.js`, `web/style.css`, `web/index.html` |
| Change a card, economy or game rule | [Development: rules and cards](docs/DEVELOPMENT.md#rules-and-cards) | `engine/game.bend`, `engine/econ.bend` |
| Add a policy, client or game-agent integration | [Game-agent interface](docs/AGENTS-API.md) | `scripts/agent.py`, `scripts/example_policy.py` |
| Change HTTP or native transports | [Development: transports](docs/DEVELOPMENT.md#transports) | `engine/main.bend`, `engine/cli.bend`, `engine/runner.bend` |
| Inspect a law or state a verification claim | [Verification](docs/VERIFICATION.md) | `LAWS.bend`, `PROOF.bend`, `tests/*.bend` |
| Assess hosting on Linux or another target | [Development: hosting](docs/DEVELOPMENT.md#hosting) | `scripts/start.sh`, `engine/main.bend` |

[Development](docs/DEVELOPMENT.md) maps focused checks to each task. Existing
Toolchain, Game-agent interface and Verification documents own their detailed
contracts; avoid copying those contracts into new instruction files.
[Agent workflow](docs/AGENT-WORKFLOW.md) is a retrospective, not additional runtime
instructions or permission to launch training.

## Validate the actual change

Run commands from the repository root. Select focused checks using the task map;
use `bash scripts/verify.sh` for the canonical source-based release gate when
preparing an executable release. It requires the pinned compiler, Node.js and
Lean toolchain described in Toolchain. It is not a complete browser playthrough.

Do not treat a standalone API test against an existing server as evidence for a
fresh build. Do not invent a stop command: `start.sh --stop` deliberately refuses;
use Ctrl+C for an owned foreground server, otherwise inspect process identity.

Report changed files, commands actually run, results and remaining NOTRUN/UNKNOWN
items. Documentation-only navigation checks do not establish Linux support,
deployment readiness or a new game-runtime PASS.
