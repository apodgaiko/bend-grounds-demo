# Development task map

For **coding agents and contributors** changing this repository. A **game-playing agent** chooses actions through the interface in [Agent API](AGENTS-API.md); it does not need to read this entire development map.

Choose one task below, read its linked guide, then inspect the relevant source. The detailed guides remain authoritative for commands, prerequisites and limitations; this page is a routing index, not another setup manual. Run commands from the repository root.

## Find your task

| Task | Read first | Inspect or change | Validate the change |
| --- | --- | --- | --- |
| Set up, build or start locally | [Toolchain](TOOLCHAIN.md) | [`setup.sh`](../scripts/setup.sh), [`build.sh`](../scripts/build.sh), [`build_manifest.py`](../scripts/build_manifest.py), [`start.sh`](../scripts/start.sh) | Setup/build and provenance commands in Toolchain; local HTTP health and browser check. Use the release gate for release acceptance. |
| Change browser UI or combat presentation | [Agent API](AGENTS-API.md) for the observation contract; [finite-test boundaries](VERIFICATION.md#3-finite-tests-and-real-surfaces) | [`web/app.js`](../web/app.js), [`web/index.html`](../web/index.html), [`web/style.css`](../web/style.css) | `node --check web/app.js`; `node tests/web_regression_test.js`; exercise the changed UI in a real browser against the built engine. |
| Change cards, economy or game rules | [Verification](VERIFICATION.md), then [Agent API](AGENTS-API.md) for protocol impact | [`engine/game.bend`](../engine/game.bend): `card`, `p_apply`, `g_apply`, `replay`; [`engine/econ.bend`](../engine/econ.bend) | Rebuild; add focused scenarios/laws under [`tests/`](../tests/); run `bash scripts/verify.sh`. Check UI/rules descriptions and protocol compatibility as well as engine outcomes. |
| Add a game-playing policy or change API/transport | [Agent API](AGENTS-API.md) | [`example_policy.py`](../scripts/example_policy.py), [`agent.py`](../scripts/agent.py); native Rook: `bot_choice` in [`game.bend`](../engine/game.bend); HTTP: [`main.bend`](../engine/main.bend); incremental transport: [`runner.bend`](../engine/runner.bend) | Example-policy play and saved-replay commands in Agent API; `python3 tests/release_regression_test.py` for client regressions; release gate for engine/HTTP changes. |
| Add or explain a proof | [explicit laws and boundaries](VERIFICATION.md#2-explicit-laws-and-dependent-proof-results), [proof prerequisites](TOOLCHAIN.md#prerequisites) | [`LAWS.bend`](../LAWS.bend), [`PROOF.bend`](../PROOF.bend), [`tests/engine_invariants.bend`](../tests/engine_invariants.bend), [`tests/action_laws.bend`](../tests/action_laws.bend) and the relevant law file | Run the affected file with the documented `--verdict` command, then the release gate when preparing a release. State the exact quantified claim or finite scenario; do not promote it to full-game correctness. |
| Assess Linux/Hetzner or other public hosting | [Toolchain](TOOLCHAIN.md), [HTTP contract](AGENTS-API.md#http-contract), hosting boundary below | [`main.bend`](../engine/main.bend): `serve_on`, request limits/routing; [`start.sh`](../scripts/start.sh); transport selection near the start of [`app.js`](../web/app.js) | Build and test on the actual target; validate proxy/HTTPS, browser/API behavior, limits and rollback. Local macOS results are not Linux deployment acceptance. |

For the development retrospective and authorship—not build instructions—see [Agent workflow](AGENT-WORKFLOW.md).

<a id="browser-ui"></a>
### Browser UI

Start with the browser row above: the UI renders observations and replay events; game rules belong in Bend, not a second JavaScript rules engine. Source-helper tests need a real-browser check for interaction or visual changes.

<a id="rules-and-cards"></a>
### Rules and cards

Start with the rules row above. Follow an affected action from the card definition through player/game application, then check observations and laws. Rebuild native entry points after changing shared Bend sources.

<a id="transports"></a>
### Transports and game-playing agents

Start with the policy/API row above. The default fast client uses the native runner without an HTTP server; the CLI and HTTP backends exercise different entry points. Follow [Agent API](AGENTS-API.md) for argument ordering and the `bot`/Rook distinction.

## Use the right evidence

- **Cheap checks:** JavaScript syntax and the focused Python/JavaScript regression tests above do not require a running game server. They do not replace engine, HTTP or browser acceptance.
- **Release gate:** [Verification](VERIFICATION.md#canonical-release-gate) documents prerequisites and `bash scripts/verify.sh`. It rebuilds and starts an owned isolated HTTP server, refusing an occupied port. Standalone `tests/api_test.py` can reuse an existing server; its PASS alone does not establish that your new build was exercised.
- **Lifecycle:** foreground `bash scripts/start.sh --fg` stops with Ctrl+C. `start.sh --stop` is deliberately rejected, not a supported shutdown command. Inspect background process identity before stopping it; do not trust a stale PID file.
- **Proof scope:** typed-action acceptance does not prove JSON action strings or parser roundtrips; finite card checks do not prove all combat. See the guide before changing public claims.

<a id="hosting"></a>
## Hosting and policy trust boundary

Linux is **unvalidated**, not a promised supported target. The native server binds `127.0.0.1`; run it from the repository root to serve `web/`. The current UI normally uses same-origin API requests. Its `?api=` override accepts loopback HTTP origins only, not arbitrary remote API hosts.

Public hosting needs a deliberately configured HTTPS reverse proxy and target-specific resource, rate/concurrency and timeout limits. The game server is not an authenticated, TLS-terminating or secure ranked-match service. Transcripts are query-string data and may appear in proxy logs; stateless replay permits lookahead and undo. Do not expose a generic policy-upload/execution endpoint: custom Python policy modules run with ordinary local Python privileges and are **not sandboxed**. No deployment, external model service or credentials are required for local play.
