# Agent interface

The browser, HTTP agents, replay CLI and persistent runner use the same Bend rules engine. Python supplies transports and optional policies, not a second rules implementation.

## Quick examples

Run from the repository root after `bash scripts/build.sh`:

```sh
python3 scripts/agent.py rules
python3 scripts/agent.py state --seed 42 --moves buy:0,play:0 --legal
python3 scripts/agent.py play --seed 42 --policy scripts/example_policy.py:policy
python3 scripts/agent.py human --seat 0 --policies scripts/example_policy.py:policy,bot,bot
python3 scripts/agent.py selfplay --seed 42 --policies tempo,econ,random,bot
```

The default `fast` backend uses `build/runner` and needs no HTTP server. `--backend cli` uses `build/cli`; `--backend http` uses the server. Global transport arguments must precede the subcommand:

```sh
python3 scripts/agent.py --backend http --url http://127.0.0.1:8765 play --seed 42 --policy tempo
```

There is no silent backend fallback. Rebuild if native binary provenance is stale.

## Custom policy

Use `file.py:function`, for example `scripts/example_policy.py:policy`. The callable signature is:

```python
def policy(obs, rng, state):
    legal = obs["legalActions"]
    return "end" if "end" in legal else legal[0]
```

This intentionally passive example shows the interface, not a competitive strategy. The supplied example policy recruits and deploys units. `rng` is a client random generator; `state` is policy memory maintained by the harness. Return exactly one legal action and inspect the next observation before choosing again. A nonlegal return fails the client run.

Built-in client policies include `first`, `random`, `tempo`, `econ`, `climber` and `bot`. `bot` sends `auto`, delegating the acting seat's turn to the Bend bot.

**Trust boundary:** policy modules run as ordinary local Python. They are not sandboxed. Only load code you trust. There is no integrated external model service or required API key.

## HTTP contract

Start the native server with `bash scripts/start.sh --fg`. It listens on loopback, normally `http://127.0.0.1:8765`.

| GET endpoint | Result |
| --- | --- |
| `/api/health` | Liveness and protocol information. |
| `/api/rules` | Authoritative costs, action syntax, card definitions and explanatory text. |
| `/api/game?seed=42&mode=bots&v=3&moves=` | Observation after replaying the transcript. |

A game is **`(seed, mode, moves)`**, not a server-side session. `seed` is an unsigned 32-bit integer; `moves` is a comma-separated list of lowercase action tokens without spaces. Send `v=3`, and check `protocolVersion` in the rules response. Older protocol transcripts have different meanings and must not be silently replayed.

```sh
curl 'http://127.0.0.1:8765/api/rules'
curl 'http://127.0.0.1:8765/api/game?seed=42&mode=bots&v=3&moves=buy:0,play:0,end'
```

A minimal client repeatedly fetches the transcript state, checks `error`, chooses from `legalActions`, appends one action and fetches again. Stop when `phase` is `finished`. URL-encode query values in a real client. HTTP transcripts are limited to 1024 moves; free actions can exhaust that budget, so policies must end their turns.

### Modes

- **`bots`**: you act for seat 0. `end` runs the other three Bend bots and resolves the round.
- **`manual`**: the transcript drives every seat. `player` identifies the next actor. `end` advances to the next living seat; the last seat's end resolves the round. Route observations to separate policies for multi-agent play.
- **`auto`**, in either mode: let the Bend bot recruit for the acting seat, then end that seat's turn.

Manual recruiting is sequential. Later seats see earlier seats' current-round boards; rotate seats when comparing policies. Stateless replay also permits undo and lookahead. Neither mode is a secure ranked-match protocol.

### Actions

All indexes are zero-based. Choose from `legalActions` rather than reconstructing legality.

| Token | Meaning |
| --- | --- |
| `buy:i` | Shop slot to private hand; costs 3 gold. |
| `play:i` | Hand slot to the right end of the board, resolving play effects. |
| `sell:i` | Sell a board unit; `sellGold` reports its gold payout. |
| `swap:i:j` | Reorder board units. |
| `roll` | Refresh the shop for 1 gold. |
| `freeze` | Toggle preservation of unsold shop offers. |
| `upgrade` | Pay `upgradeCost` to increase tier. |
| `invest` | Pay 2 gold for later income. |
| `end` | End this seat's turn. |
| `auto` | Bend bot turn, followed by end. |

Hand cards cannot be sold. There is no positional `play:i:j`; deploy then swap. Buys remove shop slots, plays remove hand slots, and golden merges can remove hand and board cards: indexes can change after any successful action.

### Observations and errors

Game observations include:

- `schemaVersion`, `protocolVersion`, `seed`, `mode`, `round`, `phase`, `player` and `movesApplied`;
- `players`, including your resources, shop and hand, and opponents' public boards, HP, tier and hand counts;
- `legalActions` and `nextOpponent`;
- structured `combat` events, summary `history` and `lastFight`;
- `winner` and `rank` when finished, plus `error`.

Other seats' gold, shop and hand contents are hidden (`null`). This is an observation boundary, not protection against a client deliberately querying other transcript branches.

Check both HTTP status and response `error`. Malformed queries or unsupported versions can return error-only responses; rejected moves in a replay can accompany the state of the accepted prefix. Do not assume every error response contains a complete observation or that every submitted move was applied.

## Replays

```sh
python3 scripts/agent.py play --seed 42 --policy tempo --save build/replay.json
python3 scripts/agent.py replay build/replay.json
```

The client stores protocol information, transcript and a final-observation hash, then checks reproduction on replay. In the browser, the Transcript tab copies a replay link. Reproduction assumes the same rules implementation; a protocol number alone does not pin every future rules change.
