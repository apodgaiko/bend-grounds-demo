"""Example custom agent policy for scripts/agent.py (protocol 3).

Use it with:
  python3 scripts/agent.py human --policies scripts/example_policy.py:policy
  python3 scripts/agent.py selfplay --policies scripts/example_policy.py:policy,tempo,econ,bot
  python3 scripts/agent.py play --policy scripts/example_policy.py:policy

A policy receives the server observation for the seat that must act
(obs["player"]) and must return one string from obs["legalActions"]. It sees
only what the Bend server reveals. Other seats' gold, shop and hand are null;
their handCount and board are public.

Protocol 3: `buy:i` puts a unit into your hand; it does nothing in combat
until you `play:i` it onto the board.
"""


def _power(u):
    return (u or {}).get("attack", 0) + (u or {}).get("health", 0)


def policy(obs, rng, state):
    legal = obs["legalActions"]
    # Per-turn action budget: never loop forever on a cheap legal action.
    turn = (obs["player"], obs["round"])
    state[turn] = state.get(turn, 0) + 1
    if state[turn] > 20 and "end" in legal:
        return "end"
    me = next(p for p in obs["players"] if p["id"] == obs["player"])
    opp = next((p for p in obs["players"] if p["id"] == obs.get("nextOpponent")), None)
    hand = me.get("hand") or []
    shop = me.get("shop") or []

    # Scouting: if the next opponent's public board outnumbers ours, buy tempo.
    behind = opp is not None and len(opp.get("board") or []) > len(me.get("board") or [])

    # Deploy first: a unit in hand does not fight.
    plays = [a for a in legal if a.startswith("play:")]
    if plays:
        return max(plays, key=lambda a: _power(hand[int(a.split(":")[1])]))
    # Invest once early unless we are behind on board.
    if obs["round"] <= 2 and "invest" in legal and not behind:
        return "invest"
    buys = [a for a in legal if a.startswith("buy:")]
    if buys:
        return max(buys, key=lambda a: _power(shop[int(a.split(":")[1])] if int(a.split(":")[1]) < len(shop) else None))
    if "upgrade" in legal and not behind:
        return "upgrade"
    return "end"
