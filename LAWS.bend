# Bend Grounds: the laws. Every law is universally quantified over all the
# Nats / lists it names; PROOF.bend proves each one. No concrete examples
# appear here: each law is a claim about every input.
#
#   bun vendor/bend/bend2/main.ts PROOF.bend [--verdict]
#
# Subject: engine/econ.bend, the economy helpers the rules engine
# (engine/game.bend) calls for gold payments, income, upgrade costs,
# hero hit points, combat damage and board capacity.

import Base
import ./engine/econ.bend as Econ

# Spending (Econ.spend)
# ---------------------
# spend_pays and spend_rejects together settle spend on every input:
# any (gold, cost) pair is either (cost + rest, cost) or (gold, gold + 1 + k).

# LAW: an affordable payment succeeds and leaves exactly gold - cost
# (resource preservation: rest + cost == gold)
law spend_pays:
  for cost: Nat
  for rest: Nat
  {Econ.spend(Nat.add(cost, rest), cost) == Some{rest} : Maybe<&2, Nat>}

# LAW: a payment above the purse is rejected (no debt, no partial spend)
law spend_rejects:
  for gold: Nat
  for k: Nat
  {Econ.spend(gold, Nat.add(gold, 1n+k)) == None{} : Maybe<&2, Nat>}

# LAW: spending never raises gold: whatever spend answers (0 standing in
# for a rejection), it is at most the starting gold
law spend_le:
  for +gold: Nat
  for +cost: Nat
  {Nat.is_le(Maybe.default(&2, Nat, Econ.spend(gold, cost), 0n), gold) == True{} : Bool}

# LAW: any upper bound on gold survives every spend attempt
law spend_keeps_bound:
  for +gold: Nat
  for +cost: Nat
  for max: Nat
  for h: {Nat.is_le(gold, max) == True{} : Bool}
  {Nat.is_le(Maybe.default(&2, Nat, Econ.spend(gold, cost), 0n), max) == True{} : Bool}

# Caps (Econ.cap)
# ---------------

# LAW: cap(a, c) <= c
law cap_le:
  for a: Nat
  for c: Nat
  {Nat.is_le(Econ.cap(a, c), c) == True{} : Bool}

# LAW: cap(a, c) <= a
law cap_below:
  for a: Nat
  for c: Nat
  {Nat.is_le(Econ.cap(a, c), a) == True{} : Bool}

# LAW: cap leaves any value within the cap unchanged
law cap_keeps:
  for a: Nat
  for k: Nat
  {Econ.cap(a, Nat.add(a, k)) == a : Nat}

# Income (Econ.base_income, Econ.income)
# --------------------------------------
# Total income is NOT bounded by 10: investment and bonus add on top.

# LAW: base income never exceeds 10, in any round
law base_income_le:
  for round: Nat
  {Nat.is_le(Econ.base_income(round), 10n) == True{} : Bool}

# LAW: base income is at least 2, in any round
law base_income_ge:
  for round: Nat
  {Nat.is_le(2n, Econ.base_income(round)) == True{} : Bool}

# LAW: base income never shrinks from one round to the next
law base_income_mono:
  for round: Nat
  {Nat.is_le(Econ.base_income(round), Econ.base_income(1n+round)) == True{} : Bool}

# LAW: each point of investment adds exactly one gold of income, in every
# round and with every bonus (the investment payoff)
law income_invest:
  for round: Nat
  for invest: Nat
  for bonus: Nat
  {Econ.income(round, 1n+invest, bonus) == 1n+Econ.income(round, invest, bonus) : Nat}

# LAW: each bonus point adds exactly one gold of income
law income_bonus:
  for round: Nat
  for invest: Nat
  for bonus: Nat
  {Econ.income(round, invest, 1n+bonus) == 1n+Econ.income(round, invest, bonus) : Nat}

# LAW: income is never below the base income
law income_ge_base:
  for +round: Nat
  for +invest: Nat
  for +bonus: Nat
  {Nat.is_le(Econ.base_income(round), Econ.income(round, invest, bonus)) == True{} : Bool}

# Upgrade costs (Econ.decay, Econ.upgrade_base, Econ.upgrade_floor,
# Econ.upgrade_cost_next, Econ.cost_after)
# ------------------------------------------------------------------
# Five tiers. A player at tier t (1..4) sees a stored upgrade cost that
# starts at upgrade_base(t) and, once per round, becomes
# upgrade_cost_next(t, cost): one gold cheaper, never below
# upgrade_floor(t). Tier 0 and tier >= 5 (max tier) cost 0.

# LAW: decay never raises a cost
law decay_le:
  for +c: Nat
  {Nat.is_le(Econ.decay(c), c) == True{} : Bool}

# LAW: decay lowers every positive cost by exactly one
law decay_step:
  for c: Nat
  {Econ.decay(1n+c) == c : Nat}

# CONCRETE TABLE (not quantified): base costs to leave tiers 1, 2, 3, 4
law upgrade_bases:
  {[Econ.upgrade_base(1n), Econ.upgrade_base(2n), Econ.upgrade_base(3n), Econ.upgrade_base(4n)] == [5n, 8n, 11n, 13n] : List<&2, Nat>}

# CONCRETE TABLE (not quantified): floors for tiers 1, 2, 3, 4
law upgrade_floors:
  {[Econ.upgrade_floor(1n), Econ.upgrade_floor(2n), Econ.upgrade_floor(3n), Econ.upgrade_floor(4n)] == [3n, 5n, 8n, 10n] : List<&2, Nat>}

# LAW: no tier's base upgrade cost exceeds 13
law upgrade_base_le:
  for tier: Nat
  {Nat.is_le(Econ.upgrade_base(tier), 13n) == True{} : Bool}

# LAW: from the max tier (5) up, there is nothing to buy: base cost 0
law upgrade_base_top:
  for k: Nat
  {Econ.upgrade_base(5n+k) == 0n : Nat}

# LAW: every tier's floor is at most its base cost (so the base is a
# valid starting cost)
law upgrade_floor_le_base:
  for tier: Nat
  {Nat.is_le(Econ.upgrade_floor(tier), Econ.upgrade_base(tier)) == True{} : Bool}

# LAW: no floor exceeds 10, the cap on base income
law upgrade_floor_le:
  for tier: Nat
  {Nat.is_le(Econ.upgrade_floor(tier), 10n) == True{} : Bool}

# LAW: from round 8 on, one round's income (any investment, any bonus)
# covers every tier's floor: a fully discounted upgrade is always
# affordable in one late round, if nothing else is bought
law upgrade_floor_affordable:
  for +tier: Nat
  for +k: Nat
  for +invest: Nat
  for +bonus: Nat
  {Nat.is_le(Econ.upgrade_floor(tier), Econ.income(8n+k, invest, bonus)) == True{} : Bool}

# LAW: at the max tier and above, the next stored cost is 0 whatever the
# current cost
law upgrade_next_top:
  for k: Nat
  for c: Nat
  {Econ.upgrade_cost_next(5n+k, c) == 0n : Nat}

# LAW: the per-round step never goes below the tier's floor, from any cost
law upgrade_next_ge_floor:
  for +tier: Nat
  for +c: Nat
  {Nat.is_le(Econ.upgrade_floor(tier), Econ.upgrade_cost_next(tier, c)) == True{} : Bool}

# LAW: from any cost at or above the floor, the per-round step never
# raises the cost
law upgrade_next_le:
  for +tier: Nat
  for +c: Nat
  for h: {Nat.is_le(Econ.upgrade_floor(tier), c) == True{} : Bool}
  {Nat.is_le(Econ.upgrade_cost_next(tier, c), c) == True{} : Bool}

# LAW: for tiers 1..4, a cost above the floor drops by exactly one gold
# per round
law upgrade_next_step:
  for +u: Nat
  for hu: {Nat.is_lt(u, 4n) == True{} : Bool}
  for +k: Nat
  {Econ.upgrade_cost_next(1n+u, 1n+Nat.add(k, Econ.upgrade_floor(1n+u))) == Nat.add(k, Econ.upgrade_floor(1n+u)) : Nat}

# LAW: the floor is a fixed point: once reached, the cost stays there
law upgrade_next_floor:
  for tier: Nat
  {Econ.upgrade_cost_next(tier, Econ.upgrade_floor(tier)) == Econ.upgrade_floor(tier) : Nat}

# LAW: over any number of rounds, a cost that starts at or above the
# floor never rises above where it started
law cost_after_le:
  for +tier: Nat
  for +c: Nat
  for +n: Nat
  for +h: {Nat.is_le(Econ.upgrade_floor(tier), c) == True{} : Bool}
  {Nat.is_le(Econ.cost_after(tier, c, n), c) == True{} : Bool}

# LAW: over any number of rounds, a cost that starts at or above the
# floor never drops below the floor
law cost_after_ge_floor:
  for +tier: Nat
  for +c: Nat
  for +n: Nat
  for +h: {Nat.is_le(Econ.upgrade_floor(tier), c) == True{} : Bool}
  {Nat.is_le(Econ.upgrade_floor(tier), Econ.cost_after(tier, c, n)) == True{} : Bool}

# LAW: for tiers 1..4, a cost k gold above the floor reaches the floor
# after exactly k rounds and stays there for every later round. With
# base - floor = 2, 3, 3, 3 this is how long waiting can pay off.
law cost_after_reach:
  for +u: Nat
  for +hu: {Nat.is_lt(u, 4n) == True{} : Bool}
  for +k: Nat
  for +n: Nat
  {Econ.cost_after(1n+u, Nat.add(k, Econ.upgrade_floor(1n+u)), Nat.add(k, n)) == Econ.upgrade_floor(1n+u) : Nat}

# LAW: for tiers 1..4, k rounds before the floor the cost is exactly
# floor + k gold (one gold per round, no early jump to the floor)
law cost_after_exact:
  for +u: Nat
  for +hu: {Nat.is_lt(u, 4n) == True{} : Bool}
  for +n: Nat
  for +k: Nat
  {Econ.cost_after(1n+u, Nat.add(n, Nat.add(k, Econ.upgrade_floor(1n+u))), n) == Nat.add(k, Econ.upgrade_floor(1n+u)) : Nat}

# Hit points (Econ.hp_after)
# --------------------------

# LAW: taking damage never heals
law hp_after_le:
  for +hp: Nat
  for +dmg: Nat
  {Nat.is_le(Econ.hp_after(hp, dmg), hp) == True{} : Bool}

# LAW: non-lethal damage subtracts exactly
law hp_after_exact:
  for dmg: Nat
  for rest: Nat
  {Econ.hp_after(Nat.add(dmg, rest), dmg) == rest : Nat}

# LAW: damage at or above hp floors at 0 (no negative or wrapped hp)
law hp_after_floor:
  for hp: Nat
  for k: Nat
  {Econ.hp_after(hp, Nat.add(hp, k)) == 0n : Nat}

# Combat damage (Econ.damage)
# ---------------------------

# LAW: a winner deals at least its tier, for every list of survivors
law damage_ge_tier:
  for +tier: Nat
  for +survivors: List<&2, Nat>
  {Nat.is_le(tier, Econ.damage(tier, survivors)) == True{} : Bool}

# LAW: one more survivor of tier t adds exactly t damage
law damage_survivor:
  for tier: Nat
  for t: Nat
  for ts: List<&2, Nat>
  {Econ.damage(tier, t <> ts) == Nat.add(t, Econ.damage(tier, ts)) : Nat}

# Board capacity (Econ.has_room)
# ------------------------------

# LAW: a board holding 5 or more units has no room
law room_full:
  for k: Nat
  {Econ.has_room(Nat.add(5n, k)) == False{} : Bool}

# LAW: room means the board stays within 5 after one insertion
law room_keeps_cap:
  for len: Nat
  for h: {Econ.has_room(len) == True{} : Bool}
  {Nat.is_le(1n+len, 5n) == True{} : Bool}

# LAW: whenever one insertion keeps the board within 5, there is room
law room_open:
  for len: Nat
  for h: {Nat.is_le(1n+len, 5n) == True{} : Bool}
  {Econ.has_room(len) == True{} : Bool}
