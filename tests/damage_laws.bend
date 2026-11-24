# Bend Grounds: universal laws about the player-damage cap (adopted from
# balance candidate C1). Every law is about the real engine functions in
# engine/game.bend; no shadow model, no holes, no axioms, no @unsafe.
#
#   bun vendor/bend/bend2/main.ts tests/damage_laws.bend --verdict
#
# Proven for EVERY round, result, final lines, tiers and combat state:
#   A. dmg_capped       fight_dmg(round, ...) <= 3 + round
#   B. dmg_le_raw       fight_dmg(round, ...) <= fight_dmg_raw(...)
#                       (the cap never raises a loss)
#   C. dmg_below_cap    fight_dmg_raw(...) <= 3 + round implies
#                       fight_dmg(round, ...) == fight_dmg_raw(...)
#                       (losses under the cap are exactly the old formula)
#   D. fight_end_capped the Fight built by fight_end, for any combat state,
#                       records damage <= 3 + round
#   E. fight_capped     every Fight produced by G.fight (any seed, seats,
#                       names, tiers, boards) records damage <= 3 + round
# Not covered here: that the HP a player loses in a round equals this
# damage (tests/engine_invariants.bend and the HTTP/fast-lane tests cover
# HP transitions separately), and no balance claim of any kind.

import Base
import ../engine/game.bend as G
import ./proof_kit.bend as K

# Nat.min lemmas
# --------------

def min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      K.le0(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      min_le_r(p, q)

def min_le_l(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      K.le0(1n+p)
    case 1n+p 1n+q:
      min_le_l(p, q)

def min_eq_l(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      K.ft_absurd({Nat.min(1n+p, 0n) == 1n+p : Nat}, h)
    case 1n+p 1n+q:
      %min_eq_l(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# A. the cap
# ----------

law dmg_capped:
  for round: Nat
  for res: Nat
  for xa: List<&2, G.Mon>
  for xb: List<&2, G.Mon>
  for ta: Nat
  for tb: Nat
  {Nat.is_le(G.fight_dmg(round, res, xa, xb, ta, tb), Nat.add(3n, round)) == True{} : Bool}

def dmg_capped(round, res, xa, xb, ta, tb):
  min_le_r(G.fight_dmg_raw(res, xa, xb, ta, tb), G.damage_cap(round))

# B. the cap only ever lowers a loss
# ----------------------------------

law dmg_le_raw:
  for round: Nat
  for res: Nat
  for xa: List<&2, G.Mon>
  for xb: List<&2, G.Mon>
  for ta: Nat
  for tb: Nat
  {Nat.is_le(G.fight_dmg(round, res, xa, xb, ta, tb), G.fight_dmg_raw(res, xa, xb, ta, tb)) == True{} : Bool}

def dmg_le_raw(round, res, xa, xb, ta, tb):
  min_le_l(G.fight_dmg_raw(res, xa, xb, ta, tb), G.damage_cap(round))

# C. below the cap nothing changes
# --------------------------------

def dmg_below_cap(round: Nat, res: Nat, xa: List<&2, G.Mon>, xb: List<&2, G.Mon>, ta: Nat, tb: Nat,
    h: {Nat.is_le(G.fight_dmg_raw(res, xa, xb, ta, tb), Nat.add(3n, round)) == True{} : Bool})
    -> {G.fight_dmg(round, res, xa, xb, ta, tb) == G.fight_dmg_raw(res, xa, xb, ta, tb) : Nat}:
  min_eq_l(G.fight_dmg_raw(res, xa, xb, ta, tb), G.damage_cap(round), h)

# D/E. the recorded damage of every fight
# ---------------------------------------

def f_dmg(f: G.Fight) -> Nat:
  G.Fight{round, a, b, res, dmg, ba, bb, log, evs} = f
  dmg

law fight_end_capped:
  for st: G.CSt
  for +round: Nat
  for +a: Nat
  for +b: Nat
  for +na: String
  for +nb: String
  for +ta: Nat
  for +tb: Nat
  for +ba: List<&2, G.Mon>
  for +bb: List<&2, G.Mon>
  {Nat.is_le(f_dmg(G.fight_end(st, round, a, b, na, nb, ta, tb, ba, bb)), Nat.add(3n, round)) == True{} : Bool}

def fight_end_capped(st, round, a, b, na, nb, ta, tb, ba, bb):
  match st:
    case G.CSt{+xa, +xb, turn, n, log, evs}:
      dmg_capped(round, G.fight_res(xa, xb), xa, xb, ta, tb)

law fight_capped:
  for +seed: U32
  for +round: Nat
  for +a: Nat
  for +b: Nat
  for +na: String
  for +nb: String
  for +ta: Nat
  for +tb: Nat
  for +ba: List<&2, G.Mon>
  for +bb: List<&2, G.Mon>
  {Nat.is_le(f_dmg(G.fight(seed, round, a, b, na, nb, ta, tb, ba, bb)), Nat.add(3n, round)) == True{} : Bool}

def fight_capped(seed, round, a, b, na, nb, ta, tb, ba, bb):
  fight_end_capped(G.cloop(G.combat_fuel(), seed, round, a, b, na, nb, G.CSt{ba, bb, G.first_turn(G.len(G.Mon, ba), G.len(G.Mon, bb), G.hash(seed, [3n, round, a, b])), 0n, Nil{}, Nil{}}), round, a, b, na, nb, ta, tb, ba, bb)

def main() -> String:
  "damage laws: run with --verdict"
