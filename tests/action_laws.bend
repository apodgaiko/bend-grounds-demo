# Bend Grounds v2: action and interaction laws, proven on the real engine.
#
#   bun vendor/bend/bend2/main.ts tests/action_laws.bend --verdict
#
# Where tests/engine_invariants.bend proves global bounds (board <= 5,
# hand <= 7), this file pins down WHAT each move does:
#   A. the acceptance relation: an action is accepted exactly when the
#      preconditions stated independently below hold;
#   B. exact postconditions: what each accepted move changes, and by how
#      much gold;
#   C. the effect algebra of the ability interpreter;
#   D. combat damage laws;
#   E. replay laws (error index, sticky errors) and cross-seat frame;
#   F. legal-action soundness (move-text round trip is not proven here).
# Everything is universally quantified over the engine's own functions,
# except where a law says "for every ... < N" (exhaustive finite domain).

import Base
import ../engine/econ.bend as Econ
import ../engine/game.bend as G
import ./proof_kit.bend as K

# A. The acceptance relation
# ==========================

# The precondition column of the rules table, written down independently
# of the engine: costs buy 3, roll 1, invest 2 (at most 3 investments),
# upgrade = current upgrade cost, hand at most 7, board at most 5, tier at
# most 5. End and Auto are game-level actions, never recruit actions.
def Pre(p: G.Player, a: G.Act) -> Bool:
  G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, +board, shop, alive, out, +hand, plays} = p
  match a:
    case G.Buy{i}:
      Nat.is_lt(i, List.length(&2, Nat, shop)) && (Nat.is_lt(List.length(&2, G.Mon, hand), 7n) && Nat.is_le(3n, gold))
    case G.Play{i}:
      Nat.is_lt(i, List.length(&2, G.Mon, hand)) && Nat.is_lt(List.length(&2, G.Mon, board), 5n)
    case G.Sell{i}:
      Nat.is_lt(i, List.length(&2, G.Mon, board))
    case G.Swap{+i, +j}:
      Nat.is_lt(i, List.length(&2, G.Mon, board)) && Nat.is_lt(j, List.length(&2, G.Mon, board)) && Nat.is_ne(i, j)
    case G.Roll{}:
      Nat.is_le(1n, gold)
    case G.Freeze{}:
      True{}
    case G.Upgrade{}:
      Nat.is_lt(tier, 5n) && Nat.is_le(upcost, gold)
    case G.Invest{}:
      Nat.is_lt(invest, 3n) && Nat.is_le(2n, gold)
    case G.End{}:
      False{}
    case G.Auto{}:
      False{}

# a payment succeeds exactly when the purse covers the cost
law spend_some:
  for gold: Nat
  for cost: Nat
  {Maybe.is_some(&2, Nat, Econ.spend(gold, cost)) == Nat.is_le(cost, gold) : Bool}

def spend_some(gold, cost):
  match gold cost:
    case 0n 0n:
      {==}
    case 1n+g 0n:
      {==}
    case 0n 1n+c:
      {==}
    case 1n+g 1n+c:
      spend_some(g, c)

# a list index is present exactly when it is below the length
def get_some(-A: Data, xs: List<&2, A>, i: Nat) -> {Maybe.is_some(&2, A, List.get(&2, A, xs, i)) == Nat.is_lt(i, List.length(&2, A, xs)) : Bool}:
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      get_some(A, t, p)

def buy_acc(mc: Maybe<&2, Nat>, room: Bool, mg: Maybe<&2, Nat>, +p: G.Player, +i: Nat)
  -> {G.pres_ok(G.buy_go(mc, room, mg, p, i)) == (Maybe.is_some(&2, Nat, mc) && (room && Maybe.is_some(&2, Nat, mg))) : Bool}:
  match mc room mg:
    case None{} _ _:
      {==}
    case Some{c} False{} _:
      {==}
    case Some{c} True{} None{}:
      {==}
    case Some{c} True{} Some{g}:
      {==}

def play_acc(mm: Maybe<&2, G.Mon>, room: Bool, +seed: U32, +round: Nat, +p: G.Player, +i: Nat)
  -> {G.pres_ok(G.play_go(mm, room, seed, round, p, i)) == (Maybe.is_some(&2, G.Mon, mm) && room) : Bool}:
  match mm room:
    case None{} _:
      {==}
    case Some{m} False{}:
      {==}
    case Some{m} True{}:
      {==}

def sell_acc(mm: Maybe<&2, G.Mon>, +seed: U32, +round: Nat, +p: G.Player, +i: Nat)
  -> {G.pres_ok(G.sell_go(mm, seed, round, p, i)) == Maybe.is_some(&2, G.Mon, mm) : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{m}:
      {==}

def swap_acc(ok: Bool, +p: G.Player, +i: Nat, +j: Nat) -> {G.pres_ok(G.swap_go(ok, p, i, j)) == ok : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def roll_acc(mg: Maybe<&2, Nat>, +seed: U32, +round: Nat, +p: G.Player) -> {G.pres_ok(G.roll_go(mg, seed, round, p)) == Maybe.is_some(&2, Nat, mg) : Bool}:
  match mg p:
    case None{} _:
      {==}
    case Some{g} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      {==}

def up_acc(ok: Bool, mg: Maybe<&2, Nat>, +p: G.Player) -> {G.pres_ok(G.upgrade_go(ok, mg, p)) == (ok && Maybe.is_some(&2, Nat, mg)) : Bool}:
  match ok mg p:
    case False{} _ _:
      {==}
    case True{} None{} _:
      {==}
    case True{} Some{g} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      {==}

def inv_acc(ok: Bool, mg: Maybe<&2, Nat>, +p: G.Player) -> {G.pres_ok(G.invest_go(ok, mg, p)) == (ok && Maybe.is_some(&2, Nat, mg)) : Bool}:
  match ok mg p:
    case False{} _ _:
      {==}
    case True{} None{} _:
      {==}
    case True{} Some{g} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      {==}

# LAW (the acceptance relation): for every seed, round, player and action,
# the engine accepts the action exactly when the rules-table precondition
# holds. One direction: every documented rejection (bad index, full hand,
# full board, not enough gold, max tier, max investment) really rejects.
# The other: the engine has no undocumented guard.
law accept_iff:
  for +seed: U32
  for +round: Nat
  for +p: G.Player
  for a: G.Act
  {G.pres_ok(G.p_apply(seed, round, p, a)) == Pre(p, a) : Bool}

def accept_iff(seed, round, p, a):
  match p:
    case G.Player{+id, +hp, +gold, +tier, +upcost, +invest, +frozen, +rolls, +board, +shop, +alive, +out, +hand, +plays}:
      match a:
        case G.Buy{+i}:
          %get_some(Nat, shop, i) : {G.pres_ok(G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Buy{i})) == (_ && (Nat.is_lt(List.length(&2, G.Mon, hand), 7n) && Nat.is_le(3n, gold))) : Bool}
          %spend_some(gold, 3n) : {G.pres_ok(G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Buy{i})) == (Maybe.is_some(&2, Nat, List.get(&2, Nat, shop, i)) && (Nat.is_lt(List.length(&2, G.Mon, hand), 7n) && _)) : Bool}
          buy_acc(List.get(&2, Nat, shop, i), G.hand_room(G.len(G.Mon, hand)), Econ.spend(gold, G.buy_cost()), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i)
        case G.Play{+i}:
          %get_some(G.Mon, hand, i) : {G.pres_ok(G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Play{i})) == (_ && Nat.is_lt(List.length(&2, G.Mon, board), 5n)) : Bool}
          play_acc(List.get(&2, G.Mon, hand, i), Econ.has_room(G.len(G.Mon, board)), seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i)
        case G.Sell{+i}:
          %get_some(G.Mon, board, i) : {G.pres_ok(G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Sell{i})) == _ : Bool}
          sell_acc(List.get(&2, G.Mon, board, i), seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i)
        case G.Swap{+i, +j}:
          +n = G.len(G.Mon, board)
          swap_acc(Nat.is_lt(i, n) && Nat.is_lt(j, n) && Nat.is_ne(i, j), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i, j)
        case G.Roll{}:
          %spend_some(gold, 1n) : {G.pres_ok(G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Roll{})) == _ : Bool}
          roll_acc(Econ.spend(gold, G.roll_cost()), seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
        case G.Freeze{}:
          {==}
        case G.Upgrade{}:
          %spend_some(gold, upcost) : {G.pres_ok(G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Upgrade{})) == (Nat.is_lt(tier, 5n) && _) : Bool}
          up_acc(Nat.is_lt(tier, G.max_tier()), Econ.spend(gold, upcost), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
        case G.Invest{}:
          %spend_some(gold, 2n) : {G.pres_ok(G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Invest{})) == (Nat.is_lt(invest, 3n) && _) : Bool}
          inv_acc(Nat.is_lt(invest, G.max_invest()), Econ.spend(gold, G.invest_cost()), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
        case G.End{}:
          {==}
        case G.Auto{}:
          {==}

# B. Exact postconditions of accepted moves
# =========================================
# Premises name the real index/room/payment facts; the conclusion is the
# complete resulting player record, so every field the move does NOT
# change is pinned too (frame).

law spend_pays:
  for cost: Nat
  for rest: Nat
  {Econ.spend(Nat.add(cost, rest), cost) == Some{rest} : Maybe<&2, Nat>}

def spend_pays(cost, rest):
  match cost rest:
    case 0n 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+c _:
      spend_pays(c, rest)

# LAW: buy:i with card c at shop index i, room in the hand (hr, as
# copyable Bool evidence) and 3 + rest
# gold leaves exactly rest gold, removes exactly shop entry i, appends
# exactly mon_of(c) to the hand, and changes nothing else (board included)
# BEFORE triple assembly; V4: the accepted result is exactly G.p_norm of
# that record (assembly is stated separately, see section G)
law buy_exact:
  for +seed: U32
  for +round: Nat
  for +id: Nat
  for +hp: Nat
  for +rest: Nat
  for +tier: Nat
  for +upcost: Nat
  for +invest: Nat
  for +frozen: Bool
  for +rolls: Nat
  for +board: List<&2, G.Mon>
  for +shop: List<&2, Nat>
  for +alive: Bool
  for +out: Nat
  for +hand: List<&2, G.Mon>
  for +plays: Nat
  for +i: Nat
  for +c: Nat
  for hc: {List.get(&2, Nat, shop, i) == Some{c} : Maybe<&2, Nat>}
  for +hr: K.T(G.hand_room(G.len(G.Mon, hand)))
  {G.pres_or(G.p_apply(seed, round, G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Buy{i}),
             G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
    == G.p_norm(G.Player{id, hp, rest, tier, upcost, invest, frozen, rolls, board, G.remove_at(Nat, shop, i), alive, out, G.snoc(G.Mon, hand, G.mon_of(c)), plays}) : G.Player}

def buy_exact(seed, round, id, hp, rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, i, c, hc, hr):
  %K.sym(Maybe<&2, Nat>, List.get(&2, Nat, shop, i), Some{c}, hc)
    : {G.pres_or(G.buy_go(_, G.hand_room(G.len(G.Mon, hand)), Econ.spend(3n+rest, 3n), G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i),
                 G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
       == G.p_norm(G.Player{id, hp, rest, tier, upcost, invest, frozen, rolls, board, G.remove_at(Nat, shop, i), alive, out, G.snoc(G.Mon, hand, G.mon_of(c)), plays}) : G.Player}
  %K.sym(Bool, G.hand_room(G.len(G.Mon, hand)), True{}, K.from_T(G.hand_room(G.len(G.Mon, hand)), hr))
    : {G.pres_or(G.buy_go(Some{c}, _, Econ.spend(3n+rest, 3n), G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i),
                 G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
       == G.p_norm(G.Player{id, hp, rest, tier, upcost, invest, frozen, rolls, board, G.remove_at(Nat, shop, i), alive, out, G.snoc(G.Mon, hand, G.mon_of(c)), plays}) : G.Player}
  %K.sym(Maybe<&2, Nat>, Econ.spend(3n+rest, 3n), Some{rest}, spend_pays(3n, rest))
    : {G.pres_or(G.buy_go(Some{c}, True{}, _, G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i), G.Player{id, hp, 3n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}) == G.p_norm(G.Player{id, hp, rest, tier, upcost, invest, frozen, rolls, board, G.remove_at(Nat, shop, i), alive, out, G.snoc(G.Mon, hand, G.mon_of(c)), plays}) : G.Player}
  %K.sym(Bool, G.hand_room(G.len(G.Mon, hand)), True{}, K.from_T(G.hand_room(G.len(G.Mon, hand)), hr))
    : {G.p_norm(G.Player{id, hp, rest, tier, upcost, invest, frozen, rolls, board, G.remove_at(Nat, shop, i), alive, out, G.hand_put(_, hand, G.mon_of(c)), plays})
       == G.p_norm(G.Player{id, hp, rest, tier, upcost, invest, frozen, rolls, board, G.remove_at(Nat, shop, i), alive, out, G.snoc(G.Mon, hand, G.mon_of(c)), plays}) : G.Player}
  {==}

# no ability in xs fires on trigger want
def NoTrig(xs: List<&2, G.Abil>, +want: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.not(G.nat_eq(G.abil_trig(x), want)) && NoTrig(t, want)

def if_off(ok: Bool, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, x: G.Abil, fx: G.Fx, h: {Bool.not(ok) == True{} : Bool})
  -> {G.fx_if(ok, seed, key, src, tr, gd, x, fx) == fx : G.Fx}:
  match ok:
    case True{}:
      K.ft_absurd({G.fx_if(True{}, seed, key, src, tr, gd, x, fx) == fx : G.Fx}, h)
    case False{}:
      {==}

# abilities with no matching trigger leave the effect state untouched
def abils_off(xs: List<&2, G.Abil>, +want: Nat, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, +slot: Nat, +fx: G.Fx,
  +h: {NoTrig(xs, want) == True{} : Bool}) -> {G.fx_abils(xs, want, seed, key, src, tr, gd, slot, fx) == fx : G.Fx}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      +ok = G.nat_eq(G.abil_trig(x), want)
      %K.sym(G.Fx, G.fx_if(ok, seed, G.snoc(Nat, key, slot), src, tr, gd, x, fx), fx, if_off(ok, seed, G.snoc(Nat, key, slot), src, tr, gd, x, fx, K.and_l(Bool.not(ok), NoTrig(t, want), h)))
        : {G.fx_abils(t, want, seed, key, src, tr, gd, 1n+slot, _) == fx : G.Fx}
      abils_off(t, want, seed, key, src, tr, gd, 1n+slot, fx, K.and_r(Bool.not(ok), NoTrig(t, want), h))

# LAW (V4 board sale; replaces V3 sellhand_exact): selling board unit i
# whose (golden-scaled) abilities have no SELL trigger is accepted and
# yields exactly p_norm of the player with that unit removed and
# sell_refund() gold added; hand, shop and every other field unchanged.
# Units with Sell abilities are covered by concrete fixtures
# (card_interactions: eel/pup/broker, golden sells).
law sell_exact:
  for +seed: U32
  for +round: Nat
  for +id: Nat
  for +hp: Nat
  for +gold: Nat
  for +tier: Nat
  for +upcost: Nat
  for +invest: Nat
  for +frozen: Bool
  for +rolls: Nat
  for +board: List<&2, G.Mon>
  for +shop: List<&2, Nat>
  for +alive: Bool
  for +out: Nat
  for +hand: List<&2, G.Mon>
  for +plays: Nat
  for +i: Nat
  for +m: G.Mon
  for hm: {List.get(&2, G.Mon, board, i) == Some{m} : Maybe<&2, G.Mon>}
  for hs: {NoTrig(G.mon_abils(m), 3n) == True{} : Bool}
  {G.p_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Sell{i}) == G.PGood{G.p_norm(G.Player{id, hp, Nat.add(gold, G.sell_refund()), tier, upcost, invest, frozen, rolls, G.remove_at(G.Mon, board, i), shop, alive, out, hand, plays})} : G.PRes}

def sell_exact(seed, round, id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, i, m, hm, hs):
  +f0 = {G.Fx{G.remove_at(G.Mon, board, i), m, hand, Nat.add(gold, G.sell_refund()), plays} : G.Fx}
  %K.sym(Maybe<&2, G.Mon>, List.get(&2, G.Mon, board, i), Some{m}, hm)
    : {G.sell_go(_, seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i) == G.PGood{G.p_norm(G.Player{id, hp, Nat.add(gold, G.sell_refund()), tier, upcost, invest, frozen, rolls, G.remove_at(G.Mon, board, i), shop, alive, out, hand, plays})} : G.PRes}
  %K.sym(G.Fx, G.fx_abils(G.mon_abils(m), 3n, seed, [12n, id, round, plays, gold], G.entering(), G.mon_tribe(m), G.mon_golden(m), 0n, f0), f0,
      abils_off(G.mon_abils(m), 3n, seed, [12n, id, round, plays, gold], G.entering(), G.mon_tribe(m), G.mon_golden(m), 0n, f0, hs))
    : {G.PGood{G.p_norm(G.sell_fin(_, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}))} == G.PGood{G.p_norm(G.Player{id, hp, Nat.add(gold, G.sell_refund()), tier, upcost, invest, frozen, rolls, G.remove_at(G.Mon, board, i), shop, alive, out, hand, plays})} : G.PRes}
  {==}

# LAW: roll with 1 + rest gold leaves exactly rest gold, draws the shop for
# the next roll counter, clears freeze; board and hand are untouched
law roll_exact:
  for +seed: U32
  for +round: Nat
  for +id: Nat
  for +hp: Nat
  for +rest: Nat
  for +tier: Nat
  for +upcost: Nat
  for +invest: Nat
  for +frozen: Bool
  for +rolls: Nat
  for +board: List<&2, G.Mon>
  for +shop: List<&2, Nat>
  for +alive: Bool
  for +out: Nat
  for +hand: List<&2, G.Mon>
  for +plays: Nat
  {G.pres_or(G.p_apply(seed, round, G.Player{id, hp, 1n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Roll{}),
             G.Player{id, hp, 1n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
    == G.Player{id, hp, rest, tier, upcost, invest, False{}, 1n+rolls, board, G.make_shop(seed, id, round, 1n+rolls, tier), alive, out, hand, plays} : G.Player}

def roll_exact(seed, round, id, hp, rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays):
  %K.sym(Maybe<&2, Nat>, Econ.spend(1n+rest, 1n), Some{rest}, spend_pays(1n, rest))
    : {G.pres_or(G.roll_go(_, seed, round, G.Player{id, hp, 1n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}), G.Player{id, hp, 1n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}) == G.Player{id, hp, rest, tier, upcost, invest, False{}, 1n+rolls, board, G.make_shop(seed, id, round, 1n+rolls, tier), alive, out, hand, plays} : G.Player}
  {==}

# LAW: invest below the maximum with 2 + rest gold leaves exactly rest gold
# and one more investment; nothing else changes
law invest_exact:
  for +seed: U32
  for +round: Nat
  for +id: Nat
  for +hp: Nat
  for +rest: Nat
  for +tier: Nat
  for +upcost: Nat
  for +invest: Nat
  for +frozen: Bool
  for +rolls: Nat
  for +board: List<&2, G.Mon>
  for +shop: List<&2, Nat>
  for +alive: Bool
  for +out: Nat
  for +hand: List<&2, G.Mon>
  for +plays: Nat
  for hi: {Nat.is_lt(invest, 3n) == True{} : Bool}
  {G.pres_or(G.p_apply(seed, round, G.Player{id, hp, 2n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Invest{}),
             G.Player{id, hp, 2n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
    == G.Player{id, hp, rest, tier, upcost, 1n+invest, frozen, rolls, board, shop, alive, out, hand, plays} : G.Player}

def invest_exact(seed, round, id, hp, rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, hi):
  %K.sym(Bool, Nat.is_lt(invest, 3n), True{}, hi)
    : {G.pres_or(G.invest_go(_, Econ.spend(2n+rest, 2n), G.Player{id, hp, 2n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}),
                 G.Player{id, hp, 2n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
       == G.Player{id, hp, rest, tier, upcost, 1n+invest, frozen, rolls, board, shop, alive, out, hand, plays} : G.Player}
  %K.sym(Maybe<&2, Nat>, Econ.spend(2n+rest, 2n), Some{rest}, spend_pays(2n, rest))
    : {G.pres_or(G.invest_go(True{}, _, G.Player{id, hp, 2n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}), G.Player{id, hp, 2n+rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}) == G.Player{id, hp, rest, tier, upcost, 1n+invest, frozen, rolls, board, shop, alive, out, hand, plays} : G.Player}
  {==}

# LAW: upgrade below the top tier with upcost + rest gold leaves exactly
# rest gold, raises the tier by one and resets the upgrade cost to the
# base cost of the new tier; nothing else changes
law upgrade_exact:
  for +seed: U32
  for +round: Nat
  for +id: Nat
  for +hp: Nat
  for +rest: Nat
  for +tier: Nat
  for +upcost: Nat
  for +invest: Nat
  for +frozen: Bool
  for +rolls: Nat
  for +board: List<&2, G.Mon>
  for +shop: List<&2, Nat>
  for +alive: Bool
  for +out: Nat
  for +hand: List<&2, G.Mon>
  for +plays: Nat
  for ht: {Nat.is_lt(tier, 5n) == True{} : Bool}
  {G.pres_or(G.p_apply(seed, round, G.Player{id, hp, Nat.add(upcost, rest), tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, G.Upgrade{}),
             G.Player{id, hp, Nat.add(upcost, rest), tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
    == G.Player{id, hp, rest, 1n+tier, Econ.upgrade_base(1n+tier), invest, frozen, rolls, board, shop, alive, out, hand, plays} : G.Player}

def upgrade_exact(seed, round, id, hp, rest, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, ht):
  %K.sym(Bool, Nat.is_lt(tier, 5n), True{}, ht)
    : {G.pres_or(G.upgrade_go(_, Econ.spend(Nat.add(upcost, rest), upcost), G.Player{id, hp, Nat.add(upcost, rest), tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}),
                 G.Player{id, hp, Nat.add(upcost, rest), tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
       == G.Player{id, hp, rest, 1n+tier, Econ.upgrade_base(1n+tier), invest, frozen, rolls, board, shop, alive, out, hand, plays} : G.Player}
  %K.sym(Maybe<&2, Nat>, Econ.spend(Nat.add(upcost, rest), upcost), Some{rest}, spend_pays(upcost, rest))
    : {G.pres_or(G.upgrade_go(True{}, _, G.Player{id, hp, Nat.add(upcost, rest), tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}),
                 G.Player{id, hp, Nat.add(upcost, rest), tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})
       == G.Player{id, hp, rest, 1n+tier, Econ.upgrade_base(1n+tier), invest, frozen, rolls, board, shop, alive, out, hand, plays} : G.Player}
  {==}

# C. Effect algebra of the ability interpreter
# ============================================
# Every stat effect goes through G.mon_add; KIN effects through G.kin_go.

# LAW: two stat gains commute
law mon_add_comm:
  for +a1: Nat
  for +h1: Nat
  for +a2: Nat
  for +h2: Nat
  for m: G.Mon
  {G.mon_add(a1, h1, G.mon_add(a2, h2, m)) == G.mon_add(a2, h2, G.mon_add(a1, h1, m)) : G.Mon}

def mon_add_comm(a1, h1, a2, h2, m):
  match m:
    case G.Mon{c, +a, +h, s, g}:
      %K.sym(Nat, Nat.add(Nat.add(a, a2), a1), Nat.add(Nat.add(a, a1), a2), K.add_swap(a, a2, a1)) : {G.Mon{c, _, Nat.add(Nat.add(h, h2), h1), s, g} == G.Mon{c, Nat.add(Nat.add(a, a1), a2), Nat.add(Nat.add(h, h1), h2), s, g} : G.Mon}
      %K.sym(Nat, Nat.add(Nat.add(h, h2), h1), Nat.add(Nat.add(h, h1), h2), K.add_swap(h, h2, h1)) : {G.Mon{c, Nat.add(Nat.add(a, a1), a2), _, s, g} == G.Mon{c, Nat.add(Nat.add(a, a1), a2), Nat.add(Nat.add(h, h1), h2), s, g} : G.Mon}
      {==}

# LAW: two stat gains fuse into one gain of the sums
law mon_add_fuse:
  for +a1: Nat
  for +h1: Nat
  for +a2: Nat
  for +h2: Nat
  for m: G.Mon
  {G.mon_add(a1, h1, G.mon_add(a2, h2, m)) == G.mon_add(Nat.add(a2, a1), Nat.add(h2, h1), m) : G.Mon}

def mon_add_fuse(a1, h1, a2, h2, m):
  match m:
    case G.Mon{c, +a, +h, s, g}:
      %K.sym(Nat, Nat.add(Nat.add(a, a2), a1), Nat.add(a, Nat.add(a2, a1)), K.add_assoc(a, a2, a1)) : {G.Mon{c, _, Nat.add(Nat.add(h, h2), h1), s, g} == G.Mon{c, Nat.add(a, Nat.add(a2, a1)), Nat.add(h, Nat.add(h2, h1)), s, g} : G.Mon}
      %K.sym(Nat, Nat.add(Nat.add(h, h2), h1), Nat.add(h, Nat.add(h2, h1)), K.add_assoc(h, h2, h1)) : {G.Mon{c, Nat.add(a, Nat.add(a2, a1)), _, s, g} == G.Mon{c, Nat.add(a, Nat.add(a2, a1)), Nat.add(h, Nat.add(h2, h1)), s, g} : G.Mon}
      {==}

# LAW: a +0/+0 gain is the identity
law mon_add_zero:
  for m: G.Mon
  {G.mon_add(0n, 0n, m) == m : G.Mon}

def mon_add_zero(m):
  match m:
    case G.Mon{c, +a, +h, s, g}:
      %K.sym(Nat, Nat.add(a, 0n), a, K.add_zero_r(a)) : {G.Mon{c, _, Nat.add(h, 0n), s, g} == G.Mon{c, a, h, s, g} : G.Mon}
      %K.sym(Nat, Nat.add(h, 0n), h, K.add_zero_r(h)) : {G.Mon{c, a, _, s, g} == G.Mon{c, a, h, s, g} : G.Mon}
      {==}

# a gain never changes a unit's card, hence never its tribe
def tribe_keep(c1: Bool, +da: Nat, +dh: Nat, m: G.Mon) -> {G.mon_tribe(G.pick(G.Mon, c1, G.mon_add(da, dh, m), m)) == G.mon_tribe(m) : Nat}:
  match c1 m:
    case True{} G.Mon{c, a, h, s, g}:
      {==}
    case False{} G.Mon{c, a, h, s, g}:
      {==}

def cond_keep(c1: Bool, +da: Nat, +dh: Nat, +m: G.Mon, +tr: Nat, +pos: Nat, +skip: Nat)
  -> {(G.kin_match(G.mon_tribe(G.pick(G.Mon, c1, G.mon_add(da, dh, m), m)), tr) && Bool.not(G.nat_eq(pos, skip))) == (G.kin_match(G.mon_tribe(m), tr) && Bool.not(G.nat_eq(pos, skip))) : Bool}:
  %K.sym(Nat, G.mon_tribe(G.pick(G.Mon, c1, G.mon_add(da, dh, m), m)), G.mon_tribe(m), tribe_keep(c1, da, dh, m)) : {(G.kin_match(_, tr) && Bool.not(G.nat_eq(pos, skip))) == (G.kin_match(G.mon_tribe(m), tr) && Bool.not(G.nat_eq(pos, skip))) : Bool}
  {==}

def el_comm2(+m: G.Mon, +a1: Nat, +h1: Nat, +a2: Nat, +h2: Nat, c1: Bool, c2: Bool)
  -> {G.pick(G.Mon, c2, G.mon_add(a2, h2, G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m))
      == G.pick(G.Mon, c1, G.mon_add(a1, h1, G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)) : G.Mon}:
  match c1 c2:
    case True{} True{}:
      mon_add_comm(a2, h2, a1, h1, m)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def el_comm(+m: G.Mon, +a1: Nat, +h1: Nat, +a2: Nat, +h2: Nat, c1: Bool, c2: Bool, d1: Bool, d2: Bool,
  e2: {d2 == c2 : Bool}, e1: {d1 == c1 : Bool})
  -> {G.pick(G.Mon, d2, G.mon_add(a2, h2, G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m))
      == G.pick(G.Mon, d1, G.mon_add(a1, h1, G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)) : G.Mon}:
  %K.sym(Bool, d2, c2, e2) : {G.pick(G.Mon, _, G.mon_add(a2, h2, G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m))
      == G.pick(G.Mon, d1, G.mon_add(a1, h1, G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)) : G.Mon}
  %K.sym(Bool, d1, c1, e1) : {G.pick(G.Mon, c2, G.mon_add(a2, h2, G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m))
      == G.pick(G.Mon, _, G.mon_add(a1, h1, G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)) : G.Mon}
  el_comm2(m, a1, h1, a2, h2, c1, c2)

# LAW (fixed-effect algebra): two KIN stat effects with fixed amounts
# commute, for every board, tribes and sources. This does not establish
# observer or end-of-turn order independence: MAKE before STATS_HAND can
# change the amount. End-of-turn resolution remains sequential.
law kin_comm:
  for b: List<&2, G.Mon>
  for +t1: Nat
  for +s1: Nat
  for +a1: Nat
  for +h1: Nat
  for +t2: Nat
  for +s2: Nat
  for +a2: Nat
  for +h2: Nat
  for +pos: Nat
  {G.kin_go(G.kin_go(b, t1, s1, pos, a1, h1), t2, s2, pos, a2, h2) == G.kin_go(G.kin_go(b, t2, s2, pos, a2, h2), t1, s1, pos, a1, h1) : List<&2, G.Mon>}

def kin_comm(b, t1, s1, a1, h1, t2, s2, a2, h2, pos):
  match b:
    case Nil{}:
      {==}
    case +m <> t:
      +c1 = G.kin_match(G.mon_tribe(m), t1) && Bool.not(G.nat_eq(pos, s1))
      +c2 = G.kin_match(G.mon_tribe(m), t2) && Bool.not(G.nat_eq(pos, s2))
      %kin_comm(t, t1, s1, a1, h1, t2, s2, a2, h2, 1n+pos)
        : {(G.pick(G.Mon, G.kin_match(G.mon_tribe(G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), t2) && Bool.not(G.nat_eq(pos, s2)), G.mon_add(a2, h2, G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)) <> G.kin_go(G.kin_go(t, t1, s1, 1n+pos, a1, h1), t2, s2, 1n+pos, a2, h2))
           == (G.pick(G.Mon, G.kin_match(G.mon_tribe(G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), t1) && Bool.not(G.nat_eq(pos, s1)), G.mon_add(a1, h1, G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)) <> _) : List<&2, G.Mon>}
      Equal.cong(G.Mon, List<&2, G.Mon>, x => x <> G.kin_go(G.kin_go(t, t1, s1, 1n+pos, a1, h1), t2, s2, 1n+pos, a2, h2), G.pick(G.Mon, G.kin_match(G.mon_tribe(G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), t2) && Bool.not(G.nat_eq(pos, s2)), G.mon_add(a2, h2, G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), G.pick(G.Mon, G.kin_match(G.mon_tribe(G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), t1) && Bool.not(G.nat_eq(pos, s1)), G.mon_add(a1, h1, G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)),
        el_comm(m, a1, h1, a2, h2, c1, c2, G.kin_match(G.mon_tribe(G.pick(G.Mon, c2, G.mon_add(a2, h2, m), m)), t1) && Bool.not(G.nat_eq(pos, s1)), G.kin_match(G.mon_tribe(G.pick(G.Mon, c1, G.mon_add(a1, h1, m), m)), t2) && Bool.not(G.nat_eq(pos, s2)),
          cond_keep(c1, a1, h1, m, t2, pos, s2), cond_keep(c2, a2, h2, m, t1, pos, s1)))

# D. Combat damage (G.hurt)
# =========================

# LAW: zero damage changes nothing (in particular it never breaks a Shield)
law hurt_zero:
  for +m: G.Mon
  {G.hurt(m, 0n) == m : G.Mon}

def hurt_zero(m):
  {==}

# LAW: a Shield absorbs any positive hit completely and breaks
law hurt_shield:
  for +c: Nat
  for +a: Nat
  for +h: Nat
  for +d: Nat
  for +gd: Bool
  {G.hurt(G.Mon{c, a, h, True{}, gd}, 1n+d) == G.Mon{c, a, h, False{}, gd} : G.Mon}

def hurt_shield(c, a, h, d, gd):
  {==}

# LAW: an unshielded unit loses exactly the hit minus its Armor,
# saturating at 0; card, attack and golden flag never change. V4: the
# Armor is the printed card Armor for regular AND golden units (gd is
# universally quantified), so a golden unit never doubles its Armor.
law hurt_plain:
  for +c: Nat
  for +a: Nat
  for +h: Nat
  for +d: Nat
  for +gd: Bool
  {G.hurt(G.Mon{c, a, h, False{}, gd}, 1n+d) == G.Mon{c, a, Econ.hp_after(h, Nat.sub(1n+d, G.c_armor(c))), False{}, gd} : G.Mon}

def hurt_plain(c, a, h, d, gd):
  {==}

def mon_hp(m: G.Mon) -> Nat:
  G.Mon{c, a, h, s, g} = m
  h

def hp_after_le(+hp: Nat, +dmg: Nat) -> {Nat.is_le(Econ.hp_after(hp, dmg), hp) == True{} : Bool}:
  match hp dmg:
    case 0n _:
      {==}
    case 1n+h 0n:
      K.le_refl(h)
    case 1n+h 1n+d:
      K.le_step(Nat.sub(h, d), h, hp_after_le(h, d))

def hurt_go_le(z: Bool, +m: G.Mon, +d: Nat) -> {Nat.is_le(mon_hp(G.hurt_go(z, m, d)), mon_hp(m)) == True{} : Bool}:
  match z m:
    case True{} G.Mon{c, a, +h, s, g}:
      K.le_refl(h)
    case False{} G.Mon{+c, a, +h, s, g}:
      match s:
        case True{}:
          K.le_refl(h)
        case False{}:
          hp_after_le(h, Nat.sub(d, G.c_armor(c)))

# LAW: combat damage never heals a unit
law hurt_le:
  for +m: G.Mon
  for +d: Nat
  {Nat.is_le(mon_hp(G.hurt(m, d)), mon_hp(m)) == True{} : Bool}

def hurt_le(m, d):
  hurt_go_le(G.nat_eq(d, 0n), m, d)

# E. Replay and frame laws
# ========================

# LAW: once a replay has recorded an error, no later move changes the
# state, the applied count or the error (the accepted prefix is final)
law replay_sticky:
  for ms: List<&2, String>
  for +g: G.Game
  for +n: Nat
  for +e: G.RErr
  {G.replay_go(ms, G.RSt{g, n, Some{e}}) == G.RSt{g, n, Some{e}} : G.RSt}

def replay_sticky(ms, g, n, e):
  match ms:
    case Nil{}:
      {==}
    case m <> t:
      replay_sticky(t, g, n, e)

# error.index == movesApplied, as a Bool over the engine's replay state
def ErrIdx(st: G.RSt) -> Bool:
  match st:
    case G.RSt{g, +n, err}:
      match err:
        case None{}:
          True{}
        case Some{e}:
          match e:
            case G.RErr{c, msg, idx, mv}:
              G.nat_eq(idx, n)

def eq_refl(n: Nat) -> {G.nat_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def res_idx(r: G.GRes, +g: G.Game, +m: String, +n: Nat) -> {ErrIdx(G.rstep_res(r, g, m, n)) == True{} : Bool}:
  match r:
    case G.GGood{g2}:
      {==}
    case G.GBad{c, msg}:
      eq_refl(n)

def parse_idx(mp: Maybe<&2, G.Act>, +m: String, +g: G.Game, +n: Nat) -> {ErrIdx(G.rstep_parse(mp, m, g, n)) == True{} : Bool}:
  match mp:
    case None{}:
      eq_refl(n)
    case Some{+a}:
      res_idx(G.g_apply(g, a), g, m, n)

def step_idx(+m: String, st: G.RSt, h: {ErrIdx(st) == True{} : Bool}) -> {ErrIdx(G.rstep(m, st)) == True{} : Bool}:
  match st:
    case G.RSt{+g, +n, err}:
      match err:
        case None{}:
          parse_idx(G.parse_move(m), m, g, n)
        case Some{e}:
          h

def go_idx(ms: List<&2, String>, +st: G.RSt, h: {ErrIdx(st) == True{} : Bool}) -> {ErrIdx(G.replay_go(ms, st)) == True{} : Bool}:
  match ms:
    case Nil{}:
      h
    case +m <> t:
      go_idx(t, G.rstep(m, st), step_idx(m, st, h))

def cap_idx(over: Bool, +seed: U32, +mode: Nat, ms: List<&2, String>) -> {ErrIdx(G.replay_cap(over, seed, mode, ms)) == True{} : Bool}:
  match over:
    case True{}:
      {==}
    case False{}:
      go_idx(ms, G.RSt{G.new_game(seed, mode), 0n, None{}}, {==})

# LAW: for every seed, mode and move list, a replay error's index equals
# the number of moves applied (the API's error.index == movesApplied)
law error_index:
  for +seed: U32
  for +mode: Nat
  for +ms: List<&2, String>
  {ErrIdx(G.replay(seed, mode, ms)) == True{} : Bool}

def error_index(seed, mode, ms):
  cap_idx(Nat.is_gt(G.len(String, ms), G.max_moves()), seed, mode, ms)

# Cross-seat frame: a recruit action only ever rewrites the acting seat
def IsRecruit(a: G.Act) -> Bool:
  match a:
    case G.End{}:
      False{}
    case G.Auto{}:
      False{}
    case _:
      True{}

def Frame(g: G.Game, +k: Nat, r: G.GRes) -> Type:
  match r:
    case G.GGood{g2}:
      {G.pget(G.g_players(g2), k) == G.pget(G.g_players(g), k) : G.Player}
    case G.GBad{c, m}:
      Unit

def lift_frame(r: G.PRes, +seed: U32, +mode: Nat, +round: Nat, +actor: Nat, +players: List<&2, G.Player>,
  +fights: List<&2, G.Fight>, +hist: List<&2, G.Fight>, +done: Bool, +k: Nat, hk: {Nat.is_eq(actor, k) == False{} : Bool})
  -> Frame(G.Game{seed, mode, round, actor, players, fights, hist, done}, k, G.lift(r, G.Game{seed, mode, round, actor, players, fights, hist, done})):
  match r:
    case G.PGood{q}:
      Equal.cong(Maybe<&2, G.Player>, G.Player, x => Maybe.default(&2, G.Player, x, G.no_player()),
        List.get(&2, G.Player, List.set(&2, G.Player, players, actor, q), k), List.get(&2, G.Player, players, k),
        K.get_set_ne(G.Player, players, actor, k, q, hk))
    case G.PBad{m}:
      Unit{}

# LAW: for every game state, recruit action and seat k other than the
# actor, the move leaves seat k's record (board, hand, gold, shop, ...)
# exactly as it was: no recruit action writes another seat's record.
# This law makes no claim about reads.
law recruit_frame:
  for +g: G.Game
  for a: G.Act
  for +k: Nat
  for hk: {Nat.is_eq(G.g_actor(g), k) == False{} : Bool}
  for ha: {IsRecruit(a) == True{} : Bool}
  Frame(g, k, G.g_apply(g, a))

def recruit_frame(g, a, k, hk, ha):
  match g:
    case G.Game{+seed, +mode, +round, +actor, +players, +fights, +hist, done}:
      match done a:
        case True{} _:
          Unit{}
        case False{} G.End{}:
          K.ft_absurd(Frame(G.Game{seed, mode, round, actor, players, fights, hist, False{}}, k, G.g_apply(G.Game{seed, mode, round, actor, players, fights, hist, False{}}, G.End{})), ha)
        case False{} G.Auto{}:
          K.ft_absurd(Frame(G.Game{seed, mode, round, actor, players, fights, hist, False{}}, k, G.g_apply(G.Game{seed, mode, round, actor, players, fights, hist, False{}}, G.Auto{})), ha)
        case False{} G.Buy{+i}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Buy{i}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)
        case False{} G.Play{+i}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Play{i}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)
        case False{} G.Sell{+i}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Sell{i}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)
        case False{} G.Swap{+i, +j}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Swap{i, j}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)
        case False{} G.Roll{}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Roll{}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)
        case False{} G.Freeze{}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Freeze{}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)
        case False{} G.Upgrade{}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Upgrade{}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)
        case False{} G.Invest{}:
          lift_frame(G.p_apply(seed, round, G.pget(players, actor), G.Invest{}), seed, mode, round, actor, players, fights, hist, False{}, k, hk)

# F. Legal actions
# ================

# every action of a list is accepted by p_apply, as copyable evidence
def AllAcc(+seed: U32, +round: Nat, +p: G.Player, xs: List<&2, G.Act>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case a <> t:
      K.Both<K.T(G.pres_ok(G.p_apply(seed, round, p, a))), AllAcc(seed, round, p, t)>

def keep_acc(c: Bool, +seed: U32, +round: Nat, +p: G.Player, +a: G.Act, +r: List<&2, G.Act>,
  e: {G.pres_ok(G.p_apply(seed, round, p, a)) == c : Bool}, h: AllAcc(seed, round, p, r))
  -> AllAcc(seed, round, p, G.pick(List<&2, G.Act>, c, a <> r, r)):
  match c:
    case True{}:
      K.Both{K.to_T(G.pres_ok(G.p_apply(seed, round, p, a)), e), h}
    case False{}:
      h

def filter_acc(+xs: List<&2, G.Act>, +seed: U32, +round: Nat, +p: G.Player) -> AllAcc(seed, round, p, G.legal_filter(xs, seed, round, p)):
  match xs:
    case Nil{}:
      Unit{}
    case +a <> t:
      keep_acc(G.pres_ok(G.p_apply(seed, round, p, a)), seed, round, p, a, G.legal_filter(t, seed, round, p), {==}, filter_acc(t, seed, round, p))

# LAW (legal-action soundness): every recruit action the engine lists as
# legal for a player is accepted by the same p_apply the replay runs
law legal_sound:
  for +seed: U32
  for +round: Nat
  for +p: G.Player
  AllAcc(seed, round, p, G.legal_acts(seed, round, p))

def legal_sound(seed, round, p):
  filter_acc(G.recruit_cands(p), seed, round, p)
