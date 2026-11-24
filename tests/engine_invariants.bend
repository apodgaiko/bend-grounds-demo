# Bend Grounds v2: whole-engine zone invariants, proven on the real engine.
#
#   bun vendor/bend/bend2/main.ts tests/engine_invariants.bend --verdict
#
# Every law below is universally quantified over the engine's own types
# and functions (G.Player, G.Game, G.Act, G.p_apply, G.g_apply, G.replay).
# Nothing in the engine is re-implemented. The zone predicate reads state
# through the engine's own accessors p_board / p_hand.
#
# Result: every state the API can return has at most 5 units on every
# seat's board AND at most 7 cards in every seat's hand, for every seed,
# mode and move list (replay_zone_cap, with board/hand corollaries).

import Base
import ../engine/econ.bend as Econ
import ../engine/game.bend as G
import ./proof_kit.bend as K
import ./v4_golden_laws.bend as V

law hp_after_le:
  for +hp: Nat
  for +dmg: Nat
  {Nat.is_le(Econ.hp_after(hp, dmg), hp) == True{} : Bool}

def hp_after_le(hp, dmg):
  match hp dmg:
    case 0n _:
      {==}
    case 1n+h 0n:
      K.le_refl(h)
    case 1n+h 1n+d:
      K.le_step(Nat.sub(h, d), h, hp_after_le(h, d))

# Length lemmas over the engine's own list helpers
# ------------------------------------------------

law remove_le:
  for -A: Data
  for +xs: List<&2, A>
  for n: Nat
  {Nat.is_le(G.len(A, G.remove_at(A, xs, n)), G.len(A, xs)) == True{} : Bool}

def remove_le(A, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      K.le_step(G.len(A, t), G.len(A, t), K.le_refl(G.len(A, t)))
    case h <> t 1n+p:
      remove_le(A, t, p)

# snoc adds exactly one element
def len_snoc(-A: Data, xs: List<&2, A>, x: A) -> {1n+G.len(A, xs) == G.len(A, G.snoc(A, xs, x)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %len_snoc(A, t, x) : {2n+G.len(A, t) == 1n+_ : Nat}
      {==}

def len_swap_fin(-A: Data, +xs: List<&2, A>, +i: Nat, +j: Nat, mi: Maybe<&2, A>, mj: Maybe<&2, A>) -> {G.len(A, G.swap_fin(A, xs, i, j, mi, mj)) == G.len(A, xs) : Nat}:
  match mi mj:
    case Some{+x} Some{+y}:
      Equal.trans(Nat, G.len(A, List.set(&2, A, List.set(&2, A, xs, i, y), j, x)),
        G.len(A, List.set(&2, A, xs, i, y)), G.len(A, xs),
        K.len_set(A, List.set(&2, A, xs, i, y), j, x), K.len_set(A, xs, i, y))
    case Some{x} None{}:
      {==}
    case None{} _:
      {==}

# The zone predicate
# ------------------

def BoardOk(p: G.Player) -> Bool:
  Nat.is_le(G.len(G.Mon, G.p_board(p)), 5n)

def HandOk(p: G.Player) -> Bool:
  Nat.is_le(G.len(G.Mon, G.p_hand(p)), 7n)

# board <= 5 and hand <= 7, as copyable evidence
def ZOk(p: G.Player) -> Data:
  K.Both<K.T(BoardOk(p)), K.T(HandOk(p))>

# V4: triple assembly (p_norm) never grows a zone (V.norm_zones, proven for
# every player), so it keeps board <= 5 and hand <= 7
def norm_ok_go(+p: G.Player, h: ZOk(p), hn: V.Lens(G.p_norm(p), G.len(G.Mon, G.p_hand(p)), G.len(G.Mon, G.p_board(p)))) -> ZOk(G.p_norm(p)):
  K.Both{wb, wh} = h
  K.Both{nh, nb} = hn
  K.Both{K.to_T(BoardOk(G.p_norm(p)),
      K.le_trans(G.len(G.Mon, G.p_board(G.p_norm(p))), G.len(G.Mon, G.p_board(p)), 5n,
        K.from_T(Nat.is_le(G.len(G.Mon, G.p_board(G.p_norm(p))), G.len(G.Mon, G.p_board(p))), nb), K.from_T(BoardOk(p), wb))),
    K.to_T(HandOk(G.p_norm(p)),
      K.le_trans(G.len(G.Mon, G.p_hand(G.p_norm(p))), G.len(G.Mon, G.p_hand(p)), 7n,
        K.from_T(Nat.is_le(G.len(G.Mon, G.p_hand(G.p_norm(p))), G.len(G.Mon, G.p_hand(p))), nh), K.from_T(HandOk(p), wh)))}

def norm_ok(+p: G.Player, h: ZOk(p)) -> ZOk(G.p_norm(p)):
  norm_ok_go(p, h, V.norm_zones(p))

# The effect interpreter (Fx) never adds or removes board units
# -------------------------------------------------------------
# Every stat effect is a map over the board; GOLD and MAKE leave the board
# alone; only fx_enter (the played card joining) adds exactly one unit.

def FB(fx: G.Fx) -> Nat:
  G.len(G.Mon, G.fx_board(fx))

def FH(fx: G.Fx) -> Nat:
  G.len(G.Mon, G.fx_hand(fx))

def len_kin(b: List<&2, G.Mon>, +tr: Nat, +skip: Nat, +pos: Nat, +da: Nat, +dh: Nat) -> {G.len(G.Mon, G.kin_go(b, tr, skip, pos, da, dh)) == G.len(G.Mon, b) : Nat}:
  match b:
    case Nil{}:
      {==}
    case +m <> t:
      %len_kin(t, tr, skip, 1n+pos, da, dh) : {1n+G.len(G.Mon, G.kin_go(t, tr, skip, 1n+pos, da, dh)) == 1n+_ : Nat}
      {==}

def len_at(b: List<&2, G.Mon>, +k: Nat, +pos: Nat, +da: Nat, +dh: Nat) -> {G.len(G.Mon, G.at_go(b, k, pos, da, dh)) == G.len(G.Mon, b) : Nat}:
  match b:
    case Nil{}:
      {==}
    case +m <> t:
      %len_at(t, k, 1n+pos, da, dh) : {1n+G.len(G.Mon, G.at_go(t, k, 1n+pos, da, dh)) == 1n+_ : Nat}
      {==}

def self_len(ob: Bool, +src: Nat, +da: Nat, +dh: Nat, fx: G.Fx) -> {FB(G.fx_self(ob, src, da, dh, fx)) == FB(fx) : Nat}:
  match ob fx:
    case True{} G.Fx{board, me, hand, gold, fp}:
      len_at(board, src, 0n, da, dh)
    case False{} G.Fx{board, me, hand, gold, fp}:
      {==}

def stats_len(tgt: Nat, +src: Nat, +tr: Nat, +da: Nat, +dh: Nat, fx: G.Fx) -> {FB(G.fx_stats(tgt, src, tr, da, dh, fx)) == FB(fx) : Nat}:
  match tgt:
    case 0n:
      self_len(Bool.not(G.nat_eq(src, G.entering())), src, da, dh, fx)
    case 1n+u:
      match fx:
        case G.Fx{board, me, hand, gold, fp}:
          len_kin(board, tr, src, 0n, da, dh)

# MAKE (fired once, or twice for a golden source) only touches the hand
def make_len(+seed: U32, +key: List<&2, Nat>, +tr: Nat, +tier: Nat, fx: G.Fx) -> {FB(G.fx_make(seed, key, tr, tier, fx)) == FB(fx) : Nat}:
  match fx:
    case G.Fx{board, me, hand, gold, fp}:
      {==}

def make_n_len(gd: Bool, +seed: U32, +key: List<&2, Nat>, +tr: Nat, +tier: Nat, +fx: G.Fx) -> {FB(G.fx_make_n(gd, seed, key, tr, tier, fx)) == FB(fx) : Nat}:
  match gd:
    case True{}:
      Equal.trans(Nat, FB(G.fx_make(seed, G.snoc(Nat, key, 1n), tr, tier, G.fx_make(seed, key, tr, tier, fx))), FB(G.fx_make(seed, key, tr, tier, fx)), FB(fx),
        make_len(seed, G.snoc(Nat, key, 1n), tr, tier, G.fx_make(seed, key, tr, tier, fx)), make_len(seed, key, tr, tier, fx))
    case False{}:
      make_len(seed, key, tr, tier, fx)

def abil_len(+seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, x: G.Abil, +fx: G.Fx) -> {FB(G.fx_abil(seed, key, src, tr, gd, x, fx)) == FB(fx) : Nat}:
  match x:
    case G.Abil{trig, tgt, eff, +a, +h}:
      match eff:
        case 0n:
          stats_len(tgt, src, tr, a, h, fx)
        case 1n+u:
          match u:
            case 0n:
              +k = Nat.min(G.len(G.Mon, G.fx_hand(fx)), 4n)
              stats_len(tgt, src, tr, Nat.mul(a, k), Nat.mul(h, k), fx)
            case 1n+v:
              match v:
                case 0n:
                  match fx:
                    case G.Fx{board, me, hand, gold, fp}:
                      {==}
                case 1n+w:
                  match w:
                    case 0n:
                      make_n_len(gd, seed, key, tr, a, fx)
                    case 1n+z:
                      +k = Nat.min(G.fx_plays(fx), 4n)
                      stats_len(tgt, src, tr, Nat.mul(a, k), Nat.mul(h, k), fx)

def if_len(ok: Bool, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, x: G.Abil, +fx: G.Fx) -> {FB(G.fx_if(ok, seed, key, src, tr, gd, x, fx)) == FB(fx) : Nat}:
  match ok:
    case True{}:
      abil_len(seed, key, src, tr, gd, x, fx)
    case False{}:
      {==}

law abils_len:
  for xs: List<&2, G.Abil>
  for +want: Nat
  for +seed: U32
  for +key: List<&2, Nat>
  for +src: Nat
  for +tr: Nat
  for +gd: Bool
  for +slot: Nat
  for +fx: G.Fx
  {FB(G.fx_abils(xs, want, seed, key, src, tr, gd, slot, fx)) == FB(fx) : Nat}

def abils_len(xs, want, seed, key, src, tr, gd, slot, fx):
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      +fx2 = G.fx_if(G.nat_eq(G.abil_trig(x), want), seed, G.snoc(Nat, key, slot), src, tr, gd, x, fx)
      Equal.trans(Nat, FB(G.fx_abils(t, want, seed, key, src, tr, gd, 1n+slot, fx2)), FB(fx2), FB(fx),
        abils_len(t, want, seed, key, src, tr, gd, 1n+slot, fx2),
        if_len(G.nat_eq(G.abil_trig(x), want), seed, G.snoc(Nat, key, slot), src, tr, gd, x, fx))

def when_len(ok: Bool, xs: List<&2, G.Abil>, +want: Nat, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, +fx: G.Fx) -> {FB(G.fx_when(ok, xs, want, seed, key, src, tr, gd, fx)) == FB(fx) : Nat}:
  match ok:
    case True{}:
      abils_len(xs, want, seed, key, src, tr, gd, 0n, fx)
    case False{}:
      {==}

law observe_len:
  for fuel: Nat
  for +pos: Nat
  for +seed: U32
  for +key: List<&2, Nat>
  for +tr: Nat
  for +fx: G.Fx
  {FB(G.observe(fuel, pos, seed, key, tr, fx)) == FB(fx) : Nat}

def observe_len(fuel, pos, seed, key, tr, fx):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      +u = G.get_or(G.Mon, G.fx_board(fx), pos, G.mon_of(0n))
      +fx2 = G.fx_when(G.kin_match(G.mon_tribe(u), tr), G.mon_abils(u), 1n, seed, G.snoc(Nat, key, pos), pos, tr, G.mon_golden(u), fx)
      Equal.trans(Nat, FB(G.observe(f, 1n+pos, seed, key, tr, fx2)), FB(fx2), FB(fx),
        observe_len(f, 1n+pos, seed, key, tr, fx2),
        when_len(G.kin_match(G.mon_tribe(u), tr), G.mon_abils(u), 1n, seed, G.snoc(Nat, key, pos), pos, tr, G.mon_golden(u), fx))

law endturn_len:
  for fuel: Nat
  for +pos: Nat
  for +seed: U32
  for +key: List<&2, Nat>
  for +fx: G.Fx
  {FB(G.endturn(fuel, pos, seed, key, fx)) == FB(fx) : Nat}

def endturn_len(fuel, pos, seed, key, fx):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      +u = G.get_or(G.Mon, G.fx_board(fx), pos, G.mon_of(0n))
      +fx2 = G.fx_abils(G.mon_abils(u), 2n, seed, G.snoc(Nat, key, pos), pos, G.mon_tribe(u), G.mon_golden(u), 0n, fx)
      Equal.trans(Nat, FB(G.endturn(f, 1n+pos, seed, key, fx2)), FB(fx2), FB(fx),
        endturn_len(f, 1n+pos, seed, key, fx2),
        abils_len(G.mon_abils(u), 2n, seed, G.snoc(Nat, key, pos), pos, G.mon_tribe(u), G.mon_golden(u), 0n, fx))

def enter_len(fx: G.Fx) -> {FB(G.fx_enter(fx)) == 1n+FB(fx) : Nat}:
  match fx:
    case G.Fx{board, +me, hand, gold, fp}:
      K.sym(Nat, 1n+G.len(G.Mon, board), G.len(G.Mon, G.snoc(G.Mon, board, me)), len_snoc(G.Mon, board, me))

# LAW: a play adds exactly one unit to the board, whatever the abilities
law play_fx_len:
  for +seed: U32
  for +id: Nat
  for +round: Nat
  for +plays: Nat
  for +m: G.Mon
  for +board: List<&2, G.Mon>
  for +hand: List<&2, G.Mon>
  for +gold: Nat
  {FB(G.play_fx(seed, id, round, plays, m, board, hand, gold)) == 1n+G.len(G.Mon, board) : Nat}

def play_fx_len(seed, id, round, plays, m, board, hand, gold):
  +tr = G.mon_tribe(m)
  +f0 = {G.Fx{board, m, hand, gold, plays} : G.Fx}
  +f1 = G.fx_abils(G.mon_abils(m), 0n, seed, [10n, id, round, plays], G.entering(), tr, G.mon_golden(m), 0n, f0)
  +f2 = G.fx_enter(f1)
  Equal.trans(Nat, FB(G.observe(G.len(G.Mon, board), 0n, seed, [13n, id, round, plays], tr, f2)), FB(f2), 1n+G.len(G.Mon, board),
    observe_len(G.len(G.Mon, board), 0n, seed, [13n, id, round, plays], tr, f2),
    Equal.trans(Nat, FB(f2), 1n+FB(f1), 1n+G.len(G.Mon, board), enter_len(f1),
      Equal.cong(Nat, Nat, x => 1n+x, FB(f1), FB(f0),
        abils_len(G.mon_abils(m), 0n, seed, [10n, id, round, plays], G.entering(), tr, G.mon_golden(m), 0n, f0))))

# The hand only grows through the guarded hand_put
# ------------------------------------------------

def H7(fx: G.Fx) -> Bool:
  Nat.is_le(FH(fx), 7n)

def hand_put_ok(room: Bool, +hand: List<&2, G.Mon>, m: G.Mon, hr: {G.hand_room(G.len(G.Mon, hand)) == room : Bool},
  h: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool}) -> {Nat.is_le(G.len(G.Mon, G.hand_put(room, hand, m)), 7n) == True{} : Bool}:
  match room:
    case True{}:
      %len_snoc(G.Mon, hand, m) : {Nat.is_le(_, 7n) == True{} : Bool}
      K.lt_succ_le(G.len(G.Mon, hand), 7n, hr)
    case False{}:
      h

# LAW: hand_add never takes a hand of at most 7 above 7
law hand_add_ok:
  for +hand: List<&2, G.Mon>
  for m: G.Mon
  for h: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool}
  {Nat.is_le(G.len(G.Mon, G.hand_add(hand, m)), 7n) == True{} : Bool}

def hand_add_ok(hand, m, h):
  hand_put_ok(G.hand_room(G.len(G.Mon, hand)), hand, m, {==}, h)

def maybe_ok(mc: Maybe<&2, Nat>, +hand: List<&2, G.Mon>, h: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool}) -> {Nat.is_le(G.len(G.Mon, G.hand_maybe(mc, hand)), 7n) == True{} : Bool}:
  match mc:
    case None{}:
      h
    case Some{c}:
      hand_add_ok(hand, G.mon_of(c), h)

def self_hand(ob: Bool, +src: Nat, +da: Nat, +dh: Nat, fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_self(ob, src, da, dh, fx)) == True{} : Bool}:
  match ob fx:
    case True{} G.Fx{board, me, hand, gold, fp}:
      h
    case False{} G.Fx{board, me, hand, gold, fp}:
      h

def stats_hand(tgt: Nat, +src: Nat, +tr: Nat, +da: Nat, +dh: Nat, fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_stats(tgt, src, tr, da, dh, fx)) == True{} : Bool}:
  match tgt:
    case 0n:
      self_hand(Bool.not(G.nat_eq(src, G.entering())), src, da, dh, fx, h)
    case 1n+u:
      match fx:
        case G.Fx{board, me, hand, gold, fp}:
          h

def make_hand(+seed: U32, +key: List<&2, Nat>, +tr: Nat, +tier: Nat, fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_make(seed, key, tr, tier, fx)) == True{} : Bool}:
  match fx:
    case G.Fx{board, me, +hand, gold, fp}:
      +pool = G.make_pool(G.card_list(), tr, tier)
      maybe_ok(G.make_pick(G.len(Nat, pool), pool, G.hash(seed, key)), hand, h)

def make_n_hand(gd: Bool, +seed: U32, +key: List<&2, Nat>, +tr: Nat, +tier: Nat, +fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_make_n(gd, seed, key, tr, tier, fx)) == True{} : Bool}:
  match gd:
    case True{}:
      make_hand(seed, G.snoc(Nat, key, 1n), tr, tier, G.fx_make(seed, key, tr, tier, fx), make_hand(seed, key, tr, tier, fx, h))
    case False{}:
      make_hand(seed, key, tr, tier, fx, h)

def abil_hand(+seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, x: G.Abil, +fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_abil(seed, key, src, tr, gd, x, fx)) == True{} : Bool}:
  match x:
    case G.Abil{trig, tgt, eff, +a, +h2}:
      match eff:
        case 0n:
          stats_hand(tgt, src, tr, a, h2, fx, h)
        case 1n+u:
          match u:
            case 0n:
              +k = Nat.min(G.len(G.Mon, G.fx_hand(fx)), 4n)
              stats_hand(tgt, src, tr, Nat.mul(a, k), Nat.mul(h2, k), fx, h)
            case 1n+v:
              match v:
                case 0n:
                  match fx:
                    case G.Fx{board, me, hand, gold, fp}:
                      h
                case 1n+w:
                  match w:
                    case 0n:
                      make_n_hand(gd, seed, key, tr, a, fx, h)
                    case 1n+z:
                      +k = Nat.min(G.fx_plays(fx), 4n)
                      stats_hand(tgt, src, tr, Nat.mul(a, k), Nat.mul(h2, k), fx, h)

def if_hand(ok: Bool, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, x: G.Abil, +fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_if(ok, seed, key, src, tr, gd, x, fx)) == True{} : Bool}:
  match ok:
    case True{}:
      abil_hand(seed, key, src, tr, gd, x, fx, h)
    case False{}:
      h

def abils_hand(xs: List<&2, G.Abil>, +want: Nat, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, +slot: Nat, +fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_abils(xs, want, seed, key, src, tr, gd, slot, fx)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> t:
      abils_hand(t, want, seed, key, src, tr, gd, 1n+slot, G.fx_if(G.nat_eq(G.abil_trig(x), want), seed, G.snoc(Nat, key, slot), src, tr, gd, x, fx),
        if_hand(G.nat_eq(G.abil_trig(x), want), seed, G.snoc(Nat, key, slot), src, tr, gd, x, fx, h))

def when_hand(ok: Bool, xs: List<&2, G.Abil>, +want: Nat, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, +fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_when(ok, xs, want, seed, key, src, tr, gd, fx)) == True{} : Bool}:
  match ok:
    case True{}:
      abils_hand(xs, want, seed, key, src, tr, gd, 0n, fx, h)
    case False{}:
      h

def observe_hand(fuel: Nat, +pos: Nat, +seed: U32, +key: List<&2, Nat>, +tr: Nat, +fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.observe(fuel, pos, seed, key, tr, fx)) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+f:
      +u = G.get_or(G.Mon, G.fx_board(fx), pos, G.mon_of(0n))
      observe_hand(f, 1n+pos, seed, key, tr, G.fx_when(G.kin_match(G.mon_tribe(u), tr), G.mon_abils(u), 1n, seed, G.snoc(Nat, key, pos), pos, tr, G.mon_golden(u), fx),
        when_hand(G.kin_match(G.mon_tribe(u), tr), G.mon_abils(u), 1n, seed, G.snoc(Nat, key, pos), pos, tr, G.mon_golden(u), fx, h))

def endturn_hand(fuel: Nat, +pos: Nat, +seed: U32, +key: List<&2, Nat>, +fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.endturn(fuel, pos, seed, key, fx)) == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+f:
      +u = G.get_or(G.Mon, G.fx_board(fx), pos, G.mon_of(0n))
      endturn_hand(f, 1n+pos, seed, key, G.fx_abils(G.mon_abils(u), 2n, seed, G.snoc(Nat, key, pos), pos, G.mon_tribe(u), G.mon_golden(u), 0n, fx),
        abils_hand(G.mon_abils(u), 2n, seed, G.snoc(Nat, key, pos), pos, G.mon_tribe(u), G.mon_golden(u), 0n, fx, h))

def enter_hand(fx: G.Fx, h: {H7(fx) == True{} : Bool}) -> {H7(G.fx_enter(fx)) == True{} : Bool}:
  match fx:
    case G.Fx{board, me, hand, gold, fp}:
      h

def play_fx_hand(+seed: U32, +id: Nat, +round: Nat, +plays: Nat, +m: G.Mon, +board: List<&2, G.Mon>, +hand: List<&2, G.Mon>, +gold: Nat,
  h: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool}) -> {H7(G.play_fx(seed, id, round, plays, m, board, hand, gold)) == True{} : Bool}:
  +tr = G.mon_tribe(m)
  +f1 = G.fx_abils(G.mon_abils(m), 0n, seed, [10n, id, round, plays], G.entering(), tr, G.mon_golden(m), 0n, G.Fx{board, m, hand, gold, plays})
  observe_hand(G.len(G.Mon, board), 0n, seed, [13n, id, round, plays], tr, G.fx_enter(f1),
    enter_hand(f1, abils_hand(G.mon_abils(m), 0n, seed, [10n, id, round, plays], G.entering(), tr, G.mon_golden(m), 0n, G.Fx{board, m, hand, gold, plays}, h)))

# Reading an Fx back into the player (play_fin / sell_fin / grow_fin)
def fin_ok(fx: G.Fx, +p: G.Player, hb: {Nat.is_le(FB(fx), 5n) == True{} : Bool}, hh: {H7(fx) == True{} : Bool}) -> ZOk(G.play_fin(fx, p)):
  match fx p:
    case G.Fx{nb, me, nh, ng, np} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, nb), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, nh), 7n), hh)}

def sfin_ok(fx: G.Fx, +p: G.Player, hb: {Nat.is_le(FB(fx), 5n) == True{} : Bool}, hh: {H7(fx) == True{} : Bool}) -> ZOk(G.sell_fin(fx, p)):
  match fx p:
    case G.Fx{nb, me, nh, ng, np} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, nb), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, nh), 7n), hh)}

def gfin_ok(fx: G.Fx, +p: G.Player, hb: {Nat.is_le(FB(fx), 5n) == True{} : Bool}, hh: {H7(fx) == True{} : Bool}) -> ZOk(G.grow_fin(fx, p)):
  match fx p:
    case G.Fx{nb, me, nh, ng, np} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, nb), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, nh), 7n), hh)}

# Per-action lemmas: each recruit helper keeps both zones in bounds.
# Guards are tied to the engine's own expression (hr), never a free Bool.

def buy_lem(mc: Maybe<&2, Nat>, room: Bool, mg: Maybe<&2, Nat>, +id: Nat, +hp: Nat, +gold: Nat, +tier: Nat, +upcost: Nat, +invest: Nat, +frozen: Bool, +rolls: Nat, +board: List<&2, G.Mon>, +shop: List<&2, Nat>, +alive: Bool, +out: Nat, +hand: List<&2, G.Mon>, +plays: Nat, +i: Nat, hr: {G.hand_room(G.len(G.Mon, hand)) == room : Bool},
  hb: {Nat.is_le(G.len(G.Mon, board), 5n) == True{} : Bool}, hh: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool})
  -> ZOk(G.pres_or(G.buy_go(mc, room, mg, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})):
  match mc room mg:
    case None{} _ _:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case Some{c} False{} _:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case Some{c} True{} None{}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case Some{+c} True{} Some{+g}:
      norm_ok(G.buy_apply(G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i, c, g),
        K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb),
          K.to_T(Nat.is_le(G.len(G.Mon, G.hand_add(hand, G.mon_of(c))), 7n), hand_add_ok(hand, G.mon_of(c), hh))})
def play_lem(mm: Maybe<&2, G.Mon>, room: Bool, +seed: U32, +round: Nat, +id: Nat, +hp: Nat, +gold: Nat, +tier: Nat, +upcost: Nat, +invest: Nat, +frozen: Bool, +rolls: Nat, +board: List<&2, G.Mon>, +shop: List<&2, Nat>, +alive: Bool, +out: Nat, +hand: List<&2, G.Mon>, +plays: Nat, +i: Nat, hr: {Econ.has_room(G.len(G.Mon, board)) == room : Bool},
  hb: {Nat.is_le(G.len(G.Mon, board), 5n) == True{} : Bool}, hh: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool})
  -> ZOk(G.pres_or(G.play_go(mm, room, seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})):
  match mm room:
    case None{} _:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case Some{m} False{}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case Some{+m} True{}:
      +h2 = G.remove_at(G.Mon, hand, i)
      +fx = G.play_fx(seed, id, round, plays, m, board, h2, gold)
      norm_ok(G.play_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i, m),
        fin_ok(fx, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays},
          %K.sym(Nat, FB(fx), 1n+G.len(G.Mon, board), play_fx_len(seed, id, round, plays, m, board, h2, gold)) : {Nat.is_le(_, 5n) == True{} : Bool}
          K.lt_succ_le(G.len(G.Mon, board), 5n, hr),
          play_fx_hand(seed, id, round, plays, m, board, h2, gold,
            K.le_trans(G.len(G.Mon, h2), G.len(G.Mon, hand), 7n, remove_le(G.Mon, hand, i), hh))))
def sell_lem(mm: Maybe<&2, G.Mon>, +seed: U32, +round: Nat, +id: Nat, +hp: Nat, +gold: Nat, +tier: Nat, +upcost: Nat, +invest: Nat, +frozen: Bool, +rolls: Nat, +board: List<&2, G.Mon>, +shop: List<&2, Nat>, +alive: Bool, +out: Nat, +hand: List<&2, G.Mon>, +plays: Nat, +i: Nat,
  hb: {Nat.is_le(G.len(G.Mon, board), 5n) == True{} : Bool}, hh: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool})
  -> ZOk(G.pres_or(G.sell_go(mm, seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})):
  match mm:
    case None{}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case Some{+m}:
      +b2 = G.remove_at(G.Mon, board, i)
      +f0 = {G.Fx{b2, m, hand, Nat.add(gold, G.sell_refund()), plays} : G.Fx}
      +xs = G.mon_abils(m)
      +gd = G.mon_golden(m)
      +key = {[12n, id, round, plays, gold] : List<&2, Nat>}
      norm_ok(G.sell_apply(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i, m),
        sfin_ok(G.fx_abils(xs, 3n, seed, key, G.entering(), G.mon_tribe(m), gd, 0n, f0), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays},
          %K.sym(Nat, FB(G.fx_abils(xs, 3n, seed, key, G.entering(), G.mon_tribe(m), gd, 0n, f0)), FB(f0), abils_len(xs, 3n, seed, key, G.entering(), G.mon_tribe(m), gd, 0n, f0)) : {Nat.is_le(_, 5n) == True{} : Bool}
          K.le_trans(G.len(G.Mon, b2), G.len(G.Mon, board), 5n, remove_le(G.Mon, board, i), hb),
          abils_hand(xs, 3n, seed, key, G.entering(), G.mon_tribe(m), gd, 0n, f0, hh)))
def swap_lem(ok: Bool, +id: Nat, +hp: Nat, +gold: Nat, +tier: Nat, +upcost: Nat, +invest: Nat, +frozen: Bool, +rolls: Nat, +board: List<&2, G.Mon>, +shop: List<&2, Nat>, +alive: Bool, +out: Nat, +hand: List<&2, G.Mon>, +plays: Nat, +i: Nat, +j: Nat,
  hb: {Nat.is_le(G.len(G.Mon, board), 5n) == True{} : Bool}, hh: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool})
  -> ZOk(G.pres_or(G.swap_go(ok, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, i, j), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})):
  match ok:
    case False{}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case True{}:
      +mi = List.get(&2, G.Mon, board, i)
      +mj = List.get(&2, G.Mon, board, j)
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, G.swap_fin(G.Mon, board, i, j, mi, mj)), 5n),
          %K.sym(Nat, G.len(G.Mon, G.swap_fin(G.Mon, board, i, j, mi, mj)), G.len(G.Mon, board), len_swap_fin(G.Mon, board, i, j, mi, mj)) : {Nat.is_le(_, 5n) == True{} : Bool}
          hb),
        K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
def roll_lem(mg: Maybe<&2, Nat>, +seed: U32, +round: Nat, +id: Nat, +hp: Nat, +gold: Nat, +tier: Nat, +upcost: Nat, +invest: Nat, +frozen: Bool, +rolls: Nat, +board: List<&2, G.Mon>, +shop: List<&2, Nat>, +alive: Bool, +out: Nat, +hand: List<&2, G.Mon>, +plays: Nat,
  hb: {Nat.is_le(G.len(G.Mon, board), 5n) == True{} : Bool}, hh: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool})
  -> ZOk(G.pres_or(G.roll_go(mg, seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})):
  match mg:
    case None{}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case Some{g}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
def upgrade_lem(ok: Bool, mg: Maybe<&2, Nat>, +id: Nat, +hp: Nat, +gold: Nat, +tier: Nat, +upcost: Nat, +invest: Nat, +frozen: Bool, +rolls: Nat, +board: List<&2, G.Mon>, +shop: List<&2, Nat>, +alive: Bool, +out: Nat, +hand: List<&2, G.Mon>, +plays: Nat,
  hb: {Nat.is_le(G.len(G.Mon, board), 5n) == True{} : Bool}, hh: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool})
  -> ZOk(G.pres_or(G.upgrade_go(ok, mg, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})):
  match ok mg:
    case False{} _:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case True{} None{}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case True{} Some{g}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
def invest_lem(ok: Bool, mg: Maybe<&2, Nat>, +id: Nat, +hp: Nat, +gold: Nat, +tier: Nat, +upcost: Nat, +invest: Nat, +frozen: Bool, +rolls: Nat, +board: List<&2, G.Mon>, +shop: List<&2, Nat>, +alive: Bool, +out: Nat, +hand: List<&2, G.Mon>, +plays: Nat,
  hb: {Nat.is_le(G.len(G.Mon, board), 5n) == True{} : Bool}, hh: {Nat.is_le(G.len(G.Mon, hand), 7n) == True{} : Bool})
  -> ZOk(G.pres_or(G.invest_go(ok, mg, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}), G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays})):
  match ok mg:
    case False{} _:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case True{} None{}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
    case True{} Some{g}:
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, board), 5n), hb), K.to_T(Nat.is_le(G.len(G.Mon, hand), 7n), hh)}
# split copyable zone evidence into its two equalities
def zb(+b: List<&2, G.Mon>, -hd: List<&2, G.Mon>, h: K.Both<K.T(Nat.is_le(G.len(G.Mon, b), 5n)), K.T(Nat.is_le(G.len(G.Mon, hd), 7n))>) -> {Nat.is_le(G.len(G.Mon, b), 5n) == True{} : Bool}:
  K.Both{wb, wh} = h
  K.from_T(Nat.is_le(G.len(G.Mon, b), 5n), wb)

def zh(-b: List<&2, G.Mon>, +hd: List<&2, G.Mon>, h: K.Both<K.T(Nat.is_le(G.len(G.Mon, b), 5n)), K.T(Nat.is_le(G.len(G.Mon, hd), 7n))>) -> {Nat.is_le(G.len(G.Mon, hd), 7n) == True{} : Bool}:
  K.Both{wb, wh} = h
  K.from_T(Nat.is_le(G.len(G.Mon, hd), 7n), wh)

# LAW: every recruit action (human, agent or bot: bots call the same
# p_apply), accepted or rejected, keeps board <= 5 and hand <= 7. A
# rejected action is read the way the engine reads it: pres_or keeps p.
law zone_cap_step:
  for +seed: U32
  for +round: Nat
  for +p: G.Player
  for a: G.Act
  for +h: ZOk(p)
  ZOk(G.pres_or(G.p_apply(seed, round, p, a), p))

def zone_cap_step(seed, round, p, a, h):
  match p:
    case G.Player{+id, +hp, +gold, +tier, +upcost, +invest, +frozen, +rolls, +board, +shop, +alive, +out, +hand, +plays}:
      match a:
        case G.Buy{+i}:
          buy_lem(List.get(&2, Nat, shop, i), G.hand_room(G.len(G.Mon, hand)), Econ.spend(gold, G.buy_cost()),
            id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, i, {==}, zb(board, hand, h), zh(board, hand, h))
        case G.Play{+i}:
          play_lem(List.get(&2, G.Mon, hand, i), Econ.has_room(G.len(G.Mon, board)), seed, round,
            id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, i, {==}, zb(board, hand, h), zh(board, hand, h))
        case G.Sell{+i}:
          sell_lem(List.get(&2, G.Mon, board, i), seed, round, id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, i, zb(board, hand, h), zh(board, hand, h))
        case G.Swap{+i, +j}:
          +n = G.len(G.Mon, board)
          swap_lem(Nat.is_lt(i, n) && Nat.is_lt(j, n) && Nat.is_ne(i, j), id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, i, j, zb(board, hand, h), zh(board, hand, h))
        case G.Roll{}:
          roll_lem(Econ.spend(gold, G.roll_cost()), seed, round, id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, zb(board, hand, h), zh(board, hand, h))
        case G.Freeze{}:
          h
        case G.Upgrade{}:
          upgrade_lem(Nat.is_lt(tier, G.max_tier()), Econ.spend(gold, upcost), id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, zb(board, hand, h), zh(board, hand, h))
        case G.Invest{}:
          invest_lem(Nat.is_lt(invest, G.max_invest()), Econ.spend(gold, G.invest_cost()), id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays, zb(board, hand, h), zh(board, hand, h))
        case G.End{}:
          h
        case G.Auto{}:
          h

# Bots: every bot step goes through p_apply
# -----------------------------------------

def bot_try_ok(ma: Maybe<&2, G.Act>, +seed: U32, +round: Nat, +p: G.Player, +h: ZOk(p)) -> ZOk(G.bot_try(ma, seed, round, p)):
  match ma:
    case None{}:
      h
    case Some{a}:
      zone_cap_step(seed, round, p, a, h)

# LAW: any number of bot steps keeps both zones in bounds
law bot_steps_ok:
  for fuel: Nat
  for +seed: U32
  for +round: Nat
  for +p: G.Player
  for +h: ZOk(p)
  ZOk(G.bot_steps(fuel, seed, round, p))

def bot_steps_ok(fuel, seed, round, p, h):
  match fuel:
    case 0n:
      h
    case 1n+f:
      bot_steps_ok(f, seed, round, G.bot_try(G.bot_choice(round, p), seed, round, p),
        bot_try_ok(G.bot_choice(round, p), seed, round, p, h))

# arrange (guards to the front) keeps the board size
def part_fin(k: Bool, +h: G.Mon, +r1: List<&2, G.Mon>, +r2: List<&2, G.Mon>, +t: List<&2, G.Mon>,
  e: {Nat.add(G.len(G.Mon, r1), G.len(G.Mon, r2)) == G.len(G.Mon, t) : Nat})
  -> {Nat.add(G.len(G.Mon, List.filter.put(G.Mon, h, r1, k)), G.len(G.Mon, List.filter.put(G.Mon, h, r2, Bool.not(k)))) == 1n+G.len(G.Mon, t) : Nat}:
  match k:
    case True{}:
      %e : {1n+Nat.add(G.len(G.Mon, r1), G.len(G.Mon, r2)) == 1n+_ : Nat}
      {==}
    case False{}:
      %e : {Nat.add(G.len(G.Mon, r1), 1n+G.len(G.Mon, r2)) == 1n+_ : Nat}
      K.sym(Nat, 1n+Nat.add(G.len(G.Mon, r1), G.len(G.Mon, r2)), Nat.add(G.len(G.Mon, r1), 1n+G.len(G.Mon, r2)),
        K.add_succ(G.len(G.Mon, r1), G.len(G.Mon, r2)))

def len_partition(+b: List<&2, G.Mon>)
  -> {Nat.add(G.len(G.Mon, List.filter(~G.Mon, ~G.mon_guard, b)), G.len(G.Mon, List.filter(~G.Mon, ~G.mon_not_guard, b))) == G.len(G.Mon, b) : Nat}:
  match b:
    case Nil{}:
      {==}
    case +h <> t:
      part_fin(G.mon_guard(h), h, List.filter(~G.Mon, ~G.mon_guard, t), List.filter(~G.Mon, ~G.mon_not_guard, t), t, len_partition(t))

def len_arrange(+b: List<&2, G.Mon>) -> {G.len(G.Mon, G.arrange(b)) == G.len(G.Mon, b) : Nat}:
  %K.len_append(G.Mon, List.filter(~G.Mon, ~G.mon_guard, b), List.filter(~G.Mon, ~G.mon_not_guard, b))
    : {_ == G.len(G.Mon, b) : Nat}
  len_partition(b)

def arrange_ok(+q: G.Player, h: ZOk(q)) -> ZOk(G.p_set_board(q, G.arrange(G.p_board(q)))):
  match q:
    case G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, +board, shop, alive, out, hand, plays}:
      K.Both{wb, wh} = h
      K.Both{%K.sym(Nat, G.len(G.Mon, G.arrange(board)), G.len(G.Mon, board), len_arrange(board)) : K.T(Nat.is_le(_, 5n))
        wb, wh}

# LAW: a whole bot turn (up to bot_fuel() actions, then the guard-first
# arrangement) keeps both zones in bounds
law bot_play_ok:
  for +seed: U32
  for +round: Nat
  for +p: G.Player
  for +h: ZOk(p)
  ZOk(G.bot_play(seed, round, p))

def bot_play_ok(seed, round, p, h):
  arrange_ok(G.bot_steps(G.bot_fuel(), seed, round, p), bot_steps_ok(G.bot_fuel(), seed, round, p, h))

# Game level: every seat's zones stay in bounds
# ---------------------------------------------

def AllOk(ps: List<&2, G.Player>) -> Data:
  match ps:
    case Nil{}:
      Unit
    case p <> t:
      K.Both<ZOk(p), AllOk(t)>

def GameOk(g: G.Game) -> Data:
  AllOk(G.g_players(g))

def pick_ok(-A: Type, -P: A -> Type, c: Bool, -a: A, -b: A, ha: P(a), hb: P(b)) -> P(G.pick(A, c, a, b)):
  match c:
    case True{}:
      ha
    case False{}:
      hb

def get_ok(ps: List<&2, G.Player>, k: Nat, h: AllOk(ps)) -> ZOk(G.pget(ps, k)):
  match ps k:
    case Nil{} _:
      K.Both{Unit{}, Unit{}}
    case p <> t 0n:
      K.Both{hp, ht} = h
      hp
    case p <> t 1n+j:
      K.Both{hp, ht} = h
      get_ok(t, j, ht)

def set_ok(ps: List<&2, G.Player>, k: Nat, -q: G.Player, h: AllOk(ps), hq: ZOk(q)) -> AllOk(G.pset(ps, k, q)):
  match ps k:
    case Nil{} _:
      Unit{}
    case p <> t 0n:
      K.Both{hp, ht} = h
      K.Both{hq, ht}
    case p <> t 1n+j:
      K.Both{hp, ht} = h
      K.Both{hp, set_ok(t, j, q, ht, hq)}

# End of recruit: ENDTURN abilities never add board units and only grow
# the hand through hand_add
def grow_player_ok(+seed: U32, +round: Nat, +p: G.Player, +h: ZOk(p)) -> ZOk(G.grow_player(seed, round, p)):
  match p:
    case G.Player{+id, +hp, +gold, +tier, +upcost, +invest, +frozen, +rolls, +board, +shop, +alive, +out, +hand, +plays}:
      +f0 = {G.Fx{board, G.mon_of(0n), hand, gold, plays} : G.Fx}
      +key = {[11n, id, round] : List<&2, Nat>}
      +fx = G.endturn(G.len(G.Mon, board), 0n, seed, key, f0)
      pick_ok(G.Player, q => ZOk(q), alive,
        G.grow_live(seed, round, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}),
        G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays},
        gfin_ok(fx, G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays},
          %K.sym(Nat, FB(fx), FB(f0), endturn_len(G.len(G.Mon, board), 0n, seed, key, f0)) : {Nat.is_le(_, 5n) == True{} : Bool}
          zb(board, hand, h),
          endturn_hand(G.len(G.Mon, board), 0n, seed, key, f0, zh(board, hand, h))),
        h)

def grow_all_ok(ps: List<&2, G.Player>, +seed: U32, +round: Nat, h: AllOk(ps)) -> AllOk(G.grow_all(ps, seed, round)):
  match ps:
    case Nil{}:
      Unit{}
    case +p <> t:
      K.Both{hp, ht} = h
      K.Both{grow_player_ok(seed, round, p, hp), grow_all_ok(t, seed, round, ht)}

# Combat never writes boards back: a fight only lowers one seat's HP
def set_hp_ok(+p: G.Player, +v: Nat, h: ZOk(p)) -> ZOk(G.p_set_hp(p, v)):
  match p:
    case G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      h

def damage_ok(+ps: List<&2, G.Player>, +k: Nat, +d: Nat, +h: AllOk(ps)) -> AllOk(G.damage_player(ps, k, d)):
  +p = G.pget(ps, k)
  set_ok(ps, k, G.p_set_hp(p, Econ.hp_after(G.p_hp(p), d)), h,
    set_hp_ok(p, Econ.hp_after(G.p_hp(p), d), get_ok(ps, k, h)))

def fight_ok(+ps: List<&2, G.Player>, f: G.Fight, +h: AllOk(ps)) -> AllOk(G.apply_fight(ps, f)):
  match f:
    case G.Fight{round, +a, +b, +res, +dmg, ba, bb, log, evs}:
      pick_ok(List<&2, G.Player>, qs => AllOk(qs), G.nat_eq(res, 0n), ps,
        G.damage_player(ps, G.pick(Nat, G.nat_eq(res, 1n), b, a), dmg),
        h, damage_ok(ps, G.pick(Nat, G.nat_eq(res, 1n), b, a), dmg, h))

def FOk(fo: G.FOut) -> Data:
  match fo:
    case G.FOut{ps, fs}:
      AllOk(ps)

def run_fights_ok(prs: List<&2, G.P2>, +seed: U32, +round: Nat, +mode: Nat, +ps: List<&2, G.Player>, +fs: List<&2, G.Fight>,
  h: AllOk(ps)) -> FOk(G.run_fights(prs, seed, round, mode, ps, fs)):
  match prs:
    case Nil{}:
      h
    case G.P2{+a, +b} <> t:
      +pa = G.pget(ps, a)
      +pb = G.pget(ps, b)
      +f = G.fight(seed, round, a, b, G.seat_name(mode, a), G.seat_name(mode, b), G.p_tier(pa), G.p_tier(pb), G.p_board(pa), G.p_board(pb))
      run_fights_ok(t, seed, round, mode, G.apply_fight(ps, f), f <> fs, fight_ok(ps, f, h))

# elimination and the next round's income/shop never touch board or hand
def elim_one_ok(+round: Nat, +p: G.Player, +h: ZOk(p)) -> ZOk(G.elim_one(round, p)):
  match p:
    case G.Player{+id, +hp, +gold, +tier, +upcost, +invest, +frozen, +rolls, +board, +shop, +alive, +out, +hand, +plays}:
      pick_ok(G.Player, q => ZOk(q), alive && G.nat_eq(hp, 0n),
        G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, False{}, round, hand, plays},
        G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}, h, h)

def elim_all_ok(ps: List<&2, G.Player>, +round: Nat, h: AllOk(ps)) -> AllOk(G.elim_all(ps, round)):
  match ps:
    case Nil{}:
      Unit{}
    case +p <> t:
      K.Both{hp, ht} = h
      K.Both{elim_one_ok(round, p, hp), elim_all_ok(t, round, ht)}

def next_live_ok(+seed: U32, +r2: Nat, +q: G.Player, h: ZOk(q)) -> ZOk(G.next_round_live(seed, r2, q)):
  match q:
    case G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      h

# V4: recruit start assembles triples first (p_norm), then income and shop
def next_player_ok(+seed: U32, +r2: Nat, +p: G.Player, +h: ZOk(p)) -> ZOk(G.next_round_player(seed, r2, p)):
  pick_ok(G.Player, q => ZOk(q), G.p_alive(p),
    G.next_round_live(seed, r2, G.p_norm(p)), p,
    next_live_ok(seed, r2, G.p_norm(p), norm_ok(p, h)), h)

def next_all_ok(ps: List<&2, G.Player>, +seed: U32, +r2: Nat, h: AllOk(ps)) -> AllOk(G.next_round_all(ps, seed, r2)):
  match ps:
    case Nil{}:
      Unit{}
    case +p <> t:
      K.Both{hp, ht} = h
      K.Both{next_player_ok(seed, r2, p, hp), next_all_ok(t, seed, r2, ht)}

def finish_ok(fo: G.FOut, +seed: U32, +mode: Nat, +round: Nat, +hist: List<&2, G.Fight>, h: FOk(fo))
  -> GameOk(G.finish_round(fo, seed, mode, round, hist)):
  match fo:
    case G.FOut{+ps2, +fs}:
      +ps3 = G.elim_all(ps2, round)
      +h3 = elim_all_ok(ps2, round, h)
      +over = Nat.is_le(G.len(Nat, G.alive_ids(ps3)), 1n) || Nat.is_ge(round, G.max_rounds())
      +hist2 = List.append(&2, G.Fight, hist, fs)
      +ps4 = G.next_round_all(ps3, seed, 1n+round)
      pick_ok(G.Game, g => GameOk(g), over,
        G.Game{seed, mode, round, G.first_alive(mode, ps3), ps3, fs, hist2, True{}},
        G.Game{seed, mode, 1n+round, G.first_alive(mode, ps4), ps4, fs, hist2, False{}},
        h3, next_all_ok(ps3, seed, 1n+round, h3))

# resolving a round (growth, all fights, eliminations, next-round income
# and shops) keeps every seat's zones in bounds
def end_round_ok(g: G.Game, h: GameOk(g)) -> GameOk(G.end_round(g)):
  match g:
    case G.Game{+seed, +mode, +round, actor, +players, fights, +hist, done}:
      +ps1 = G.grow_all(players, seed, round)
      finish_ok(G.run_fights(G.pairings(G.alive_ids(ps1), round), seed, round, mode, ps1, Nil{}), seed, mode, round, hist,
        run_fights_ok(G.pairings(G.alive_ids(ps1), round), seed, round, mode, ps1, Nil{}, grow_all_ok(players, seed, round, h)))

# bot turns at game level. The bot's result q stays a variable here, so
# the kernel never unfolds bot_steps(bot_fuel(), ..) (24 steps).
def seat_ok(+g: G.Game, +k: Nat, -q: G.Player, c: Bool, h: GameOk(g), hq: ZOk(q))
  -> GameOk(G.pick(G.Game, c, G.g_set_players(g, G.pset(G.g_players(g), k, q)), g)):
  match g:
    case G.Game{+seed, +mode, +round, +actor, +players, +fights, +hist, +done}:
      match c:
        case True{}:
          set_ok(players, k, q, h, hq)
        case False{}:
          h

def bot_seat_ok(+g: G.Game, +k: Nat, +h: GameOk(g)) -> GameOk(G.bot_seat(g, k)):
  +p = G.pget(G.g_players(g), k)
  seat_ok(g, k, G.bot_play(G.g_seed(g), G.g_round(g), p), G.p_alive(p), h,
    bot_play_ok(G.g_seed(g), G.g_round(g), p, get_ok(G.g_players(g), k, h)))

def bots_all_ok(+seats: List<&2, Nat>, +g: G.Game, h: GameOk(g)) -> GameOk(G.bots_all(seats, g)):
  match seats:
    case Nil{}:
      h
    case k <> t:
      bots_all_ok(t, G.bot_seat(g, k), bot_seat_ok(g, k, h))

def auto_round_ok(+g: G.Game, +h: GameOk(g)) -> GameOk(G.auto_round(g)):
  +go = Bool.not(G.g_done(g)) && Bool.not(G.p_alive(G.pget(G.g_players(g), 0n)))
  pick_ok(G.Game, x => GameOk(x), go, G.end_round(G.bots_all([1n, 2n, 3n], g)), g,
    end_round_ok(G.bots_all([1n, 2n, 3n], g), bots_all_ok([1n, 2n, 3n], g, h)), h)

def auto_rest_ok(fuel: Nat, +g: G.Game, h: GameOk(g)) -> GameOk(G.auto_rest(fuel, g)):
  match fuel:
    case 0n:
      h
    case 1n+f:
      auto_rest_ok(f, G.auto_round(g), auto_round_ok(g, h))

def manual_next_ok(m: Maybe<&2, Nat>, +g: G.Game, h: GameOk(g)) -> GameOk(G.manual_next(m, g)):
  match m:
    case None{}:
      end_round_ok(g, h)
    case Some{k}:
      match g:
        case G.Game{seed, mode, round, actor, players, fights, hist, done}:
          h

def g_end_ok(+g: G.Game, +h: GameOk(g)) -> GameOk(G.g_end(g)):
  pick_ok(G.Game, x => GameOk(x), G.nat_eq(G.g_mode(g), 0n),
    G.auto_rest(G.max_rounds(), G.end_round(G.bots_all([1n, 2n, 3n], g))),
    G.manual_next(G.next_alive(G.g_players(g), G.g_actor(g)), g),
    auto_rest_ok(G.max_rounds(), G.end_round(G.bots_all([1n, 2n, 3n], g)),
      end_round_ok(G.bots_all([1n, 2n, 3n], g), bots_all_ok([1n, 2n, 3n], g, h))),
    manual_next_ok(G.next_alive(G.g_players(g), G.g_actor(g)), g, h))

def GOk(r: G.GRes) -> Data:
  match r:
    case G.GGood{g}:
      GameOk(g)
    case G.GBad{c, m}:
      Unit

def lift_ok(r: G.PRes, +seed: U32, +mode: Nat, +round: Nat, +actor: Nat, +players: List<&2, G.Player>,
  +fights: List<&2, G.Fight>, +hist: List<&2, G.Fight>, +done: Bool, -d: G.Player,
  hq: ZOk(G.pres_or(r, d)), h: AllOk(players))
  -> GOk(G.lift(r, G.Game{seed, mode, round, actor, players, fights, hist, done})):
  match r:
    case G.PGood{q}:
      set_ok(players, actor, q, h, hq)
    case G.PBad{m}:
      Unit{}

# a recruit action applied by the game to the seat that is acting
def act_ok(+a: G.Act, +seed: U32, +mode: Nat, +round: Nat, +actor: Nat, +players: List<&2, G.Player>,
  +fights: List<&2, G.Fight>, +hist: List<&2, G.Fight>, +done: Bool, +h: AllOk(players))
  -> GOk(G.lift(G.p_apply(seed, round, G.pget(players, actor), a), G.Game{seed, mode, round, actor, players, fights, hist, done})):
  +p = G.pget(players, actor)
  lift_ok(G.p_apply(seed, round, p, a), seed, mode, round, actor, players, fights, hist, done, p,
    zone_cap_step(seed, round, p, a, get_ok(players, actor, h)), h)

def end_branch_ok(+seed: U32, +mode: Nat, +round: Nat, +actor: Nat, +players: List<&2, G.Player>,
  +fights: List<&2, G.Fight>, +hist: List<&2, G.Fight>, +h: AllOk(players))
  -> GOk(G.g_apply_go(False{}, G.End{}, G.Game{seed, mode, round, actor, players, fights, hist, False{}})):
  g_end_ok(G.Game{seed, mode, round, actor, players, fights, hist, False{}}, h)

def auto_gen(+g: G.Game, +h: GameOk(g)) -> GameOk(G.g_end(G.bot_seat(g, G.g_actor(g)))):
  g_end_ok(G.bot_seat(g, G.g_actor(g)), bot_seat_ok(g, G.g_actor(g), h))

def auto_branch_ok(+seed: U32, +mode: Nat, +round: Nat, +actor: Nat, +players: List<&2, G.Player>,
  +fights: List<&2, G.Fight>, +hist: List<&2, G.Fight>, +h: AllOk(players))
  -> GOk(G.g_apply_go(False{}, G.Auto{}, G.Game{seed, mode, round, actor, players, fights, hist, False{}})):
  auto_gen(G.Game{seed, mode, round, actor, players, fights, hist, False{}}, h)

def apply_go_ok(done: Bool, a: G.Act, +seed: U32, +mode: Nat, +round: Nat, +actor: Nat, +players: List<&2, G.Player>,
  +fights: List<&2, G.Fight>, +hist: List<&2, G.Fight>, +h: AllOk(players))
  -> GOk(G.g_apply_go(done, a, G.Game{seed, mode, round, actor, players, fights, hist, done})):
  match done a:
    case True{} _:
      Unit{}
    case False{} G.End{}:
      end_branch_ok(seed, mode, round, actor, players, fights, hist, h)
    case False{} G.Auto{}:
      auto_branch_ok(seed, mode, round, actor, players, fights, hist, h)
    case False{} G.Buy{i}:
      act_ok(G.Buy{i}, seed, mode, round, actor, players, fights, hist, False{}, h)
    case False{} G.Play{i}:
      act_ok(G.Play{i}, seed, mode, round, actor, players, fights, hist, False{}, h)
    case False{} G.Sell{i}:
      act_ok(G.Sell{i}, seed, mode, round, actor, players, fights, hist, False{}, h)
    case False{} G.Swap{i, j}:
      act_ok(G.Swap{i, j}, seed, mode, round, actor, players, fights, hist, False{}, h)
    case False{} G.Roll{}:
      act_ok(G.Roll{}, seed, mode, round, actor, players, fights, hist, False{}, h)
    case False{} G.Freeze{}:
      act_ok(G.Freeze{}, seed, mode, round, actor, players, fights, hist, False{}, h)
    case False{} G.Upgrade{}:
      act_ok(G.Upgrade{}, seed, mode, round, actor, players, fights, hist, False{}, h)
    case False{} G.Invest{}:
      act_ok(G.Invest{}, seed, mode, round, actor, players, fights, hist, False{}, h)

# LAW: every game transition the API can perform (any action, legal or
# rejected, including End and Auto with all bot turns, fights, round
# resolution and the bots-mode autoplay) keeps every seat's board <= 5 and
# hand <= 7
law g_apply_zone_cap:
  for +g: G.Game
  for a: G.Act
  for h: GameOk(g)
  GOk(G.g_apply(g, a))

def g_apply_zone_cap(g, a, h):
  match g:
    case G.Game{+seed, +mode, +round, +actor, +players, +fights, +hist, done}:
      apply_go_ok(done, a, seed, mode, round, actor, players, fights, hist, h)

# Replay: the API's only way to reach a state
# --------------------------------------------

def ROk(st: G.RSt) -> Data:
  match st:
    case G.RSt{g, n, err}:
      GameOk(g)

def rstep_res_ok(r: G.GRes, +g: G.Game, +m: String, +n: Nat, hr: GOk(r), h: GameOk(g)) -> ROk(G.rstep_res(r, g, m, n)):
  match r:
    case G.GGood{g2}:
      hr
    case G.GBad{c, msg}:
      h

def rstep_parse_ok(mp: Maybe<&2, G.Act>, +m: String, +g: G.Game, +n: Nat, +h: GameOk(g)) -> ROk(G.rstep_parse(mp, m, g, n)):
  match mp:
    case None{}:
      h
    case Some{+a}:
      rstep_res_ok(G.g_apply(g, a), g, m, n, g_apply_zone_cap(g, a, h), h)

def rstep_go_ok(err: Maybe<&2, G.RErr>, +m: String, +g: G.Game, +n: Nat, +h: GameOk(g)) -> ROk(G.rstep_go(err, m, g, n)):
  match err:
    case Some{e}:
      h
    case None{}:
      rstep_parse_ok(G.parse_move(m), m, g, n, h)

def rstep_ok(+m: String, st: G.RSt, h: ROk(st)) -> ROk(G.rstep(m, st)):
  match st:
    case G.RSt{+g, +n, err}:
      rstep_go_ok(err, m, g, n, h)

def replay_go_ok(ms: List<&2, String>, +st: G.RSt, h: ROk(st)) -> ROk(G.replay_go(ms, st)):
  match ms:
    case Nil{}:
      h
    case +m <> t:
      replay_go_ok(t, G.rstep(m, st), rstep_ok(m, st, h))

def new_game_ok(+seed: U32, +mode: Nat) -> GameOk(G.new_game(seed, mode)):
  K.Both{K.Both{Unit{}, Unit{}}, K.Both{K.Both{Unit{}, Unit{}}, K.Both{K.Both{Unit{}, Unit{}}, K.Both{K.Both{Unit{}, Unit{}}, Unit{}}}}}

def replay_cap_ok(over: Bool, +seed: U32, +mode: Nat, ms: List<&2, String>) -> ROk(G.replay_cap(over, seed, mode, ms)):
  match over:
    case True{}:
      new_game_ok(seed, mode)
    case False{}:
      replay_go_ok(ms, G.RSt{G.new_game(seed, mode), 0n, None{}}, new_game_ok(seed, mode))

# LAW (whole engine): for every seed, every mode and every list of move
# strings, the state replay() returns (the state the HTTP API serializes)
# has at most 5 units on every board and at most 7 cards in every hand
law replay_zone_cap:
  for +seed: U32
  for +mode: Nat
  for +ms: List<&2, String>
  ROk(G.replay(seed, mode, ms))

def replay_zone_cap(seed, mode, ms):
  replay_cap_ok(Nat.is_gt(G.len(String, ms), G.max_moves()), seed, mode, ms)

# Corollaries in the v1 shape: the board bound and the hand bound alone
# -----------------------------------------------------------------------

def BoardAll(ps: List<&2, G.Player>) -> Data:
  match ps:
    case Nil{}:
      Unit
    case p <> t:
      K.Both<K.T(BoardOk(p)), BoardAll(t)>

def HandAll(ps: List<&2, G.Player>) -> Data:
  match ps:
    case Nil{}:
      Unit
    case p <> t:
      K.Both<K.T(HandOk(p)), HandAll(t)>

def all_board(ps: List<&2, G.Player>, h: AllOk(ps)) -> BoardAll(ps):
  match ps:
    case Nil{}:
      Unit{}
    case p <> t:
      K.Both{hp, ht} = h
      K.Both{wb, wh} = hp
      K.Both{wb, all_board(t, ht)}

def all_hand(ps: List<&2, G.Player>, h: AllOk(ps)) -> HandAll(ps):
  match ps:
    case Nil{}:
      Unit{}
    case p <> t:
      K.Both{hp, ht} = h
      K.Both{wb, wh} = hp
      K.Both{wh, all_hand(t, ht)}

def RBoard(st: G.RSt) -> Data:
  match st:
    case G.RSt{g, n, err}:
      BoardAll(G.g_players(g))

def RHand(st: G.RSt) -> Data:
  match st:
    case G.RSt{g, n, err}:
      HandAll(G.g_players(g))

def r_board(st: G.RSt, h: ROk(st)) -> RBoard(st):
  match st:
    case G.RSt{g, n, err}:
      all_board(G.g_players(g), h)

def r_hand(st: G.RSt, h: ROk(st)) -> RHand(st):
  match st:
    case G.RSt{g, n, err}:
      all_hand(G.g_players(g), h)

# LAW (v1 theorem, kept): every replayed state has every board <= 5
law replay_board_cap:
  for +seed: U32
  for +mode: Nat
  for +ms: List<&2, String>
  RBoard(G.replay(seed, mode, ms))

def replay_board_cap(seed, mode, ms):
  r_board(G.replay(seed, mode, ms), replay_zone_cap(seed, mode, ms))

# LAW (new): every replayed state has every hand <= 7
law replay_hand_cap:
  for +seed: U32
  for +mode: Nat
  for +ms: List<&2, String>
  RHand(G.replay(seed, mode, ms))

def replay_hand_cap(seed, mode, ms):
  r_hand(G.replay(seed, mode, ms), replay_zone_cap(seed, mode, ms))
