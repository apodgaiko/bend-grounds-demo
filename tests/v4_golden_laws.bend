# Bend Grounds V4: golden assembly, shop and Armor laws, proven on the real engine.
#
#   bun vendor/bend/bend2/main.ts tests/v4_golden_laws.bend --verdict
#
# Every `law` is universally quantified over the engine's own functions
# (G.take, G.copies, G.merge_hb, G.p_norm, G.make_shop, G.mon_armor, ...);
# nothing in the engine is re-implemented. Concrete golden examples live in
# tests/card_interactions.bend (V4 fixtures), not here.
#
# Proven (domain stated per law; all over the engine's own definitions):
#   take_split / take_count   take(xs, c, n) splits xs into the first
#                             min(n, copies) regular copies of c and the rest
#   take_weight / taken_weight take conserves every card's weight; what it
#                             takes is only regular copies of c
#   merge_three               a merge consumes exactly 3 units (A1, count)
#   merge_zones               a merge never grows the hand nor the board
#   triple_sound              triple_of only names a card with >= 3 regular
#                             copies in hand ++ board
#   merge_weight              card conservation with golden multiplicity: for
#                             every card d, sum over hand+board of (3 per
#                             golden d, 1 per regular d) is unchanged by a
#                             merge (A1, cards)
#   norm_zones                p_norm (any player record) never grows the hand
#                             nor the board (A2); used by engine_invariants
#   norm_weight               p_norm (any player record) conserves every
#                             card's golden-weighted count
#   armor_le2 / mon_armor_le2 Armor <= 2 for every card id and every unit,
#                             golden included (A4)
#   shop_tier                 every id a drawn shop holds has tier <= the
#                             player's tier, every seed/seat/round/roll count
#                             and tier >= 1 (A3; frozen carry-over not covered)
#   sellhand_rejected         no token list starting with "sellhand" parses
#                             (A6, token level; string split not modelled)
#   regular_parity            a regular unit's effective abilities, Rally and
#                             Income are the printed card's (A5, m = 1)
#   golden_double             a golden unit pays 2x printed Rally and Income
# NOT proven here (stated honestly): I1 "no three regular copies remain
# after p_norm" (the fuel-4 bound is not proved sufficient; fixtures only);
# merged stats (golden = sum - printed, Nat subtraction, by definition);
# that p_norm runs before income at recruit start is proven only as zone
# bounds in engine_invariants; the order is a concrete fixture
# (card_interactions gold_recruit_start).

import Base
import ../engine/game.bend as G
import ./proof_kit.bend as K

# Small Nat facts
# ===============

def le_two(+x: Nat) -> {Nat.is_le(x, 2n+x) == True{} : Bool}:
  K.le_step(x, 1n+x, K.le_step(x, x, K.le_refl(x)))

def le_one(+x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  K.le_step(x, x, K.le_refl(x))

# Length helpers over the engine's list functions
# ===============================================

def len_snoc(-A: Data, xs: List<&2, A>, x: A) -> {1n+G.len(A, xs) == G.len(A, G.snoc(A, xs, x)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %len_snoc(A, t, x) : {2n+G.len(A, t) == 1n+_ : Nat}
      {==}

def len_insert(-A: Data, xs: List<&2, A>, n: Nat, x: A) -> {1n+G.len(A, xs) == G.len(A, G.insert_at(A, xs, n, x)) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      %len_insert(A, t, q, x) : {2n+G.len(A, t) == 1n+_ : Nat}
      {==}

# Take: the split used by a merge
# ===============================

def got_got(+h: G.Mon, r: G.Take) -> {h <> G.take_taken(r) == G.take_taken(G.take_got(h, r)) : List<&2, G.Mon>}:
  match r:
    case G.Take{rest, got}:
      {==}

def rest_got(+h: G.Mon, r: G.Take) -> {G.take_rest(r) == G.take_rest(G.take_got(h, r)) : List<&2, G.Mon>}:
  match r:
    case G.Take{rest, got}:
      {==}

def got_kept(+h: G.Mon, r: G.Take) -> {G.take_taken(r) == G.take_taken(G.take_kept(h, r)) : List<&2, G.Mon>}:
  match r:
    case G.Take{rest, got}:
      {==}

def rest_kept(+h: G.Mon, r: G.Take) -> {h <> G.take_rest(r) == G.take_rest(G.take_kept(h, r)) : List<&2, G.Mon>}:
  match r:
    case G.Take{rest, got}:
      {==}

def GL(r: G.Take) -> Nat:
  G.len(G.Mon, G.take_taken(r))

def RL(r: G.Take) -> Nat:
  G.len(G.Mon, G.take_rest(r))

def split_step(hit: Bool, +h: G.Mon, +t: List<&2, G.Mon>, +c: Nat, +k: Nat,
  e0: {Nat.add(GL(G.take(t, c, k)), RL(G.take(t, c, k))) == G.len(G.Mon, t) : Nat},
  e1: {Nat.add(GL(G.take(t, c, 1n+k)), RL(G.take(t, c, 1n+k))) == G.len(G.Mon, t) : Nat})
  -> {Nat.add(GL(G.pick(G.Take, hit, G.take_got(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))), G.take_kept(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))))),
              RL(G.pick(G.Take, hit, G.take_got(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))), G.take_kept(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))))))
      == 1n+G.len(G.Mon, t) : Nat}:
  match hit:
    case True{}:
      +r = G.take(t, c, k)
      %got_got(h, r) : {Nat.add(G.len(G.Mon, _), RL(G.take_got(h, r))) == 1n+G.len(G.Mon, t) : Nat}
      %rest_got(h, r) : {Nat.add(1n+GL(r), G.len(G.Mon, _)) == 1n+G.len(G.Mon, t) : Nat}
      %e0 : {1n+Nat.add(GL(r), RL(r)) == 1n+_ : Nat}
      {==}
    case False{}:
      +r = G.take(t, c, 1n+k)
      %got_kept(h, r) : {Nat.add(G.len(G.Mon, _), RL(G.take_kept(h, r))) == 1n+G.len(G.Mon, t) : Nat}
      %rest_kept(h, r) : {Nat.add(GL(r), G.len(G.Mon, _)) == 1n+G.len(G.Mon, t) : Nat}
      %K.add_succ(GL(r), RL(r)) : {_ == 1n+G.len(G.Mon, t) : Nat}
      %e1 : {1n+Nat.add(GL(r), RL(r)) == 1n+_ : Nat}
      {==}

# LAW: take never loses or invents a unit: taken + rest = all
law take_split:
  for +xs: List<&2, G.Mon>
  for +c: Nat
  for +n: Nat
  {Nat.add(GL(G.take(xs, c, n)), RL(G.take(xs, c, n))) == G.len(G.Mon, xs) : Nat}

def take_split(xs, c, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+(+k):
      split_step(G.is_copy(c, h), h, t, c, k, take_split(t, c, k), take_split(t, c, 1n+k))

def count_step(hit: Bool, +h: G.Mon, +t: List<&2, G.Mon>, +c: Nat, +k: Nat,
  e0: {GL(G.take(t, c, k)) == Nat.min(k, G.copies(t, c)) : Nat},
  e1: {GL(G.take(t, c, 1n+k)) == Nat.min(1n+k, G.copies(t, c)) : Nat})
  -> {GL(G.pick(G.Take, hit, G.take_got(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))), G.take_kept(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k)))))
      == Nat.min(1n+k, Nat.add(G.pick(Nat, hit, 1n, 0n), G.copies(t, c))) : Nat}:
  match hit:
    case True{}:
      +r = G.take(t, c, k)
      %got_got(h, r) : {G.len(G.Mon, _) == 1n+Nat.min(k, G.copies(t, c)) : Nat}
      %e0 : {1n+GL(r) == 1n+_ : Nat}
      {==}
    case False{}:
      +r = G.take(t, c, 1n+k)
      %got_kept(h, r) : {G.len(G.Mon, _) == Nat.min(1n+k, G.copies(t, c)) : Nat}
      e1

# LAW: take(xs, c, n) takes exactly min(n, regular copies of c in xs) units
law take_count:
  for +xs: List<&2, G.Mon>
  for +c: Nat
  for +n: Nat
  {GL(G.take(xs, c, n)) == Nat.min(n, G.copies(xs, c)) : Nat}

def take_count(xs, c, n):
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+(+k):
      count_step(G.is_copy(c, h), h, t, c, k, take_count(t, c, k), take_count(t, c, 1n+k))

# copies distributes over append
def copies_append(+xs: List<&2, G.Mon>, +ys: List<&2, G.Mon>, +c: Nat)
  -> {Nat.add(G.copies(xs, c), G.copies(ys, c)) == G.copies(List.append(&2, G.Mon, xs, ys), c) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +m <> t:
      +p = G.pick(Nat, G.is_copy(c, m), 1n, 0n)
      %K.sym(Nat, Nat.add(Nat.add(p, G.copies(t, c)), G.copies(ys, c)), Nat.add(p, Nat.add(G.copies(t, c), G.copies(ys, c))), K.add_assoc(p, G.copies(t, c), G.copies(ys, c)))
        : {_ == Nat.add(p, G.copies(List.append(&2, G.Mon, t, ys), c)) : Nat}
      %copies_append(t, ys, c) : {Nat.add(p, Nat.add(G.copies(t, c), G.copies(ys, c))) == Nat.add(p, _) : Nat}
      {==}

# with at least 3 copies in hand + board, hand-first taking consumes exactly 3
def three(ch: Nat, cb: Nat, h: {Nat.is_ge(Nat.add(ch, cb), 3n) == True{} : Bool})
  -> {G.nat_eq(Nat.add(Nat.min(3n, ch), Nat.min(Nat.sub(3n, Nat.min(3n, ch)), cb)), 3n) == True{} : Bool}:
  match ch cb:
    case 0n 0n:
      K.ft_absurd({G.nat_eq(0n, 3n) == True{} : Bool}, h)
    case 0n 1n:
      K.ft_absurd({G.nat_eq(1n, 3n) == True{} : Bool}, h)
    case 0n 2n:
      K.ft_absurd({G.nat_eq(2n, 3n) == True{} : Bool}, h)
    case 0n 3n+q:
      {==}
    case 1n 0n:
      K.ft_absurd({G.nat_eq(1n, 3n) == True{} : Bool}, h)
    case 1n 1n:
      K.ft_absurd({G.nat_eq(2n, 3n) == True{} : Bool}, h)
    case 1n 2n+q:
      {==}
    case 2n 0n:
      K.ft_absurd({G.nat_eq(2n, 3n) == True{} : Bool}, h)
    case 2n 1n+q:
      {==}
    case 3n+q _:
      {==}

# Merge: zones never grow
# =======================

def HBh(hb: G.HB) -> List<&2, G.Mon>:
  G.HB{h, b} = hb
  h

def HBb(hb: G.HB) -> List<&2, G.Mon>:
  G.HB{h, b} = hb
  b

# hand <= H and board <= B, as copyable evidence
def LensHB(hb: G.HB, +H: Nat, +B: Nat) -> Data:
  K.Both<K.T(Nat.is_le(G.len(G.Mon, HBh(hb)), H)), K.T(Nat.is_le(G.len(G.Mon, HBb(hb)), B))>

# the final step of merge_hb on abstract pieces: gh/gb taken from the
# hand/board, rh/rb the rests, exactly 3 taken in all
def hb_lens(gh: List<&2, G.Mon>, +rh: List<&2, G.Mon>, gb: List<&2, G.Mon>, +rb: List<&2, G.Mon>, +fi: Nat, +gm: G.Mon, +H: Nat, +B: Nat,
  eh: {Nat.add(G.len(G.Mon, gh), G.len(G.Mon, rh)) == H : Nat},
  eb: {Nat.add(G.len(G.Mon, gb), G.len(G.Mon, rb)) == B : Nat},
  e3: {G.nat_eq(Nat.add(G.len(G.Mon, gh), G.len(G.Mon, gb)), 3n) == True{} : Bool})
  -> LensHB(G.pick(G.HB, Nat.is_gt(G.len(G.Mon, gh), 0n), G.HB{G.snoc(G.Mon, rh, gm), rb}, G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}), H, B):
  match gh gb:
    case Nil{} Nil{}:
      K.ft_absurd(LensHB(G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}, H, B), e3)
    case Nil{} x1 <> Nil{}:
      K.ft_absurd(LensHB(G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}, H, B), e3)
    case Nil{} x1 <> x2 <> Nil{}:
      K.ft_absurd(LensHB(G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}, H, B), e3)
    case Nil{} x1 <> x2 <> x3 <> Nil{}:
      %eh : LensHB(G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}, _, B)
      %eb : LensHB(G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}, G.len(G.Mon, rh), _)
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, rh), G.len(G.Mon, rh)), K.le_refl(G.len(G.Mon, rh))),
        K.to_T(Nat.is_le(G.len(G.Mon, G.insert_at(G.Mon, rb, fi, gm)), 3n+G.len(G.Mon, rb)),
          %len_insert(G.Mon, rb, fi, gm) : {Nat.is_le(_, 3n+G.len(G.Mon, rb)) == True{} : Bool}
          le_two(1n+G.len(G.Mon, rb)))}
    case Nil{} x1 <> x2 <> x3 <> x4 <> t:
      K.ft_absurd(LensHB(G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}, H, B), e3)
    case y1 <> Nil{} Nil{}:
      K.ft_absurd(LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, H, B), e3)
    case y1 <> Nil{} x1 <> Nil{}:
      K.ft_absurd(LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, H, B), e3)
    case y1 <> Nil{} x1 <> x2 <> Nil{}:
      %eh : LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, _, B)
      %eb : LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, 1n+G.len(G.Mon, rh), _)
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, G.snoc(G.Mon, rh, gm)), 1n+G.len(G.Mon, rh)),
          %len_snoc(G.Mon, rh, gm) : {Nat.is_le(_, 1n+G.len(G.Mon, rh)) == True{} : Bool}
          K.le_refl(1n+G.len(G.Mon, rh))),
        K.to_T(Nat.is_le(G.len(G.Mon, rb), 2n+G.len(G.Mon, rb)), le_two(G.len(G.Mon, rb)))}
    case y1 <> Nil{} x1 <> x2 <> x3 <> t:
      K.ft_absurd(LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, H, B), e3)
    case y1 <> y2 <> Nil{} Nil{}:
      K.ft_absurd(LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, H, B), e3)
    case y1 <> y2 <> Nil{} x1 <> Nil{}:
      %eh : LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, _, B)
      %eb : LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, 2n+G.len(G.Mon, rh), _)
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, G.snoc(G.Mon, rh, gm)), 2n+G.len(G.Mon, rh)),
          %len_snoc(G.Mon, rh, gm) : {Nat.is_le(_, 2n+G.len(G.Mon, rh)) == True{} : Bool}
          le_one(1n+G.len(G.Mon, rh))),
        K.to_T(Nat.is_le(G.len(G.Mon, rb), 1n+G.len(G.Mon, rb)), le_one(G.len(G.Mon, rb)))}
    case y1 <> y2 <> Nil{} x1 <> x2 <> t:
      K.ft_absurd(LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, H, B), e3)
    case y1 <> y2 <> y3 <> Nil{} Nil{}:
      %eh : LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, _, B)
      %eb : LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, 3n+G.len(G.Mon, rh), _)
      K.Both{K.to_T(Nat.is_le(G.len(G.Mon, G.snoc(G.Mon, rh, gm)), 3n+G.len(G.Mon, rh)),
          %len_snoc(G.Mon, rh, gm) : {Nat.is_le(_, 3n+G.len(G.Mon, rh)) == True{} : Bool}
          le_two(1n+G.len(G.Mon, rh))),
        K.to_T(Nat.is_le(G.len(G.Mon, rb), G.len(G.Mon, rb)), K.le_refl(G.len(G.Mon, rb)))}
    case y1 <> y2 <> y3 <> Nil{} x1 <> t:
      K.ft_absurd(LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, H, B), e3)
    case y1 <> y2 <> y3 <> y4 <> u _:
      K.ft_absurd(LensHB(G.HB{G.snoc(G.Mon, rh, gm), rb}, H, B), e3)

# with >= 3 regular copies of c in hand ++ board, the hand take and the
# board take together consume exactly 3 units
def took_three(+c: Nat, +hand: List<&2, G.Mon>, +board: List<&2, G.Mon>,
  h3: {Nat.is_ge(G.copies(List.append(&2, G.Mon, hand, board), c), 3n) == True{} : Bool})
  -> {G.nat_eq(Nat.add(GL(G.take(hand, c, 3n)), GL(G.take(board, c, Nat.sub(3n, GL(G.take(hand, c, 3n)))))), 3n) == True{} : Bool}:
  +ch = G.copies(hand, c)
  +cb = G.copies(board, c)
  %K.sym(Nat, GL(G.take(board, c, Nat.sub(3n, GL(G.take(hand, c, 3n))))), Nat.min(Nat.sub(3n, GL(G.take(hand, c, 3n))), cb), take_count(board, c, Nat.sub(3n, GL(G.take(hand, c, 3n)))))
    : {G.nat_eq(Nat.add(GL(G.take(hand, c, 3n)), _), 3n) == True{} : Bool}
  %K.sym(Nat, GL(G.take(hand, c, 3n)), Nat.min(3n, ch), take_count(hand, c, 3n))
    : {G.nat_eq(Nat.add(_, Nat.min(Nat.sub(3n, _), cb)), 3n) == True{} : Bool}
  three(ch, cb,
    %K.sym(Nat, Nat.add(ch, cb), G.copies(List.append(&2, G.Mon, hand, board), c), copies_append(hand, board, c)) : {Nat.is_ge(_, 3n) == True{} : Bool}
    h3)

# LAW: merging card c (with >= 3 regular copies in hand ++ board, the
# premise triple_of guarantees) never grows the hand nor the board
law merge_zones:
  for +c: Nat
  for +hand: List<&2, G.Mon>
  for +board: List<&2, G.Mon>
  for h3: {Nat.is_ge(G.copies(List.append(&2, G.Mon, hand, board), c), 3n) == True{} : Bool}
  LensHB(G.merge_hb(c, hand, board), G.len(G.Mon, hand), G.len(G.Mon, board))

def merge_zones(c, hand, board, h3):
  +th = G.take(hand, c, 3n)
  +tb = G.take(board, c, Nat.sub(3n, GL(th)))
  hb_lens(G.take_taken(th), G.take_rest(th), G.take_taken(tb), G.take_rest(tb), G.first_copy(board, c, 0n),
    G.fuse(c, List.append(&2, G.Mon, G.take_taken(th), G.take_taken(tb))), G.len(G.Mon, hand), G.len(G.Mon, board),
    take_split(hand, c, 3n), take_split(board, c, Nat.sub(3n, GL(th))), took_three(c, hand, board, h3))

# Triple choice: triple_of only ever names a card with >= 3 regular copies
# ========================================================================

def TriOk(+all: List<&2, G.Mon>, mc: Maybe<&2, Nat>) -> Data:
  match mc:
    case None{}:
      Unit
    case Some{c}:
      K.T(Nat.is_ge(G.copies(all, c), 3n))

def tri_pick(x1: Bool, x2: Bool, x3: Bool, +c: Nat, +all: List<&2, G.Mon>, +best: Maybe<&2, Nat>,
  e2: {Nat.is_ge(G.copies(all, c), 3n) == x2 : Bool}, hb: TriOk(all, best))
  -> TriOk(all, G.pick(Maybe<&2, Nat>, x1 && x2 && x3, Some{c}, best)):
  match x1 x2 x3:
    case True{} True{} True{}:
      K.to_T(Nat.is_ge(G.copies(all, c), 3n), e2)
    case True{} True{} False{}:
      hb
    case True{} False{} _:
      hb
    case False{} _ _:
      hb

def tri_go(xs: List<&2, G.Mon>, +all: List<&2, G.Mon>, +best: Maybe<&2, Nat>, hb: TriOk(all, best))
  -> TriOk(all, G.tri_best(xs, all, best)):
  match xs:
    case Nil{}:
      hb
    case +m <> t:
      +c = G.mon_cid(m)
      +x2 = Nat.is_ge(G.copies(all, c), 3n)
      tri_go(t, all, G.pick(Maybe<&2, Nat>, G.is_copy(c, m) && x2 && G.tri_better(c, best), Some{c}, best),
        tri_pick(G.is_copy(c, m), x2, G.tri_better(c, best), c, all, best, {==}, hb))

# LAW: whenever triple_of names a card, it has >= 3 regular copies
law triple_sound:
  for +hand: List<&2, G.Mon>
  for +board: List<&2, G.Mon>
  TriOk(List.append(&2, G.Mon, hand, board), G.triple_of(hand, board))

def triple_sound(hand, board):
  tri_go(List.append(&2, G.Mon, hand, board), List.append(&2, G.Mon, hand, board), None{}, Unit{})

# Normalization never grows a zone (A2)
# =====================================

def Lens(p: G.Player, +H: Nat, +B: Nat) -> Data:
  K.Both<K.T(Nat.is_le(G.len(G.Mon, G.p_hand(p)), H)), K.T(Nat.is_le(G.len(G.Mon, G.p_board(p)), B))>

def fin_lens(hb: G.HB, +p: G.Player, +H: Nat, +B: Nat, h: LensHB(hb, H, B)) -> Lens(G.merge_fin(hb, p), H, B):
  match hb p:
    case G.HB{nh, nb} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      h

def lens_trans(+q: G.Player, +p: G.Player, +H: Nat, +B: Nat,
  hq: Lens(q, G.len(G.Mon, G.p_hand(p)), G.len(G.Mon, G.p_board(p))), hp: Lens(p, H, B)) -> Lens(q, H, B):
  K.Both{wq1, wq2} = hq
  K.Both{wp1, wp2} = hp
  K.Both{K.to_T(Nat.is_le(G.len(G.Mon, G.p_hand(q)), H),
      K.le_trans(G.len(G.Mon, G.p_hand(q)), G.len(G.Mon, G.p_hand(p)), H,
        K.from_T(Nat.is_le(G.len(G.Mon, G.p_hand(q)), G.len(G.Mon, G.p_hand(p))), wq1), K.from_T(Nat.is_le(G.len(G.Mon, G.p_hand(p)), H), wp1))),
    K.to_T(Nat.is_le(G.len(G.Mon, G.p_board(q)), B),
      K.le_trans(G.len(G.Mon, G.p_board(q)), G.len(G.Mon, G.p_board(p)), B,
        K.from_T(Nat.is_le(G.len(G.Mon, G.p_board(q)), G.len(G.Mon, G.p_board(p))), wq2), K.from_T(Nat.is_le(G.len(G.Mon, G.p_board(p)), B), wp2)))}

def norm_go_lens(fuel: Nat, mc: Maybe<&2, Nat>, +p: G.Player, +H: Nat, +B: Nat,
  ht: TriOk(List.append(&2, G.Mon, G.p_hand(p), G.p_board(p)), mc), hz: Lens(p, H, B)) -> Lens(G.norm_go(fuel, mc, p), H, B):
  match fuel mc:
    case _ None{}:
      hz
    case 0n Some{c}:
      hz
    case 1n+f Some{+c}:
      +q = G.merge_p(c, p)
      norm_go_lens(f, G.triple_of(G.p_hand(q), G.p_board(q)), q, H, B,
        triple_sound(G.p_hand(q), G.p_board(q)),
        lens_trans(q, p, H, B,
          fin_lens(G.merge_hb(c, G.p_hand(p), G.p_board(p)), p, G.len(G.Mon, G.p_hand(p)), G.len(G.Mon, G.p_board(p)),
            merge_zones(c, G.p_hand(p), G.p_board(p),
              K.from_T(Nat.is_ge(G.copies(List.append(&2, G.Mon, G.p_hand(p), G.p_board(p)), c), 3n), ht))),
          hz))

# LAW (A2): for EVERY player record, p_norm never grows the hand nor the
# board (no reachability premise: a merge only runs on a card triple_of
# names, which has >= 3 regular copies)
law norm_zones:
  for +p: G.Player
  Lens(G.p_norm(p), G.len(G.Mon, G.p_hand(p)), G.len(G.Mon, G.p_board(p)))

def norm_zones(p):
  norm_go_lens(4n, G.triple_of(G.p_hand(p), G.p_board(p)), p, G.len(G.Mon, G.p_hand(p)), G.len(G.Mon, G.p_board(p)),
    triple_sound(G.p_hand(p), G.p_board(p)),
    K.Both{K.to_T(Nat.is_le(G.len(G.Mon, G.p_hand(p)), G.len(G.Mon, G.p_hand(p))), K.le_refl(G.len(G.Mon, G.p_hand(p)))),
      K.to_T(Nat.is_le(G.len(G.Mon, G.p_board(p)), G.len(G.Mon, G.p_board(p))), K.le_refl(G.len(G.Mon, G.p_board(p))))})


# A1 (count): a merge consumes exactly three units
# ================================================

# LAW: with >= 3 regular copies of c in hand ++ board, the hand-first take
# and the board take of merge_hb consume exactly 3 units together
law merge_three:
  for +c: Nat
  for +hand: List<&2, G.Mon>
  for +board: List<&2, G.Mon>
  for h3: {Nat.is_ge(G.copies(List.append(&2, G.Mon, hand, board), c), 3n) == True{} : Bool}
  {G.nat_eq(Nat.add(GL(G.take(hand, c, 3n)), GL(G.take(board, c, Nat.sub(3n, GL(G.take(hand, c, 3n)))))), 3n) == True{} : Bool}

def merge_three(c, hand, board, h3):
  took_three(c, hand, board, h3)

# A4: Armor <= 2 for every card id and every unit (golden included)
# ================================================================

# LAW (exhaustive over every Nat: ids 0..43 one by one, 44+ is no_card)
law armor_le2:
  for c: Nat
  {Nat.is_le(G.c_armor(c), 2n) == True{} : Bool}

def armor_le2(c):
  match c:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n+k:
      {==}

# LAW: the effective Armor of ANY unit, regular or golden and whatever its
# stats, is at most 2 (mon_armor reads the printed card Armor only)
law mon_armor_le2:
  for m: G.Mon
  {Nat.is_le(G.mon_armor(m), 2n) == True{} : Bool}

def mon_armor_le2(m):
  match m:
    case G.Mon{c, a, h, s, g}:
      armor_le2(c)

# A3: the shop only offers cards of the player's tier or lower
# ===========================================================

# every card's id field names a card of the same tier (no_card for 44+ is
# id 0, tier 1, as card 0)
def cid_tier(c: Nat) -> {G.c_tier(G.cd_cid(G.card(c))) == G.cd_tier(G.card(c)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n+k:
      {==}

def AllLe(+tier: Nat, ids: List<&2, Nat>) -> Data:
  match ids:
    case Nil{}:
      Unit
    case i <> t:
      K.Both<K.T(Nat.is_le(G.c_tier(i), tier)), AllLe(tier, t)>

def elig_pick(b: Bool, +i: Nat, +tier: Nat, +r: List<&2, Nat>, e: {Nat.is_le(G.cd_tier(G.card(i)), tier) == b : Bool}, hr: AllLe(tier, r))
  -> AllLe(tier, G.pick(List<&2, Nat>, b, G.cd_cid(G.card(i)) <> r, r)):
  match b:
    case True{}:
      K.Both{K.to_T(Nat.is_le(G.c_tier(G.cd_cid(G.card(i))), tier),
          %K.sym(Nat, G.c_tier(G.cd_cid(G.card(i))), G.cd_tier(G.card(i)), cid_tier(i)) : {Nat.is_le(_, tier) == True{} : Bool}
          e),
        hr}
    case False{}:
      hr

def elig_ok(+ids: List<&2, Nat>, +tier: Nat) -> AllLe(tier, G.elig_go(G.map_card(ids), tier)):
  match ids:
    case Nil{}:
      Unit{}
    case +i <> t:
      elig_pick(Nat.is_le(G.cd_tier(G.card(i)), tier), i, tier, G.elig_go(G.map_card(t), tier), {==}, elig_ok(t, tier))

def get_le(xs: List<&2, Nat>, n: Nat, +d: Nat, +tier: Nat, hx: AllLe(tier, xs), hd: K.T(Nat.is_le(G.c_tier(d), tier)))
  -> K.T(Nat.is_le(G.c_tier(G.get_or(Nat, xs, n, d)), tier)):
  match xs n:
    case Nil{} _:
      hd
    case i <> t 0n:
      K.Both{hi, ht} = hx
      hi
    case i <> t 1n+q:
      K.Both{hi, ht} = hx
      get_le(t, q, d, tier, ht, hd)

def shop_go_le(+seed: U32, +seat: Nat, +round: Nat, +rolls: Nat, +pool: List<&2, Nat>, slot: Nat, +tier: Nat,
  +hp: AllLe(tier, pool), +h0: K.T(Nat.is_le(G.c_tier(0n), tier))) -> AllLe(tier, G.shop_go(seed, seat, round, rolls, pool, slot)):
  match slot:
    case 0n:
      Unit{}
    case 1n+(+s):
      K.Both{get_le(pool, G.below(G.hash(seed, [1n, seat, round, rolls, s]), Nat.max(G.len(Nat, pool), 1n)), 0n, tier, hp, h0),
        shop_go_le(seed, seat, round, rolls, pool, s, tier, hp, h0)}

# LAW (A3): for every seed, seat, round, roll count and tier >= 1, every
# card id of the drawn shop has tier <= that tier. (A frozen shop keeps
# cards drawn at an earlier, lower or equal, tier; that step is not
# covered here.)
law shop_tier:
  for +seed: U32
  for +seat: Nat
  for +round: Nat
  for +rolls: Nat
  for +tier: Nat
  for ht: {Nat.is_le(1n, tier) == True{} : Bool}
  AllLe(tier, G.make_shop(seed, seat, round, rolls, tier))

def shop_tier(seed, seat, round, rolls, tier, ht):
  shop_go_le(seed, seat, round, rolls, G.shop_pool(tier), G.shop_size(), tier,
    elig_ok(List.range(G.card_count()), tier), K.to_T(Nat.is_le(1n, tier), ht))

# A6: no hand sale command
# ========================

# LAW: whatever follows it, a command whose first token is "sellhand"
# parses to nothing (so a replay records bad_move and changes no state).
# Token level: the String.split step of parse_move is not modelled here;
# tests/card_interactions.bend has the concrete parse_move fixtures.
law sellhand_rejected:
  for rest: List<&2, String>
  {G.parse_toks("sellhand" <> rest) == None{} : Maybe<&2, G.Act>}

def sellhand_rejected(rest):
  {==}

# A1 (cards): conservation with golden multiplicity
# =================================================

# spec weight of a unit for card d: 3 for a golden d, 1 for a regular d,
# 0 for any other card (a golden stands for the three copies it absorbed)
def wt(+d: Nat, m: G.Mon) -> Nat:
  match m:
    case G.Mon{c, a, h, s, g}:
      G.pick(Nat, G.nat_eq(c, d), G.pick(Nat, g, 3n, 1n), 0n)

def W(xs: List<&2, G.Mon>, +d: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case m <> t:
      Nat.add(wt(d, m), W(t, d))

def WHB(hb: G.HB, +d: Nat) -> Nat:
  match hb:
    case G.HB{h, b}:
      Nat.add(W(h, d), W(b, d))

def eq_sound(a: Nat, b: Nat, h: {G.nat_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      K.ft_absurd({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      K.ft_absurd({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %eq_sound(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# a + (b + c) == b + (a + c)
def add_lr(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      %K.add_succ(b, Nat.add(p, c)) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), add_lr(p, b, c))

# r + ((x + y) + b) == (r + x) + (b + y)
def ac_ins(r: Nat, +x: Nat, +y: Nat, +b: Nat) -> {Nat.add(r, Nat.add(Nat.add(x, y), b)) == Nat.add(Nat.add(r, x), Nat.add(b, y)) : Nat}:
  match r:
    case 0n:
      Equal.trans(Nat, Nat.add(Nat.add(x, y), b), Nat.add(x, Nat.add(y, b)), Nat.add(x, Nat.add(b, y)),
        K.add_assoc(x, y, b), Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.add(y, b), Nat.add(b, y), K.add_comm(y, b)))
    case 1n+(+p):
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, Nat.add(Nat.add(x, y), b)), Nat.add(Nat.add(p, x), Nat.add(b, y)), ac_ins(p, x, y, b))

# (r + (x + y)) + b == (r + x) + (b + y)
def ac_snoc(+r: Nat, +x: Nat, +y: Nat, +b: Nat) -> {Nat.add(Nat.add(r, Nat.add(x, y)), b) == Nat.add(Nat.add(r, x), Nat.add(b, y)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(r, Nat.add(x, y)), b), Nat.add(r, Nat.add(Nat.add(x, y), b)), Nat.add(Nat.add(r, x), Nat.add(b, y)),
    K.add_assoc(r, Nat.add(x, y), b), ac_ins(r, x, y, b))

def w_snoc(+xs: List<&2, G.Mon>, +x: G.Mon, +d: Nat) -> {W(G.snoc(G.Mon, xs, x), d) == Nat.add(W(xs, d), wt(d, x)) : Nat}:
  match xs:
    case Nil{}:
      K.add_zero_r(wt(d, x))
    case +m <> t:
      Equal.trans(Nat, Nat.add(wt(d, m), W(G.snoc(G.Mon, t, x), d)), Nat.add(wt(d, m), Nat.add(W(t, d), wt(d, x))), Nat.add(Nat.add(wt(d, m), W(t, d)), wt(d, x)),
        Equal.cong(Nat, Nat, z => Nat.add(wt(d, m), z), W(G.snoc(G.Mon, t, x), d), Nat.add(W(t, d), wt(d, x)), w_snoc(t, x, d)),
        K.sym(Nat, Nat.add(Nat.add(wt(d, m), W(t, d)), wt(d, x)), Nat.add(wt(d, m), Nat.add(W(t, d), wt(d, x))), K.add_assoc(wt(d, m), W(t, d), wt(d, x))))

def w_ins(+xs: List<&2, G.Mon>, +n: Nat, +x: G.Mon, +d: Nat) -> {W(G.insert_at(G.Mon, xs, n, x), d) == Nat.add(wt(d, x), W(xs, d)) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+q:
      Equal.trans(Nat, Nat.add(wt(d, h), W(G.insert_at(G.Mon, t, q, x), d)), Nat.add(wt(d, h), Nat.add(wt(d, x), W(t, d))), Nat.add(wt(d, x), Nat.add(wt(d, h), W(t, d))),
        Equal.cong(Nat, Nat, z => Nat.add(wt(d, h), z), W(G.insert_at(G.Mon, t, q, x), d), Nat.add(wt(d, x), W(t, d)), w_ins(t, q, x, d)),
        add_lr(wt(d, h), wt(d, x), W(t, d)))

def WR(r: G.Take, +d: Nat) -> Nat:
  W(G.take_rest(r), d)

def WG(r: G.Take, +d: Nat) -> Nat:
  W(G.take_taken(r), d)

def tw_step(hit: Bool, +h: G.Mon, +t: List<&2, G.Mon>, +c: Nat, +k: Nat, +d: Nat,
  e0: {Nat.add(WR(G.take(t, c, k), d), WG(G.take(t, c, k), d)) == W(t, d) : Nat},
  e1: {Nat.add(WR(G.take(t, c, 1n+k), d), WG(G.take(t, c, 1n+k), d)) == W(t, d) : Nat})
  -> {Nat.add(WR(G.pick(G.Take, hit, G.take_got(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))), G.take_kept(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k)))), d),
              WG(G.pick(G.Take, hit, G.take_got(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))), G.take_kept(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k)))), d))
      == Nat.add(wt(d, h), W(t, d)) : Nat}:
  match hit:
    case True{}:
      +r = G.take(t, c, k)
      %got_got(h, r) : {Nat.add(WR(G.take_got(h, r), d), W(_, d)) == Nat.add(wt(d, h), W(t, d)) : Nat}
      %rest_got(h, r) : {Nat.add(W(_, d), Nat.add(wt(d, h), WG(r, d))) == Nat.add(wt(d, h), W(t, d)) : Nat}
      Equal.trans(Nat, Nat.add(WR(r, d), Nat.add(wt(d, h), WG(r, d))), Nat.add(wt(d, h), Nat.add(WR(r, d), WG(r, d))), Nat.add(wt(d, h), W(t, d)),
        add_lr(WR(r, d), wt(d, h), WG(r, d)),
        Equal.cong(Nat, Nat, z => Nat.add(wt(d, h), z), Nat.add(WR(r, d), WG(r, d)), W(t, d), e0))
    case False{}:
      +r = G.take(t, c, 1n+k)
      %got_kept(h, r) : {Nat.add(WR(G.take_kept(h, r), d), W(_, d)) == Nat.add(wt(d, h), W(t, d)) : Nat}
      %rest_kept(h, r) : {Nat.add(W(_, d), WG(r, d)) == Nat.add(wt(d, h), W(t, d)) : Nat}
      Equal.trans(Nat, Nat.add(Nat.add(wt(d, h), WR(r, d)), WG(r, d)), Nat.add(wt(d, h), Nat.add(WR(r, d), WG(r, d))), Nat.add(wt(d, h), W(t, d)),
        K.add_assoc(wt(d, h), WR(r, d), WG(r, d)),
        Equal.cong(Nat, Nat, z => Nat.add(wt(d, h), z), Nat.add(WR(r, d), WG(r, d)), W(t, d), e1))

# LAW: take keeps every card's weight: weight(rest) + weight(taken) = weight(all)
law take_weight:
  for +xs: List<&2, G.Mon>
  for +c: Nat
  for +n: Nat
  for +d: Nat
  {Nat.add(WR(G.take(xs, c, n), d), WG(G.take(xs, c, n), d)) == W(xs, d) : Nat}

def take_weight(xs, c, n, d):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      K.add_zero_r(W(h <> t, d))
    case +h <> t 1n+(+k):
      tw_step(G.is_copy(c, h), h, t, c, k, d, take_weight(t, c, k, d), take_weight(t, c, 1n+k, d))

# a regular copy of c weighs 1 for c and 0 for any other card
def copy_wt(+c: Nat, +d: Nat, m: G.Mon, hc: {G.is_copy(c, m) == True{} : Bool}) -> {wt(d, m) == G.pick(Nat, G.nat_eq(c, d), 1n, 0n) : Nat}:
  match m:
    case G.Mon{+mc, +a, +h, +s, g}:
      match g:
        case True{}:
          K.ft_absurd({wt(d, G.Mon{mc, a, h, s, True{}}) == G.pick(Nat, G.nat_eq(c, d), 1n, 0n) : Nat},
            K.and_r(G.nat_eq(mc, c), False{}, hc))
        case False{}:
          %eq_sound(mc, c, K.and_l(G.nat_eq(mc, c), True{}, hc)) : {G.pick(Nat, G.nat_eq(mc, d), 1n, 0n) == G.pick(Nat, G.nat_eq(_, d), 1n, 0n) : Nat}
          {==}

def pick_succ(e: Bool, +l: Nat) -> {Nat.add(G.pick(Nat, e, 1n, 0n), G.pick(Nat, e, l, 0n)) == G.pick(Nat, e, 1n+l, 0n) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def pick0(e: Bool) -> {0n == G.pick(Nat, e, 0n, 0n) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def tg_step(hit: Bool, +h: G.Mon, +t: List<&2, G.Mon>, +c: Nat, +k: Nat, +d: Nat,
  eh: {G.is_copy(c, h) == hit : Bool},
  e0: {WG(G.take(t, c, k), d) == G.pick(Nat, G.nat_eq(c, d), GL(G.take(t, c, k)), 0n) : Nat},
  e1: {WG(G.take(t, c, 1n+k), d) == G.pick(Nat, G.nat_eq(c, d), GL(G.take(t, c, 1n+k)), 0n) : Nat})
  -> {WG(G.pick(G.Take, hit, G.take_got(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))), G.take_kept(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k)))), d)
      == G.pick(Nat, G.nat_eq(c, d), GL(G.pick(G.Take, hit, G.take_got(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))), G.take_kept(h, G.take(t, c, G.pick(Nat, hit, k, 1n+k))))), 0n) : Nat}:
  match hit:
    case True{}:
      +r = G.take(t, c, k)
      %got_got(h, r) : {W(_, d) == G.pick(Nat, G.nat_eq(c, d), G.len(G.Mon, _), 0n) : Nat}
      %K.sym(Nat, wt(d, h), G.pick(Nat, G.nat_eq(c, d), 1n, 0n), copy_wt(c, d, h, eh)) : {Nat.add(_, WG(r, d)) == G.pick(Nat, G.nat_eq(c, d), 1n+GL(r), 0n) : Nat}
      %K.sym(Nat, WG(r, d), G.pick(Nat, G.nat_eq(c, d), GL(r), 0n), e0) : {Nat.add(G.pick(Nat, G.nat_eq(c, d), 1n, 0n), _) == G.pick(Nat, G.nat_eq(c, d), 1n+GL(r), 0n) : Nat}
      pick_succ(G.nat_eq(c, d), GL(r))
    case False{}:
      +r = G.take(t, c, 1n+k)
      %got_kept(h, r) : {W(_, d) == G.pick(Nat, G.nat_eq(c, d), G.len(G.Mon, _), 0n) : Nat}
      e1

# LAW: everything take(xs, c, n) takes is a regular copy of c: for card d
# the taken units weigh (taken count) if d = c, else 0
law taken_weight:
  for +xs: List<&2, G.Mon>
  for +c: Nat
  for +n: Nat
  for +d: Nat
  {WG(G.take(xs, c, n), d) == G.pick(Nat, G.nat_eq(c, d), GL(G.take(xs, c, n)), 0n) : Nat}

def taken_weight(xs, c, n, d):
  match xs n:
    case Nil{} _:
      pick0(G.nat_eq(c, d))
    case h <> t 0n:
      pick0(G.nat_eq(c, d))
    case +h <> t 1n+(+k):
      tg_step(G.is_copy(c, h), h, t, c, k, d, {==}, taken_weight(t, c, k, d), taken_weight(t, c, 1n+k, d))

def pick_sum3(e: Bool, +x: Nat, +y: Nat, h: {G.nat_eq(Nat.add(x, y), 3n) == True{} : Bool})
  -> {G.pick(Nat, e, 3n, 0n) == Nat.add(G.pick(Nat, e, x, 0n), G.pick(Nat, e, y, 0n)) : Nat}:
  match e:
    case True{}:
      K.sym(Nat, Nat.add(x, y), 3n, eq_sound(Nat.add(x, y), 3n, h))
    case False{}:
      {==}

def hb_w(b: Bool, +rh: List<&2, G.Mon>, +rb: List<&2, G.Mon>, +fi: Nat, +gm: G.Mon, +d: Nat, +x: Nat, +y: Nat,
  eg: {wt(d, gm) == Nat.add(x, y) : Nat})
  -> {WHB(G.pick(G.HB, b, G.HB{G.snoc(G.Mon, rh, gm), rb}, G.HB{rh, G.insert_at(G.Mon, rb, fi, gm)}), d) == Nat.add(Nat.add(W(rh, d), x), Nat.add(W(rb, d), y)) : Nat}:
  match b:
    case True{}:
      %K.sym(Nat, W(G.snoc(G.Mon, rh, gm), d), Nat.add(W(rh, d), wt(d, gm)), w_snoc(rh, gm, d)) : {Nat.add(_, W(rb, d)) == Nat.add(Nat.add(W(rh, d), x), Nat.add(W(rb, d), y)) : Nat}
      %K.sym(Nat, wt(d, gm), Nat.add(x, y), eg) : {Nat.add(Nat.add(W(rh, d), _), W(rb, d)) == Nat.add(Nat.add(W(rh, d), x), Nat.add(W(rb, d), y)) : Nat}
      ac_snoc(W(rh, d), x, y, W(rb, d))
    case False{}:
      %K.sym(Nat, W(G.insert_at(G.Mon, rb, fi, gm), d), Nat.add(wt(d, gm), W(rb, d)), w_ins(rb, fi, gm, d)) : {Nat.add(W(rh, d), _) == Nat.add(Nat.add(W(rh, d), x), Nat.add(W(rb, d), y)) : Nat}
      %K.sym(Nat, wt(d, gm), Nat.add(x, y), eg) : {Nat.add(W(rh, d), Nat.add(_, W(rb, d))) == Nat.add(Nat.add(W(rh, d), x), Nat.add(W(rb, d), y)) : Nat}
      ac_ins(W(rh, d), x, y, W(rb, d))

# LAW (A1, cards): a merge of c (>= 3 regular copies) conserves, for EVERY
# card d, the hand + board weight with golden multiplicity (golden = 3)
law merge_weight:
  for +c: Nat
  for +hand: List<&2, G.Mon>
  for +board: List<&2, G.Mon>
  for +d: Nat
  for h3: {Nat.is_ge(G.copies(List.append(&2, G.Mon, hand, board), c), 3n) == True{} : Bool}
  {WHB(G.merge_hb(c, hand, board), d) == Nat.add(W(hand, d), W(board, d)) : Nat}

def merge_weight(c, hand, board, d, h3):
  +th = G.take(hand, c, 3n)
  +tb = G.take(board, c, Nat.sub(3n, GL(th)))
  +gm = G.fuse(c, List.append(&2, G.Mon, G.take_taken(th), G.take_taken(tb)))
  %take_weight(hand, c, 3n, d) : {WHB(G.merge_hb(c, hand, board), d) == Nat.add(_, W(board, d)) : Nat}
  %take_weight(board, c, Nat.sub(3n, GL(th)), d) : {WHB(G.merge_hb(c, hand, board), d) == Nat.add(Nat.add(WR(th, d), WG(th, d)), _) : Nat}
  hb_w(Nat.is_gt(GL(th), 0n), G.take_rest(th), G.take_rest(tb), G.first_copy(board, c, 0n), gm, d, WG(th, d), WG(tb, d),
    %K.sym(Nat, WG(th, d), G.pick(Nat, G.nat_eq(c, d), GL(th), 0n), taken_weight(hand, c, 3n, d)) : {G.pick(Nat, G.nat_eq(c, d), 3n, 0n) == Nat.add(_, WG(tb, d)) : Nat}
    %K.sym(Nat, WG(tb, d), G.pick(Nat, G.nat_eq(c, d), GL(tb), 0n), taken_weight(board, c, Nat.sub(3n, GL(th)), d)) : {G.pick(Nat, G.nat_eq(c, d), 3n, 0n) == Nat.add(G.pick(Nat, G.nat_eq(c, d), GL(th), 0n), _) : Nat}
    pick_sum3(G.nat_eq(c, d), GL(th), GL(tb), took_three(c, hand, board, h3)))

def WP(+p: G.Player, +d: Nat) -> Nat:
  Nat.add(W(G.p_hand(p), d), W(G.p_board(p), d))

def fin_w(hb: G.HB, +p: G.Player, +d: Nat) -> {WP(G.merge_fin(hb, p), d) == WHB(hb, d) : Nat}:
  match hb p:
    case G.HB{nh, nb} G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}:
      {==}

def norm_go_w(fuel: Nat, mc: Maybe<&2, Nat>, +p: G.Player, +d: Nat,
  ht: TriOk(List.append(&2, G.Mon, G.p_hand(p), G.p_board(p)), mc)) -> {WP(G.norm_go(fuel, mc, p), d) == WP(p, d) : Nat}:
  match fuel mc:
    case _ None{}:
      {==}
    case 0n Some{c}:
      {==}
    case 1n+f Some{+c}:
      +q = G.merge_p(c, p)
      Equal.trans(Nat, WP(G.norm_go(f, G.triple_of(G.p_hand(q), G.p_board(q)), q), d), WP(q, d), WP(p, d),
        norm_go_w(f, G.triple_of(G.p_hand(q), G.p_board(q)), q, d, triple_sound(G.p_hand(q), G.p_board(q))),
        Equal.trans(Nat, WP(q, d), WHB(G.merge_hb(c, G.p_hand(p), G.p_board(p)), d), WP(p, d),
          fin_w(G.merge_hb(c, G.p_hand(p), G.p_board(p)), p, d),
          merge_weight(c, G.p_hand(p), G.p_board(p), d,
            K.from_T(Nat.is_ge(G.copies(List.append(&2, G.Mon, G.p_hand(p), G.p_board(p)), c), 3n), ht))))

# LAW (card conservation, golden multiplicity): for EVERY player and EVERY
# card d, p_norm keeps sum over hand + board of (3 per golden d, 1 per
# regular d): assembly never loses, duplicates or retypes a card
law norm_weight:
  for +p: G.Player
  for +d: Nat
  {WP(G.p_norm(p), d) == WP(p, d) : Nat}

def norm_weight(p, d):
  norm_go_w(4n, G.triple_of(G.p_hand(p), G.p_board(p)), p, d, triple_sound(G.p_hand(p), G.p_board(p)))

# A5: multiplier-1 parity (a regular unit reads its printed card exactly)
# ======================================================================

def scale_false(+xs: List<&2, G.Abil>) -> {G.scale_abils(False{}, xs) == xs : List<&2, G.Abil>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      Equal.cong(List<&2, G.Abil>, List<&2, G.Abil>, z => x <> z, G.scale_abils(False{}, t), t, scale_false(t))

# LAW: for EVERY regular (non-golden) unit, the effective abilities,
# Rally and Income are the printed card's, unchanged from V3
law regular_parity:
  for +c: Nat
  for a: Nat
  for h: Nat
  for s: Bool
  K.Both<{G.mon_abils(G.Mon{c, a, h, s, False{}}) == G.c_abils(c) : List<&2, G.Abil>},
    K.Both<{G.mon_rally(G.Mon{c, a, h, s, False{}}) == G.c_rally(c) : Nat}, {G.mon_income(G.Mon{c, a, h, s, False{}}) == G.c_income(c) : Nat}>>

def regular_parity(c, a, h, s):
  K.Both{scale_false(G.c_abils(c)), K.Both{{==}, {==}}}

# LAW: a golden unit pays exactly twice the printed Rally and Income
law golden_double:
  for +c: Nat
  for a: Nat
  for h: Nat
  for s: Bool
  K.Both<{G.mon_rally(G.Mon{c, a, h, s, True{}}) == Nat.add(G.c_rally(c), G.c_rally(c)) : Nat},
    {G.mon_income(G.Mon{c, a, h, s, True{}}) == Nat.add(G.c_income(c), G.c_income(c)) : Nat}>

def golden_double(c, a, h, s):
  K.Both{{==}, {==}}
