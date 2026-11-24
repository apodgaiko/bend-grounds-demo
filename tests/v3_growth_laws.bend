# Growth laws and fixtures through engine/game.bend.
#
# What is proven and what is only an example:
# - `law kin_skip` is UNIVERSAL: for every board, tribe, index, offset and
#   amounts, a KIN stat pass (G.kin_go, the only KIN stat path of the
#   ability interpreter) leaves the unit at the source index unchanged.
#   This is "other allies never include the source", for all inputs.
# - `law roster_*` are EXHAUSTIVE over the finite roster (all card ids,
#   computed from G.card; V4: 44 ids, cause e): tier stat bands strictly separate tiers, every
#   tier-4 card has a double-digit base stat, Armor stays 0..2, the tier-1
#   cards are exactly the v2 baseline. Exhaustive over 36 ids, so complete
#   for the printed table; they say nothing about buffed units.
# - `law g_*` are CONCRETE, hash-free fixtures through the real engine
#   (G.p_apply, G.grow_player) with HAND-CALCULATED expectations
#   (calculations in the comments). Examples, not universal laws.
# - `main` also prints hash-using fixtures (MAKE, end-of-turn order with a
#   card maker, no-duplication over all 36 cards) that are too costly for
#   the kernel; the expected PASS block is recorded at the end of this file.
#
# Check: bun vendor/bend/bend2/main.ts tests/v3_growth_laws.bend [--verdict]
import Base
import ../engine/game.bend as G
import ./proof_kit.bend as K

type Case is Data:
  Case{name: String, got: String, want: String}

# Universal: KIN skips its source
# ===============================

def eq_refl(n: Nat) -> {G.nat_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def head_skip(c: Bool, +x: G.Mon, +m: G.Mon, rest: List<&2, G.Mon>) -> {List.get(&2, G.Mon, G.pick(G.Mon, c && False{}, x, m) <> rest, 0n) == Some{m} : Maybe<&2, G.Mon>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the unit at the source index (pos + n, counting from pos) is
# untouched by a KIN pass, whatever its tribe and the amounts
law kin_skip:
  for b: List<&2, G.Mon>
  for +tr: Nat
  for n: Nat
  for +pos: Nat
  for +da: Nat
  for +dh: Nat
  {List.get(&2, G.Mon, G.kin_go(b, tr, Nat.add(n, pos), pos, da, dh), n) == List.get(&2, G.Mon, b, n) : Maybe<&2, G.Mon>}

def kin_skip(b, tr, n, pos, da, dh):
  match b n:
    case Nil{} _:
      {==}
    case +m <> t 0n:
      %K.sym(Bool, G.nat_eq(pos, pos), True{}, eq_refl(pos))
        : {List.get(&2, G.Mon, G.pick(G.Mon, G.kin_match(G.mon_tribe(m), tr) && Bool.not(_), G.mon_add(da, dh, m), m) <> G.kin_go(t, tr, pos, 1n+pos, da, dh), 0n) == Some{m} : Maybe<&2, G.Mon>}
      head_skip(G.kin_match(G.mon_tribe(m), tr), G.mon_add(da, dh, m), m, G.kin_go(t, tr, pos, 1n+pos, da, dh))
    case +m <> t 1n+(+k):
      %K.sym(Nat, 1n+Nat.add(k, pos), Nat.add(k, 1n+pos), K.add_succ(k, pos))
        : {List.get(&2, G.Mon, G.kin_go(t, tr, _, 1n+pos, da, dh), k) == List.get(&2, G.Mon, t, k) : Maybe<&2, G.Mon>}
      kin_skip(t, tr, k, 1n+pos, da, dh)

# Exhaustive over the roster (V4: all 44 ids, Neutral 36..43 included)
# ===================================================================

def mon_budget(x: G.Mon) -> Nat:
  G.Mon{i, a, h, s, g} = x
  Nat.add(a, h)

def budget(+c: Nat) -> Nat:
  mon_budget(G.mon_of(c))

def ids() -> List<&2, Nat>:
  List.range(G.card_count())

# min / max printed attack+health among cards of tier t
def band_min(xs: List<&2, Nat>, +t: Nat, +best: Nat) -> Nat:
  match xs:
    case Nil{}:
      best
    case +c <> r:
      band_min(r, t, G.pick(Nat, G.nat_eq(G.c_tier(c), t), Nat.min(best, budget(c)), best))

def band_max(xs: List<&2, Nat>, +t: Nat, +best: Nat) -> Nat:
  match xs:
    case Nil{}:
      best
    case +c <> r:
      band_max(r, t, G.pick(Nat, G.nat_eq(G.c_tier(c), t), Nat.max(best, budget(c)), best))

def bands(+t: Nat) -> String:
  "t" ++ Nat.show(t) ++ ":" ++ Nat.show(band_min(ids(), t, 1000n)) ++ ".." ++ Nat.show(band_max(ids(), t, 0n))

def bands_all() -> String:
  bands(1n) ++ " " ++ bands(2n) ++ " " ++ bands(3n) ++ " " ++ bands(4n) ++ " " ++ bands(5n)

# LAW (exhaustive): printed attack+health bands per tier; each band lies
# strictly above the previous one (4 < 6, 8 < 12, 16 < 22, 26 < 36)
law roster_bands:
  {bands_all() == "t1:2..4 t2:6..8 t3:12..16 t4:22..26 t5:36..48" : String}

def roster_bands():
  {==}

def mon_big(x: G.Mon) -> Bool:
  G.Mon{i, a, h, s, g} = x
  Nat.is_le(10n, a) || Nat.is_le(10n, h)

def t4_big(+c: Nat) -> Bool:
  Bool.not(G.nat_eq(G.c_tier(c), 4n)) || mon_big(G.mon_of(c))

def all_big(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +c <> r:
      t4_big(c) && all_big(r)

def all_armor(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +c <> r:
      Nat.is_le(G.c_armor(c), 2n) && all_armor(r)

# LAW (exhaustive): every tier-4 card has a base attack or health >= 10
law roster_t4_double_digit:
  {all_big(ids()) == True{} : Bool}

def roster_t4_double_digit():
  {==}

# LAW (exhaustive): Armor is 0, 1 or 2 on every card (no exponential Armor)
law roster_armor_le2:
  {all_armor(ids()) == True{} : Bool}

def roster_armor_le2():
  {==}

def mon_ah(x: G.Mon) -> String:
  G.Mon{i, a, h, s, g} = x
  Nat.show(a) ++ "/" ++ Nat.show(h)

def row(+c: Nat) -> String:
  Nat.show(c) ++ ":" ++ mon_ah(G.mon_of(c)) ++ " " ++ G.card_text(G.card(c))

def rows(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case c <> r:
      row(c) ++ "; " ++ rows(r)

# LAW (exhaustive over tier 1): the nine tier-1 cards are the v2 baseline
# (stats and abilities; Shell Scout's text gained "(if it has room)")
law roster_t1_baseline:
  {rows(List.range(9n)) == "0:2/1 Rally 1.; 1:1/2 After you play another Ember card: gain +1 attack.; 2:1/2 Play: give other Ember allies +1 attack.; 3:1/1 Income 1.; 4:1/2 Shield. Sell: gain 1 gold.; 5:1/1 Play: add a random Tide card of tier 1 or lower to your hand (if it has room).; 6:1/3 Guard.; 7:1/3 Armor 1.; 8:1/2 End of turn: gain +1 health.; " : String}

def roster_t1_baseline():
  {==}

# Concrete fixtures (real engine, hand-calculated)
# ================================================

def m(+c: Nat, +a: Nat, +h: Nat) -> G.Mon:
  G.Mon{c, a, h, False{}, False{}}

def ms(+c: Nat, +a: Nat, +h: Nat) -> G.Mon:
  G.Mon{c, a, h, True{}, False{}}

def fill(+k: Nat, +x: G.Mon) -> List<&2, G.Mon>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      x <> fill(j, x)

# seat 0, 20 hp, tier 5, no upgrade cost, alive; `plays` made so far
def PP(+gold: Nat, board: List<&2, G.Mon>, hand: List<&2, G.Mon>, +plays: Nat) -> G.Player:
  G.Player{0n, 20n, gold, 5n, 0n, 0n, False{}, 0n, board, [], True{}, 0n, hand, plays}

def seed() -> U32:
  7

def sm(x: G.Mon) -> String:
  G.Mon{c, a, h, s, g} = x
  Nat.show(c) ++ ":" ++ Nat.show(a) ++ "/" ++ Nat.show(h) ++ G.pick(String, s, "s", "") ++ G.pick(String, g, "G", "")

def sms(b: List<&2, G.Mon>) -> String:
  match b:
    case Nil{}:
      ""
    case x <> t:
      match t:
        case Nil{}:
          sm(x)
        case y <> r:
          sm(x) ++ "," ++ sms(t)

def after(acts: List<&2, G.Act>, +p: G.Player) -> G.Player:
  match acts:
    case Nil{}:
      p
    case a <> t:
      after(t, G.pres_or(G.p_apply(seed(), 9n, p, a), p))

def view(+p: G.Player) -> String:
  "g=" ++ Nat.show(G.p_gold(p)) ++ " n=" ++ Nat.show(G.p_plays(p)) ++ " b=[" ++ sms(G.p_board(p)) ++ "] h=[" ++ sms(G.p_hand(p)) ++ "]"

def eot(+p: G.Player) -> G.Player:
  G.grow_player(seed(), 9n, p)

# Ember chain: Pyre Captain 10/12 and Inferno Drake 6/6 on the board, three
# Spark Imps played in one turn (0 earlier plays at the start).
# play 1 (0 earlier): Captain x0; Drake +1/+1 to Captain 11/13, Imp1 3/2
# play 2 (1 earlier): Captain +1/+1 to Drake 7/7, Imp1 4/3, Imp2 3/2;
#   Drake +1/+1 to Captain 12/14, Imp1 5/4, Imp2 4/3
# play 3 (2 earlier): Captain +2/+2 to Drake 9/9, Imp1 7/6, Imp2 6/5,
#   Imp3 4/3; Drake +1/+1 to Captain 13/15, Imp1 8/7, Imp2 7/6, Imp3 5/4
# (the per-play gain grows with each play: a quadratic chain)
# V4 cause (f): after play 1 the board Imp and the two held Imps are three
# regular copies, so they assemble (hand first): golden Imp (2+2+3-2)/
# (1+1+2-1) = 5/3 to the hand. Play 2 (1 earlier) plays it: Captain
# +1/+1 to Drake 7/7 and the Imp 6/4; Drake +1/+1 to Captain 12/14 and the
# Imp 7/5. The hand is then empty, so the third play is rejected (n=2).
def g_ember_chain_t() -> String:
  view(after([G.Play{0n}, G.Play{0n}, G.Play{0n}], PP(0n, [m(24n, 10n, 12n), m(18n, 6n, 6n)], fill(3n, m(0n, 2n, 1n)), 0n)))

law g_ember_chain:
  {g_ember_chain_t() == "g=0 n=2 b=[24:12/14,18:7/7,0:7/5G] h=[]" : String}

def g_ember_chain():
  {==}

# the V3 quadratic chain with no triple: two Imps, then a Blaze Charger
# (4/4, no abilities) as the third play.
# plays 1-2 as above (Captain 12/14, Drake 7/7, Imp1 5/4, Imp2 4/3);
# play 3 (2 earlier): Captain +2/+2 to Drake 9/9, Imp1 7/6, Imp2 6/5,
#   Charger 6/6; Drake +1/+1 to Captain 13/15, Imp1 8/7, Imp2 7/6, Charger 7/7
def g_ember_chain_mixed_t() -> String:
  view(after([G.Play{0n}, G.Play{0n}, G.Play{0n}], PP(0n, [m(24n, 10n, 12n), m(18n, 6n, 6n)], [m(0n, 2n, 1n), m(0n, 2n, 1n), m(11n, 4n, 4n)], 0n)))

law g_ember_chain_mixed:
  {g_ember_chain_mixed_t() == "g=0 n=3 b=[24:13/15,18:9/9,0:8/7,0:7/6,11:7/7] h=[]" : String}

def g_ember_chain_mixed():
  {==}

# Tide hand: Maelstrom Queen, Abyss Choir, Reef Warden; 4 cards held.
# end of turn 1: Queen gives the other Tide allies +8/+8 (Choir 18/22,
#   Warden 11/11s); Choir gains +8/+8 (26/30)
# end of turn 2: Queen +8/+8 (Choir 34/38, Warden 19/19s); Choir 42/46
def g_tide_hand_t() -> String:
  +p0 = PP(0n, [ms(32n, 16n, 22n), m(27n, 10n, 14n), ms(12n, 3n, 3n)], fill(4n, m(6n, 1n, 3n)), 0n)
  +p1 = eot(p0)
  sms(G.p_board(p1)) ++ " | " ++ sms(G.p_board(eot(p1)))

law g_tide_hand:
  {g_tide_hand_t() == "32:16/22s,27:26/30,12:11/11s | 32:16/22s,27:42/46,12:19/19s" : String}

def g_tide_hand():
  {==}

# Stone end of turn, two turns: Worldroot 14/30, Quarry Drummer 12/12,
# Mountain Heart 5/8, Granite Titan 5/11, board left to right.
# turn 1: Worldroot +2/+4 others (D 14/16, M 7/12, T 7/15); Drummer +2/+1
#   others (W 16/31, M 9/13, T 9/16); Heart +1/+1 others (W 17/32,
#   D 15/17, T 10/17); Titan +1/+2 itself (11/19)
# turn 2: W: D 17/21, M 11/17, T 13/23; D: W 19/33, M 13/18, T 15/24;
#   M: W 20/34, D 18/22, T 16/25; T: 17/27
def g_stone_eot_t() -> String:
  +p0 = PP(0n, [m(34n, 14n, 30n), m(29n, 12n, 12n), m(23n, 5n, 8n), m(22n, 5n, 11n)], [], 0n)
  +p1 = eot(p0)
  sms(G.p_board(p1)) ++ " | " ++ sms(G.p_board(eot(p1)))

law g_stone_eot:
  {g_stone_eot_t() == "34:17/32,29:15/17,23:9/13,22:11/19 | 34:20/34,29:18/22,23:13/18,22:17/27" : String}

def g_stone_eot():
  {==}

# Cinder Queen at end of a turn with 3 plays: the other Ember allies get
# +2/+2 x3 = +6/+6 (Captain 16/18, Imp 8/7); the Queen itself is not buffed
def g_queen_chain_t() -> String:
  sms(G.p_board(eot(PP(0n, [ms(31n, 18n, 18n), m(24n, 10n, 12n), m(0n, 2n, 1n)], [], 3n))))

law g_queen_chain:
  {g_queen_chain_t() == "31:18/18s,24:16/18,0:8/7" : String}

def g_queen_chain():
  {==}

# source excluded: a lone Worldroot (with an Ember Imp) buffs nobody; a
# Pyre Captain with 3 earlier plays buffs the entering Imp +3/+3 and not
# itself
def g_source_excluded_t() -> String:
  sms(G.p_board(eot(PP(0n, [m(34n, 14n, 30n), m(0n, 2n, 1n)], [], 0n)))) ++ " | " ++ view(after([G.Play{0n}], PP(0n, [m(24n, 10n, 12n)], [m(0n, 2n, 1n)], 3n)))

law g_source_excluded:
  {g_source_excluded_t() == "34:14/30,0:2/1 | g=0 n=4 b=[24:10/12,0:5/4] h=[]" : String}

def g_source_excluded():
  {==}

# the played card is not counted: Kiln Matron's "+2/+1 per earlier play"
# is checked in main (Matron also makes a card, which uses the hash);
# Tidecaller counts the hand after it left: 3 cards held -> +3/+3
def g_hand_after_leave_t() -> String:
  view(after([G.Play{0n}], PP(0n, [], [m(13n, 3n, 3n), m(6n, 1n, 3n), m(6n, 1n, 3n), m(6n, 1n, 3n)], 0n)))

# V4 cause (f): the three held regular Pebble Guards (an unreachable
# start) assemble after the play: 3/9 - 1/3 = 2/6, golden
law g_hand_after_leave:
  {g_hand_after_leave_t() == "g=0 n=1 b=[13:6/6] h=[6:2/6G]" : String}

def g_hand_after_leave():
  {==}

# the V3 intent with no triple: 3 cards held after it left -> +3/+3
def g_hand_after_leave_mixed_t() -> String:
  view(after([G.Play{0n}], PP(0n, [], [m(13n, 3n, 3n), m(6n, 1n, 3n), m(6n, 1n, 3n), m(7n, 1n, 3n)], 0n)))

law g_hand_after_leave_mixed:
  {g_hand_after_leave_mixed_t() == "g=0 n=1 b=[13:6/6] h=[6:1/3,6:1/3,7:1/3]" : String}

def g_hand_after_leave_mixed():
  {==}

# board cap: a sixth unit is refused, nothing changes (Imp stays in hand)
def g_board_cap_t() -> String:
  view(after([G.Play{0n}], PP(0n, fill(5n, m(24n, 10n, 12n)), [m(0n, 2n, 1n)], 0n)))

law g_board_cap:
  {g_board_cap_t() == "g=0 n=0 b=[24:10/12,24:10/12,24:10/12,24:10/12,24:10/12] h=[0:2/1]" : String}

def g_board_cap():
  {==}

# Hash-using fixtures (main only)
# ===============================

def tide_ok(+x: G.Mon, +maxt: Nat) -> Bool:
  G.nat_eq(G.mon_tribe(x), 1n) && Nat.is_le(G.mon_tier(x), maxt)

# full hand (7): Tidal Sovereign makes nothing and gains +8/+8 (cap 4)
def h_hand_cap_t() -> String:
  +p = eot(PP(0n, [m(33n, 16n, 24n)], fill(7n, m(6n, 1n, 3n)), 0n))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def first_tide(r: List<&2, G.Mon>, +maxt: Nat) -> String:
  match r:
    case Nil{}:
      "none"
    case +x <> t:
      G.pick(String, tide_ok(x, maxt), "made-ok", "BAD:" ++ sm(x))

def last_tide(h: List<&2, G.Mon>, +maxt: Nat) -> String:
  first_tide(List.reverse(&2, G.Mon, h), maxt)

# end-of-turn ORDER with a maker, 2 cards held:
# Sovereign first: makes 1 (hand 3), gains +6/+6 (22/30); Choir +6/+6 (16/20)
# Choir first: +4/+4 (14/18); Sovereign makes 1 (hand 3), +6/+6 (22/30)
def h_order_t() -> String:
  +a = eot(PP(0n, [m(33n, 16n, 24n), m(27n, 10n, 14n)], fill(2n, m(6n, 1n, 3n)), 0n))
  +b = eot(PP(0n, [m(27n, 10n, 14n), m(33n, 16n, 24n)], fill(2n, m(6n, 1n, 3n)), 0n))
  sms(G.p_board(a)) ++ " " ++ last_tide(G.p_hand(a), 4n) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(a))) ++ " | " ++ sms(G.p_board(b)) ++ " " ++ last_tide(G.p_hand(b), 4n) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(b)))

def all_mon(h: List<&2, G.Mon>, +tr: Nat, +maxt: Nat) -> Bool:
  match h:
    case Nil{}:
      True{}
    case +x <> r:
      G.nat_eq(G.mon_tribe(x), tr) && Nat.is_le(G.mon_tier(x), maxt) && all_mon(r, tr, maxt)

# Kiln Matron with 2 earlier plays: makes one Ember card (tier <= 3), then
# +2/+1 x2 -> 16/12
def h_matron_t() -> String:
  +p = after([G.Play{0n}], PP(0n, [], [m(25n, 12n, 10n)], 2n))
  +h = G.p_hand(p)
  sms(G.p_board(p)) ++ " made=" ++ Nat.show(G.len(G.Mon, h)) ++ " ok=" ++ G.pick(String, all_mon(h, 0n, 3n), "T", "F")

# no duplication, all cards (V4: 44 ids; Copper Tinker 37 also gains 1
# gold on Play): playing card c (base unit) from a hand
# holding only it onto an empty board leaves exactly one unit, of card c;
# the hand then holds only cards made by a Play MAKE (Shell Scout 5 and
# Kiln Matron 25, one each). Selling it back leaves an empty board and a
# hand holding only the Sell MAKE card (Pearl Broker 26). Gold changes only
# by Coin Eel's Play (+1) and the sell refund (+1, +1 more for Tide Pup and
# Coin Eel).
def makes_on_play(+c: Nat) -> Nat:
  G.pick(Nat, G.nat_eq(c, 5n) || G.nat_eq(c, 25n), 1n, 0n)

def makes_on_sell(+c: Nat) -> Nat:
  G.pick(Nat, G.nat_eq(c, 26n), 1n, 0n)

def gold_on_play(+c: Nat) -> Nat:
  G.pick(Nat, G.nat_eq(c, 14n) || G.nat_eq(c, 37n), 1n, 0n)

def gold_on_sell(+c: Nat) -> Nat:
  G.pick(Nat, G.nat_eq(c, 4n) || G.nat_eq(c, 14n), 2n, 1n)

def one_of(b: List<&2, G.Mon>, +c: Nat) -> Bool:
  match b:
    case Nil{}:
      False{}
    case x <> r:
      G.nat_eq(G.mon_cid(x), c) && List.is_empty(&2, G.Mon, r)

def nodup_one(+c: Nat) -> Bool:
  +p1 = after([G.Play{0n}], PP(0n, [], [G.mon_of(c)], 0n))
  +p2 = G.pres_or(G.p_apply(seed(), 9n, PP(0n, G.p_board(p1), [], 1n), G.Sell{0n}), p1)
  one_of(G.p_board(p1), c) && G.nat_eq(G.len(G.Mon, G.p_hand(p1)), makes_on_play(c)) && G.nat_eq(G.p_gold(p1), gold_on_play(c))
    && List.is_empty(&2, G.Mon, G.p_board(p2)) && G.nat_eq(G.len(G.Mon, G.p_hand(p2)), makes_on_sell(c)) && G.nat_eq(G.p_gold(p2), gold_on_sell(c))

def nodup_bad(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case +c <> r:
      G.pick(String, nodup_one(c), "", Nat.show(c) ++ " ") ++ nodup_bad(r)

def h_nodup_t() -> String:
  "bad=[" ++ nodup_bad(ids()) ++ "]"

# Report
# ======

def verdict(+n: String, +g: String, +w: String) -> String:
  G.pick(String, String.eq(g, w), "PASS " ++ n, "FAIL " ++ n ++ "\n  got:  " ++ g ++ "\n  want: " ++ w)

def line(c: Case) -> String:
  Case{n, g, w} = c
  verdict(n, g, w)

def lines(cs: List<&2, Case>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      line(c) <> lines(t)

def cases() -> List<&2, Case>:
  [ Case{"roster_bands", bands_all(), "t1:2..4 t2:6..8 t3:12..16 t4:22..26 t5:36..48"}
  , Case{"ember_chain", g_ember_chain_t(), "g=0 n=2 b=[24:12/14,18:7/7,0:7/5G] h=[]"}
  , Case{"ember_chain_mixed", g_ember_chain_mixed_t(), "g=0 n=3 b=[24:13/15,18:9/9,0:8/7,0:7/6,11:7/7] h=[]"}
  , Case{"tide_hand", g_tide_hand_t(), "32:16/22s,27:26/30,12:11/11s | 32:16/22s,27:42/46,12:19/19s"}
  , Case{"stone_eot", g_stone_eot_t(), "34:17/32,29:15/17,23:9/13,22:11/19 | 34:20/34,29:18/22,23:13/18,22:17/27"}
  , Case{"queen_chain", g_queen_chain_t(), "31:18/18s,24:16/18,0:8/7"}
  , Case{"source_excluded", g_source_excluded_t(), "34:14/30,0:2/1 | g=0 n=4 b=[24:10/12,0:5/4] h=[]"}
  , Case{"hand_after_leave", g_hand_after_leave_t(), "g=0 n=1 b=[13:6/6] h=[6:2/6G]"}
  , Case{"hand_after_leave_mixed", g_hand_after_leave_mixed_t(), "g=0 n=1 b=[13:6/6] h=[6:1/3,6:1/3,7:1/3]"}
  , Case{"board_cap", g_board_cap_t(), "g=0 n=0 b=[24:10/12,24:10/12,24:10/12,24:10/12,24:10/12] h=[0:2/1]"}
  , Case{"hand_cap_sovereign", h_hand_cap_t(), "33:24/32 handlen=7"}
  , Case{"eot_order_maker", h_order_t(), "33:22/30,27:16/20 made-ok handlen=3 | 27:14/18,33:22/30 made-ok handlen=3"}
  , Case{"matron_earlier_plays", h_matron_t(), "25:16/12 made=1 ok=T"}
  , Case{"no_duplication_all", h_nodup_t(), "bad=[]"}
  ]

def main() -> IO(Unit):
  IO.print(String.join(lines(cases()), "\n"))

#|PASS roster_bands
#|PASS ember_chain
#|PASS ember_chain_mixed
#|PASS tide_hand
#|PASS stone_eot
#|PASS queen_chain
#|PASS source_excluded
#|PASS hand_after_leave
#|PASS hand_after_leave_mixed
#|PASS board_cap
#|PASS hand_cap_sovereign
#|PASS eot_order_maker
#|PASS matron_earlier_plays
#|PASS no_duplication_all
