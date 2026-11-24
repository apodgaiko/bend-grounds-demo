# EMBER card-interaction fixtures (finite, concrete), migrated to the V3
# roster: every expected result was computed by
# hand from the V3 card text, then compared with the engine.
#
# Every case builds a real engine Player (G.Player), runs real engine
# functions (G.p_apply, G.grow_player, G.board_income, card table), and
# compares a printed summary with a HAND-CALCULATED expected string. The
# expected strings are constants written from the card text in
# the printed card descriptions; no rule is
# re-implemented here.
#
# Two layers:
# - `law k_*` facts: closed equalities over hash-free cases. bend2 checks
#   them, and `--verdict` rechecks them with the Lean-proven kernel.
# - `main` prints PASS/FAIL for every case, including the hash-using MAKE
#   cases that are too costly for the kernel (they only assert membership
#   in the hand-written pool, never a specific random id). The expected
#   output is the block of PASS lines at the end of this file;
#   tests/card_interactions_test.py compares it.
#
# These are concrete examples, NOT universal proofs. Universal laws live in
# tests/engine_invariants.bend and tests/action_laws.bend.
#
# Player summary (sp):
#   g=<gold> n=<plays> b=[board] h=[hand] s=[shop] r=<hp/tier/upcost/invest/frozen/rolls/alive/out>
# A unit is cid:attack/health, with a trailing "s" when shielded and a
# trailing "G" when golden (V4). A run
# prints one tag per action ("+" accepted, "x" rejected), then "|", then
# the final summary; a rejected action keeps the previous player.
import Base
import ../engine/game.bend as G

type Case is Data:
  Case{name: String, got: String, want: String}

# Fixture builders
# ----------------

def m(+c: Nat, +a: Nat, +h: Nat) -> G.Mon:
  G.Mon{c, a, h, False{}, False{}}

def ms(+c: Nat, +a: Nat, +h: Nat) -> G.Mon:
  G.Mon{c, a, h, True{}, False{}}

# V4 golden units (shown with a trailing "G")
def mg(+c: Nat, +a: Nat, +h: Nat) -> G.Mon:
  G.Mon{c, a, h, False{}, True{}}

def mgs(+c: Nat, +a: Nat, +h: Nat) -> G.Mon:
  G.Mon{c, a, h, True{}, True{}}

# a mid-game player: seat 0, 20 hp, tier 3, upgrade cost 7, no investment,
# shop not frozen, no rolls, alive, `plays` plays made this recruit phase
def PP(+gold: Nat, board: List<&2, G.Mon>, shop: List<&2, Nat>, hand: List<&2, G.Mon>, +plays: Nat) -> G.Player:
  G.Player{0n, 20n, gold, 3n, 7n, 0n, False{}, 0n, board, shop, True{}, 0n, hand, plays}

def P(+gold: Nat, board: List<&2, G.Mon>, shop: List<&2, Nat>, hand: List<&2, G.Mon>) -> G.Player:
  PP(gold, board, shop, hand, 0n)

def fill(+k: Nat, +x: G.Mon) -> List<&2, G.Mon>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      x <> fill(j, x)

def seed() -> U32:
  7

# Summaries
# ---------

def sb(b: Bool) -> String:
  G.pick(String, b, "T", "F")

def sm(x: G.Mon) -> String:
  G.Mon{c, a, h, s, g} = x
  Nat.show(c) ++ ":" ++ Nat.show(a) ++ "/" ++ Nat.show(h) ++ G.pick(String, s, "s", "") ++ G.pick(String, g, "G", "")

def sms_rest(b: List<&2, G.Mon>) -> String:
  match b:
    case Nil{}:
      ""
    case x <> t:
      "," ++ sm(x) ++ sms_rest(t)

def sms(b: List<&2, G.Mon>) -> String:
  match b:
    case Nil{}:
      ""
    case x <> t:
      sm(x) ++ sms_rest(t)

def sns_rest(b: List<&2, Nat>) -> String:
  match b:
    case Nil{}:
      ""
    case x <> t:
      "," ++ Nat.show(x) ++ sns_rest(t)

def sns(b: List<&2, Nat>) -> String:
  match b:
    case Nil{}:
      ""
    case x <> t:
      Nat.show(x) ++ sns_rest(t)

def sp(p: G.Player) -> String:
  G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  "g=" ++ Nat.show(gold) ++ " n=" ++ Nat.show(plays) ++ " b=[" ++ sms(board) ++ "] h=[" ++ sms(hand) ++ "] s=[" ++ sns(shop)
    ++ "] r=" ++ Nat.show(hp) ++ "/" ++ Nat.show(tier) ++ "/" ++ Nat.show(upcost) ++ "/" ++ Nat.show(invest) ++ "/" ++ sb(frozen)
    ++ "/" ++ Nat.show(rolls) ++ "/" ++ sb(alive) ++ "/" ++ Nat.show(out)

def act_or_none(ma: Maybe<&2, G.Act>) -> String:
  match ma:
    case None{}:
      "none"
    case Some{a}:
      G.act_str(a)

# board and hand only
def zones(p: G.Player) -> String:
  G.Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  "b=[" ++ sms(board) ++ "] h=[" ++ sms(hand) ++ "]"

def tag(r: G.PRes) -> String:
  match r:
    case G.PGood{p}:
      "+"
    case G.PBad{msg}:
      "x"

def run(acts: List<&2, G.Act>, +p: G.Player) -> String:
  match acts:
    case Nil{}:
      "|" ++ sp(p)
    case a <> t:
      +r = G.p_apply(seed(), 3n, p, a)
      tag(r) ++ run(t, G.pres_or(r, p))

def after(acts: List<&2, G.Act>, +p: G.Player) -> G.Player:
  match acts:
    case Nil{}:
      p
    case a <> t:
      after(t, G.pres_or(G.p_apply(seed(), 3n, p, a), p))

# end of the recruit phase for one player (ENDTURN abilities)
def endturn_p(board: List<&2, G.Mon>, hand: List<&2, G.Mon>, +plays: Nat) -> G.Player:
  G.grow_player(seed(), 3n, PP(0n, board, [], hand, plays))

def endturn(board: List<&2, G.Mon>, hand: List<&2, G.Mon>) -> G.Player:
  endturn_p(board, hand, 0n)

# hand-written expectation: tags, gold, plays, board, hand, shop; the other
# fields must still be the fixture's (20 hp, tier 3, upcost 7, ...)
def W(tags: String, +g: Nat, +n: Nat, b: String, h: String, s: String) -> String:
  tags ++ "|g=" ++ Nat.show(g) ++ " n=" ++ Nat.show(n) ++ " b=[" ++ b ++ "] h=[" ++ h ++ "] s=[" ++ s ++ "] r=20/3/7/0/F/0/T/0"

# MAKE pools, from the table: base units of the tribe with tier <= a
def in_pool(+s: String, pool: List<&2, String>) -> Bool:
  match pool:
    case Nil{}:
      False{}
    case x <> t:
      String.eq(s, x) || in_pool(s, t)

def tide1() -> List<&2, String>:
  ["3:1/1", "4:1/2s", "5:1/1"]

def tide2() -> List<&2, String>:
  List.append(&2, String, tide1(), ["12:3/3s", "13:3/3", "14:3/3"])

def tide3() -> List<&2, String>:
  List.append(&2, String, tide2(), ["20:5/7s", "21:4/8"])

def tide4() -> List<&2, String>:
  List.append(&2, String, tide3(), ["26:10/12", "27:10/14"])

def ember3() -> List<&2, String>:
  ["0:2/1", "1:1/2", "2:1/2", "9:3/3", "10:3/4", "11:4/4", "18:6/6", "19:8/6s"]

def pool_tags(+tg: String, +pool: List<&2, String>, h: List<&2, G.Mon>) -> String:
  match h:
    case Nil{}:
      ""
    case x <> t:
      +s = sm(x)
      G.pick(String, in_pool(s, pool), tg, "BAD:" ++ s) ++ " " ++ pool_tags(tg, pool, t)

def card_row(+c: Nat) -> String:
  Nat.show(c) ++ " " ++ G.c_name(c) ++ " " ++ G.tribe_name(G.c_tribe(c)) ++ " t" ++ Nat.show(G.c_tier(c)) ++ " " ++ sm(G.mon_of(c))
    ++ " g" ++ sb(G.c_guard(c)) ++ " a" ++ Nat.show(G.c_armor(c)) ++ " r" ++ Nat.show(G.c_rally(c)) ++ " i" ++ Nat.show(G.c_income(c))
    ++ " | " ++ G.card_text(G.card(c))

def roster_go(k: Nat, +c: Nat) -> List<&2, String>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      card_row(c) <> roster_go(j, 1n+c)

def PI(+id: Nat, board: List<&2, G.Mon>, +plays: Nat) -> G.Player:
  G.Player{id, 20n, 0n, 3n, 7n, 0n, False{}, 0n, board, [], True{}, 0n, [], plays}

def seat_bn(+p: G.Player) -> String:
  "b=[" ++ sms(G.p_board(p)) ++ "] n=" ++ Nat.show(G.p_plays(p))

def round_board(g: G.Game) -> String:
  seat_bn(G.pget(G.g_players(g), 0n))

def atk_sum(o: G.AtkOut) -> String:
  G.AtkOut{xs, ys, line, ti, ai2, ti2, asb, tsb, ad, td, ral, aatk} = o
  "xs=[" ++ sms(xs) ++ "] ys=[" ++ sms(ys) ++ "] asb=" ++ sb(asb) ++ " tsb=" ++ sb(tsb) ++ " ad=" ++ sb(ad) ++ " td=" ++ sb(td) ++ " ral=" ++ Nat.show(ral) ++ " aatk=" ++ Nat.show(aatk)

def ns_rest(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      "," ++ Nat.show(x) ++ ns_rest(t)

def ral_one(e: G.Ev) -> List<&2, Nat>:
  match e:
    case G.EvAtk{step, side, ti, ai2, ti2, ba, bb, aa, ab, asb, tsb, ad, td, ral, aatk, text}:
      G.pick(List<&2, Nat>, G.nat_eq(ral, 0n), Nil{}, [aatk])
    case G.EvEnd{step, res, dmg, why, aa, ab, text}:
      Nil{}

def ral_atks(es: List<&2, G.Ev>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      List.append(&2, Nat, ral_one(e), ral_atks(t))

def end_of(es: List<&2, G.Ev>) -> String:
  match es:
    case Nil{}:
      "no end"
    case e <> t:
      match e:
        case G.EvAtk{step, side, ti, ai2, ti2, ba, bb, aa, ab, asb, tsb, ad, td, ral, aatk, text}:
          end_of(t)
        case G.EvEnd{step, res, dmg, why, aa, ab, text}:
          "end a=[" ++ sms(aa) ++ "] b=[" ++ sms(ab) ++ "]"

def nums(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      Nat.show(x) ++ ns_rest(t)

def fsum(f: G.Fight) -> String:
  G.Fight{round, a, b, res, dmg, aboard, bboard, log, +events} = f
  "res=" ++ Nat.show(res) ++ " dmg=" ++ Nat.show(dmg) ++ " rally=[" ++ nums(ral_atks(events)) ++ "] " ++ end_of(events)

def two_made(h: List<&2, G.Mon>) -> String:
  match h:
    case Nil{}:
      "none"
    case x <> t:
      match t:
        case Nil{}:
          "one"
        case y <> r:
          +a = sm(x)
          +b = sm(y)
          G.pick(String, in_pool(a, tide2()), "tide2", "BAD:" ++ a) ++ " " ++ G.pick(String, in_pool(b, tide4()), "tide4", "BAD:" ++ b) ++ G.pick(String, G.nat_eq(G.len(G.Mon, r), 0n), "", " extra")

# Zones and atomicity (VAL-V2-BUY / VAL-V2-PLAY)
# ----------------------------------------------

# buy moves shop[0] to the right end of the hand as its base unit, charges 3,
# and fires nothing: Cinder Whelp and Inferno Drake observers stay unbuffed
def t_buy_no_triggers() -> String:
  run([G.Buy{0n}], P(5n, [m(1n, 1n, 2n), m(18n, 5n, 4n)], [0n, 9n, 3n], [m(6n, 1n, 3n)]))

def w_buy_no_triggers() -> String:
  W("+", 2n, 0n, "1:1/2,18:5/4", "6:1/3,0:2/1", "9,3")

law k_buy_no_triggers:
  {t_buy_no_triggers() == w_buy_no_triggers() : String}

def k_buy_no_triggers():
  {==}

# a bought battlecry card is only held: Ember Herald's Play does not fire
def t_buy_battlecry_held() -> String:
  run([G.Buy{1n}], P(3n, [m(0n, 2n, 1n)], [3n, 9n], []))

def w_buy_battlecry_held() -> String:
  W("+", 0n, 0n, "0:2/1", "9:3/3", "3")

law k_buy_battlecry_held:
  {t_buy_battlecry_held() == w_buy_battlecry_held() : String}

def k_buy_battlecry_held():
  {==}

# buying needs no board room: a full board still buys into the hand
def t_buy_full_board() -> String:
  run([G.Buy{0n}], P(3n, fill(5n, m(6n, 1n, 3n)), [4n], []))

# V4 cause (f): five regular Pebble Guards (an unreachable all-board
# triple) assemble at the buy boundary; no hand copy is consumed, so the
# golden (3/9 - 1/3 = 2/6) takes the first consumed board slot
def w_buy_full_board() -> String:
  W("+", 0n, 0n, "6:2/6G,6:1/3,6:1/3", "4:1/2s", "")

# the V3 intent with no triple: a full board still buys into the hand
def t_buy_full_board_mixed() -> String:
  run([G.Buy{0n}], P(3n, [m(6n, 1n, 3n), m(6n, 1n, 3n), m(7n, 1n, 3n), m(7n, 1n, 3n), m(8n, 1n, 2n)], [4n], []))

def w_buy_full_board_mixed() -> String:
  W("+", 0n, 0n, "6:1/3,6:1/3,7:1/3,7:1/3,8:1/2", "4:1/2s", "")

law k_buy_full_board_mixed:
  {t_buy_full_board_mixed() == w_buy_full_board_mixed() : String}

def k_buy_full_board_mixed():
  {==}

law k_buy_full_board:
  {t_buy_full_board() == w_buy_full_board() : String}

def k_buy_full_board():
  {==}

# 2 gold: rejected, nothing charged or moved
def t_buy_poor() -> String:
  run([G.Buy{0n}], P(2n, [], [0n, 3n, 6n], []))

def w_buy_poor() -> String:
  W("x", 2n, 0n, "", "", "0,3,6")

law k_buy_poor:
  {t_buy_poor() == w_buy_poor() : String}

def k_buy_poor():
  {==}

# hand of 7: rejected even with gold
def t_buy_hand_full() -> String:
  run([G.Buy{0n}], P(9n, [], [3n], fill(7n, m(0n, 2n, 1n))))

def w_buy_hand_full() -> String:
  W("x", 9n, 0n, "", "0:2/1,0:2/1,0:2/1,0:2/1,0:2/1,0:2/1,0:2/1", "3")

law k_buy_hand_full:
  {t_buy_hand_full() == w_buy_hand_full() : String}

def k_buy_hand_full():
  {==}

# out-of-range shop index: rejected
def t_buy_bad_index() -> String:
  run([G.Buy{1n}], P(9n, [], [3n], []))

def w_buy_bad_index() -> String:
  W("x", 9n, 0n, "", "", "3")

law k_buy_bad_index:
  {t_buy_bad_index() == w_buy_bad_index() : String}

def k_buy_bad_index():
  {==}

# play: hand[1] leaves the hand, joins the right end of the board, free;
# plays counts up
def t_play_basic() -> String:
  run([G.Play{1n}], P(4n, [m(15n, 2n, 5n)], [], [m(6n, 1n, 3n), m(0n, 2n, 1n)]))

def w_play_basic() -> String:
  W("+", 4n, 1n, "15:2/5,0:2/1", "6:1/3", "")

law k_play_basic:
  {t_play_basic() == w_play_basic() : String}

def k_play_basic():
  {==}

# full board: rejected; the Kindler in hand fires nothing
def t_play_full_board() -> String:
  run([G.Play{0n}], P(1n, fill(5n, m(0n, 2n, 1n)), [], [m(2n, 1n, 2n)]))

def w_play_full_board() -> String:
  W("x", 1n, 0n, "0:2/1,0:2/1,0:2/1,0:2/1,0:2/1", "2:1/2", "")

law k_play_full_board:
  {t_play_full_board() == w_play_full_board() : String}

def k_play_full_board():
  {==}

# bad hand index: rejected
def t_play_bad_index() -> String:
  run([G.Play{1n}], P(1n, [], [], [m(0n, 2n, 1n)]))

def w_play_bad_index() -> String:
  W("x", 1n, 0n, "", "0:2/1", "")

law k_play_bad_index:
  {t_play_bad_index() == w_play_bad_index() : String}

def k_play_bad_index():
  {==}

# sell takes from the board and refunds 1; the hand is untouched.
# V4 cause (a): the hand sale is gone (no constructor), so the second
# V3 action (sellhand:0) is dropped and the hand card stays.
def t_sell_zones() -> String:
  run([G.Sell{0n}], P(0n, [m(6n, 1n, 3n)], [], [m(0n, 2n, 1n)]))

def w_sell_zones() -> String:
  W("+", 1n, 0n, "", "0:2/1", "")

law k_sell_zones:
  {t_sell_zones() == w_sell_zones() : String}

def k_sell_zones():
  {==}

# empty zones reject; a valid sell between them still works
def t_sell_bad_index() -> String:
  run([G.Sell{0n}, G.Sell{0n}, G.Sell{1n}], P(0n, [m(6n, 1n, 3n)], [], []))

def w_sell_bad_index() -> String:
  W("+xx", 1n, 0n, "", "", "")

law k_sell_bad_index:
  {t_sell_bad_index() == w_sell_bad_index() : String}

def k_sell_bad_index():
  {==}

# Ember (VAL-V2-EFFECTS)
# ----------------------

# Kindler: its Play gives other Ember units on the PRIOR board +1 attack (Imp,
# Whelp; the Tide Moth is skipped); Kindler enters unbuffed; then Whelp
# observes another Ember play: +1 attack. The Imp still in hand is untouched.
def t_kindler_whelp() -> String:
  run([G.Play{0n}], P(0n, [m(0n, 2n, 1n), m(3n, 1n, 1n), m(1n, 1n, 2n)], [], [m(2n, 1n, 2n), m(0n, 2n, 1n)]))

def w_kindler_whelp() -> String:
  W("+", 0n, 1n, "0:3/1,3:1/1,1:3/2,2:1/2", "0:2/1", "")

law k_kindler_whelp:
  {t_kindler_whelp() == w_kindler_whelp() : String}

def k_kindler_whelp():
  {==}

# Cinder Whelp never observes its own play; the second Whelp's play buffs
# only the first Whelp
def t_whelp_self_excluded() -> String:
  run([G.Play{0n}, G.Play{0n}], P(0n, [], [], [m(1n, 1n, 2n), m(1n, 1n, 2n)]))

def w_whelp_self_excluded() -> String:
  W("++", 0n, 2n, "1:2/2,1:1/2", "", "")

law k_whelp_self_excluded:
  {t_whelp_self_excluded() == w_whelp_self_excluded() : String}

def k_whelp_self_excluded():
  {==}

# Whelp ignores a Tide play
def t_whelp_other_tribe() -> String:
  run([G.Play{0n}], P(0n, [m(1n, 1n, 2n)], [], [m(3n, 1n, 1n)]))

def w_whelp_other_tribe() -> String:
  W("+", 0n, 1n, "1:1/2,3:1/1", "", "")

law k_whelp_other_tribe:
  {t_whelp_other_tribe() == w_whelp_other_tribe() : String}

def k_whelp_other_tribe():
  {==}

# Flame Dancer gains +2/+1 when another Ember card is played
def t_dancer() -> String:
  run([G.Play{0n}], P(0n, [m(10n, 2n, 3n)], [], [m(0n, 2n, 1n)]))

def w_dancer() -> String:
  W("+", 0n, 1n, "10:4/4,0:2/1", "", "")

law k_dancer:
  {t_dancer() == w_dancer() : String}

def k_dancer():
  {==}

# Inferno Drake observer: other Ember allies +1/+1, INCLUDING the unit
# that just entered; the Drake itself is unchanged
def t_drake_includes_entering() -> String:
  run([G.Play{0n}], P(0n, [m(18n, 5n, 4n), m(0n, 2n, 1n)], [], [m(0n, 2n, 1n)]))

def w_drake_includes_entering() -> String:
  W("+", 0n, 1n, "18:5/4,0:3/2,0:3/2", "", "")

law k_drake_includes_entering:
  {t_drake_includes_entering() == w_drake_includes_entering() : String}

def k_drake_includes_entering():
  {==}

# playing the Drake itself: it does not observe its own play; Whelp does
def t_drake_played() -> String:
  run([G.Play{0n}], P(0n, [m(1n, 1n, 2n)], [], [m(18n, 5n, 4n)]))

def w_drake_played() -> String:
  W("+", 0n, 1n, "1:2/2,18:5/4", "", "")

law k_drake_played:
  {t_drake_played() == w_drake_played() : String}

def k_drake_played():
  {==}

# Ember Herald: other Ember allies on the prior board +2/+1; Tide untouched
def t_herald() -> String:
  run([G.Play{0n}], P(0n, [m(0n, 2n, 1n), ms(12n, 2n, 3n)], [], [m(9n, 3n, 2n)]))

def w_herald() -> String:
  W("+", 0n, 1n, "0:4/2,12:2/3s,9:3/2", "", "")

law k_herald:
  {t_herald() == w_herald() : String}

def k_herald():
  {==}

# order: Herald's Play +2/+1 (Drake 7/5, Dancer 4/4), Herald enters 3/2,
# then observers left to right: Drake gives Dancer and Herald +1/+1 (5/5,
# 4/3), Dancer gains +2/+1 (7/6)
def t_herald_drake_dancer() -> String:
  run([G.Play{0n}], P(0n, [m(18n, 5n, 4n), m(10n, 2n, 3n)], [], [m(9n, 3n, 2n)]))

def w_herald_drake_dancer() -> String:
  W("+", 0n, 1n, "18:7/5,10:7/6,9:4/3", "", "")

law k_herald_drake_dancer:
  {t_herald_drake_dancer() == w_herald_drake_dancer() : String}

def k_herald_drake_dancer():
  {==}

# Duplicates: KIN excludes the source by board position, not by card id
# ---------------------------------------------------------------------

# a second Kindler buffs the Kindler already on the board (same id, other unit)
def t_kindler_dup() -> String:
  run([G.Play{0n}], P(0n, [m(2n, 1n, 2n)], [], [m(2n, 1n, 2n)]))

def w_kindler_dup() -> String:
  W("+", 0n, 1n, "2:2/2,2:1/2", "", "")

law k_kindler_dup:
  {t_kindler_dup() == w_kindler_dup() : String}

def k_kindler_dup():
  {==}

# two Drakes observe one Ember play: each buffs the other Drake and the
# entering Imp +1/+1 (+2/+2 in total); neither buffs itself; no snapshot
# overwrite
def t_drake_pair() -> String:
  run([G.Play{0n}], P(0n, [m(18n, 5n, 4n), m(18n, 5n, 4n)], [], [m(0n, 2n, 1n)]))

def w_drake_pair() -> String:
  W("+", 0n, 1n, "18:6/5,18:6/5,0:4/3", "", "")

law k_drake_pair:
  {t_drake_pair() == w_drake_pair() : String}

def k_drake_pair():
  {==}

# Herald buffs every other Ember unit on the prior board, duplicates included
def t_herald_two_imps() -> String:
  run([G.Play{0n}], P(0n, [m(0n, 2n, 1n), m(0n, 2n, 1n)], [], [m(9n, 3n, 2n)]))

def w_herald_two_imps() -> String:
  W("+", 0n, 1n, "0:4/2,0:4/2,9:3/2", "", "")

law k_herald_two_imps:
  {t_herald_two_imps() == w_herald_two_imps() : String}

def k_herald_two_imps():
  {==}

# two Whelps on board: each gains +1 attack once from one Ember play
def t_whelp_pair() -> String:
  run([G.Play{0n}], P(0n, [m(1n, 1n, 2n), m(1n, 1n, 2n)], [], [m(0n, 2n, 1n)]))

def w_whelp_pair() -> String:
  W("+", 0n, 1n, "1:2/2,1:2/2,0:2/1", "", "")

law k_whelp_pair:
  {t_whelp_pair() == w_whelp_pair() : String}

def k_whelp_pair():
  {==}

# Tide
# ----

# Reef Warden: other Tide allies +1/+2 (shield kept); Ember untouched; the
# Warden enters with its own Shield
def t_reef_warden() -> String:
  run([G.Play{0n}], P(0n, [m(3n, 1n, 1n), ms(4n, 1n, 2n), m(0n, 2n, 1n)], [], [ms(12n, 2n, 3n)]))

def w_reef_warden() -> String:
  W("+", 0n, 1n, "3:2/3,4:2/4s,0:2/1,12:2/3s", "", "")

law k_reef_warden:
  {t_reef_warden() == w_reef_warden() : String}

def k_reef_warden():
  {==}

# Tidecaller counts the hand AFTER it leaves: 2 cards -> +2/+2
def t_tidecaller_two() -> String:
  run([G.Play{0n}], P(0n, [], [], [m(13n, 2n, 3n), m(0n, 2n, 1n), m(6n, 1n, 3n)]))

def w_tidecaller_two() -> String:
  W("+", 0n, 1n, "13:4/5", "0:2/1,6:1/3", "")

law k_tidecaller_two:
  {t_tidecaller_two() == w_tidecaller_two() : String}

def k_tidecaller_two():
  {==}

# 6 cards left, capped at 4 -> +4/+4
def t_tidecaller_cap() -> String:
  run([G.Play{0n}], P(0n, [], [], m(13n, 2n, 3n) <> fill(6n, m(6n, 1n, 3n))))

# V4 cause (f): the six regular Pebble Guards in hand assemble after the
# play (normalization runs after the ability, so the count still saw 6):
# hand 0..2 -> golden at the right end, then the next three -> 2 goldens.
def w_tidecaller_cap() -> String:
  W("+", 0n, 1n, "13:6/7", "6:2/6G,6:2/6G", "")

law k_tidecaller_cap:
  {t_tidecaller_cap() == w_tidecaller_cap() : String}

def k_tidecaller_cap():
  {==}

# alone in hand -> 0 cards left -> no gain
def t_tidecaller_alone() -> String:
  run([G.Play{0n}], P(0n, [], [], [m(13n, 2n, 3n)]))

def w_tidecaller_alone() -> String:
  W("+", 0n, 1n, "13:2/3", "", "")

law k_tidecaller_alone:
  {t_tidecaller_alone() == w_tidecaller_alone() : String}

def k_tidecaller_alone():
  {==}

# Storm Siren from the middle of a 3-card hand: 2 left -> other Tide allies
# +2/+2; the Siren itself and Ember untouched
def t_siren_two() -> String:
  run([G.Play{1n}], P(0n, [m(3n, 1n, 1n), m(0n, 2n, 1n)], [], [m(0n, 2n, 1n), ms(20n, 4n, 4n), m(6n, 1n, 3n)]))

def w_siren_two() -> String:
  W("+", 0n, 1n, "3:3/3,0:2/1,20:4/4s", "0:2/1,6:1/3", "")

law k_siren_two:
  {t_siren_two() == w_siren_two() : String}

def k_siren_two():
  {==}

# 6 left, capped at 4 -> Tide Pup +4/+4
def t_siren_cap() -> String:
  run([G.Play{0n}], P(0n, [ms(4n, 1n, 2n)], [], ms(20n, 4n, 4n) <> fill(6n, m(6n, 1n, 3n))))

# V4 cause (f): the six regular Pebble Guards in hand assemble after the
# play (normalization runs after the ability, so the count still saw 6):
# hand 0..2 -> golden at the right end, then the next three -> 2 goldens.
def w_siren_cap() -> String:
  W("+", 0n, 1n, "4:5/6s,20:4/4s", "6:2/6G,6:2/6G", "")

law k_siren_cap:
  {t_siren_cap() == w_siren_cap() : String}

def k_siren_cap():
  {==}

# Coin Eel: Play gives 1 gold; Sell gives refund 1 + Sell 1
def t_eel_play_sell() -> String:
  run([G.Play{0n}, G.Sell{0n}], P(0n, [], [], [m(14n, 2n, 2n)]))

def w_eel_play_sell() -> String:
  W("++", 3n, 1n, "", "", "")

law k_eel_play_sell:
  {t_eel_play_sell() == w_eel_play_sell() : String}

def k_eel_play_sell():
  {==}

# V4 cause (a): `sellhand:i` is not a move any more; the parser rejects it
# (no state change happens: the replay records bad_move)
def t_sellhand_parse() -> String:
  String.join([act_or_none(G.parse_move("sellhand:0")), act_or_none(G.parse_move("sellhand:6")), act_or_none(G.parse_move("sellhand")), act_or_none(G.parse_move("sell:0"))], ",")

def w_sellhand_parse() -> String:
  "none,none,none,sell:0"

law k_sellhand_parse:
  {t_sellhand_parse() == w_sellhand_parse() : String}

def k_sellhand_parse():
  {==}

# V4 golden Coin Eel (cause f): Sell gold doubles (2), the refund stays 1
def t_eel_golden_sell() -> String:
  run([G.Sell{0n}], P(0n, [mg(14n, 6n, 6n)], [], []))

def w_eel_golden_sell() -> String:
  W("+", 3n, 0n, "", "", "")

law k_eel_golden_sell:
  {t_eel_golden_sell() == w_eel_golden_sell() : String}

def k_eel_golden_sell():
  {==}

# Tide Pup: Sell 1 + refund 1 = 2 once; a repeated sell:0 on the now empty
# board is rejected and pays nothing
def t_pup_sell_twice() -> String:
  run([G.Sell{0n}, G.Sell{0n}], P(0n, [ms(4n, 1n, 2n)], [], []))

def w_pup_sell_twice() -> String:
  W("+x", 2n, 0n, "", "", "")

law k_pup_sell_twice:
  {t_pup_sell_twice() == w_pup_sell_twice() : String}

def k_pup_sell_twice():
  {==}

# V4 golden Tide Pup (cause f): Sell 2 + refund 1 = 3; Shield kept
def t_pup_golden_sell() -> String:
  run([G.Sell{0n}], P(0n, [mgs(4n, 2n, 4n)], [], []))

def w_pup_golden_sell() -> String:
  W("+", 3n, 0n, "", "", "")

law k_pup_golden_sell:
  {t_pup_golden_sell() == w_pup_golden_sell() : String}

def k_pup_golden_sell():
  {==}


# Tier 4-5 observers
# ------------------

# Pyre Captain: other Ember allies +1/+1 for each card played earlier this
# turn (2 earlier plays here: +2/+2), entering unit included
def t_captain_includes_entering() -> String:
  run([G.Play{0n}], PP(0n, [m(24n, 4n, 4n), m(0n, 2n, 1n)], [], [m(0n, 2n, 1n)], 2n))

def w_captain_includes_entering() -> String:
  W("+", 0n, 3n, "24:4/4,0:4/3,0:4/3", "", "")

law k_captain_includes_entering:
  {t_captain_includes_entering() == w_captain_includes_entering() : String}

def k_captain_includes_entering():
  {==}


# the FIRST play of a turn: Pyre Captain counts 0 earlier plays, so it adds
# +0/+0 (the resolving play is not counted)
def t_captain_first_play() -> String:
  run([G.Play{0n}], P(0n, [m(24n, 4n, 4n), m(0n, 2n, 1n)], [], [m(0n, 2n, 1n)]))

def w_captain_first_play() -> String:
  W("+", 0n, 1n, "24:4/4,0:2/1,0:2/1", "", "")

law k_captain_first_play:
  {t_captain_first_play() == w_captain_first_play() : String}

def k_captain_first_play():
  {==}

# 1 earlier play; observers left to right: Tyrant gives Captain and Whelp
# +2/+1 x1 (6/5, 3/3), then Captain gives Tyrant and Whelp +1/+1 x1 (7/6,
# 4/4); the entering Whelp does not observe
def t_tyrant_captain() -> String:
  run([G.Play{0n}], PP(0n, [m(30n, 6n, 5n), m(24n, 4n, 4n)], [], [m(1n, 1n, 2n)], 1n))

def w_tyrant_captain() -> String:
  W("+", 0n, 2n, "30:7/6,24:6/5,1:4/4", "", "")

# the same with 3 earlier plays (compounding chain): Tyrant gives +6/+3
# (Captain 10/7, Whelp 7/5), then Captain gives +3/+3 (Tyrant 9/8, Whelp 10/8)
def t_tyrant_captain_chain() -> String:
  run([G.Play{0n}], PP(0n, [m(30n, 6n, 5n), m(24n, 4n, 4n)], [], [m(1n, 1n, 2n)], 3n))

def w_tyrant_captain_chain() -> String:
  W("+", 0n, 4n, "30:9/8,24:10/7,1:10/8", "", "")

law k_tyrant_captain_chain:
  {t_tyrant_captain_chain() == w_tyrant_captain_chain() : String}

def k_tyrant_captain_chain():
  {==}

law k_tyrant_captain:
  {t_tyrant_captain() == w_tyrant_captain() : String}

def k_tyrant_captain():
  {==}

# Sunfire Tyrant played onto an empty board: no self trigger
def t_tyrant_played() -> String:
  run([G.Play{0n}], P(0n, [], [], [m(30n, 6n, 5n)]))

def w_tyrant_played() -> String:
  W("+", 0n, 1n, "30:6/5", "", "")

law k_tyrant_played:
  {t_tyrant_played() == w_tyrant_played() : String}

def k_tyrant_played():
  {==}

# Cards without Play/observer abilities change nothing when played
# ----------------------------------------------------------------

# tier 1
def t_static_t1() -> String:
  run([G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}], P(0n, [], [], [m(0n, 2n, 1n), m(3n, 1n, 1n), m(6n, 1n, 3n), m(7n, 1n, 3n), m(8n, 1n, 2n)]))

def w_static_t1() -> String:
  W("+++++", 0n, 5n, "0:2/1,3:1/1,6:1/3,7:1/3,8:1/2", "", "")

law k_static_t1:
  {t_static_t1() == w_static_t1() : String}

def k_static_t1():
  {==}

# tier 2
def t_static_t2() -> String:
  run([G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}], P(0n, [], [], [m(11n, 3n, 3n), m(15n, 2n, 5n), m(16n, 2n, 4n), m(17n, 2n, 3n), ms(19n, 4n, 2n)]))

def w_static_t2() -> String:
  W("+++++", 0n, 5n, "11:3/3,15:2/5,16:2/4,17:2/3,19:4/2s", "", "")

law k_static_t2:
  {t_static_t2() == w_static_t2() : String}

def k_static_t2():
  {==}

# tier 3
def t_static_t3() -> String:
  run([G.Play{0n}, G.Play{0n}, G.Play{0n}], P(0n, [], [], [m(21n, 3n, 5n), m(22n, 3n, 8n), m(23n, 3n, 6n)]))

def w_static_t3() -> String:
  W("+++", 0n, 3n, "21:3/5,22:3/8,23:3/6", "", "")

law k_static_t3:
  {t_static_t3() == w_static_t3() : String}

def k_static_t3():
  {==}

# tier 4-5 (Captain played last with no other Ember observer present)
def t_static_t45() -> String:
  run([G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}], P(0n, [], [], [m(26n, 3n, 4n), ms(31n, 5n, 5n), m(33n, 4n, 8n), m(35n, 7n, 9n), m(24n, 4n, 4n)]))

def w_static_t45() -> String:
  W("+++++", 0n, 5n, "26:3/4,31:5/5s,33:4/8,35:7/9,24:4/4", "", "")

law k_static_t45:
  {t_static_t45() == w_static_t45() : String}

def k_static_t45():
  {==}

# more tier 4-5
def t_static_t45b() -> String:
  run([G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}, G.Play{0n}], P(0n, [], [], [m(27n, 3n, 6n), m(28n, 3n, 7n), m(29n, 3n, 6n), ms(32n, 5n, 7n), m(34n, 4n, 10n)]))

def w_static_t45b() -> String:
  W("+++++", 0n, 5n, "27:3/6,28:3/7,29:3/6,32:5/7s,34:4/10", "", "")

law k_static_t45b:
  {t_static_t45b() == w_static_t45b() : String}

def k_static_t45b():
  {==}

# End of turn (G.grow_player): ENDTURN abilities, board left to right
# -------------------------------------------------------------------

# Sprout +1 health; Rootwarden gives the other Stones +2 health; Mountain
# Heart gives the other Stones +1/+1; the Ember Imp is untouched
def t_endturn_stone() -> String:
  zones(endturn([m(8n, 1n, 2n), m(17n, 2n, 3n), m(0n, 2n, 1n), m(23n, 3n, 6n), m(6n, 1n, 3n)], []))

def w_endturn_stone() -> String:
  "b=[8:2/6,17:3/4,0:2/1,23:3/8,6:2/6] h=[]"

law k_endturn_stone:
  {t_endturn_stone() == w_endturn_stone() : String}

def k_endturn_stone():
  {==}

# Granite Titan gains +1/+2 itself only
def t_endturn_titan() -> String:
  zones(endturn([m(22n, 3n, 8n), m(7n, 1n, 3n)], []))

def w_endturn_titan() -> String:
  "b=[22:4/10,7:1/3] h=[]"

law k_endturn_titan:
  {t_endturn_titan() == w_endturn_titan() : String}

def k_endturn_titan():
  {==}

# two Rootwardens each give the other +2 health
def t_endturn_rootwarden_pair() -> String:
  zones(endturn([m(17n, 2n, 3n), m(17n, 2n, 3n)], []))

def w_endturn_rootwarden_pair() -> String:
  "b=[17:2/5,17:2/5] h=[]"

law k_endturn_rootwarden_pair:
  {t_endturn_rootwarden_pair() == w_endturn_rootwarden_pair() : String}

def k_endturn_rootwarden_pair():
  {==}

# two Mountain Hearts each give the other +1/+1
def t_endturn_heart_pair() -> String:
  zones(endturn([m(23n, 3n, 6n), m(23n, 3n, 6n)], []))

def w_endturn_heart_pair() -> String:
  "b=[23:4/7,23:4/7] h=[]"

law k_endturn_heart_pair:
  {t_endturn_heart_pair() == w_endturn_heart_pair() : String}

def k_endturn_heart_pair():
  {==}

# units without ENDTURN abilities, and the hand, are untouched
def t_endturn_no_growth() -> String:
  zones(endturn([m(0n, 2n, 1n), ms(4n, 1n, 2n), m(15n, 2n, 5n)], [m(8n, 1n, 2n)]))

def w_endturn_no_growth() -> String:
  "b=[0:2/1,4:1/2s,15:2/5] h=[8:1/2]"

law k_endturn_no_growth:
  {t_endturn_no_growth() == w_endturn_no_growth() : String}

def k_endturn_no_growth():
  {==}

# Abyss Choir: +2/+2 per hand card at end of turn, 2 cards
def t_choir_hand() -> String:
  zones(endturn([m(27n, 3n, 6n)], [m(0n, 2n, 1n), m(6n, 1n, 3n)]))

def w_choir_hand() -> String:
  "b=[27:7/10] h=[0:2/1,6:1/3]"

law k_choir_hand:
  {t_choir_hand() == w_choir_hand() : String}

def k_choir_hand():
  {==}

# Abyss Choir with 6 hand cards: capped at 4 cards, +8/+8
def t_choir_cap() -> String:
  zones(endturn([m(27n, 3n, 6n)], fill(6n, m(6n, 1n, 3n))))

def w_choir_cap() -> String:
  "b=[27:11/14] h=[6:1/3,6:1/3,6:1/3,6:1/3,6:1/3,6:1/3]"

law k_choir_cap:
  {t_choir_cap() == w_choir_cap() : String}

def k_choir_cap():
  {==}

# Basalt Bastion: +1/+3 itself
def t_bastion() -> String:
  zones(endturn([m(28n, 3n, 7n), m(6n, 1n, 3n)], []))

def w_bastion() -> String:
  "b=[28:4/10,6:1/3] h=[]"

law k_bastion:
  {t_bastion() == w_bastion() : String}

def k_bastion():
  {==}

# two Quarry Drummers: each gives the other Stones +2/+1 (Ember skipped)
def t_drummer_pair() -> String:
  zones(endturn([m(29n, 3n, 6n), m(6n, 1n, 3n), m(0n, 2n, 1n), m(29n, 3n, 6n)], []))

def w_drummer_pair() -> String:
  "b=[29:5/7,6:5/5,0:2/1,29:5/7] h=[]"

law k_drummer_pair:
  {t_drummer_pair() == w_drummer_pair() : String}

def k_drummer_pair():
  {==}

# Cinder Queen after 3 plays: other Ember allies +6/+6; Stone untouched
def t_queen_plays3() -> String:
  zones(endturn_p([ms(31n, 5n, 5n), m(0n, 2n, 1n), m(6n, 1n, 3n)], [], 3n))

def w_queen_plays3() -> String:
  "b=[31:5/5s,0:8/7,6:1/3] h=[]"

law k_queen_plays3:
  {t_queen_plays3() == w_queen_plays3() : String}

def k_queen_plays3():
  {==}

# Cinder Queen after 6 plays: capped at 4 plays, +8/+8
def t_queen_cap() -> String:
  zones(endturn_p([ms(31n, 5n, 5n), m(0n, 2n, 1n)], [], 6n))

def w_queen_cap() -> String:
  "b=[31:5/5s,0:10/9] h=[]"

law k_queen_cap:
  {t_queen_cap() == w_queen_cap() : String}

def k_queen_cap():
  {==}

# Cinder Queen after no plays: nothing
def t_queen_zero() -> String:
  zones(endturn_p([ms(31n, 5n, 5n), m(0n, 2n, 1n)], [], 0n))

def w_queen_zero() -> String:
  "b=[31:5/5s,0:2/1] h=[]"

law k_queen_zero:
  {t_queen_zero() == w_queen_zero() : String}

def k_queen_zero():
  {==}

# plays counts successful plays of any tribe (Stone, Tide); the rejected
# play:5 does not count; end of turn then gives the Imp +4/+4 (2 plays)
def t_queen_any_tribe() -> String:
  zones(G.grow_player(seed(), 3n, after([G.Play{0n}, G.Play{5n}, G.Play{0n}], P(0n, [ms(31n, 5n, 5n), m(0n, 2n, 1n)], [], [m(6n, 1n, 3n), m(3n, 1n, 1n)]))))

def w_queen_any_tribe() -> String:
  "b=[31:5/5s,0:6/5,6:1/3,3:1/1] h=[]"

law k_queen_any_tribe:
  {t_queen_any_tribe() == w_queen_any_tribe() : String}

def k_queen_any_tribe():
  {==}

# Maelstrom Queen with 3 hand cards: other Tide allies +6/+6
def t_maelstrom() -> String:
  zones(endturn([ms(32n, 5n, 7n), m(3n, 1n, 1n), m(6n, 1n, 3n)], [m(0n, 2n, 1n), m(0n, 2n, 1n), m(0n, 2n, 1n)]))

def w_maelstrom() -> String:
  "b=[32:5/7s,3:7/7,6:1/3] h=[0:2/1,0:2/1,0:2/1]"

law k_maelstrom:
  {t_maelstrom() == w_maelstrom() : String}

def k_maelstrom():
  {==}

# two Worldroots each give the other Stones +2/+4
def t_worldroot_pair() -> String:
  zones(endturn([m(34n, 4n, 10n), m(6n, 1n, 3n), m(34n, 4n, 10n)], []))

def w_worldroot_pair() -> String:
  "b=[34:6/14,6:5/11,34:6/14] h=[]"

law k_worldroot_pair:
  {t_worldroot_pair() == w_worldroot_pair() : String}

def k_worldroot_pair():
  {==}

# Avalanche Lord: other Stone allies +3/+1
def t_avalanche() -> String:
  zones(endturn([m(35n, 7n, 9n), m(6n, 1n, 3n), m(0n, 2n, 1n)], []))

def w_avalanche() -> String:
  "b=[35:7/9,6:4/4,0:2/1] h=[]"

law k_avalanche:
  {t_avalanche() == w_avalanche() : String}

def k_avalanche():
  {==}

# Income keywords: Moth 1 + Broker 1 + Sovereign 2 + Oracle 1 = 5; Imp 0
def t_board_income() -> String:
  "income=" ++ Nat.show(G.board_income([m(3n, 1n, 1n), m(26n, 3n, 4n), m(33n, 4n, 8n), m(21n, 3n, 5n), m(0n, 2n, 1n)]))

def w_board_income() -> String:
  "income=5"

law k_board_income:
  {t_board_income() == w_board_income() : String}

def k_board_income():
  {==}

# Roster: name, tribe, tier, base unit, keywords and generated text of all 36 cards
# ---------------------------------------------------------------------------------

# card ids 0..11 against the hand-written expected rows below
def t_roster_0_11() -> String:
  String.join(roster_go(12n, 0n), "; ")

def w_roster_0_11() -> String:
  String.join(
    [ "0 Spark Imp Ember t1 0:2/1 gF a0 r1 i0 | Rally 1."
    , "1 Cinder Whelp Ember t1 1:1/2 gF a0 r0 i0 | After you play another Ember card: gain +1 attack."
    , "2 Kindler Ember t1 2:1/2 gF a0 r0 i0 | Play: give other Ember allies +1 attack."
    , "3 Purse Moth Tide t1 3:1/1 gF a0 r0 i1 | Income 1."
    , "4 Tide Pup Tide t1 4:1/2s gF a0 r0 i0 | Shield. Sell: gain 1 gold."
    , "5 Shell Scout Tide t1 5:1/1 gF a0 r0 i0 | Play: add a random Tide card of tier 1 or lower to your hand (if it has room)."
    , "6 Pebble Guard Stone t1 6:1/3 gT a0 r0 i0 | Guard."
    , "7 Moss Turtle Stone t1 7:1/3 gF a1 r0 i0 | Armor 1."
    , "8 Root Sprout Stone t1 8:1/2 gF a0 r0 i0 | End of turn: gain +1 health."
    , "9 Ember Herald Ember t2 9:3/3 gF a0 r0 i0 | Play: give other Ember allies +2/+1."
    , "10 Flame Dancer Ember t2 10:3/4 gF a0 r0 i0 | After you play another Ember card: gain +2/+1."
    , "11 Blaze Charger Ember t2 11:4/4 gF a0 r2 i0 | Rally 2."
    ], "; ")

law k_roster_0_11:
  {t_roster_0_11() == w_roster_0_11() : String}

def k_roster_0_11():
  {==}

# card ids 12..23 against the hand-written expected rows below
def t_roster_12_23() -> String:
  String.join(roster_go(12n, 12n), "; ")

def w_roster_12_23() -> String:
  String.join(
    [ "12 Reef Warden Tide t2 12:3/3s gF a0 r0 i0 | Shield. Play: give other Tide allies +1/+2."
    , "13 Tidecaller Tide t2 13:3/3 gF a0 r0 i0 | Play: gain +1/+1 for each card in your hand (max 4)."
    , "14 Coin Eel Tide t2 14:3/3 gF a0 r0 i0 | Play: gain 1 gold. Sell: gain 1 gold."
    , "15 Boulder Ox Stone t2 15:3/5 gT a0 r0 i0 | Guard."
    , "16 Cairn Mason Stone t2 16:2/5 gT a1 r0 i0 | Guard. Armor 1."
    , "17 Rootwarden Stone t2 17:3/3 gF a0 r0 i0 | End of turn: give other Stone allies +2 health."
    , "18 Inferno Drake Ember t3 18:6/6 gF a0 r0 i0 | After you play another Ember card: give other Ember allies +1/+1."
    , "19 Ash Phoenix Ember t3 19:8/6s gF a0 r3 i0 | Shield. Rally 3."
    , "20 Storm Siren Tide t3 20:5/7s gF a0 r0 i0 | Shield. Play: give other Tide allies +1/+1 for each card in your hand (max 4)."
    , "21 Tide Oracle Tide t3 21:4/8 gF a0 r0 i1 | Income 1. End of turn: add a random Tide card of tier 2 or lower to your hand (if it has room)."
    , "22 Granite Titan Stone t3 22:5/11 gT a1 r0 i0 | Guard. Armor 1. End of turn: gain +1/+2."
    , "23 Mountain Heart Stone t3 23:5/8 gF a0 r0 i0 | End of turn: give other Stone allies +1/+1."
    ], "; ")

law k_roster_12_23:
  {t_roster_12_23() == w_roster_12_23() : String}

def k_roster_12_23():
  {==}

# card ids 24..35 against the hand-written expected rows below
def t_roster_24_35() -> String:
  String.join(roster_go(12n, 24n), "; ")

def w_roster_24_35() -> String:
  String.join(
    [ "24 Pyre Captain Ember t4 24:10/12 gF a0 r0 i0 | After you play another Ember card: give other Ember allies +1/+1 for each card you played earlier this turn (max 4)."
    , "25 Kiln Matron Ember t4 25:12/10 gF a0 r0 i0 | Play: add a random Ember card of tier 3 or lower to your hand (if it has room). Play: gain +2/+1 for each card you played earlier this turn (max 4)."
    , "26 Pearl Broker Tide t4 26:10/12 gF a0 r0 i1 | Income 1. Sell: add a random Tide card of tier 4 or lower to your hand (if it has room)."
    , "27 Abyss Choir Tide t4 27:10/14 gF a0 r0 i0 | End of turn: gain +2/+2 for each card in your hand (max 4)."
    , "28 Basalt Bastion Stone t4 28:8/18 gT a2 r0 i0 | Guard. Armor 2. End of turn: gain +1/+3."
    , "29 Quarry Drummer Stone t4 29:12/12 gF a0 r0 i0 | End of turn: give other Stone allies +2/+1."
    , "30 Sunfire Tyrant Ember t5 30:20/16 gF a0 r3 i0 | Rally 3. After you play another Ember card: give other Ember allies +2/+1 for each card you played earlier this turn (max 4)."
    , "31 Cinder Queen Ember t5 31:18/18s gF a0 r0 i0 | Shield. End of turn: give other Ember allies +2/+2 for each card you played this turn (max 4)."
    , "32 Maelstrom Queen Tide t5 32:16/22s gF a0 r0 i0 | Shield. End of turn: give other Tide allies +2/+2 for each card in your hand (max 4)."
    , "33 Tidal Sovereign Tide t5 33:16/24 gF a0 r0 i2 | Income 2. End of turn: add a random Tide card of tier 4 or lower to your hand (if it has room). End of turn: gain +2/+2 for each card in your hand (max 4)."
    , "34 Worldroot Stone t5 34:14/30 gT a2 r0 i0 | Guard. Armor 2. End of turn: give other Stone allies +2/+4."
    , "35 Avalanche Lord Stone t5 35:26/22 gF a1 r0 i0 | Armor 1. End of turn: give other Stone allies +3/+1."
    ], "; ")

law k_roster_24_35:
  {t_roster_24_35() == w_roster_24_35() : String}

def k_roster_24_35():
  {==}

# the roster has exactly 44 cards (V4 cause e: 8 Neutral ids 36..43)
def t_card_count() -> String:
  "count=" ++ Nat.show(G.card_count())

def w_card_count() -> String:
  "count=44"

law k_card_count:
  {t_card_count() == w_card_count() : String}

def k_card_count():
  {==}

# MAKE (hash-based; runtime only, membership in the hand-written pool, never a fixed id)
# --------------------------------------------------------------------------------------

# Shell Scout: enters 1/1, then one base Tide tier-1 card joins the hand
def t_scout_make() -> String:
  +p = after([G.Play{0n}], P(0n, [], [], [m(5n, 1n, 1n)]))
  sms(G.p_board(p)) ++ " hand=" ++ pool_tags("tide1", tide1(), G.p_hand(p)) ++ "n=" ++ Nat.show(G.p_plays(p))

def w_scout_make() -> String:
  "5:1/1 hand=tide1 n=1"

# Shell Scout from a full hand of 7: it leaves first, so MAKE refills to 7
def t_scout_full_hand() -> String:
  +p = after([G.Play{0n}], P(0n, [], [], m(5n, 1n, 1n) <> fill(6n, m(6n, 1n, 3n))))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

# V4 cause (f): the six Pebble Guards assemble after the play -> 2 goldens
# + the made card = 3 (the made card is tier-1 Tide, never a Pebble Guard)
def w_scout_full_hand() -> String:
  "5:1/1 handlen=3"

# the V3 intent with no triple: MAKE refills the hand to 7
def t_scout_full_hand_mixed() -> String:
  +p = after([G.Play{0n}], P(0n, [], [], [m(5n, 1n, 1n), m(6n, 1n, 3n), m(6n, 1n, 3n), m(7n, 1n, 3n), m(7n, 1n, 3n), m(8n, 1n, 2n), m(8n, 1n, 2n)]))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def w_scout_full_hand_mixed() -> String:
  "5:1/1 handlen=7"

# two Scouts played in a row: each makes exactly one tide1 card
def t_scout_twice() -> String:
  +p = after([G.Play{0n}, G.Play{0n}], P(0n, [], [], [m(5n, 1n, 1n), m(5n, 1n, 1n)]))
  sms(G.p_board(p)) ++ " hand=" ++ pool_tags("tide1", tide1(), G.p_hand(p))

# V4 cause (f): with seed 7 the first Scout's MAKE draws a third Shell
# Scout (board 1 + hand 2 regular copies) -> golden Scout 2/2 to the hand
# (hand copies first); the second play plays that golden Scout, whose
# MAKE fires twice: board one golden Scout, hand two tier-1 Tide cards.
# Hash-dependent (seed 7), runtime only.
def w_scout_twice() -> String:
  "5:2/2G hand=tide1 tide1 "

# Kiln Matron, first play of the turn: its +2/+1 per earlier play adds 0;
# Whelp observes the Ember play (+1 attack); one base Ember card of
# tier <= 3 joins the hand and is NOT played (no further trigger)
def t_matron_make() -> String:
  +p = after([G.Play{0n}], P(0n, [m(1n, 1n, 2n)], [], [m(25n, 4n, 3n)]))
  sms(G.p_board(p)) ++ " hand=" ++ pool_tags("ember3", ember3(), G.p_hand(p)) ++ "n=" ++ Nat.show(G.p_plays(p))

def w_matron_make() -> String:
  "1:2/2,25:4/3 hand=ember3 n=1"

# Kiln Matron after 2 earlier plays: MAKE first (one base Ember card of
# tier <= 3), then +2/+1 x2 -> 8/5; Whelp observes (+1 attack)
def t_matron_plays() -> String:
  +p = after([G.Play{0n}], PP(0n, [m(1n, 1n, 2n)], [], [m(25n, 4n, 3n)], 2n))
  sms(G.p_board(p)) ++ " hand=" ++ pool_tags("ember3", ember3(), G.p_hand(p)) ++ "n=" ++ Nat.show(G.p_plays(p))

def w_matron_plays() -> String:
  "1:2/2,25:8/5 hand=ember3 n=3"

# Pearl Broker sold from the board: refund 1, then one base Tide card of
# tier <= 4 joins the hand
def t_broker_sell_make() -> String:
  +p = after([G.Sell{0n}], P(0n, [m(26n, 3n, 4n)], [], []))
  "g=" ++ Nat.show(G.p_gold(p)) ++ " b=[" ++ sms(G.p_board(p)) ++ "] hand=" ++ pool_tags("tide4", tide4(), G.p_hand(p))

def w_broker_sell_make() -> String:
  "g=1 b=[] hand=tide4 "

# Pearl Broker sold with a full hand: refund only, hand unchanged
def t_broker_sell_full_hand() -> String:
  run([G.Sell{0n}], P(0n, [m(26n, 3n, 4n)], [], fill(7n, m(6n, 1n, 3n))))

# V4 cause (f): MAKE is refused (hand full), then the seven regular Pebble
# Guards assemble at the sell boundary: 7 -> [6, 6G, 6G]
def w_broker_sell_full_hand() -> String:
  W("+", 1n, 0n, "", "6:1/3,6:2/6G,6:2/6G", "")

# the V3 intent with no triple: refund only, hand unchanged
def t_broker_sell_full_hand_mixed() -> String:
  run([G.Sell{0n}], P(0n, [m(26n, 3n, 4n)], [], [m(6n, 1n, 3n), m(6n, 1n, 3n), m(7n, 1n, 3n), m(7n, 1n, 3n), m(8n, 1n, 2n), m(8n, 1n, 2n), m(15n, 3n, 5n)]))

def w_broker_sell_full_hand_mixed() -> String:
  W("+", 1n, 0n, "", "6:1/3,6:1/3,7:1/3,7:1/3,8:1/2,8:1/2,15:3/5", "")

# Tide Oracle at end of turn: one base Tide card of tier <= 2 joins the hand
def t_oracle_make() -> String:
  pool_tags("tide2", tide2(), G.p_hand(endturn([m(21n, 3n, 5n)], [])))

def w_oracle_make() -> String:
  "tide2 "

# Tide Oracle with a full hand of 7: nothing is added, the hand is unchanged
def t_oracle_full_hand() -> String:
  zones(endturn([m(21n, 3n, 5n)], fill(7n, m(6n, 1n, 3n))))

def w_oracle_full_hand() -> String:
  "b=[21:3/5] h=[6:1/3,6:1/3,6:1/3,6:1/3,6:1/3,6:1/3,6:1/3]"

# Tidal Sovereign at end of turn: one base Tide card of tier <= 4
def t_sovereign_make() -> String:
  pool_tags("tide4", tide4(), G.p_hand(endturn([m(33n, 4n, 8n)], [])))

def w_sovereign_make() -> String:
  "tide4 "

# Oracle and Sovereign on one board: two cards made, one from each pool
# (Oracle's tier<=2 card first, as the board is processed left to right)
def t_oracle_sovereign_two() -> String:
  two_made(G.p_hand(endturn([m(21n, 3n, 5n), m(33n, 4n, 8n)], [])))

def w_oracle_sovereign_two() -> String:
  "tide2 tide4"

# End-of-turn ORDER: MAKE grows the hand before later hand-scaling units read it
# ------------------------------------------------------------------------------

# Oracle left of Choir, empty hand: Oracle makes 1 card, then Choir counts 1 -> +2/+2
def t_oracle_then_choir() -> String:
  +p = endturn([m(21n, 3n, 5n), m(27n, 3n, 6n)], [])
  sms(G.p_board(p)) ++ " hand=" ++ pool_tags("tide2", tide2(), G.p_hand(p))

def w_oracle_then_choir() -> String:
  "21:3/5,27:5/8 hand=tide2 "

# Choir left of Oracle, empty hand: Choir counts 0 -> +0, then Oracle makes 1 card
def t_choir_then_oracle() -> String:
  +p = endturn([m(27n, 3n, 6n), m(21n, 3n, 5n)], [])
  sms(G.p_board(p)) ++ " hand=" ++ pool_tags("tide2", tide2(), G.p_hand(p))

def w_choir_then_oracle() -> String:
  "27:3/6,21:3/5 hand=tide2 "

# hand 3, Oracle first: hand 4 -> Choir +8/+8
def t_oracle_then_choir_h3() -> String:
  +p = endturn([m(21n, 3n, 5n), m(27n, 3n, 6n)], fill(3n, m(6n, 1n, 3n)))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def w_oracle_then_choir_h3() -> String:
  "21:3/5,27:11/14 handlen=4"

# hand 3, Choir first: +6/+6, then hand 4
def t_choir_then_oracle_h3() -> String:
  +p = endturn([m(27n, 3n, 6n), m(21n, 3n, 5n)], fill(3n, m(6n, 1n, 3n)))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def w_choir_then_oracle_h3() -> String:
  "27:9/12,21:3/5 handlen=4"

# hand 4, Oracle first: hand 5, Choir capped at +8/+8 (same as without Oracle)
def t_oracle_then_choir_cap() -> String:
  +p = endturn([m(21n, 3n, 5n), m(27n, 3n, 6n)], fill(4n, m(6n, 1n, 3n)))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def w_oracle_then_choir_cap() -> String:
  "21:3/5,27:11/14 handlen=5"

# hand 7, Oracle first: nothing made, Choir +8/+8, hand still 7
def t_oracle_full_then_choir() -> String:
  +p = endturn([m(21n, 3n, 5n), m(27n, 3n, 6n)], fill(7n, m(6n, 1n, 3n)))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def w_oracle_full_then_choir() -> String:
  "21:3/5,27:11/14 handlen=7"

# hand 3, Sovereign left of Maelstrom Queen: Sovereign makes 1 (hand 4) and
# gains +8/+8 (12/16), then the Queen gives the other Tide allies
# (Sovereign, Moth) +8/+8
def t_sovereign_then_maelstrom() -> String:
  +p = endturn([m(33n, 4n, 8n), ms(32n, 5n, 7n), m(3n, 1n, 1n)], fill(3n, m(6n, 1n, 3n)))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def w_sovereign_then_maelstrom() -> String:
  "33:20/24,32:5/7s,3:9/9 handlen=4"

# hand 3, Queen first: other Tide allies +6/+6 (Sovereign 10/14, Moth 7/7),
# then Sovereign makes 1 (hand 4) and gains +8/+8
def t_maelstrom_then_sovereign() -> String:
  +p = endturn([ms(32n, 5n, 7n), m(33n, 4n, 8n), m(3n, 1n, 1n)], fill(3n, m(6n, 1n, 3n)))
  sms(G.p_board(p)) ++ " handlen=" ++ Nat.show(G.len(G.Mon, G.p_hand(p)))

def w_maelstrom_then_sovereign() -> String:
  "32:5/7s,33:18/22,3:7/7 handlen=4"

# Combat damage and Rally, unit level (G.hurt, G.rally)
# -----------------------------------------------------

# a 0-damage hit does not break a Shield
def t_hurt_shield_zero() -> String:
  sm(G.hurt(ms(4n, 1n, 2n), 0n))

def w_hurt_shield_zero() -> String:
  "4:1/2s"

law k_hurt_shield_zero:
  {t_hurt_shield_zero() == w_hurt_shield_zero() : String}

def k_hurt_shield_zero():
  {==}

# a positive hit on a shielded Armor unit breaks the Shield first: no health lost
def t_hurt_shield_before_armor() -> String:
  sm(G.hurt(ms(7n, 1n, 3n), 5n))

def w_hurt_shield_before_armor() -> String:
  "7:1/3"

law k_hurt_shield_before_armor:
  {t_hurt_shield_before_armor() == w_hurt_shield_before_armor() : String}

def k_hurt_shield_before_armor():
  {==}

# Armor 1 absorbs a 1-damage hit completely
def t_hurt_armor1_absorbs() -> String:
  sm(G.hurt(m(7n, 1n, 3n), 1n))

def w_hurt_armor1_absorbs() -> String:
  "7:1/3"

law k_hurt_armor1_absorbs:
  {t_hurt_armor1_absorbs() == w_hurt_armor1_absorbs() : String}

def k_hurt_armor1_absorbs():
  {==}

# Armor 1: a 3-damage hit takes 2 health
def t_hurt_armor1() -> String:
  sm(G.hurt(m(7n, 1n, 3n), 3n))

def w_hurt_armor1() -> String:
  "7:1/1"

law k_hurt_armor1:
  {t_hurt_armor1() == w_hurt_armor1() : String}

def k_hurt_armor1():
  {==}

# Armor 2 (Basalt Bastion): 5 damage takes 3; 2 damage takes 0
def t_hurt_armor2() -> String:
  sm(G.hurt(m(28n, 3n, 7n), 5n)) ++ " " ++ sm(G.hurt(m(28n, 3n, 7n), 2n))

def w_hurt_armor2() -> String:
  "28:3/4 28:3/7"

law k_hurt_armor2:
  {t_hurt_armor2() == w_hurt_armor2() : String}

def k_hurt_armor2():
  {==}

# Armor 2 (Worldroot): 3 damage takes 1
def t_hurt_armor2_worldroot() -> String:
  sm(G.hurt(m(34n, 4n, 10n), 3n))

def w_hurt_armor2_worldroot() -> String:
  "34:4/9"

law k_hurt_armor2_worldroot:
  {t_hurt_armor2_worldroot() == w_hurt_armor2_worldroot() : String}

def k_hurt_armor2_worldroot():
  {==}

# Armor 1 on Cairn Mason (3 -> -2), Granite Titan (2 -> -1), Avalanche Lord (1 -> -0)
def t_hurt_armor_roster() -> String:
  sms([G.hurt(m(16n, 2n, 4n), 3n), G.hurt(m(22n, 3n, 8n), 2n), G.hurt(m(35n, 7n, 9n), 1n)])

def w_hurt_armor_roster() -> String:
  "16:2/2,22:3/7,35:7/9"

law k_hurt_armor_roster:
  {t_hurt_armor_roster() == w_hurt_armor_roster() : String}

def k_hurt_armor_roster():
  {==}

# raw 0 on a shielded Armor 1 unit (Moss Turtle): Shield stays, health unchanged
def t_hurt_shield_armor_raw0() -> String:
  sm(G.hurt(ms(7n, 1n, 3n), 0n))

def w_hurt_shield_armor_raw0() -> String:
  "7:1/3s"

law k_hurt_shield_armor_raw0:
  {t_hurt_shield_armor_raw0() == w_hurt_shield_armor_raw0() : String}

def k_hurt_shield_armor_raw0():
  {==}

# 1 damage on a shielded Armor 1 unit: Shield breaks, health unchanged
def t_hurt_shield_armor_dmg1() -> String:
  sm(G.hurt(ms(7n, 1n, 3n), 1n))

def w_hurt_shield_armor_dmg1() -> String:
  "7:1/3"

law k_hurt_shield_armor_dmg1:
  {t_hurt_shield_armor_dmg1() == w_hurt_shield_armor_dmg1() : String}

def k_hurt_shield_armor_dmg1():
  {==}

# 1 damage on a shielded Armor 2 unit (Basalt Bastion): Shield breaks, health unchanged;
# raw 0 on it: unchanged
def t_hurt_shield_armor2_dmg1() -> String:
  sm(G.hurt(ms(28n, 3n, 7n), 1n)) ++ " " ++ sm(G.hurt(ms(28n, 3n, 7n), 0n))

def w_hurt_shield_armor2_dmg1() -> String:
  "28:3/7 28:3/7s"

law k_hurt_shield_armor2_dmg1:
  {t_hurt_shield_armor2_dmg1() == w_hurt_shield_armor2_dmg1() : String}

def k_hurt_shield_armor2_dmg1():
  {==}

# two hits of 3 on a shielded Armor 1 unit: the first only breaks Shield, the
# second takes 3 - 1 = 2
def t_hurt_shield_then_armor_seq() -> String:
  sm(G.hurt(G.hurt(ms(7n, 1n, 4n), 3n), 3n))

def w_hurt_shield_then_armor_seq() -> String:
  "7:1/2"

law k_hurt_shield_then_armor_seq:
  {t_hurt_shield_then_armor_seq() == w_hurt_shield_then_armor_seq() : String}

def k_hurt_shield_then_armor_seq():
  {==}

# raw 0 on an unshielded unit: unchanged
def t_hurt_raw0_plain() -> String:
  sm(G.hurt(m(0n, 2n, 1n), 0n))

def w_hurt_raw0_plain() -> String:
  "0:2/1"

law k_hurt_raw0_plain:
  {t_hurt_raw0_plain() == w_hurt_raw0_plain() : String}

def k_hurt_raw0_plain():
  {==}

# one simultaneous exchange (G.attack_with, target index given, no hash): Imp
# rallies to 3, Turtle (Armor 1) takes 2 -> 1/2; the Imp takes 1 and dies
def t_exchange_rally_armor() -> String:
  atk_sum(G.attack_with("A", "B", m(0n, 2n, 1n), [], [m(7n, 1n, 4n)], 0n))

def w_exchange_rally_armor() -> String:
  "xs=[] ys=[7:1/2] asb=F tsb=F ad=T td=F ral=1 aatk=3"

law k_exchange_rally_armor:
  {t_exchange_rally_armor() == w_exchange_rally_armor() : String}

def k_exchange_rally_armor():
  {==}

# Imp rallies to 3 into a shielded Turtle: only the Shield breaks (health 4
# kept); the Imp takes 1 and dies
def t_exchange_rally_shield_armor() -> String:
  atk_sum(G.attack_with("A", "B", m(0n, 2n, 1n), [], [ms(7n, 1n, 4n)], 0n))

def w_exchange_rally_shield_armor() -> String:
  "xs=[] ys=[7:1/4] asb=F tsb=T ad=T td=F ral=1 aatk=3"

law k_exchange_rally_shield_armor:
  {t_exchange_rally_shield_armor() == w_exchange_rally_shield_armor() : String}

def k_exchange_rally_shield_armor():
  {==}

# a surviving attacker keeps its Rally gain inside the combat lists only: Charger
# 3 -> 5 hits the 0-attack Ox (30 -> 25) and rotates to the end of its side
def t_exchange_rally_carried() -> String:
  atk_sum(G.attack_with("A", "B", m(11n, 3n, 9n), [m(6n, 0n, 9n)], [m(15n, 0n, 30n)], 0n))

def w_exchange_rally_carried() -> String:
  "xs=[6:0/9,11:5/9] ys=[15:0/25] asb=F tsb=F ad=F td=F ral=2 aatk=5"

law k_exchange_rally_carried:
  {t_exchange_rally_carried() == w_exchange_rally_carried() : String}

def k_exchange_rally_carried():
  {==}

# a 0-attack defender (and attacker) leaves both Shields intact
def t_exchange_zero_attack_shield() -> String:
  atk_sum(G.attack_with("A", "B", ms(4n, 0n, 2n), [], [ms(4n, 0n, 2n)], 0n))

def w_exchange_zero_attack_shield() -> String:
  "xs=[4:0/2s] ys=[4:0/2s] asb=F tsb=F ad=F td=F ral=0 aatk=0"

law k_exchange_zero_attack_shield:
  {t_exchange_zero_attack_shield() == w_exchange_zero_attack_shield() : String}

def k_exchange_zero_attack_shield():
  {==}

# no Armor: overkill saturates at 0 health
def t_hurt_plain_overkill() -> String:
  sm(G.hurt(m(0n, 2n, 1n), 5n))

def w_hurt_plain_overkill() -> String:
  "0:2/0"

law k_hurt_plain_overkill:
  {t_hurt_plain_overkill() == w_hurt_plain_overkill() : String}

def k_hurt_plain_overkill():
  {==}

# Rally adds its value to attack only: Imp +1, Charger +2, Phoenix +3 (Shield
# kept), Tyrant +3; a card without Rally is unchanged
def t_rally_values() -> String:
  sms([G.rally(m(0n, 2n, 1n)), G.rally(m(11n, 3n, 3n)), G.rally(ms(19n, 4n, 2n)), G.rally(m(30n, 6n, 5n)), G.rally(m(6n, 1n, 3n))])

def w_rally_values() -> String:
  "0:3/1,11:5/3,19:7/2s,30:9/5,6:1/3"

law k_rally_values:
  {t_rally_values() == w_rally_values() : String}

def k_rally_values():
  {==}

# Fights (hash-based target/turn choice; runtime only)
# ----------------------------------------------------

# A=[Imp, Imp] attacks first (more units). Step 0: Imp rallies to 3,
# hits Turtle (Armor 1) for 2 -> 1/2, takes 1 and dies. Step 1: Turtle hits
# the other Imp, which deals 2 (a defender does not rally) - 1 armor -> Turtle
# 1/1 survives. B wins; damage = tier 1 + Turtle tier 1 = 2
def t_fight_rally_armor() -> String:
  fsum(G.fight(seed(), 3n, 0n, 1n, "A", "B", 1n, 1n, [m(0n, 2n, 1n), m(0n, 2n, 1n)], [m(7n, 1n, 4n)]))

def w_fight_rally_armor() -> String:
  "res=2 dmg=2 rally=[3] end a=[] b=[7:1/1]"

# Rally stacks for the rest of a combat: Charger (Rally 2) attacks the
# 0-attack Ox (30 health) at 5, 7, 9, 11 (Pebble Guard soaks the Ox's
# attacks); the Ox dies on the 4th; A wins with Charger 11/9. Damage =
# tier 1 + Pebble 1 + Charger 2 = 4
def t_fight_rally_accumulates() -> String:
  fsum(G.fight(seed(), 3n, 0n, 1n, "A", "B", 1n, 1n, [m(11n, 3n, 9n), m(6n, 0n, 9n)], [m(15n, 0n, 30n)]))

def w_fight_rally_accumulates() -> String:
  "res=1 dmg=4 rally=[5,7,9,11] end a=[6:0/9,11:11/9] b=[]"

# after a whole round (end_round: end of turn, fights, next round) the
# Charger on seat 0's board is still 3/3 and plays reset to 0
def t_rally_not_persisted() -> String:
  round_board(G.end_round(G.Game{seed(), 1n, 3n, 0n, [PI(0n, [m(11n, 3n, 3n)], 2n), PI(1n, [m(7n, 1n, 4n)], 0n), PI(2n, [m(7n, 1n, 4n)], 0n), PI(3n, [m(7n, 1n, 4n)], 0n)], [], [], False{}}))

def w_rally_not_persisted() -> String:
  "b=[11:3/3] n=0"

# V4 fixtures: golden assembly, golden effects, Neutral cards
# ===========================================================
# Expectations are hand-calculated from the printed card descriptions;
# concrete examples, not universal proofs.

# a mid-game seat 0 for next-round checks (tier 3, upcost 7, no investment)
def PI0(board: List<&2, G.Mon>, hand: List<&2, G.Mon>) -> G.Player:
  G.Player{0n, 20n, 0n, 3n, 7n, 0n, False{}, 0n, board, [], True{}, 0n, hand, 0n}

# gold and zones after a next-round step (the fresh shop is hash-drawn)
def nr(+p: G.Player) -> String:
  "g=" ++ Nat.show(G.p_gold(p)) ++ " " ++ zones(p)

def fres(f: G.Fight) -> String:
  G.Fight{round, a, b, res, dmg, aboard, bboard, log, events} = f
  "res=" ++ Nat.show(res) ++ " dmg=" ++ Nat.show(dmg)

def scout_g() -> String:
  +p = after([G.Play{0n}], P(0n, [], [], [mg(5n, 2n, 2n)]))
  sms(G.p_board(p)) ++ " hand=" ++ pool_tags("tide1", tide1(), G.p_hand(p))

def gtexts(k: Nat, +c: Nat) -> List<&2, String>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      (Nat.show(c) ++ " " ++ G.card_text_g(True{}, G.card(c))) <> gtexts(j, 1n+c)

# two board copies (one buffed +1/+1) + buying the third: hand copy first, then the board copies left to right; golden = (1+1+2)/(3+3+4) - printed 1/3 = 3/7, to the hand
def t_gold_buy_third() -> String:
  run([G.Buy{0n}], P(3n, [m(6n, 1n, 3n), m(6n, 2n, 4n)], [6n], []))

def w_gold_buy_third() -> String:
  W("+", 0n, 0n, "", "6:3/7G", "")

law k_gold_buy_third:
  {t_gold_buy_third() == w_gold_buy_third() : String}

def k_gold_buy_third():
  {==}

# two in hand + buying the third: 3/9 - 1/3 = 2/6
def t_gold_three_in_hand() -> String:
  run([G.Buy{0n}], P(3n, [], [7n], [m(7n, 1n, 3n), m(7n, 1n, 3n)]))

def w_gold_three_in_hand() -> String:
  W("+", 0n, 0n, "", "7:2/6G", "")

law k_gold_three_in_hand:
  {t_gold_three_in_hand() == w_gold_three_in_hand() : String}

def k_gold_three_in_hand():
  {==}

# hand copies are consumed first (all three here), the board copy and the other units keep their order; golden 3/10 - 1/3 = 2/7 at the hand's right end
def t_gold_hand_first_order() -> String:
  run([G.Buy{0n}], P(3n, [m(6n, 5n, 5n), m(0n, 2n, 1n)], [6n], [m(6n, 1n, 3n), m(0n, 2n, 1n), m(6n, 1n, 4n)]))

def w_gold_hand_first_order() -> String:
  W("+", 0n, 0n, "6:5/5,0:2/1", "0:2/1,6:2/7G", "")

law k_gold_hand_first_order:
  {t_gold_hand_first_order() == w_gold_hand_first_order() : String}

def k_gold_hand_first_order():
  {==}

# two triples at one boundary: card 6 (hand 1 + board 2) merges before card 7 (hand 3)
def t_gold_lowest_cid_first() -> String:
  run([G.Buy{0n}], P(3n, [m(6n, 1n, 3n), m(6n, 1n, 3n)], [7n], [m(7n, 1n, 3n), m(7n, 1n, 3n), m(6n, 1n, 3n)]))

def w_gold_lowest_cid_first() -> String:
  W("+", 0n, 0n, "", "6:2/6G,7:2/6G", "")

law k_gold_lowest_cid_first:
  {t_gold_lowest_cid_first() == w_gold_lowest_cid_first() : String}

def k_gold_lowest_cid_first():
  {==}

# a full hand rejects buying the third copy (no triple, nothing changes)
def t_gold_full_hand_third() -> String:
  run([G.Buy{0n}], P(3n, [], [6n], [m(6n, 1n, 3n), m(6n, 1n, 3n), m(7n, 1n, 3n), m(7n, 1n, 3n), m(8n, 1n, 2n), m(8n, 1n, 2n), m(15n, 3n, 5n)]))

def w_gold_full_hand_third() -> String:
  W("x", 3n, 0n, "", "6:1/3,6:1/3,7:1/3,7:1/3,8:1/2,8:1/2,15:3/5", "6")

law k_gold_full_hand_third:
  {t_gold_full_hand_third() == w_gold_full_hand_third() : String}

def k_gold_full_hand_third():
  {==}

# golden copies never merge: three goldens + a regular stay as they are
def t_gold_no_remerge() -> String:
  run([G.Buy{0n}], P(3n, [mg(6n, 2n, 6n)], [6n], [mg(6n, 2n, 6n), mg(6n, 2n, 6n)]))

def w_gold_no_remerge() -> String:
  W("+", 0n, 0n, "6:2/6G", "6:2/6G,6:2/6G,6:1/3", "")

law k_gold_no_remerge:
  {t_gold_no_remerge() == w_gold_no_remerge() : String}

def k_gold_no_remerge():
  {==}

# a golden copy is skipped; the three regular copies (hand 2, board 1) merge
def t_gold_regulars_beside_golden() -> String:
  run([G.Buy{0n}], P(3n, [m(6n, 1n, 3n)], [6n], [mg(6n, 2n, 6n), m(6n, 1n, 3n)]))

def w_gold_regulars_beside_golden() -> String:
  W("+", 0n, 0n, "", "6:2/6G,6:2/6G", "")

law k_gold_regulars_beside_golden:
  {t_gold_regulars_beside_golden() == w_gold_regulars_beside_golden() : String}

def k_gold_regulars_beside_golden():
  {==}

# Shield is kept if any consumed copy had it (Tide Pup 1/2s: 3/6 - 1/2 = 2/4)
def t_gold_shield_or() -> String:
  run([G.Buy{0n}], P(3n, [], [4n], [ms(4n, 1n, 2n), m(4n, 1n, 2n)]))

def w_gold_shield_or() -> String:
  W("+", 0n, 0n, "", "4:2/4sG", "")

law k_gold_shield_or:
  {t_gold_shield_or() == w_gold_shield_or() : String}

def k_gold_shield_or():
  {==}

# Play is a boundary: playing one of three regular copies (an unreachable start) assembles board 1 + hand 2
def t_gold_play_boundary() -> String:
  run([G.Play{0n}], P(0n, [], [], [m(6n, 1n, 3n), m(6n, 1n, 3n), m(6n, 1n, 3n)]))

def w_gold_play_boundary() -> String:
  W("+", 0n, 1n, "", "6:2/6G", "")

law k_gold_play_boundary:
  {t_gold_play_boundary() == w_gold_play_boundary() : String}

def k_gold_play_boundary():
  {==}

# end of turn never assembles: Root Sprout grows, the three regular copies stay
def t_gold_endturn_no_merge() -> String:
  zones(endturn([m(8n, 1n, 2n)], [m(8n, 1n, 2n), m(8n, 1n, 2n)]))

def w_gold_endturn_no_merge() -> String:
  "b=[8:1/3] h=[8:1/2,8:1/2]"

law k_gold_endturn_no_merge:
  {t_gold_endturn_no_merge() == w_gold_endturn_no_merge() : String}

def k_gold_endturn_no_merge():
  {==}

# recruit start assembles BEFORE income: hand copies first, then the board Moth; the golden goes to the hand, so the board pays no Income: round 2 income = 4
def t_gold_recruit_start() -> String:
  nr(G.next_round_player(seed(), 2n, PI0([m(3n, 1n, 1n)], [m(3n, 1n, 1n), m(3n, 1n, 1n)])))

def w_gold_recruit_start() -> String:
  "g=4 b=[] h=[3:2/2G]"

# a golden Purse Moth on the board pays Income 2: round 2 income = 4 + 2
def t_gold_moth_board_income() -> String:
  nr(G.next_round_player(seed(), 2n, PI0([mg(3n, 2n, 2n)], [])))

def w_gold_moth_board_income() -> String:
  "g=6 b=[3:2/2G] h=[]"

# golden Copper Tinker: Play gold doubles (2)
def t_gold_tinker_gold() -> String:
  run([G.Play{0n}], P(0n, [], [], [mg(37n, 2n, 2n)]))

def w_gold_tinker_gold() -> String:
  W("+", 2n, 1n, "37:2/2G", "", "")

law k_gold_tinker_gold:
  {t_gold_tinker_gold() == w_gold_tinker_gold() : String}

def k_gold_tinker_gold():
  {==}

# golden Coin Eel: Play +2, Sell +2 + refund 1
def t_gold_eel_play_sell() -> String:
  run([G.Play{0n}, G.Sell{0n}], P(0n, [], [], [mg(14n, 6n, 6n)]))

def w_gold_eel_play_sell() -> String:
  W("++", 5n, 1n, "", "", "")

law k_gold_eel_play_sell:
  {t_gold_eel_play_sell() == w_gold_eel_play_sell() : String}

def k_gold_eel_play_sell():
  {==}

# golden Kindler: other Ember allies +2 attack (doubled)
def t_gold_kindler_kin() -> String:
  run([G.Play{0n}], P(0n, [m(0n, 2n, 1n)], [], [mg(2n, 2n, 4n)]))

def w_gold_kindler_kin() -> String:
  W("+", 0n, 1n, "0:4/1,2:2/4G", "", "")

law k_gold_kindler_kin:
  {t_gold_kindler_kin() == w_gold_kindler_kin() : String}

def k_gold_kindler_kin():
  {==}

# golden Tidecaller: +2/+2 per hand card, count still capped at 4 (6 in hand): +8/+8
def t_gold_tidecaller_hand() -> String:
  run([G.Play{0n}], P(0n, [], [], [mg(13n, 6n, 6n), m(6n, 1n, 3n), m(6n, 1n, 3n), m(7n, 1n, 3n), m(7n, 1n, 3n), m(8n, 1n, 2n), m(8n, 1n, 2n)]))

def w_gold_tidecaller_hand() -> String:
  W("+", 0n, 1n, "13:14/14G", "6:1/3,6:1/3,7:1/3,7:1/3,8:1/2,8:1/2", "")

law k_gold_tidecaller_hand:
  {t_gold_tidecaller_hand() == w_gold_tidecaller_hand() : String}

def k_gold_tidecaller_hand():
  {==}

# golden Brass Drillmaster: +4/+4 per earlier play, count capped at 4 (5 earlier): +16/+16
def t_gold_drillmaster_plays() -> String:
  run([G.Play{0n}], PP(0n, [], [], [mg(42n, 20n, 24n)], 5n))

def w_gold_drillmaster_plays() -> String:
  W("+", 0n, 6n, "42:36/40G", "", "")

law k_gold_drillmaster_plays:
  {t_gold_drillmaster_plays() == w_gold_drillmaster_plays() : String}

def k_gold_drillmaster_plays():
  {==}

# golden Iron Apprentice: end of turn +2/+2
def t_gold_apprentice_endturn() -> String:
  zones(endturn([mg(38n, 6n, 6n)], []))

def w_gold_apprentice_endturn() -> String:
  "b=[38:8/8G] h=[]"

law k_gold_apprentice_endturn:
  {t_gold_apprentice_endturn() == w_gold_apprentice_endturn() : String}

def k_gold_apprentice_endturn():
  {==}

# board income: golden Bounty Clerk 2 + Purse Moth 1
def t_gold_income() -> String:
  "inc=" ++ Nat.show(G.board_income([mg(39n, 4n, 8n), m(3n, 1n, 1n)]))

def w_gold_income() -> String:
  "inc=3"

law k_gold_income:
  {t_gold_income() == w_gold_income() : String}

def k_gold_income():
  {==}

# Rally doubles for a golden unit: Imp +2, Grand Artificer +2; regular Imp +1
def t_gold_rally() -> String:
  sms([G.rally(mg(0n, 4n, 2n)), G.rally(mg(43n, 36n, 40n)), G.rally(m(0n, 2n, 1n))])

def w_gold_rally() -> String:
  "0:6/2G,43:38/40G,0:3/1"

law k_gold_rally:
  {t_gold_rally() == w_gold_rally() : String}

def k_gold_rally():
  {==}

# golden Basalt Bastion keeps Armor 2: a 5-hit takes 3; armor of golden Bastion/Worldroot = 2
def t_gold_armor_unscaled() -> String:
  sm(G.hurt(mg(28n, 16n, 36n), 5n)) ++ " a=" ++ Nat.show(G.mon_armor(mg(28n, 16n, 36n))) ++ "," ++ Nat.show(G.mon_armor(mg(34n, 28n, 60n)))

def w_gold_armor_unscaled() -> String:
  "28:16/33G a=2,2"

law k_gold_armor_unscaled:
  {t_gold_armor_unscaled() == w_gold_armor_unscaled() : String}

def k_gold_armor_unscaled():
  {==}

# golden Mirror Warden: one Shield (a hit only breaks it), Guard kept
def t_gold_shield_guard_once() -> String:
  sm(G.hurt(mgs(41n, 10n, 18n), 5n)) ++ " guard=" ++ sb(G.mon_guard(mgs(41n, 10n, 18n)))

def w_gold_shield_guard_once() -> String:
  "41:10/18G guard=T"

law k_gold_shield_guard_once:
  {t_gold_shield_guard_once() == w_gold_shield_guard_once() : String}

def k_gold_shield_guard_once():
  {==}

# a golden unit with no Sell ability refunds 1 (not doubled)
def t_gold_sell_refund() -> String:
  run([G.Sell{0n}], P(0n, [mg(6n, 2n, 6n)], [], []))

def w_gold_sell_refund() -> String:
  W("+", 1n, 0n, "", "", "")

law k_gold_sell_refund:
  {t_gold_sell_refund() == w_gold_sell_refund() : String}

def k_gold_sell_refund():
  {==}

# golden Shell Scout: MAKE fires twice at tier 1 (two tier-1 Tide cards)
def t_gold_scout_make_twice() -> String:
  scout_g()

def w_gold_scout_make_twice() -> String:
  "5:2/2G hand=tide1 tide1 "

# player damage counts a golden survivor by its tier: seat tier 1 + Siege Ram tier 3 = 4
def t_gold_fight_tier() -> String:
  fres(G.fight(seed(), 3n, 0n, 1n, "A", "B", 1n, 1n, [mg(40n, 24n, 6n)], [m(0n, 2n, 1n)]))

def w_gold_fight_tier() -> String:
  "res=1 dmg=4"

# Ember KIN skips a Neutral unit: Kindler gives the Imp +1, the Tin Sentry nothing
def t_neutral_kin_skip() -> String:
  run([G.Play{0n}], P(0n, [m(36n, 1n, 3n), m(0n, 2n, 1n)], [], [m(2n, 1n, 2n)]))

def w_neutral_kin_skip() -> String:
  W("+", 0n, 1n, "36:1/3,0:3/1,2:1/2", "", "")

law k_neutral_kin_skip:
  {t_neutral_kin_skip() == w_neutral_kin_skip() : String}

def k_neutral_kin_skip():
  {==}

# playing a Neutral card triggers no After-you-play observer (Cinder Whelp stays 1/2)
def t_neutral_no_kinplay() -> String:
  run([G.Play{0n}], P(0n, [m(1n, 1n, 2n)], [], [m(36n, 1n, 3n)]))

def w_neutral_no_kinplay() -> String:
  W("+", 0n, 1n, "1:1/2,36:1/3", "", "")

law k_neutral_no_kinplay:
  {t_neutral_no_kinplay() == w_neutral_no_kinplay() : String}

def k_neutral_no_kinplay():
  {==}

# kin_match: Neutral never matches, not even itself
def t_neutral_kin_match() -> String:
  sb(G.kin_match(3n, 3n)) ++ sb(G.kin_match(0n, 3n)) ++ sb(G.kin_match(3n, 0n)) ++ sb(G.kin_match(0n, 0n))

def w_neutral_kin_match() -> String:
  "FFFT"

law k_neutral_kin_match:
  {t_neutral_kin_match() == w_neutral_kin_match() : String}

def k_neutral_kin_match():
  {==}

# eligible shop ids per tier, ascending (independently enumerated expected ids)
def t_shop_pools() -> String:
  String.join([sns(G.shop_pool(1n)), sns(G.shop_pool(2n)), sns(G.shop_pool(3n)), sns(G.shop_pool(4n)), sns(G.shop_pool(5n))], " | ")

def w_shop_pools() -> String:
  "0,1,2,3,4,5,6,7,8,36,37 | 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,36,37,38,39 | 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,36,37,38,39,40,41 | 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,36,37,38,39,40,41,42 | 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43"

law k_shop_pools:
  {t_shop_pools() == w_shop_pools() : String}

def k_shop_pools():
  {==}

# MAKE pools never contain a Neutral id: Tide tier<=4, Ember tier<=3
def t_make_pools_no_neutral() -> String:
  sns(G.make_pool(G.card_list(), 1n, 4n)) ++ " | " ++ sns(G.make_pool(G.card_list(), 0n, 3n)) ++ " | " ++ sns(G.make_pool(G.card_list(), 3n, 5n))

def w_make_pools_no_neutral() -> String:
  "3,4,5,12,13,14,20,21,26,27 | 0,1,2,9,10,11,18,19 | "

law k_make_pools_no_neutral:
  {t_make_pools_no_neutral() == w_make_pools_no_neutral() : String}

def k_make_pools_no_neutral():
  {==}

# the 8 Neutral cards against hand-written expected rows and text
def t_roster_36_43() -> String:
  String.join(roster_go(8n, 36n), "; ")

def w_roster_36_43() -> String:
  String.join(
    [ "36 Tin Sentry Neutral t1 36:1/3 gT a0 r0 i0 | Guard."
    , "37 Copper Tinker Neutral t1 37:1/1 gF a0 r0 i0 | Play: gain 1 gold."
    , "38 Iron Apprentice Neutral t2 38:3/3 gF a0 r0 i0 | End of turn: gain +1/+1."
    , "39 Bounty Clerk Neutral t2 39:2/4 gF a0 r0 i1 | Income 1."
    , "40 Siege Ram Neutral t3 40:12/3 gF a0 r0 i0 | "
    , "41 Mirror Warden Neutral t3 41:5/9s gT a0 r0 i0 | Guard. Shield."
    , "42 Brass Drillmaster Neutral t4 42:10/12 gF a0 r0 i0 | Play: gain +2/+2 for each card you played earlier this turn (max 4)."
    , "43 Grand Artificer Neutral t5 43:18/20 gF a0 r1 i0 | Rally 1. End of turn: gain +3/+3."
    ], "; ")

law k_roster_36_43:
  {t_roster_36_43() == w_roster_36_43() : String}

def k_roster_36_43():
  {==}

# golden text of the 8 Neutral cards (hand-written golden expectations)
def t_roster_36_43_golden() -> String:
  String.join(gtexts(8n, 36n), "; ")

def w_roster_36_43_golden() -> String:
  String.join(
    [ "36 Guard.", "37 Play: gain 2 gold.", "38 End of turn: gain +2/+2.", "39 Income 2.", "40 "
    , "41 Guard. Shield.", "42 Play: gain +4/+4 for each card you played earlier this turn (max 4).", "43 Rally 2. End of turn: gain +6/+6." ], "; ")

law k_roster_36_43_golden:
  {t_roster_36_43_golden() == w_roster_36_43_golden() : String}

def k_roster_36_43_golden():
  {==}

# Report
# ------

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
  [ Case{"buy_no_triggers", t_buy_no_triggers(), w_buy_no_triggers()}
  , Case{"buy_battlecry_held", t_buy_battlecry_held(), w_buy_battlecry_held()}
  , Case{"buy_full_board", t_buy_full_board(), w_buy_full_board()}
  , Case{"buy_full_board_mixed", t_buy_full_board_mixed(), w_buy_full_board_mixed()}
  , Case{"buy_poor", t_buy_poor(), w_buy_poor()}
  , Case{"buy_hand_full", t_buy_hand_full(), w_buy_hand_full()}
  , Case{"buy_bad_index", t_buy_bad_index(), w_buy_bad_index()}
  , Case{"play_basic", t_play_basic(), w_play_basic()}
  , Case{"play_full_board", t_play_full_board(), w_play_full_board()}
  , Case{"play_bad_index", t_play_bad_index(), w_play_bad_index()}
  , Case{"sell_zones", t_sell_zones(), w_sell_zones()}
  , Case{"sell_bad_index", t_sell_bad_index(), w_sell_bad_index()}
  , Case{"kindler_whelp", t_kindler_whelp(), w_kindler_whelp()}
  , Case{"whelp_self_excluded", t_whelp_self_excluded(), w_whelp_self_excluded()}
  , Case{"whelp_other_tribe", t_whelp_other_tribe(), w_whelp_other_tribe()}
  , Case{"dancer", t_dancer(), w_dancer()}
  , Case{"drake_includes_entering", t_drake_includes_entering(), w_drake_includes_entering()}
  , Case{"drake_played", t_drake_played(), w_drake_played()}
  , Case{"herald", t_herald(), w_herald()}
  , Case{"herald_drake_dancer", t_herald_drake_dancer(), w_herald_drake_dancer()}
  , Case{"kindler_dup", t_kindler_dup(), w_kindler_dup()}
  , Case{"drake_pair", t_drake_pair(), w_drake_pair()}
  , Case{"herald_two_imps", t_herald_two_imps(), w_herald_two_imps()}
  , Case{"whelp_pair", t_whelp_pair(), w_whelp_pair()}
  , Case{"reef_warden", t_reef_warden(), w_reef_warden()}
  , Case{"tidecaller_two", t_tidecaller_two(), w_tidecaller_two()}
  , Case{"tidecaller_cap", t_tidecaller_cap(), w_tidecaller_cap()}
  , Case{"tidecaller_alone", t_tidecaller_alone(), w_tidecaller_alone()}
  , Case{"siren_two", t_siren_two(), w_siren_two()}
  , Case{"siren_cap", t_siren_cap(), w_siren_cap()}
  , Case{"eel_play_sell", t_eel_play_sell(), w_eel_play_sell()}
  , Case{"sellhand_parse", t_sellhand_parse(), w_sellhand_parse()}
  , Case{"eel_golden_sell", t_eel_golden_sell(), w_eel_golden_sell()}
  , Case{"pup_sell_twice", t_pup_sell_twice(), w_pup_sell_twice()}
  , Case{"pup_golden_sell", t_pup_golden_sell(), w_pup_golden_sell()}
  , Case{"captain_includes_entering", t_captain_includes_entering(), w_captain_includes_entering()}
  , Case{"captain_first_play", t_captain_first_play(), w_captain_first_play()}
  , Case{"tyrant_captain", t_tyrant_captain(), w_tyrant_captain()}
  , Case{"tyrant_captain_chain", t_tyrant_captain_chain(), w_tyrant_captain_chain()}
  , Case{"tyrant_played", t_tyrant_played(), w_tyrant_played()}
  , Case{"static_t1", t_static_t1(), w_static_t1()}
  , Case{"static_t2", t_static_t2(), w_static_t2()}
  , Case{"static_t3", t_static_t3(), w_static_t3()}
  , Case{"static_t45", t_static_t45(), w_static_t45()}
  , Case{"static_t45b", t_static_t45b(), w_static_t45b()}
  , Case{"endturn_stone", t_endturn_stone(), w_endturn_stone()}
  , Case{"endturn_titan", t_endturn_titan(), w_endturn_titan()}
  , Case{"endturn_rootwarden_pair", t_endturn_rootwarden_pair(), w_endturn_rootwarden_pair()}
  , Case{"endturn_heart_pair", t_endturn_heart_pair(), w_endturn_heart_pair()}
  , Case{"endturn_no_growth", t_endturn_no_growth(), w_endturn_no_growth()}
  , Case{"choir_hand", t_choir_hand(), w_choir_hand()}
  , Case{"choir_cap", t_choir_cap(), w_choir_cap()}
  , Case{"bastion", t_bastion(), w_bastion()}
  , Case{"drummer_pair", t_drummer_pair(), w_drummer_pair()}
  , Case{"queen_plays3", t_queen_plays3(), w_queen_plays3()}
  , Case{"queen_cap", t_queen_cap(), w_queen_cap()}
  , Case{"queen_zero", t_queen_zero(), w_queen_zero()}
  , Case{"queen_any_tribe", t_queen_any_tribe(), w_queen_any_tribe()}
  , Case{"maelstrom", t_maelstrom(), w_maelstrom()}
  , Case{"worldroot_pair", t_worldroot_pair(), w_worldroot_pair()}
  , Case{"avalanche", t_avalanche(), w_avalanche()}
  , Case{"board_income", t_board_income(), w_board_income()}
  , Case{"roster_0_11", t_roster_0_11(), w_roster_0_11()}
  , Case{"roster_12_23", t_roster_12_23(), w_roster_12_23()}
  , Case{"roster_24_35", t_roster_24_35(), w_roster_24_35()}
  , Case{"card_count", t_card_count(), w_card_count()}
  , Case{"scout_make", t_scout_make(), w_scout_make()}
  , Case{"scout_full_hand", t_scout_full_hand(), w_scout_full_hand()}
  , Case{"scout_full_hand_mixed", t_scout_full_hand_mixed(), w_scout_full_hand_mixed()}
  , Case{"scout_twice", t_scout_twice(), w_scout_twice()}
  , Case{"matron_make", t_matron_make(), w_matron_make()}
  , Case{"matron_plays", t_matron_plays(), w_matron_plays()}
  , Case{"broker_sell_make", t_broker_sell_make(), w_broker_sell_make()}
  , Case{"broker_sell_full_hand", t_broker_sell_full_hand(), w_broker_sell_full_hand()}
  , Case{"broker_sell_full_hand_mixed", t_broker_sell_full_hand_mixed(), w_broker_sell_full_hand_mixed()}
  , Case{"oracle_make", t_oracle_make(), w_oracle_make()}
  , Case{"oracle_full_hand", t_oracle_full_hand(), w_oracle_full_hand()}
  , Case{"sovereign_make", t_sovereign_make(), w_sovereign_make()}
  , Case{"oracle_sovereign_two", t_oracle_sovereign_two(), w_oracle_sovereign_two()}
  , Case{"oracle_then_choir", t_oracle_then_choir(), w_oracle_then_choir()}
  , Case{"choir_then_oracle", t_choir_then_oracle(), w_choir_then_oracle()}
  , Case{"oracle_then_choir_h3", t_oracle_then_choir_h3(), w_oracle_then_choir_h3()}
  , Case{"choir_then_oracle_h3", t_choir_then_oracle_h3(), w_choir_then_oracle_h3()}
  , Case{"oracle_then_choir_cap", t_oracle_then_choir_cap(), w_oracle_then_choir_cap()}
  , Case{"oracle_full_then_choir", t_oracle_full_then_choir(), w_oracle_full_then_choir()}
  , Case{"sovereign_then_maelstrom", t_sovereign_then_maelstrom(), w_sovereign_then_maelstrom()}
  , Case{"maelstrom_then_sovereign", t_maelstrom_then_sovereign(), w_maelstrom_then_sovereign()}
  , Case{"hurt_shield_zero", t_hurt_shield_zero(), w_hurt_shield_zero()}
  , Case{"hurt_shield_before_armor", t_hurt_shield_before_armor(), w_hurt_shield_before_armor()}
  , Case{"hurt_armor1_absorbs", t_hurt_armor1_absorbs(), w_hurt_armor1_absorbs()}
  , Case{"hurt_armor1", t_hurt_armor1(), w_hurt_armor1()}
  , Case{"hurt_armor2", t_hurt_armor2(), w_hurt_armor2()}
  , Case{"hurt_armor2_worldroot", t_hurt_armor2_worldroot(), w_hurt_armor2_worldroot()}
  , Case{"hurt_armor_roster", t_hurt_armor_roster(), w_hurt_armor_roster()}
  , Case{"hurt_shield_armor_raw0", t_hurt_shield_armor_raw0(), w_hurt_shield_armor_raw0()}
  , Case{"hurt_shield_armor_dmg1", t_hurt_shield_armor_dmg1(), w_hurt_shield_armor_dmg1()}
  , Case{"hurt_shield_armor2_dmg1", t_hurt_shield_armor2_dmg1(), w_hurt_shield_armor2_dmg1()}
  , Case{"hurt_shield_then_armor_seq", t_hurt_shield_then_armor_seq(), w_hurt_shield_then_armor_seq()}
  , Case{"hurt_raw0_plain", t_hurt_raw0_plain(), w_hurt_raw0_plain()}
  , Case{"exchange_rally_armor", t_exchange_rally_armor(), w_exchange_rally_armor()}
  , Case{"exchange_rally_shield_armor", t_exchange_rally_shield_armor(), w_exchange_rally_shield_armor()}
  , Case{"exchange_rally_carried", t_exchange_rally_carried(), w_exchange_rally_carried()}
  , Case{"exchange_zero_attack_shield", t_exchange_zero_attack_shield(), w_exchange_zero_attack_shield()}
  , Case{"hurt_plain_overkill", t_hurt_plain_overkill(), w_hurt_plain_overkill()}
  , Case{"rally_values", t_rally_values(), w_rally_values()}
  , Case{"fight_rally_armor", t_fight_rally_armor(), w_fight_rally_armor()}
  , Case{"fight_rally_accumulates", t_fight_rally_accumulates(), w_fight_rally_accumulates()}
  , Case{"rally_not_persisted", t_rally_not_persisted(), w_rally_not_persisted()}
  , Case{"gold_buy_third", t_gold_buy_third(), w_gold_buy_third()}
  , Case{"gold_three_in_hand", t_gold_three_in_hand(), w_gold_three_in_hand()}
  , Case{"gold_hand_first_order", t_gold_hand_first_order(), w_gold_hand_first_order()}
  , Case{"gold_lowest_cid_first", t_gold_lowest_cid_first(), w_gold_lowest_cid_first()}
  , Case{"gold_full_hand_third", t_gold_full_hand_third(), w_gold_full_hand_third()}
  , Case{"gold_no_remerge", t_gold_no_remerge(), w_gold_no_remerge()}
  , Case{"gold_regulars_beside_golden", t_gold_regulars_beside_golden(), w_gold_regulars_beside_golden()}
  , Case{"gold_shield_or", t_gold_shield_or(), w_gold_shield_or()}
  , Case{"gold_play_boundary", t_gold_play_boundary(), w_gold_play_boundary()}
  , Case{"gold_endturn_no_merge", t_gold_endturn_no_merge(), w_gold_endturn_no_merge()}
  , Case{"gold_recruit_start", t_gold_recruit_start(), w_gold_recruit_start()}
  , Case{"gold_moth_board_income", t_gold_moth_board_income(), w_gold_moth_board_income()}
  , Case{"gold_tinker_gold", t_gold_tinker_gold(), w_gold_tinker_gold()}
  , Case{"gold_eel_play_sell", t_gold_eel_play_sell(), w_gold_eel_play_sell()}
  , Case{"gold_kindler_kin", t_gold_kindler_kin(), w_gold_kindler_kin()}
  , Case{"gold_tidecaller_hand", t_gold_tidecaller_hand(), w_gold_tidecaller_hand()}
  , Case{"gold_drillmaster_plays", t_gold_drillmaster_plays(), w_gold_drillmaster_plays()}
  , Case{"gold_apprentice_endturn", t_gold_apprentice_endturn(), w_gold_apprentice_endturn()}
  , Case{"gold_income", t_gold_income(), w_gold_income()}
  , Case{"gold_rally", t_gold_rally(), w_gold_rally()}
  , Case{"gold_armor_unscaled", t_gold_armor_unscaled(), w_gold_armor_unscaled()}
  , Case{"gold_shield_guard_once", t_gold_shield_guard_once(), w_gold_shield_guard_once()}
  , Case{"gold_sell_refund", t_gold_sell_refund(), w_gold_sell_refund()}
  , Case{"gold_scout_make_twice", t_gold_scout_make_twice(), w_gold_scout_make_twice()}
  , Case{"gold_fight_tier", t_gold_fight_tier(), w_gold_fight_tier()}
  , Case{"neutral_kin_skip", t_neutral_kin_skip(), w_neutral_kin_skip()}
  , Case{"neutral_no_kinplay", t_neutral_no_kinplay(), w_neutral_no_kinplay()}
  , Case{"neutral_kin_match", t_neutral_kin_match(), w_neutral_kin_match()}
  , Case{"shop_pools", t_shop_pools(), w_shop_pools()}
  , Case{"make_pools_no_neutral", t_make_pools_no_neutral(), w_make_pools_no_neutral()}
  , Case{"roster_36_43", t_roster_36_43(), w_roster_36_43()}
  , Case{"roster_36_43_golden", t_roster_36_43_golden(), w_roster_36_43_golden()}
  ]

def main() -> IO(Unit):
  IO.print(String.join(lines(cases()), "\n"))

#|PASS buy_no_triggers
#|PASS buy_battlecry_held
#|PASS buy_full_board
#|PASS buy_full_board_mixed
#|PASS buy_poor
#|PASS buy_hand_full
#|PASS buy_bad_index
#|PASS play_basic
#|PASS play_full_board
#|PASS play_bad_index
#|PASS sell_zones
#|PASS sell_bad_index
#|PASS kindler_whelp
#|PASS whelp_self_excluded
#|PASS whelp_other_tribe
#|PASS dancer
#|PASS drake_includes_entering
#|PASS drake_played
#|PASS herald
#|PASS herald_drake_dancer
#|PASS kindler_dup
#|PASS drake_pair
#|PASS herald_two_imps
#|PASS whelp_pair
#|PASS reef_warden
#|PASS tidecaller_two
#|PASS tidecaller_cap
#|PASS tidecaller_alone
#|PASS siren_two
#|PASS siren_cap
#|PASS eel_play_sell
#|PASS sellhand_parse
#|PASS eel_golden_sell
#|PASS pup_sell_twice
#|PASS pup_golden_sell
#|PASS captain_includes_entering
#|PASS captain_first_play
#|PASS tyrant_captain
#|PASS tyrant_captain_chain
#|PASS tyrant_played
#|PASS static_t1
#|PASS static_t2
#|PASS static_t3
#|PASS static_t45
#|PASS static_t45b
#|PASS endturn_stone
#|PASS endturn_titan
#|PASS endturn_rootwarden_pair
#|PASS endturn_heart_pair
#|PASS endturn_no_growth
#|PASS choir_hand
#|PASS choir_cap
#|PASS bastion
#|PASS drummer_pair
#|PASS queen_plays3
#|PASS queen_cap
#|PASS queen_zero
#|PASS queen_any_tribe
#|PASS maelstrom
#|PASS worldroot_pair
#|PASS avalanche
#|PASS board_income
#|PASS roster_0_11
#|PASS roster_12_23
#|PASS roster_24_35
#|PASS card_count
#|PASS scout_make
#|PASS scout_full_hand
#|PASS scout_full_hand_mixed
#|PASS scout_twice
#|PASS matron_make
#|PASS matron_plays
#|PASS broker_sell_make
#|PASS broker_sell_full_hand
#|PASS broker_sell_full_hand_mixed
#|PASS oracle_make
#|PASS oracle_full_hand
#|PASS sovereign_make
#|PASS oracle_sovereign_two
#|PASS oracle_then_choir
#|PASS choir_then_oracle
#|PASS oracle_then_choir_h3
#|PASS choir_then_oracle_h3
#|PASS oracle_then_choir_cap
#|PASS oracle_full_then_choir
#|PASS sovereign_then_maelstrom
#|PASS maelstrom_then_sovereign
#|PASS hurt_shield_zero
#|PASS hurt_shield_before_armor
#|PASS hurt_armor1_absorbs
#|PASS hurt_armor1
#|PASS hurt_armor2
#|PASS hurt_armor2_worldroot
#|PASS hurt_armor_roster
#|PASS hurt_shield_armor_raw0
#|PASS hurt_shield_armor_dmg1
#|PASS hurt_shield_armor2_dmg1
#|PASS hurt_shield_then_armor_seq
#|PASS hurt_raw0_plain
#|PASS exchange_rally_armor
#|PASS exchange_rally_shield_armor
#|PASS exchange_rally_carried
#|PASS exchange_zero_attack_shield
#|PASS hurt_plain_overkill
#|PASS rally_values
#|PASS fight_rally_armor
#|PASS fight_rally_accumulates
#|PASS rally_not_persisted
#|PASS gold_buy_third
#|PASS gold_three_in_hand
#|PASS gold_hand_first_order
#|PASS gold_lowest_cid_first
#|PASS gold_full_hand_third
#|PASS gold_no_remerge
#|PASS gold_regulars_beside_golden
#|PASS gold_shield_or
#|PASS gold_play_boundary
#|PASS gold_endturn_no_merge
#|PASS gold_recruit_start
#|PASS gold_moth_board_income
#|PASS gold_tinker_gold
#|PASS gold_eel_play_sell
#|PASS gold_kindler_kin
#|PASS gold_tidecaller_hand
#|PASS gold_drillmaster_plays
#|PASS gold_apprentice_endturn
#|PASS gold_income
#|PASS gold_rally
#|PASS gold_armor_unscaled
#|PASS gold_shield_guard_once
#|PASS gold_sell_refund
#|PASS gold_scout_make_twice
#|PASS gold_fight_tier
#|PASS neutral_kin_skip
#|PASS neutral_no_kinplay
#|PASS neutral_kin_match
#|PASS shop_pools
#|PASS make_pools_no_neutral
#|PASS roster_36_43
#|PASS roster_36_43_golden
