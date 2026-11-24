# Bend Grounds: the pure rules engine. No IO, no @unsafe: every def here is
# total and checked. engine/main.bend wraps it in an HTTP server.
#
# Layout: cards, hashing RNG, players, actions, bots, combat, rounds,
# replay, JSON observation.
import Base
import ./econ.bend as Econ

# Types
# -----

type Abil is Data:
  Abil{trig: Nat, tgt: Nat, eff: Nat, a: Nat, h: Nat}

type Card is Data:
  Card{cid: Nat, name: String, tribe: Nat, tier: Nat, atk: Nat, hp: Nat, shield: Bool, guard: Bool, armor: Nat, rally: Nat, income: Nat, abils: List<&2, Abil>}

# golden: a unit assembled from three regular copies (see Golden below)
type Mon is Data:
  Mon{cid: Nat, atk: Nat, hp: Nat, shield: Bool, golden: Bool}

type Player is Data:
  Player{id: Nat, hp: Nat, gold: Nat, tier: Nat, upcost: Nat, invest: Nat, frozen: Bool, rolls: Nat, board: List<&2, Mon>, shop: List<&2, Nat>, alive: Bool, out: Nat, hand: List<&2, Mon>, plays: Nat}

type Fight is Data:
  Fight{round: Nat, a: Nat, b: Nat, res: Nat, dmg: Nat, aboard: List<&2, Mon>, bboard: List<&2, Mon>, log: List<&2, String>, events: List<&2, Ev>}

# a combat event: an attack (side True = seat a attacks; ti index of the
# target before; ai2/ti2 attacker/target index after; before/after lines
# of both seats; shield-break/death flags; rally gain; attack used), or
# the end (result, damage, reason, final lines)
type Ev is Data:
  EvAtk{step: Nat, side: Bool, ti: Nat, ai2: Nat, ti2: Nat, ba: List<&2, Mon>, bb: List<&2, Mon>, aa: List<&2, Mon>, ab: List<&2, Mon>, asb: Bool, tsb: Bool, ad: Bool, td: Bool, ral: Nat, aatk: Nat, text: String}
  EvEnd{step: Nat, res: Nat, dmg: Nat, why: Nat, aa: List<&2, Mon>, ab: List<&2, Mon>, text: String}

type Game is Data:
  Game{seed: U32, mode: Nat, round: Nat, actor: Nat, players: List<&2, Player>, fights: List<&2, Fight>, hist: List<&2, Fight>, done: Bool}

type Act is Data:
  Buy{i: Nat}
  Play{i: Nat}
  Sell{i: Nat}
  Swap{i: Nat, j: Nat}
  Roll{}
  Freeze{}
  Upgrade{}
  Invest{}
  End{}
  Auto{}

type PRes is Data:
  PGood{p: Player}
  PBad{msg: String}

type GRes is Data:
  GGood{g: Game}
  GBad{code: String, msg: String}

# Constants
# ---------

def max_rounds() -> Nat:
  14n

def start_hp() -> Nat:
  40n

def buy_cost() -> Nat:
  3n

def roll_cost() -> Nat:
  1n

def invest_cost() -> Nat:
  2n

def max_invest() -> Nat:
  3n

def sell_refund() -> Nat:
  1n

def max_tier() -> Nat:
  Econ.max_tier()

def shop_size() -> Nat:
  3n

def max_moves() -> Nat:
  1024n

def max_hand() -> Nat:
  7n

# protocol / schema version of the JSON observation and move language
def protocol_version() -> Nat:
  3n

def combat_fuel() -> Nat:
  80n

def bot_fuel() -> Nat:
  24n

# Small helpers
# -------------

def pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def nat_eq(a: Nat, b: Nat) -> Bool:
  Nat.is_eq(a, b)

def remove_at(-A: Data, xs: List<&2, A>, n: Nat) -> List<&2, A>:
  match xs n:
    case Nil{} _:
      Nil{}
    case h <> t 0n:
      t
    case h <> t 1n+p:
      h <> remove_at(A, t, p)

def snoc(-A: Data, xs: List<&2, A>, x: A) -> List<&2, A>:
  List.append(&2, A, xs, [x])

def len(-A: Data, xs: List<&2, A>) -> Nat:
  List.length(&2, A, xs)

def get_or(-A: Data, xs: List<&2, A>, n: Nat, d: A) -> A:
  Maybe.default(&2, A, List.get(&2, A, xs, n), d)

def swap_fin(-A: Data, xs: List<&2, A>, +i: Nat, +j: Nat, mi: Maybe<&2, A>, mj: Maybe<&2, A>) -> List<&2, A>:
  match mi mj:
    case Some{x} Some{y}:
      List.set(&2, A, List.set(&2, A, xs, i, y), j, x)
    case _ _:
      xs

def swap_at(-A: Data, +xs: List<&2, A>, +i: Nat, +j: Nat) -> List<&2, A>:
  swap_fin(A, xs, i, j, List.get(&2, A, xs, i), List.get(&2, A, xs, j))

def nat_sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(h, nat_sum(t))

# Cards
# -----
# A card is data: stats, static keywords (Shield, Guard, Armor, Rally,
# Income) and at most two abilities from one small generic table. The
# card text shown to players is generated from that data (card_text), so
# the wording cannot drift from what the engine does.
#
# Ability triggers: 0 PLAY (this card goes hand -> board), 1 KINPLAY (you
# play another card of this card's tribe while this is on the board),
# 2 ENDTURN (end of the recruit phase), 3 SELL (sold from the board).
# Targets: 0 SELF, 1 KIN (the other allies of the source's tribe).
# Effects: 0 STATS +a/+h, 1 STATS_HAND (+a/+h) x min(hand size, 4),
# 2 GOLD gain a gold, 3 MAKE add a random card of the source's tribe with
# tier <= a to the hand (nothing if the hand is full), 4 STATS_PLAYS
# (+a/+h) x min(cards played this recruit phase, 4); inside a play the
# count is the plays made before it (the resolving play is not counted).
#
# V3 roster (docs/V3-GROWTH.md): tier 1 is the v2 baseline; base stat
# budgets grow roughly geometrically (attack+health about 4/8/16/30/54 for
# tiers 1-5, utility bodies lower), Armor stays 0..2. Growth compounds
# through the same five effects: Ember chains plays (KINPLAY observers
# scaled by STATS_PLAYS), Tide holds a hand (STATS_HAND, refilled by
# MAKE), Stone grows every end of turn (ENDTURN KIN/SELF). The budgets are
# design targets for printed cards, not a bound on buffed units.

def ab(trig: Nat, tgt: Nat, eff: Nat, a: Nat, h: Nat) -> Abil:
  Abil{trig, tgt, eff, a, h}

def mk(cid: Nat, name: String, tribe: Nat, tier: Nat, atk: Nat, hp: Nat, sh: Bool, gu: Bool, armor: Nat, rally: Nat, inc: Nat, abils: List<&2, Abil>) -> Card:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, armor, rally, inc, abils}

def no_card() -> Card:
  Card{0n, "?", 0n, 1n, 0n, 0n, False{}, False{}, 0n, 0n, 0n, []}

# ids 0..35 are the tribe cards (sorted by tier), 36..43 the Neutral
# cards (tribe 3); pools filter by tier, never assume an id order.
# card(c) builds only the requested card (a match, not a list lookup).
def card(c: Nat) -> Card:
  match c:
    case 0n:
      mk(0n, "Spark Imp", 0n, 1n, 2n, 1n, False{}, False{}, 0n, 1n, 0n, [])
    case 1n:
      mk(1n, "Cinder Whelp", 0n, 1n, 1n, 2n, False{}, False{}, 0n, 0n, 0n, [ab(1n, 0n, 0n, 1n, 0n)])
    case 2n:
      mk(2n, "Kindler", 0n, 1n, 1n, 2n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 1n, 0n, 1n, 0n)])
    case 3n:
      mk(3n, "Purse Moth", 1n, 1n, 1n, 1n, False{}, False{}, 0n, 0n, 1n, [])
    case 4n:
      mk(4n, "Tide Pup", 1n, 1n, 1n, 2n, True{}, False{}, 0n, 0n, 0n, [ab(3n, 0n, 2n, 1n, 0n)])
    case 5n:
      mk(5n, "Shell Scout", 1n, 1n, 1n, 1n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 0n, 3n, 1n, 0n)])
    case 6n:
      mk(6n, "Pebble Guard", 2n, 1n, 1n, 3n, False{}, True{}, 0n, 0n, 0n, [])
    case 7n:
      mk(7n, "Moss Turtle", 2n, 1n, 1n, 3n, False{}, False{}, 1n, 0n, 0n, [])
    case 8n:
      mk(8n, "Root Sprout", 2n, 1n, 1n, 2n, False{}, False{}, 0n, 0n, 0n, [ab(2n, 0n, 0n, 0n, 1n)])
    case 9n:
      mk(9n, "Ember Herald", 0n, 2n, 3n, 3n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 1n, 0n, 2n, 1n)])
    case 10n:
      mk(10n, "Flame Dancer", 0n, 2n, 3n, 4n, False{}, False{}, 0n, 0n, 0n, [ab(1n, 0n, 0n, 2n, 1n)])
    case 11n:
      mk(11n, "Blaze Charger", 0n, 2n, 4n, 4n, False{}, False{}, 0n, 2n, 0n, [])
    case 12n:
      mk(12n, "Reef Warden", 1n, 2n, 3n, 3n, True{}, False{}, 0n, 0n, 0n, [ab(0n, 1n, 0n, 1n, 2n)])
    case 13n:
      mk(13n, "Tidecaller", 1n, 2n, 3n, 3n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 0n, 1n, 1n, 1n)])
    case 14n:
      mk(14n, "Coin Eel", 1n, 2n, 3n, 3n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 0n, 2n, 1n, 0n), ab(3n, 0n, 2n, 1n, 0n)])
    case 15n:
      mk(15n, "Boulder Ox", 2n, 2n, 3n, 5n, False{}, True{}, 0n, 0n, 0n, [])
    case 16n:
      mk(16n, "Cairn Mason", 2n, 2n, 2n, 5n, False{}, True{}, 1n, 0n, 0n, [])
    case 17n:
      mk(17n, "Rootwarden", 2n, 2n, 3n, 3n, False{}, False{}, 0n, 0n, 0n, [ab(2n, 1n, 0n, 0n, 2n)])
    case 18n:
      mk(18n, "Inferno Drake", 0n, 3n, 6n, 6n, False{}, False{}, 0n, 0n, 0n, [ab(1n, 1n, 0n, 1n, 1n)])
    case 19n:
      mk(19n, "Ash Phoenix", 0n, 3n, 8n, 6n, True{}, False{}, 0n, 3n, 0n, [])
    case 20n:
      mk(20n, "Storm Siren", 1n, 3n, 5n, 7n, True{}, False{}, 0n, 0n, 0n, [ab(0n, 1n, 1n, 1n, 1n)])
    case 21n:
      mk(21n, "Tide Oracle", 1n, 3n, 4n, 8n, False{}, False{}, 0n, 0n, 1n, [ab(2n, 0n, 3n, 2n, 0n)])
    case 22n:
      mk(22n, "Granite Titan", 2n, 3n, 5n, 11n, False{}, True{}, 1n, 0n, 0n, [ab(2n, 0n, 0n, 1n, 2n)])
    case 23n:
      mk(23n, "Mountain Heart", 2n, 3n, 5n, 8n, False{}, False{}, 0n, 0n, 0n, [ab(2n, 1n, 0n, 1n, 1n)])
    case 24n:
      mk(24n, "Pyre Captain", 0n, 4n, 10n, 12n, False{}, False{}, 0n, 0n, 0n, [ab(1n, 1n, 4n, 1n, 1n)])
    case 25n:
      mk(25n, "Kiln Matron", 0n, 4n, 12n, 10n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 0n, 3n, 3n, 0n), ab(0n, 0n, 4n, 2n, 1n)])
    case 26n:
      mk(26n, "Pearl Broker", 1n, 4n, 10n, 12n, False{}, False{}, 0n, 0n, 1n, [ab(3n, 0n, 3n, 4n, 0n)])
    case 27n:
      mk(27n, "Abyss Choir", 1n, 4n, 10n, 14n, False{}, False{}, 0n, 0n, 0n, [ab(2n, 0n, 1n, 2n, 2n)])
    case 28n:
      mk(28n, "Basalt Bastion", 2n, 4n, 8n, 18n, False{}, True{}, 2n, 0n, 0n, [ab(2n, 0n, 0n, 1n, 3n)])
    case 29n:
      mk(29n, "Quarry Drummer", 2n, 4n, 12n, 12n, False{}, False{}, 0n, 0n, 0n, [ab(2n, 1n, 0n, 2n, 1n)])
    case 30n:
      mk(30n, "Sunfire Tyrant", 0n, 5n, 20n, 16n, False{}, False{}, 0n, 3n, 0n, [ab(1n, 1n, 4n, 2n, 1n)])
    case 31n:
      mk(31n, "Cinder Queen", 0n, 5n, 18n, 18n, True{}, False{}, 0n, 0n, 0n, [ab(2n, 1n, 4n, 2n, 2n)])
    case 32n:
      mk(32n, "Maelstrom Queen", 1n, 5n, 16n, 22n, True{}, False{}, 0n, 0n, 0n, [ab(2n, 1n, 1n, 2n, 2n)])
    case 33n:
      mk(33n, "Tidal Sovereign", 1n, 5n, 16n, 24n, False{}, False{}, 0n, 0n, 2n, [ab(2n, 0n, 3n, 4n, 0n), ab(2n, 0n, 1n, 2n, 2n)])
    case 34n:
      mk(34n, "Worldroot", 2n, 5n, 14n, 30n, False{}, True{}, 2n, 0n, 0n, [ab(2n, 1n, 0n, 2n, 4n)])
    case 35n:
      mk(35n, "Avalanche Lord", 2n, 5n, 26n, 22n, False{}, False{}, 1n, 0n, 0n, [ab(2n, 1n, 0n, 3n, 1n)])
    case 36n:
      mk(36n, "Tin Sentry", 3n, 1n, 1n, 3n, False{}, True{}, 0n, 0n, 0n, [])
    case 37n:
      mk(37n, "Copper Tinker", 3n, 1n, 1n, 1n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 0n, 2n, 1n, 0n)])
    case 38n:
      mk(38n, "Iron Apprentice", 3n, 2n, 3n, 3n, False{}, False{}, 0n, 0n, 0n, [ab(2n, 0n, 0n, 1n, 1n)])
    case 39n:
      mk(39n, "Bounty Clerk", 3n, 2n, 2n, 4n, False{}, False{}, 0n, 0n, 1n, [])
    case 40n:
      mk(40n, "Siege Ram", 3n, 3n, 12n, 3n, False{}, False{}, 0n, 0n, 0n, [])
    case 41n:
      mk(41n, "Mirror Warden", 3n, 3n, 5n, 9n, True{}, True{}, 0n, 0n, 0n, [])
    case 42n:
      mk(42n, "Brass Drillmaster", 3n, 4n, 10n, 12n, False{}, False{}, 0n, 0n, 0n, [ab(0n, 0n, 4n, 2n, 2n)])
    case 43n:
      mk(43n, "Grand Artificer", 3n, 5n, 18n, 20n, False{}, False{}, 0n, 1n, 0n, [ab(2n, 0n, 0n, 3n, 3n)])
    case 44n+k:
      no_card()

def card_count() -> Nat:
  44n

def map_card(ids: List<&2, Nat>) -> List<&2, Card>:
  match ids:
    case Nil{}:
      Nil{}
    case i <> t:
      card(i) <> map_card(t)

def card_list() -> List<&2, Card>:
  map_card(List.range(card_count()))

def cd_cid(k: Card) -> Nat:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  cid

def cd_name(k: Card) -> String:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  name

def cd_tribe(k: Card) -> Nat:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  tribe

def cd_tier(k: Card) -> Nat:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  tier

def cd_guard(k: Card) -> Bool:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  gu

def cd_armor(k: Card) -> Nat:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  ar

def cd_rally(k: Card) -> Nat:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  ra

def cd_income(k: Card) -> Nat:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  inc

def cd_abils(k: Card) -> List<&2, Abil>:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  abils

def c_name(c: Nat) -> String:
  cd_name(card(c))

def c_tribe(c: Nat) -> Nat:
  cd_tribe(card(c))

def c_tier(c: Nat) -> Nat:
  cd_tier(card(c))

def c_guard(c: Nat) -> Bool:
  cd_guard(card(c))

def c_armor(c: Nat) -> Nat:
  cd_armor(card(c))

def c_rally(c: Nat) -> Nat:
  cd_rally(card(c))

def c_income(c: Nat) -> Nat:
  cd_income(card(c))

def c_abils(c: Nat) -> List<&2, Abil>:
  cd_abils(card(c))

# tribes 0 Ember, 1 Tide, 2 Stone; 3 Neutral belongs to no tribe
def tribe_name(t: Nat) -> String:
  get_or(String, ["Ember", "Tide", "Stone"], t, "Neutral")

def neutral() -> Nat:
  3n

# a tribe mechanic (KIN, After-you-play, MAKE) of tribe tr applies to a
# unit of tribe t: same tribe, and never Neutral (not even to itself)
def kin_match(+t: Nat, +tr: Nat) -> Bool:
  nat_eq(t, tr) && Nat.is_lt(tr, neutral())

def mon_of_card(k: Card) -> Mon:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  Mon{cid, atk, hp, sh, False{}}

def mon_of(c: Nat) -> Mon:
  mon_of_card(card(c))

def mon_cid(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  c

def mon_tier(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  c_tier(c)

def mon_tribe(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  c_tribe(c)

def mon_guard(m: Mon) -> Bool:
  Mon{c, a, h, s, g} = m
  c_guard(c)

def mon_golden(m: Mon) -> Bool:
  Mon{c, a, h, s, g} = m
  g

# Golden scaling: a golden unit doubles its amounts (ability stats and
# gold, Rally, Income); MAKE keeps its tier bound and fires twice; Armor,
# Shield, Guard and the sell refund are not scaled.
def dbl(gd: Bool, +n: Nat) -> Nat:
  match gd:
    case True{}:
      Nat.add(n, n)
    case False{}:
      n

def scale_abil(gd: Bool, x: Abil) -> Abil:
  match gd:
    case True{}:
      Abil{+trig, +tgt, +eff, +a, +h} = x
      pick(Abil, nat_eq(eff, 3n), Abil{trig, tgt, eff, a, h}, Abil{trig, tgt, eff, Nat.add(a, a), Nat.add(h, h)})
    case False{}:
      x

def scale_abils(+gd: Bool, xs: List<&2, Abil>) -> List<&2, Abil>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      scale_abil(gd, x) <> scale_abils(gd, t)

# the effective (golden-scaled) abilities, Rally, Income and Armor of a unit
def mon_abils(m: Mon) -> List<&2, Abil>:
  Mon{c, a, h, s, g} = m
  scale_abils(g, c_abils(c))

def mon_rally(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  dbl(g, c_rally(c))

def mon_income(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  dbl(g, c_income(c))

def mon_armor(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  c_armor(c)

# card value used by bots: tier first, then stats
def mon_score(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  Nat.add(Nat.mul(c_tier(c), 10n), Nat.add(a, h))

def card_score(c: Nat) -> Nat:
  mon_score(mon_of(c))

# Generated card text
# -------------------

def stats_text(+a: Nat, +h: Nat) -> String:
  pick(String, nat_eq(h, 0n), "+" ++ Nat.show(a) ++ " attack", pick(String, nat_eq(a, 0n), "+" ++ Nat.show(h) ++ " health", "+" ++ Nat.show(a) ++ "/+" ++ Nat.show(h)))

def trig_text(t: Nat, +tribe: String) -> String:
  match t:
    case 0n:
      "Play:"
    case 1n+u:
      match u:
        case 0n:
          "After you play another " ++ tribe ++ " card:"
        case 1n+v:
          pick(String, nat_eq(v, 0n), "End of turn:", "Sell:")

def tgt_text(t: Nat, +tribe: String) -> String:
  pick(String, nat_eq(t, 0n), "gain", "give other " ++ tribe ++ " allies")

# STATS_PLAYS counts the plays made BEFORE the resolving one: a Play or
# After-you-play ability resolves inside a play, before its own count is
# added; at end of turn every play of the turn has been counted.
def plays_text(+trig: Nat) -> String:
  pick(String, Nat.is_lt(trig, 2n), " for each card you played earlier this turn (max 4)", " for each card you played this turn (max 4)")

def make_text(+gd: Bool, +tribe: String, +a: Nat) -> String:
  pick(String, gd, "add 2 random " ++ tribe ++ " cards of tier " ++ Nat.show(a) ++ " or lower to your hand (each if it has room)", "add a random " ++ tribe ++ " card of tier " ++ Nat.show(a) ++ " or lower to your hand (if it has room)")

def eff_text(e: Nat, +trig: Nat, +tgt: String, +tribe: String, +a: Nat, +h: Nat, +gd: Bool) -> String:
  match e:
    case 0n:
      tgt ++ " " ++ stats_text(a, h)
    case 1n+u:
      match u:
        case 0n:
          tgt ++ " " ++ stats_text(a, h) ++ " for each card in your hand (max 4)"
        case 1n+v:
          match v:
            case 0n:
              "gain " ++ Nat.show(a) ++ " gold"
            case 1n+w:
              pick(String, nat_eq(w, 0n), make_text(gd, tribe, a), tgt ++ " " ++ stats_text(a, h) ++ plays_text(trig))

# x: an effective ability (already golden-scaled); gd: the source is golden
def abil_text_g(+gd: Bool, +tribe: String, x: Abil) -> String:
  Abil{+trig, tgt, eff, a, h} = x
  trig_text(trig, tribe) ++ " " ++ eff_text(eff, trig, tgt_text(tgt, tribe), tribe, a, h, gd) ++ "."

def abil_text(+tribe: String, x: Abil) -> String:
  abil_text_g(False{}, tribe, x)

def abils_text_g(+gd: Bool, +tribe: String, xs: List<&2, Abil>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      abil_text_g(gd, tribe, x) <> abils_text_g(gd, tribe, t)

def abils_text(+tribe: String, xs: List<&2, Abil>) -> List<&2, String>:
  abils_text_g(False{}, tribe, xs)

def kw_list(sh: Bool, gu: Bool, +ar: Nat, +ra: Nat, +inc: Nat) -> List<&2, String>:
  +g = pick(List<&2, String>, gu, ["Guard"], Nil{})
  +s = pick(List<&2, String>, sh, ["Shield"], Nil{})
  +r = pick(List<&2, String>, nat_eq(ar, 0n), Nil{}, ["Armor " ++ Nat.show(ar)])
  +y = pick(List<&2, String>, nat_eq(ra, 0n), Nil{}, ["Rally " ++ Nat.show(ra)])
  +i = pick(List<&2, String>, nat_eq(inc, 0n), Nil{}, ["Income " ++ Nat.show(inc)])
  List.append(&2, String, g, List.append(&2, String, s, List.append(&2, String, r, List.append(&2, String, y, i))))

# keywords of a card, or of a golden unit of it (Rally and Income doubled)
def card_keywords_g(+gd: Bool, k: Card) -> List<&2, String>:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  kw_list(sh, gu, ar, dbl(gd, ra), dbl(gd, inc))

def card_keywords(k: Card) -> List<&2, String>:
  card_keywords_g(False{}, k)

def kw_dots(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      (x ++ ".") <> kw_dots(t)

# the generated text of a card, or of a golden unit of it (effective values)
def card_text_g(+gd: Bool, +k: Card) -> String:
  String.join(List.append(&2, String, kw_dots(card_keywords_g(gd, k)), abils_text_g(gd, tribe_name(cd_tribe(k)), scale_abils(gd, cd_abils(k)))), " ")

def card_text(+k: Card) -> String:
  card_text_g(False{}, k)

# Deterministic hashing RNG
# -------------------------
# Every random draw is a pure hash of (seed, purpose, indices), so a
# player's rolls never shift another seat's shop or a combat.

def mix(+x: U32) -> U32:
  +a = U32.mul(U32.xor(x, (x >> 16n : U32)), 73244475)
  +b = U32.mul(U32.xor(a, (a >> 16n : U32)), 73244475)
  U32.xor(b, (b >> 16n : U32))

def hash_list(xs: List<&2, Nat>, h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case x <> t:
      hash_list(t, mix(U32.add(U32.xor(h, U32.from_nat(x)), 2654435769)))

def hash(seed: U32, xs: List<&2, Nat>) -> U32:
  hash_list(xs, mix(U32.add(seed, 1013904223)))

# a number in [0, n), n > 0
def below(h: U32, +n: Nat) -> Nat:
  U32.to_nat(U32.mod(h, U32.from_nat(n)))

# Shops
# -----

def count_le(xs: List<&2, Card>, +tier: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case k <> t:
      Nat.add(pick(Nat, Nat.is_le(cd_tier(k), tier), 1n, 0n), count_le(t, tier))

# the ids of every card with tier <= tier, ascending (any tribe)
def elig_go(xs: List<&2, Card>, +tier: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +k <> t:
      +r = elig_go(t, tier)
      pick(List<&2, Nat>, Nat.is_le(cd_tier(k), tier), cd_cid(k) <> r, r)

def shop_pool(+tier: Nat) -> List<&2, Nat>:
  elig_go(card_list(), tier)

def pool_size(+tier: Nat) -> Nat:
  count_le(card_list(), tier)

# each slot draws an index into the eligible-id list (ids are not sorted
# by tier, so a raw id below the pool size would not be eligible)
def shop_go(+seed: U32, +seat: Nat, +round: Nat, +rolls: Nat, +pool: List<&2, Nat>, +slot: Nat) -> List<&2, Nat>:
  match slot:
    case 0n:
      Nil{}
    case 1n+s:
      get_or(Nat, pool, below(hash(seed, [1n, seat, round, rolls, s]), Nat.max(len(Nat, pool), 1n)), 0n) <> shop_go(seed, seat, round, rolls, pool, s)

def make_shop(+seed: U32, +seat: Nat, +round: Nat, +rolls: Nat, +tier: Nat) -> List<&2, Nat>:
  shop_go(seed, seat, round, rolls, shop_pool(tier), shop_size())

# Players
# -------

def new_player(+seed: U32, +i: Nat) -> Player:
  Player{i, start_hp(), Econ.income(1n, 0n, 0n), 1n, Econ.upgrade_base(1n), 0n, False{}, 0n, Nil{}, make_shop(seed, i, 1n, 0n, 1n), True{}, 0n, Nil{}, 0n}

def p_alive(p: Player) -> Bool:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  alive

def p_hp(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  hp

def p_tier(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  tier

def p_board(p: Player) -> List<&2, Mon>:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  board

def p_hand(p: Player) -> List<&2, Mon>:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  hand

def p_plays(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  plays

def p_out(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  out

def p_set_board(p: Player, nb: List<&2, Mon>) -> Player:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, nb, shop, alive, out, hand, plays}

def no_player() -> Player:
  Player{99n, 0n, 0n, 1n, 0n, 0n, False{}, 0n, Nil{}, Nil{}, False{}, 0n, Nil{}, 0n}

def pget(ps: List<&2, Player>, k: Nat) -> Player:
  get_or(Player, ps, k, no_player())

def pset(ps: List<&2, Player>, k: Nat, p: Player) -> List<&2, Player>:
  List.set(&2, Player, ps, k, p)

# income bonus from Income units on a board
def board_income(b: List<&2, Mon>) -> Nat:
  match b:
    case Nil{}:
      0n
    case m <> t:
      Nat.add(mon_income(m), board_income(t))

def board_tiers(b: List<&2, Mon>) -> List<&2, Nat>:
  match b:
    case Nil{}:
      Nil{}
    case m <> t:
      mon_tier(m) <> board_tiers(t)

# Player actions
# --------------
# Each answers PGood with the new player or PBad with the reason.

# hand has room for another card (hand max 7)
def hand_room(n: Nat) -> Bool:
  Nat.is_lt(n, max_hand())

# Abilities
# ---------
# One interpreter runs every ability. It works on an effect context: the
# board, the source card when it is not on the board (a card being played
# or sold), the hand and the gold. Stat effects only ever add (Nat.add) to
# attack/health and keep each unit's card id; board passes are maps, so
# they never change the board length. MAKE is the only effect that adds a
# card, and it goes through hand_add, the single guarded hand insertion.
# No effect plays, sells or buys, so an ability never fires another one.

type Fx is Data:
  Fx{board: List<&2, Mon>, me: Mon, hand: List<&2, Mon>, gold: Nat, plays: Nat}

# "SELF" index of a source that is not on the board (played or sold card)
def entering() -> Nat:
  99n

def fx_board(fx: Fx) -> List<&2, Mon>:
  Fx{board, me, hand, gold, plays} = fx
  board

def fx_plays(fx: Fx) -> Nat:
  Fx{board, me, hand, gold, plays} = fx
  plays

def fx_hand(fx: Fx) -> List<&2, Mon>:
  Fx{board, me, hand, gold, plays} = fx
  hand

def abil_trig(x: Abil) -> Nat:
  Abil{trig, tgt, eff, a, h} = x
  trig

def mon_add(+da: Nat, +dh: Nat, m: Mon) -> Mon:
  Mon{c, a, h, s, g} = m
  Mon{c, Nat.add(a, da), Nat.add(h, dh), s, g}

# KIN: every unit of tribe tr except the one at board index skip (never
# a Neutral unit, and a Neutral source has no KIN)
def kin_go(b: List<&2, Mon>, +tr: Nat, +skip: Nat, +pos: Nat, +da: Nat, +dh: Nat) -> List<&2, Mon>:
  match b:
    case Nil{}:
      Nil{}
    case +m <> t:
      pick(Mon, kin_match(mon_tribe(m), tr) && Bool.not(nat_eq(pos, skip)), mon_add(da, dh, m), m) <> kin_go(t, tr, skip, 1n+pos, da, dh)

# SELF of a board unit: the unit at board index k
def at_go(b: List<&2, Mon>, +k: Nat, +pos: Nat, +da: Nat, +dh: Nat) -> List<&2, Mon>:
  match b:
    case Nil{}:
      Nil{}
    case +m <> t:
      pick(Mon, nat_eq(pos, k), mon_add(da, dh, m), m) <> at_go(t, k, 1n+pos, da, dh)

def fx_self(on_board: Bool, +src: Nat, +da: Nat, +dh: Nat, fx: Fx) -> Fx:
  match on_board:
    case True{}:
      Fx{board, me, hand, gold, plays} = fx
      Fx{at_go(board, src, 0n, da, dh), me, hand, gold, plays}
    case False{}:
      Fx{board, me, hand, gold, plays} = fx
      Fx{board, mon_add(da, dh, me), hand, gold, plays}

def fx_stats(tgt: Nat, +src: Nat, +tr: Nat, +da: Nat, +dh: Nat, fx: Fx) -> Fx:
  match tgt:
    case 0n:
      fx_self(Bool.not(nat_eq(src, entering())), src, da, dh, fx)
    case 1n+u:
      Fx{board, me, hand, gold, plays} = fx
      Fx{kin_go(board, tr, src, 0n, da, dh), me, hand, gold, plays}

# the only way a card enters a hand: refused (unchanged) when full
def hand_put(room: Bool, +hand: List<&2, Mon>, m: Mon) -> List<&2, Mon>:
  match room:
    case True{}:
      snoc(Mon, hand, m)
    case False{}:
      hand

def hand_add(+hand: List<&2, Mon>, m: Mon) -> List<&2, Mon>:
  hand_put(hand_room(len(Mon, hand)), hand, m)

def make_pool(xs: List<&2, Card>, +tr: Nat, +tier: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +k <> t:
      +r = make_pool(t, tr, tier)
      pick(List<&2, Nat>, kin_match(cd_tribe(k), tr) && Nat.is_le(cd_tier(k), tier), mon_cid(mon_of_card(k)) <> r, r)

def make_pick(+n: Nat, +pool: List<&2, Nat>, +h: U32) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+q:
      Some{get_or(Nat, pool, below(h, 1n+q), 0n)}

def hand_maybe(mc: Maybe<&2, Nat>, +hand: List<&2, Mon>) -> List<&2, Mon>:
  match mc:
    case None{}:
      hand
    case Some{c}:
      hand_add(hand, mon_of(c))

def fx_make(+seed: U32, +key: List<&2, Nat>, +tr: Nat, +tier: Nat, fx: Fx) -> Fx:
  Fx{board, me, hand, gold, plays} = fx
  +pool = make_pool(card_list(), tr, tier)
  Fx{board, me, hand_maybe(make_pick(len(Nat, pool), pool, hash(seed, key)), hand), gold, plays}

def fx_gold(+g: Nat, fx: Fx) -> Fx:
  Fx{board, me, hand, gold, plays} = fx
  Fx{board, me, hand, Nat.add(gold, g), plays}

# a golden source's MAKE fires twice: the regular key, then key ++ [1]
def fx_make_n(gd: Bool, +seed: U32, +key: List<&2, Nat>, +tr: Nat, +tier: Nat, fx: Fx) -> Fx:
  match gd:
    case True{}:
      fx_make(seed, snoc(Nat, key, 1n), tr, tier, fx_make(seed, key, tr, tier, fx))
    case False{}:
      fx_make(seed, key, tr, tier, fx)

# x: an effective ability (golden amounts already doubled by mon_abils);
# gd: the source is golden (only MAKE reads it)
def fx_abil(+seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, x: Abil, +fx: Fx) -> Fx:
  Abil{trig, tgt, eff, +a, +h} = x
  match eff:
    case 0n:
      fx_stats(tgt, src, tr, a, h, fx)
    case 1n+u:
      match u:
        case 0n:
          +k = Nat.min(len(Mon, fx_hand(fx)), 4n)
          fx_stats(tgt, src, tr, Nat.mul(a, k), Nat.mul(h, k), fx)
        case 1n+v:
          match v:
            case 0n:
              fx_gold(a, fx)
            case 1n+w:
              match w:
                case 0n:
                  fx_make_n(gd, seed, key, tr, a, fx)
                case 1n+z:
                  +k = Nat.min(fx_plays(fx), 4n)
                  fx_stats(tgt, src, tr, Nat.mul(a, k), Nat.mul(h, k), fx)

def fx_if(ok: Bool, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, x: Abil, +fx: Fx) -> Fx:
  match ok:
    case True{}:
      fx_abil(seed, key, src, tr, gd, x, fx)
    case False{}:
      fx

# fire, in list order, the abilities of a source that have trigger want
def fx_abils(xs: List<&2, Abil>, +want: Nat, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, +slot: Nat, fx: Fx) -> Fx:
  match xs:
    case Nil{}:
      fx
    case +x <> t:
      fx_abils(t, want, seed, key, src, tr, gd, 1n+slot, fx_if(nat_eq(abil_trig(x), want), seed, snoc(Nat, key, slot), src, tr, gd, x, fx))

def fx_when(ok: Bool, xs: List<&2, Abil>, +want: Nat, +seed: U32, +key: List<&2, Nat>, +src: Nat, +tr: Nat, +gd: Bool, +fx: Fx) -> Fx:
  match ok:
    case True{}:
      fx_abils(xs, want, seed, key, src, tr, gd, 0n, fx)
    case False{}:
      fx

# KINPLAY observers: left to right over the units that were on the board
# before the play (indexes 0..fuel-1); each reads its current stats.
def observe(fuel: Nat, +pos: Nat, +seed: U32, +key: List<&2, Nat>, +tr: Nat, +fx: Fx) -> Fx:
  match fuel:
    case 0n:
      fx
    case 1n+f:
      +u = get_or(Mon, fx_board(fx), pos, mon_of(0n))
      observe(f, 1n+pos, seed, key, tr, fx_when(kin_match(mon_tribe(u), tr), mon_abils(u), 1n, seed, snoc(Nat, key, pos), pos, tr, mon_golden(u), fx))

# ENDTURN: left to right over the board, each unit on the current board
def endturn(fuel: Nat, +pos: Nat, +seed: U32, +key: List<&2, Nat>, +fx: Fx) -> Fx:
  match fuel:
    case 0n:
      fx
    case 1n+f:
      +u = get_or(Mon, fx_board(fx), pos, mon_of(0n))
      endturn(f, 1n+pos, seed, key, fx_abils(mon_abils(u), 2n, seed, snoc(Nat, key, pos), pos, mon_tribe(u), mon_golden(u), 0n, fx))

# the played card joins the right end of the board
def fx_enter(fx: Fx) -> Fx:
  Fx{board, +me, hand, gold, plays} = fx
  Fx{snoc(Mon, board, me), me, hand, gold, plays}

# play resolution: (a) the card's PLAY abilities (SELF = the card, KIN =
# its tribe on the prior board); (b) it joins the board; (c) KINPLAY
# observers among the prior units of its tribe (SELF = observer, KIN =
# the observer's other tribe allies, including the new card).
# MAKE keys: [10, seat, round, plays, slot] for PLAY, [13, seat, round,
# plays, pos, slot] for observers.
def play_fx(+seed: U32, +id: Nat, +round: Nat, +plays: Nat, +m: Mon, +board: List<&2, Mon>, hand: List<&2, Mon>, gold: Nat) -> Fx:
  +tr = mon_tribe(m)
  +f1 = fx_abils(mon_abils(m), 0n, seed, [10n, id, round, plays], entering(), tr, mon_golden(m), 0n, Fx{board, m, hand, gold, plays})
  observe(len(Mon, board), 0n, seed, [13n, id, round, plays], tr, fx_enter(f1))


# Golden
# ------
# Three regular (non-golden) copies of one card among your hand and board
# assemble into one golden unit. The check runs after every accepted buy,
# play and sell and at the start of each recruit phase (copies an
# end-of-turn MAKE added merge then), never inside an ability pass. Each
# merge takes the lowest card id with 3+ copies, consumes exactly 3 of
# them (hand left to right first, then board left to right) and puts the
# golden unit at the right end of the hand; if no hand copy was consumed
# (not reachable: new copies always arrive in the hand) it takes the board
# slot of the first board copy instead. So a merge never grows the hand or
# the board. At most 4 merges per check.
# Golden stats: the sum of the three copies minus one printed card, i.e.
# twice the printed stats plus every buff the copies had; Shield if any
# copy had it.

type Take is Data:
  Take{rest: List<&2, Mon>, got: List<&2, Mon>}

type HB is Data:
  HB{hand: List<&2, Mon>, board: List<&2, Mon>}

def is_copy(+c: Nat, m: Mon) -> Bool:
  Mon{mc, a, h, s, g} = m
  nat_eq(mc, c) && Bool.not(g)

def copies(xs: List<&2, Mon>, +c: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +m <> t:
      Nat.add(pick(Nat, is_copy(c, m), 1n, 0n), copies(t, c))

def tri_better(+c: Nat, b: Maybe<&2, Nat>) -> Bool:
  match b:
    case None{}:
      True{}
    case Some{d}:
      Nat.is_lt(c, d)

# the lowest card id with at least 3 regular copies in all (hand ++ board)
def tri_best(xs: List<&2, Mon>, +all: List<&2, Mon>, +best: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      best
    case +m <> t:
      +c = mon_cid(m)
      +ok = is_copy(c, m) && Nat.is_ge(copies(all, c), 3n) && tri_better(c, best)
      tri_best(t, all, pick(Maybe<&2, Nat>, ok, Some{c}, best))

def triple_of(+hand: List<&2, Mon>, +board: List<&2, Mon>) -> Maybe<&2, Nat>:
  +all = List.append(&2, Mon, hand, board)
  tri_best(all, all, None{})

def take_got(m: Mon, r: Take) -> Take:
  Take{rest, got} = r
  Take{rest, m <> got}

def take_kept(m: Mon, r: Take) -> Take:
  Take{rest, got} = r
  Take{m <> rest, got}

def take_rest(r: Take) -> List<&2, Mon>:
  Take{rest, got} = r
  rest

def take_taken(r: Take) -> List<&2, Mon>:
  Take{rest, got} = r
  got

# the first n regular copies of c, left to right, and the rest in order
def take(xs: List<&2, Mon>, +c: Nat, n: Nat) -> Take:
  match xs n:
    case Nil{} _:
      Take{Nil{}, Nil{}}
    case h <> t 0n:
      Take{h <> t, Nil{}}
    case +h <> t 1n+(+k):
      +hit = is_copy(c, h)
      +r = take(t, c, pick(Nat, hit, k, 1n+k))
      pick(Take, hit, take_got(h, r), take_kept(h, r))

def first_copy(xs: List<&2, Mon>, +c: Nat, +pos: Nat) -> Nat:
  match xs:
    case Nil{}:
      pos
    case +m <> t:
      pick(Nat, is_copy(c, m), pos, first_copy(t, c, 1n+pos))

def insert_at(-A: Data, xs: List<&2, A>, n: Nat, x: A) -> List<&2, A>:
  match xs n:
    case Nil{} _:
      [x]
    case h <> t 0n:
      x <> h <> t
    case h <> t 1n+q:
      h <> insert_at(A, t, q, x)

def sum_atk(xs: List<&2, Mon>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case m <> t:
      Mon{c, a, h, s, g} = m
      Nat.add(a, sum_atk(t))

def sum_hp(xs: List<&2, Mon>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case m <> t:
      Mon{c, a, h, s, g} = m
      Nat.add(h, sum_hp(t))

def any_shield(xs: List<&2, Mon>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case m <> t:
      Mon{c, a, h, s, g} = m
      s || any_shield(t)

def fuse(+c: Nat, +got: List<&2, Mon>) -> Mon:
  Mon{c, Nat.sub(sum_atk(got), sum_atk([mon_of(c)])), Nat.sub(sum_hp(got), sum_hp([mon_of(c)])), any_shield(got), True{}}

def merge_hb(+c: Nat, +hand: List<&2, Mon>, +board: List<&2, Mon>) -> HB:
  +fi = first_copy(board, c, 0n)
  +th = take(hand, c, 3n)
  +rh = take_rest(th)
  +gh = take_taken(th)
  +nh = len(Mon, gh)
  +tb = take(board, c, Nat.sub(3n, nh))
  +rb = take_rest(tb)
  +gb = take_taken(tb)
  +gm = fuse(c, List.append(&2, Mon, gh, gb))
  pick(HB, Nat.is_gt(nh, 0n), HB{snoc(Mon, rh, gm), rb}, HB{rh, insert_at(Mon, rb, fi, gm)})

def merge_fin(hb: HB, +p: Player) -> Player:
  HB{nh, nb} = hb
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, nb, shop, alive, out, nh, plays}

def merge_p(+c: Nat, +p: Player) -> Player:
  merge_fin(merge_hb(c, p_hand(p), p_board(p)), p)

def norm_go(fuel: Nat, mc: Maybe<&2, Nat>, +p: Player) -> Player:
  match fuel mc:
    case _ None{}:
      p
    case 0n Some{c}:
      p
    case 1n+f Some{c}:
      +q = merge_p(c, p)
      norm_go(f, triple_of(p_hand(q), p_board(q)), q)

# assemble every triple (at most 4 merges)
def p_norm(+p: Player) -> Player:
  norm_go(4n, triple_of(p_hand(p), p_board(p)), p)

# buy: pay 3, the shop card goes to the right end of the hand. The board
# and every unit on it are untouched; effects happen on play.
def buy_apply(+p: Player, +i: Nat, +c: Nat, +g: Nat) -> Player:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, hp, g, tier, upcost, invest, frozen, rolls, board, remove_at(Nat, shop, i), alive, out, hand_add(hand, mon_of(c)), plays}

def buy_go(mc: Maybe<&2, Nat>, room: Bool, mg: Maybe<&2, Nat>, +p: Player, +i: Nat) -> PRes:
  match mc room mg:
    case None{} _ _:
      PBad{"no shop card at that index"}
    case Some{c} False{} _:
      PBad{"hand is full (max 7 cards)"}
    case Some{c} True{} None{}:
      PBad{"not enough gold to buy (costs 3)"}
    case Some{c} True{} Some{g}:
      PGood{p_norm(buy_apply(p, i, c, g))}

def p_buy(+p: Player, +i: Nat) -> PRes:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  buy_go(List.get(&2, Nat, shop, i), hand_room(len(Mon, hand)), Econ.spend(gold, buy_cost()), p, i)

# play: hand card i leaves the hand and resolves (play_fx); plays + 1
def play_fin(fx: Fx, +p: Player) -> Player:
  Fx{nb, me, nh, ng, np} = fx
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, hp, ng, tier, upcost, invest, frozen, rolls, nb, shop, alive, out, nh, 1n+plays}

def play_apply(+seed: U32, +round: Nat, +p: Player, +i: Nat, +m: Mon) -> Player:
  Player{+id, hp, +gold, tier, upcost, invest, frozen, rolls, +board, shop, alive, out, +hand, +plays} = p
  play_fin(play_fx(seed, id, round, plays, m, board, remove_at(Mon, hand, i), gold), p)

def play_go(mm: Maybe<&2, Mon>, room: Bool, +seed: U32, +round: Nat, +p: Player, +i: Nat) -> PRes:
  match mm room:
    case None{} _:
      PBad{"no hand card at that index"}
    case Some{m} False{}:
      PBad{"board is full (max 5 units)"}
    case Some{m} True{}:
      PGood{p_norm(play_apply(seed, round, p, i, m))}

def p_play(+seed: U32, +round: Nat, +p: Player, +i: Nat) -> PRes:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  play_go(List.get(&2, Mon, hand, i), Econ.has_room(len(Mon, board)), seed, round, p, i)

# sell: the unit leaves the board, +1 gold, then its SELL abilities fire
# (MAKE key [12, seat, round, plays, gold before the refund, slot])
def sell_fin(fx: Fx, +p: Player) -> Player:
  Fx{nb, me, nh, ng, np} = fx
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, hp, ng, tier, upcost, invest, frozen, rolls, nb, shop, alive, out, nh, plays}

def sell_apply(+seed: U32, +round: Nat, +p: Player, +i: Nat, +m: Mon) -> Player:
  Player{+id, hp, +gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, +plays} = p
  sell_fin(fx_abils(mon_abils(m), 3n, seed, [12n, id, round, plays, gold], entering(), mon_tribe(m), mon_golden(m), 0n, Fx{remove_at(Mon, board, i), m, hand, Nat.add(gold, sell_refund()), plays}), p)

def sell_go(mm: Maybe<&2, Mon>, +seed: U32, +round: Nat, +p: Player, +i: Nat) -> PRes:
  match mm:
    case None{}:
      PBad{"no unit at that board index"}
    case Some{m}:
      PGood{p_norm(sell_apply(seed, round, p, i, m))}

def p_sell(+seed: U32, +round: Nat, +p: Player, +i: Nat) -> PRes:
  sell_go(List.get(&2, Mon, p_board(p), i), seed, round, p, i)

def swap_go(ok: Bool, +p: Player, +i: Nat, +j: Nat) -> PRes:
  match ok:
    case False{}:
      PBad{"swap needs two different existing board indexes"}
    case True{}:
      PGood{p_set_board(p, swap_at(Mon, p_board(p), i, j))}

def p_swap(+p: Player, +i: Nat, +j: Nat) -> PRes:
  +n = len(Mon, p_board(p))
  swap_go(Nat.is_lt(i, n) && Nat.is_lt(j, n) && Nat.is_ne(i, j), p, i, j)

def roll_go(mg: Maybe<&2, Nat>, +seed: U32, +round: Nat, +p: Player) -> PRes:
  match mg:
    case None{}:
      PBad{"not enough gold to roll (costs 1)"}
    case Some{g}:
      Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
      PGood{Player{id, hp, g, tier, upcost, invest, False{}, 1n+rolls, board, make_shop(seed, id, round, 1n+rolls, tier), alive, out, hand, plays}}

def p_gold(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  gold

def p_upcost(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  upcost

def p_invest(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  invest

def p_shop(p: Player) -> List<&2, Nat>:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  shop

def p_id(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  id

def p_frozen(p: Player) -> Bool:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  frozen

def p_rolls(p: Player) -> Nat:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  rolls

def p_roll(+seed: U32, +round: Nat, +p: Player) -> PRes:
  roll_go(Econ.spend(p_gold(p), roll_cost()), seed, round, p)

def p_freeze(+p: Player) -> PRes:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  PGood{Player{id, hp, gold, tier, upcost, invest, Bool.not(frozen), rolls, board, shop, alive, out, hand, plays}}

def upgrade_go(ok: Bool, mg: Maybe<&2, Nat>, +p: Player) -> PRes:
  match ok mg:
    case False{} _:
      PBad{"already at the maximum tier"}
    case True{} None{}:
      PBad{"not enough gold to upgrade"}
    case True{} Some{g}:
      Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
      PGood{Player{id, hp, g, 1n+tier, Econ.upgrade_base(1n+tier), invest, frozen, rolls, board, shop, alive, out, hand, plays}}

def p_upgrade(+p: Player) -> PRes:
  upgrade_go(Nat.is_lt(p_tier(p), max_tier()), Econ.spend(p_gold(p), p_upcost(p)), p)

def invest_go(ok: Bool, mg: Maybe<&2, Nat>, +p: Player) -> PRes:
  match ok mg:
    case False{} _:
      PBad{"investment is already at the maximum (3)"}
    case True{} None{}:
      PBad{"not enough gold to invest (costs 2)"}
    case True{} Some{g}:
      Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
      PGood{Player{id, hp, g, tier, upcost, 1n+invest, frozen, rolls, board, shop, alive, out, hand, plays}}

def p_invest_act(+p: Player) -> PRes:
  invest_go(Nat.is_lt(p_invest(p), max_invest()), Econ.spend(p_gold(p), invest_cost()), p)

# a recruit action on one player; End and Auto are game-level
def p_apply(+seed: U32, +round: Nat, +p: Player, a: Act) -> PRes:
  match a:
    case Buy{i}:
      p_buy(p, i)
    case Play{i}:
      p_play(seed, round, p, i)
    case Sell{i}:
      p_sell(seed, round, p, i)
    case Swap{i, j}:
      p_swap(p, i, j)
    case Roll{}:
      p_roll(seed, round, p)
    case Freeze{}:
      p_freeze(p)
    case Upgrade{}:
      p_upgrade(p)
    case Invest{}:
      p_invest_act(p)
    case End{}:
      PBad{"end is a game-level action"}
    case Auto{}:
      PBad{"auto is a game-level action"}

def pres_ok(r: PRes) -> Bool:
  match r:
    case PGood{p}:
      True{}
    case PBad{m}:
      False{}

def pres_or(r: PRes, +d: Player) -> Player:
  match r:
    case PGood{p}:
      p
    case PBad{m}:
      d

# Bots
# ----
# A bot sees only its own seat (gold, tier, upgrade cost, investment,
# board, hand, shop, rolls and plays this turn) and the round number:
# bot_choice(round, p) gets no seed, no other seat and no future shop, and
# it never previews an action. It acts only through p_apply, so it obeys
# exactly the rules a human or agent does.
#
# Values are read from card data in units of attack+health, so they follow
# the roster: one gold is worth a third of the average printed body of the
# seat's tier; recurring abilities (KINPLAY, ENDTURN, Income) count over
# the rounds left (at most 5); PLAY abilities count only for a card about
# to be played; a card also counts what the KIN abilities of its tribe's
# units on the board give it, so the tribe a bot builds follows its board,
# not its seat. Hand, shop and board cards are compared on that one basis:
# a full board replaces its weakest unit (sell, then play) only for a
# clear gain, and a hand or shop card is then valued on the board without
# that unit (base), so newcomer and incumbent see the same allies. Gold
# that would be lost goes to a late upgrade, investment,
# rolls or a freeze. Seat style = id mod 3 only shifts the plan: 0 tempo
# (the latest tier curve), 1 economy (invests early), 2 climber (the
# earliest tier curve).

def max_go(xs: List<&2, Nat>, +best: Nat) -> Nat:
  match xs:
    case Nil{}:
      best
    case h <> t:
      max_go(t, Nat.max(h, best))

def argmax_go(xs: List<&2, Nat>, +pos: Nat, +bi: Nat, +bs: Nat) -> Nat:
  match xs:
    case Nil{}:
      bi
    case +h <> t:
      +better = Nat.is_gt(h, bs)
      argmax_go(t, 1n+pos, pick(Nat, better, pos, bi), pick(Nat, better, h, bs))

def argmin_go(xs: List<&2, Nat>, +pos: Nat, +bi: Nat, +bs: Nat) -> Nat:
  match xs:
    case Nil{}:
      bi
    case +h <> t:
      +better = Nat.is_lt(h, bs)
      argmin_go(t, 1n+pos, pick(Nat, better, pos, bi), pick(Nat, better, h, bs))

def min_go(xs: List<&2, Nat>, +best: Nat) -> Nat:
  match xs:
    case Nil{}:
      best
    case h <> t:
      min_go(t, Nat.min(h, best))

# best / worst entry and its first index, seeded from the first element
# (no sentinel, so any value size works); 0 for an empty list
def bt_max(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      max_go(t, h)

def bt_min(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      min_go(t, h)

def bt_argmax(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      argmax_go(t, 1n, 0n, h)

def bt_argmin(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      argmin_go(t, 1n, 0n, h)

# rounds left, this one included
def bt_left(+round: Nat) -> Nat:
  Nat.sub(Nat.add(max_rounds(), 1n), round)

def bt_tier_sum(xs: List<&2, Card>, +t: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case k <> r:
      Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
      Nat.add(pick(Nat, nat_eq(tier, t), Nat.add(atk, hp), 0n), bt_tier_sum(r, t))

def bt_tier_count(xs: List<&2, Card>, +t: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case k <> r:
      Nat.add(pick(Nat, nat_eq(cd_tier(k), t), 1n, 0n), bt_tier_count(r, t))

# the average printed attack+health of the cards of tier t (at least 1).
# SPECIFICATION: the original definition, kept verbatim. It rebuilds and
# walks the whole card catalog twice per call, so bots call bt_avg below.
def bt_avg_spec(+t: Nat) -> Nat:
  Nat.max(Nat.div(bt_tier_sum(card_list(), t), Nat.max(bt_tier_count(card_list(), t), 1n)), 1n)

# bt_avg as a table (performance only). The values were derived by
# normalizing bt_avg_spec(0..8) with the checker; law bt_avg_table proves
# bt_avg(t) == bt_avg_spec(t) for EVERY Nat t (tier 0 and tiers >= 6 hold
# no card, so the spec gives 1 there). A roster edit that moves any tier
# average, or adds a card of tier >= 6, makes that law fail the check.
def bt_avg(+t: Nat) -> Nat:
  match t:
    case 0n:
      1n
    case 1n:
      3n
    case 2n:
      6n
    case 3n:
      13n
    case 4n:
      23n
    case 5n:
      40n
    case 6n+k:
      1n

law bt_avg_table:
  for +t: Nat
  {bt_avg(t) == bt_avg_spec(t) : Nat}

def bt_avg_table(t):
  match t:
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
    case 6n+k:
      {==}

# one gold at tier t: a third of an average card of that tier
def bt_gold(+t: Nat) -> Nat:
  Nat.max(Nat.div(bt_avg(t), 3n), 1n)

# a random card of tier <= a (MAKE): three quarters of a tier-a body
def bt_made(+a: Nat) -> Nat:
  Nat.div(Nat.mul(bt_avg(Nat.min(a, max_tier())), 3n), 4n)

# v5 A2: a MAKE card's worth relative to the seat's tier (gv = a third of an
# average card of the tier): full when its body is at least half an average
# card of the tier, else a quarter (hand filler)
def bt_madev(+a: Nat, +gv: Nat) -> Nat:
  +v = bt_made(a)
  pick(Nat, Nat.is_ge(Nat.mul(v, 2n), Nat.mul(gv, 3n)), v, Nat.div(v, 4n))

# one firing of an effect; kin: the KIN count it would see, hn: hand
# size, pl: cards played this turn, gv: the worth of a gold
def bt_st(+tgt: Nat, +a: Nat, +h: Nat, +kin: Nat) -> Nat:
  Nat.mul(Nat.add(a, h), pick(Nat, nat_eq(tgt, 0n), 1n, kin))

def bt_eff(eff: Nat, +tgt: Nat, +a: Nat, +h: Nat, +kin: Nat, +hn: Nat, +pl: Nat, +gv: Nat) -> Nat:
  match eff:
    case 0n:
      bt_st(tgt, a, h, kin)
    case 1n+u:
      match u:
        case 0n:
          Nat.mul(bt_st(tgt, a, h, kin), Nat.min(hn, 4n))
        case 1n+v:
          match v:
            case 0n:
              Nat.mul(a, gv)
            case 1n+w:
              match w:
                case 0n:
                  bt_madev(a, gv)
                case 1n+z:
                  Nat.mul(bt_st(tgt, a, h, kin), Nat.min(pl, 4n))

# one ability: PLAY once if the card is being played (play); KINPLAY about
# every other round left; ENDTURN every round left (hz, at most 5); SELL
# is counted by bt_sellv. Recurring STATS_PLAYS assumes 2 plays a turn.
def bt_abil_go(trig: Nat, +eff: Nat, +tgt: Nat, +a: Nat, +h: Nat, +play: Bool, +kin: Nat, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat) -> Nat:
  match trig:
    case 0n:
      pick(Nat, play, bt_eff(eff, tgt, a, h, kin, hn, pl, gv), 0n)
    case 1n+u:
      match u:
        case 0n:
          Nat.div(Nat.mul(bt_eff(eff, tgt, a, h, kin, hn, 2n, gv), hz), 2n)
        case 1n+v:
          pick(Nat, nat_eq(v, 0n), Nat.mul(bt_eff(eff, tgt, a, h, kin, hn, 2n, gv), hz), 0n)

def bt_abil(x: Abil, +play: Bool, +kin: Nat, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat) -> Nat:
  Abil{trig, +tgt, +eff, +a, +h} = x
  bt_abil_go(trig, eff, tgt, a, h, play, kin, hn, pl, gv, hz)

def bt_abils(xs: List<&2, Abil>, +play: Bool, +kin: Nat, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(bt_abil(x, play, kin, hn, pl, gv, hz), bt_abils(t, play, kin, hn, pl, gv, hz))

# what one more member of the tribe gets from a unit's recurring KIN stat
# abilities (KINPLAY / ENDTURN with target KIN)
def bt_kin1(x: Abil, +hn: Nat, +gv: Nat, +hz: Nat) -> Nat:
  Abil{+trig, +tgt, +eff, +a, +h} = x
  +stat = Bool.not(nat_eq(eff, 2n)) && Bool.not(nat_eq(eff, 3n))
  +rec = nat_eq(trig, 1n) || nat_eq(trig, 2n)
  pick(Nat, nat_eq(tgt, 1n) && stat && rec, bt_abil(Abil{trig, tgt, eff, a, h}, False{}, 1n, hn, 2n, gv, hz), 0n)

def bt_kins(xs: List<&2, Abil>, +hn: Nat, +gv: Nat, +hz: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(bt_kin1(x, hn, gv, hz), bt_kins(t, hn, gv, hz))

# what playing a card of its tribe fires now in one observer (KINPLAY)
def bt_nows(xs: List<&2, Abil>, +kin: Nat, +hn: Nat, +pl: Nat, +gv: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Abil{+trig, +tgt, +eff, +a, +h} = x
      Nat.add(pick(Nat, nat_eq(trig, 1n), bt_eff(eff, tgt, a, h, kin, hn, pl, gv), 0n), bt_nows(t, kin, hn, pl, gv))

# board units of tribe tr, except the one at index skip
def bt_cnt(b: List<&2, Mon>, +tr: Nat, +skip: Nat, +pos: Nat) -> Nat:
  match b:
    case Nil{}:
      0n
    case +m <> t:
      Nat.add(pick(Nat, kin_match(mon_tribe(m), tr) && Bool.not(nat_eq(pos, skip)), 1n, 0n), bt_cnt(t, tr, skip, 1n+pos))

# what the board units of tribe tr (except index skip) give a card of that
# tribe: their per-member KIN value and, when it is played (now), their
# KINPLAY firing, which sees kin allies
def bt_pull(b: List<&2, Mon>, +tr: Nat, +skip: Nat, +pos: Nat, +now: Bool, +kin: Nat, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat) -> Nat:
  match b:
    case Nil{}:
      0n
    case +m <> t:
      +xs = mon_abils(m)
      +v = Nat.add(bt_kins(xs, hn, gv, hz), pick(Nat, now, bt_nows(xs, kin, hn, pl, gv), 0n))
      Nat.add(pick(Nat, kin_match(mon_tribe(m), tr) && Bool.not(nat_eq(pos, skip)), v, 0n), bt_pull(t, tr, skip, 1n+pos, now, kin, hn, pl, gv, hz))

# a body: attack + health, Shield (one blocked hit: the attack again, +1),
# Guard, Armor (about three hits), Rally, Income for the rounds after this
# one (at most 5), and a small bonus per ally of its tribe (kin)
def bt_body(m: Mon, +kin: Nat, +gv: Nat, +left: Nat) -> Nat:
  Mon{+c, +a, +h, +s, +g} = m
  +shield = pick(Nat, s, Nat.add(a, 1n), 0n)
  +guard = pick(Nat, c_guard(c), Nat.add(1n, Nat.div(h, 4n)), 0n)
  +kw = Nat.add(Nat.mul(c_armor(c), 3n), Nat.mul(dbl(g, c_rally(c)), 2n))
  +inc = Nat.mul(Nat.mul(dbl(g, c_income(c)), gv), Nat.min(Nat.sub(left, 1n), 5n))
  +focus = Nat.div(Nat.mul(kin, gv), 2n)
  Nat.add(Nat.add(Nat.add(a, h), Nat.add(shield, guard)), Nat.add(Nat.add(kw, inc), focus))

def bt_unit(+m: Mon, +play: Bool, +kin: Nat, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat, +left: Nat) -> Nat:
  Nat.add(bt_body(m, kin, gv, left), bt_abils(mon_abils(m), play, kin, hn, pl, gv, hz))

# worth of playing card m onto board b (hn: hand size after it leaves)
def bt_playv(+m: Mon, +b: List<&2, Mon>, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat, +left: Nat) -> Nat:
  +tr = mon_tribe(m)
  +cnt = bt_cnt(b, tr, entering(), 0n)
  Nat.add(bt_unit(m, True{}, cnt, hn, pl, gv, hz, left), bt_pull(b, tr, entering(), 0n, True{}, cnt, hn, pl, gv, hz))

# worth of keeping board unit m at index k
def bt_keepv(+m: Mon, +k: Nat, +b: List<&2, Mon>, +hn: Nat, +gv: Nat, +hz: Nat, +left: Nat) -> Nat:
  +tr = mon_tribe(m)
  +cnt = bt_cnt(b, tr, k, 0n)
  Nat.add(bt_unit(m, False{}, cnt, hn, 0n, gv, hz, left), bt_pull(b, tr, k, 0n, False{}, cnt, hn, 0n, gv, hz))

def bt_keeps(xs: List<&2, Mon>, +b: List<&2, Mon>, +pos: Nat, +hn: Nat, +gv: Nat, +hz: Nat, +left: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +m <> t:
      bt_keepv(m, pos, b, hn, gv, hz, left) <> bt_keeps(t, b, 1n+pos, hn, gv, hz, left)

def bt_hands(xs: List<&2, Mon>, +b: List<&2, Mon>, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat, +left: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +m <> t:
      bt_playv(m, b, hn, pl, gv, hz, left) <> bt_hands(t, b, hn, pl, gv, hz, left)

def bt_shops(xs: List<&2, Nat>, +b: List<&2, Mon>, +hn: Nat, +pl: Nat, +gv: Nat, +hz: Nat, +left: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> t:
      bt_playv(mon_of(c), b, hn, pl, gv, hz, left) <> bt_shops(t, b, hn, pl, gv, hz, left)

# what selling a board unit gives back: the refund and its SELL abilities
def bt_sells(xs: List<&2, Abil>, +gv: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Abil{+trig, +tgt, +eff, +a, +h} = x
      Nat.add(pick(Nat, nat_eq(trig, 3n), bt_eff(eff, tgt, a, h, 0n, 0n, 0n, gv), 0n), bt_sells(t, gv))

def bt_sellv(+m: Mon, +gv: Nat) -> Nat:
  Nat.add(Nat.mul(sell_refund(), gv), bt_sells(mon_abils(m), gv))

# what one more hand card earns each round from ENDTURN STATS_HAND units
# (only real hand payoffs on the board count)
def bt_hand1(xs: List<&2, Abil>, +kin: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Abil{+trig, +tgt, +eff, +a, +h} = x
      Nat.add(pick(Nat, nat_eq(trig, 2n) && nat_eq(eff, 1n), Nat.mul(Nat.add(a, h), pick(Nat, nat_eq(tgt, 0n), 1n, kin)), 0n), bt_hand1(t, kin))

def bt_handpay(xs: List<&2, Mon>, +b: List<&2, Mon>, +pos: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +m <> t:
      Nat.add(bt_hand1(mon_abils(m), bt_cnt(b, mon_tribe(m), pos, 0n)), bt_handpay(t, b, 1n+pos))

# play order when every hand card fits on the board: KINPLAY observers and
# hand-scaled PLAY cards first (2), PLAY cards that buff the tribe or scale
# with plays last (0), the rest (1)
def bt_first(xs: List<&2, Abil>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Abil{+trig, +tgt, +eff, a, h} = x
      (nat_eq(trig, 1n) || (nat_eq(trig, 0n) && nat_eq(eff, 1n))) || bt_first(t)

def bt_last(xs: List<&2, Abil>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Abil{+trig, +tgt, +eff, a, h} = x
      (nat_eq(trig, 0n) && (nat_eq(tgt, 1n) || nat_eq(eff, 4n))) || bt_last(t)

def bt_cls(+m: Mon) -> Nat:
  +xs = mon_abils(m)
  pick(Nat, bt_first(xs), 2n, pick(Nat, bt_last(xs), 0n, 1n))

def bt_clss(xs: List<&2, Mon>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case m <> t:
      bt_cls(m) <> bt_clss(t)

# values of the hand cards of class top (+1), 0 for the others
def bt_prio(xs: List<&2, Mon>, vs: List<&2, Nat>, +top: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case m <> t:
      match vs:
        case Nil{}:
          Nil{}
        case v <> u:
          pick(Nat, nat_eq(bt_cls(m), top), 1n+v, 0n) <> bt_prio(t, u, top)

def bt_ge(+r: Nat, +k: Nat) -> Nat:
  pick(Nat, Nat.is_ge(r, k), 1n, 0n)

# the tier a seat aims for by a round: with r = round + 1 (tempo), + 2
# (economy) or + 3 (climber): 2 from r 3, 3 from r 5, 4 from r 8, 5 from
# r 11 (tempo: tier 5 from round 10, climber from round 8)
def bt_target(+style: Nat, +round: Nat) -> Nat:
  +r = pick(Nat, nat_eq(style, 2n), 3n+round, pick(Nat, nat_eq(style, 0n), 1n+round, 2n+round))
  Nat.add(1n, Nat.add(Nat.add(bt_ge(r, 3n), bt_ge(r, 5n)), Nat.add(bt_ge(r, 8n), bt_ge(r, 11n))))

# v5 A1: rounds after this one in which the seat still has a gold sink
# (tiering on its own curve): 0 at the max tier, else the rounds until its
# curve reaches the max tier (at most left - 1)
def bt_tgo(n: Nat, +style: Nat, +round: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      pick(Nat, Nat.is_lt(bt_target(style, Nat.add(round, 1n)), max_tier()), 1n+bt_tgo(k, style, Nat.add(round, 1n)), 0n)

def bt_hungry(+style: Nat, +round: Nat, +tier: Nat, +left: Nat) -> Nat:
  pick(Nat, Nat.is_lt(tier, max_tier()), Nat.min(Nat.add(bt_tgo(5n, style, round), 1n), Nat.sub(left, 1n)), 0n)

# the next recruit action, or None to stop. In order: play a hand card
# when the board has room; replace the weakest unit for a clear gain;
# economy invests early; tier up on the seat's curve (not while one loss
# could knock it out: hp <= 3 + round, the bot's own danger line, which
# mirrors the damage cap); reroll a weak shop; buy for an open slot, a clear
# upgrade or a real hand payoff; then use gold that would be lost: tier
# up, invest, reroll, freeze a strong shop. (Hand cards cannot be sold.)
def bot_choice(+round: Nat, +p: Player) -> Maybe<&2, Act>:
  Player{+id, +hp, +gold, +tier, +upcost, +invest, +frozen, +rolls, +board, +shop, alive, out, +hand, +plays} = p
  +style = Nat.mod(id, 3n)
  +left = bt_left(round)
  +hz = Nat.min(left, 5n)
  +gv = bt_gold(tier)
  +blen = len(Mon, board)
  +hlen = len(Mon, hand)
  +slen = len(Nat, shop)
  +room = Econ.has_room(blen)
  +hung = bt_hungry(style, round, tier, left)
  +ileft = Nat.add(1n, Nat.add(hung, Nat.div(Nat.sub(Nat.sub(left, 1n), hung), 4n)))
  +keeps = bt_keeps(board, board, 0n, hlen, gv, hz, ileft)
  +wi = bt_argmin(keeps)
  +wv = bt_min(keeps)
  +base = pick(List<&2, Mon>, room, board, remove_at(Mon, board, wi))
  +hvals = bt_hands(hand, base, Nat.sub(hlen, 1n), plays, gv, hz, ileft)
  +svals = bt_shops(shop, base, hlen, plays, gv, hz, ileft)
  +ws = bt_sellv(get_or(Mon, board, wi, mon_of(0n)), gv)
  +hv = bt_max(hvals)
  +si = bt_argmax(svals)
  +sv = bt_max(svals)
  +maxed = Bool.not(Nat.is_lt(tier, max_tier()))
  +bar = Nat.add(Nat.add(wv, gv), Nat.div(wv, 8n))
  +hfull = Bool.not(hand_room(hlen))
  +swap_h = Bool.not(room) && Nat.is_gt(hlen, 0n) && (Nat.is_gt(Nat.add(hv, ws), bar) || (hfull && Nat.is_ge(Nat.add(hv, ws), wv)))
  +swap_s = Bool.not(room) && Nat.is_gt(Nat.add(sv, ws), bar)
  +pay = bt_handpay(board, board, 0n)
  +hold = pick(Nat, Nat.is_gt(pay, 0n), 4n, 0n)
  +holdbuy = Bool.not(room) && Nat.is_lt(hlen, hold) && Nat.is_ge(Nat.mul(pay, Nat.min(left, 3n)), Nat.mul(buy_cost(), gv))
  +fits = Econ.has_room(Nat.sub(Nat.add(blen, hlen), 1n))
  +pi = pick(Nat, fits, bt_argmax(bt_prio(hand, hvals, bt_max(bt_clss(hand)))), bt_argmax(hvals))
  +play = room && Nat.is_gt(hlen, 0n)
  +canbuy = Nat.is_gt(slen, 0n) && hand_room(hlen) && Nat.is_ge(gold, buy_cost())
  +slots = Econ.has_room(Nat.add(blen, hlen))
  +canroll = hand_room(hlen) && Nat.is_ge(gold, Nat.add(roll_cost(), buy_cost()))
  +weak = Nat.is_lt(Nat.mul(sv, 2n), bt_avg(tier))
  +rollfirst = slots && weak && canroll && Nat.is_lt(rolls, 3n)
  +buy = canbuy && (slots || swap_s || holdbuy)
  +canup = Nat.is_lt(tier, max_tier()) && Nat.is_ge(gold, upcost)
  +panic = Nat.is_le(hp, Nat.add(3n, round))
  +built = Nat.is_ge(Nat.add(blen, hlen), Nat.min(Nat.sub(round, 1n), 3n))
  +upfirst = canup && Nat.is_ge(left, 3n) && Bool.not(panic) && built && Nat.is_lt(tier, bt_target(style, round))
  +ecoinv = nat_eq(style, 1n) && Nat.is_ge(round, 2n) && Nat.is_le(round, 5n) && Nat.is_lt(invest, max_invest()) && Nat.is_ge(gold, Nat.add(invest_cost(), buy_cost()))
  +lateup = canup && Nat.is_ge(left, 2n)
  +inv = Nat.is_lt(invest, max_invest()) && Nat.is_ge(gold, invest_cost()) && Nat.is_ge(left, 6n)
  +roll = canroll && Nat.is_lt(rolls, pick(Nat, maxed, Nat.add(5n, Nat.div(gold, 3n)), 5n))
  +frz = Bool.not(frozen) && Nat.is_ge(left, 2n) && Nat.is_gt(slen, 0n) && Nat.is_lt(gold, buy_cost()) && (swap_s || (slots && Nat.is_ge(c_tier(get_or(Nat, shop, si, 0n)), tier)))
  pick(Maybe<&2, Act>, play, Some{Play{pi}},
    pick(Maybe<&2, Act>, swap_h, Some{Sell{wi}},
      pick(Maybe<&2, Act>, ecoinv, Some{Invest{}},
        pick(Maybe<&2, Act>, upfirst, Some{Upgrade{}},
          pick(Maybe<&2, Act>, rollfirst, Some{Roll{}},
            pick(Maybe<&2, Act>, buy, Some{Buy{si}},
              pick(Maybe<&2, Act>, lateup, Some{Upgrade{}},
                pick(Maybe<&2, Act>, inv, Some{Invest{}},
                  pick(Maybe<&2, Act>, roll, Some{Roll{}},
                    pick(Maybe<&2, Act>, frz, Some{Freeze{}}, None{}))))))))))

def bot_try(ma: Maybe<&2, Act>, +seed: U32, +round: Nat, +p: Player) -> Player:
  match ma:
    case None{}:
      p
    case Some{a}:
      pres_or(p_apply(seed, round, p, a), p)

def bot_steps(fuel: Nat, +seed: U32, +round: Nat, +p: Player) -> Player:
  match fuel:
    case 0n:
      p
    case 1n+f:
      bot_steps(f, seed, round, bot_try(bot_choice(round, p), seed, round, p))

def mon_not_guard(m: Mon) -> Bool:
  Bool.not(mon_guard(m))

# Guards to the front; otherwise keep the order
def arrange(+b: List<&2, Mon>) -> List<&2, Mon>:
  List.append(&2, Mon, List.filter(~Mon, ~mon_guard, b), List.filter(~Mon, ~mon_not_guard, b))

def bot_play(+seed: U32, +round: Nat, +p: Player) -> Player:
  +q = bot_steps(bot_fuel(), seed, round, p)
  p_set_board(q, arrange(p_board(q)))

# Combat
# ------
# Deterministic, bounded by combat_fuel() steps. The front unit of the
# attacking side attacks a target (a random Guard if the defender has one,
# else any unit). Rally n: right before it attacks, the attacker gains +n
# attack for the rest of this combat. Both deal damage at once. A hit of
# 0 does nothing; a positive hit on a Shield breaks the Shield and does
# nothing else; otherwise Armor n lowers the hit by n (Nat.sub) before it
# is taken from health (Econ.hp_after). The dead leave, and a surviving
# attacker moves to the back of its line. Sides alternate. Running out of
# fuel is a draw. Combat works on copies: boards are never written back.
#
# Every attack is also recorded as a structured event (Ev) with the two
# lines before and after it, so a client can animate combat without
# re-implementing any rule.

type CSt is Data:
  CSt{xa: List<&2, Mon>, xb: List<&2, Mon>, turn: Bool, n: Nat, log: List<&2, String>, evs: List<&2, Ev>}

# ai2/ti2: the attacker's / target's index after the attack (unused when
# that unit died); ral: the attacker's Rally gain
type AtkOut is Data:
  AtkOut{xs: List<&2, Mon>, ys: List<&2, Mon>, line: String, ti: Nat, ai2: Nat, ti2: Nat, asb: Bool, tsb: Bool, ad: Bool, td: Bool, ral: Nat, aatk: Nat}

def guard_idx(b: List<&2, Mon>, +pos: Nat) -> List<&2, Nat>:
  match b:
    case Nil{}:
      Nil{}
    case +m <> t:
      +r = guard_idx(t, 1n+pos)
      pick(List<&2, Nat>, mon_guard(m), pos <> r, r)

def choose_cands(gs: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match gs:
    case Nil{}:
      List.range(n)
    case h <> t:
      h <> t

def mon_alive(m: Mon) -> Bool:
  Mon{c, a, h, s, g} = m
  Nat.is_gt(h, 0n)

def mon_atk(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  a

def mon_hp(m: Mon) -> Nat:
  Mon{c, a, h, s, g} = m
  h

def mon_shield(m: Mon) -> Bool:
  Mon{c, a, h, s, g} = m
  s

def hurt_go(z: Bool, +m: Mon, +d: Nat) -> Mon:
  match z:
    case True{}:
      m
    case False{}:
      Mon{c, a, h, s, g} = m
      pick(Mon, s, Mon{c, a, h, False{}, g}, Mon{c, a, Econ.hp_after(h, Nat.sub(d, c_armor(c))), s, g})

def hurt(+m: Mon, +d: Nat) -> Mon:
  hurt_go(nat_eq(d, 0n), m, d)

def rally(+m: Mon) -> Mon:
  Mon{c, a, h, s, g} = m
  Mon{c, Nat.add(a, dbl(g, c_rally(c))), h, s, g}

def mon_desc(+m: Mon) -> String:
  Mon{c, a, h, s, g} = m
  pick(String, g, "Golden ", "") ++ c_name(c) ++ " " ++ Nat.show(a) ++ "/" ++ Nat.show(h)

def poss(+name: String) -> String:
  pick(String, String.eq(name, "You"), "Your", name ++ "'s")

def armor_note(+name: String, +m: Mon, +d: Nat) -> String:
  +ar = c_armor(mon_cid(m))
  pick(String, Bool.not(mon_shield(m)) && Nat.is_gt(d, 0n) && Nat.is_gt(ar, 0n), "; " ++ poss(name) ++ " Armor absorbs " ++ Nat.show(Nat.min(ar, d)), "")

def outcome(+name: String, +before: Mon, +after: Mon) -> String:
  pick(String, Bool.not(mon_alive(after)), "; " ++ name ++ " dies",
    pick(String, mon_shield(before) && Bool.not(mon_shield(after)), "; " ++ poss(name) ++ " Shield breaks", ""))

def rally_note(+an: String, +att: Mon, +n: Nat) -> String:
  pick(String, nat_eq(n, 0n), "", poss(an) ++ " " ++ c_name(mon_cid(att)) ++ " rallies (+" ++ Nat.show(n) ++ " attack); ")

def attack_with(+an: String, +dn: String, +att0: Mon, +rest: List<&2, Mon>, +ys: List<&2, Mon>, +ti: Nat) -> AtkOut:
  +tgt = get_or(Mon, ys, ti, mon_of(0n))
  +ral = mon_rally(att0)
  +att = rally(att0)
  +att2 = hurt(att, mon_atk(tgt))
  +tgt2 = hurt(tgt, mon_atk(att))
  +aok = mon_alive(att2)
  +tok = mon_alive(tgt2)
  +xs2 = pick(List<&2, Mon>, aok, snoc(Mon, rest, att2), rest)
  +ys2 = pick(List<&2, Mon>, tok, List.set(&2, Mon, ys, ti, tgt2), remove_at(Mon, ys, ti))
  +tname = c_name(mon_cid(tgt))
  +aname = c_name(mon_cid(att))
  +line = rally_note(an, att0, ral) ++ poss(an) ++ " " ++ mon_desc(att) ++ " attacks " ++ poss(dn) ++ " " ++ mon_desc(tgt) ++ armor_note(tname, tgt, mon_atk(att)) ++ outcome(tname, tgt, tgt2) ++ armor_note(aname, att, mon_atk(tgt)) ++ outcome(aname, att, att2)
  AtkOut{xs2, ys2, line, ti, len(Mon, rest), ti, mon_shield(att) && Bool.not(mon_shield(att2)), mon_shield(tgt) && Bool.not(mon_shield(tgt2)), Bool.not(aok), Bool.not(tok), ral, mon_atk(att)}

def target_of(+h: U32, +ys: List<&2, Mon>) -> Nat:
  +cands = choose_cands(guard_idx(ys, 0n), len(Mon, ys))
  get_or(Nat, cands, below(h, len(Nat, cands)), 0n)

def attack(xs: List<&2, Mon>, +ys: List<&2, Mon>, +h: U32, +an: String, +dn: String) -> AtkOut:
  match xs:
    case Nil{}:
      AtkOut{Nil{}, ys, "", 0n, 0n, 0n, False{}, False{}, False{}, False{}, 0n, 0n}
    case att <> rest:
      attack_with(an, dn, att, rest, ys, target_of(h, ys))

# side: True when seat a attacks
def step_fin(turn: Bool, o: AtkOut, +n: Nat, log: List<&2, String>, evs: List<&2, Ev>, +ba: List<&2, Mon>, +bb: List<&2, Mon>) -> CSt:
  match turn:
    case True{}:
      AtkOut{+xs, +ys, +line, ti, ai2, ti2, asb, tsb, ad, td, ral, aatk} = o
      CSt{xs, ys, False{}, 1n+n, line <> log, EvAtk{n, True{}, ti, ai2, ti2, ba, bb, xs, ys, asb, tsb, ad, td, ral, aatk, line} <> evs}
    case False{}:
      AtkOut{+xs, +ys, +line, ti, ai2, ti2, asb, tsb, ad, td, ral, aatk} = o
      CSt{ys, xs, True{}, 1n+n, line <> log, EvAtk{n, False{}, ti, ai2, ti2, ba, bb, ys, xs, asb, tsb, ad, td, ral, aatk, line} <> evs}

def step_go(xa: List<&2, Mon>, xb: List<&2, Mon>, turn: Bool, +n: Nat, log: List<&2, String>, evs: List<&2, Ev>, +h: U32, +na: String, +nb: String) -> CSt:
  match xa xb:
    case Nil{} _:
      CSt{Nil{}, xb, turn, n, log, evs}
    case _ Nil{}:
      CSt{xa, Nil{}, turn, n, log, evs}
    case +ha <> +ta +hb <> +tb:
      match turn:
        case True{}:
          step_fin(True{}, attack(ha <> ta, hb <> tb, h, na, nb), n, log, evs, ha <> ta, hb <> tb)
        case False{}:
          step_fin(False{}, attack(hb <> tb, ha <> ta, h, nb, na), n, log, evs, ha <> ta, hb <> tb)

def cstep(+seed: U32, +round: Nat, +a: Nat, +b: Nat, +na: String, +nb: String, st: CSt) -> CSt:
  CSt{xa, xb, turn, +n, log, evs} = st
  step_go(xa, xb, turn, n, log, evs, hash(seed, [2n, round, a, b, n]), na, nb)

def cloop(fuel: Nat, +seed: U32, +round: Nat, +a: Nat, +b: Nat, +na: String, +nb: String, st: CSt) -> CSt:
  match fuel:
    case 0n:
      st
    case 1n+f:
      cloop(f, seed, round, a, b, na, nb, cstep(seed, round, a, b, na, nb, st))

def first_turn(+la: Nat, +lb: Nat, +h: U32) -> Bool:
  pick(Bool, Nat.is_gt(la, lb), True{}, pick(Bool, Nat.is_lt(la, lb), False{}, nat_eq(below(h, 2n), 0n)))

# result code: 0 draw, 1 a wins, 2 b wins
def fight_res(xa: List<&2, Mon>, xb: List<&2, Mon>) -> Nat:
  match xa xb:
    case Nil{} _:
      pick(Nat, List.is_empty(&2, Mon, xb), 0n, 2n)
    case _ Nil{}:
      1n
    case _ _:
      0n

# why a fight ended: 0 one side was eliminated, 1 both sides are empty,
# 2 the attack limit (fuel) ran out with units on both sides
def fight_reason(xa: List<&2, Mon>, xb: List<&2, Mon>) -> Nat:
  match xa xb:
    case Nil{} _:
      pick(Nat, List.is_empty(&2, Mon, xb), 1n, 0n)
    case _ Nil{}:
      0n
    case _ _:
      2n

# the uncapped loss: winner tier + tiers of the winner's survivors (Econ.damage)
def fight_dmg_raw(+res: Nat, xa: List<&2, Mon>, xb: List<&2, Mon>, +ta: Nat, +tb: Nat) -> Nat:
  pick(Nat, nat_eq(res, 1n), Econ.damage(ta, board_tiers(xa)), pick(Nat, nat_eq(res, 2n), Econ.damage(tb, board_tiers(xb)), 0n))

# the loss is capped at 3 + round (round: the 1-based round being fought),
# adopted from balance candidate C1; tests/damage_laws.bend proves the cap
def damage_cap(+round: Nat) -> Nat:
  Nat.add(3n, round)

def fight_dmg(+round: Nat, +res: Nat, xa: List<&2, Mon>, xb: List<&2, Mon>, +ta: Nat, +tb: Nat) -> Nat:
  Nat.min(fight_dmg_raw(res, xa, xb, ta, tb), damage_cap(round))

def win_text(+name: String, +dmg: Nat) -> String:
  pick(String, String.eq(name, "You"), "You win and deal ", name ++ " wins and deals ") ++ Nat.show(dmg) ++ " damage"

def fight_end(st: CSt, +round: Nat, +a: Nat, +b: Nat, +na: String, +nb: String, +ta: Nat, +tb: Nat, +ba: List<&2, Mon>, +bb: List<&2, Mon>) -> Fight:
  CSt{+xa, +xb, turn, +n, log, evs} = st
  +res = fight_res(xa, xb)
  +dmg = fight_dmg(round, res, xa, xb, ta, tb)
  +why = fight_reason(xa, xb)
  +last = pick(String, nat_eq(res, 0n), pick(String, nat_eq(why, 2n), "Draw: the attack limit was reached, no damage", "Draw: no damage"), win_text(pick(String, nat_eq(res, 1n), na, nb), dmg))
  Fight{round, a, b, res, dmg, ba, bb, List.reverse(&2, String, last <> log), List.reverse(&2, Ev, EvEnd{n, res, dmg, why, xa, xb, last} <> evs)}

def fight(+seed: U32, +round: Nat, +a: Nat, +b: Nat, +na: String, +nb: String, +ta: Nat, +tb: Nat, +ba: List<&2, Mon>, +bb: List<&2, Mon>) -> Fight:
  +t0 = first_turn(len(Mon, ba), len(Mon, bb), hash(seed, [3n, round, a, b]))
  +st = cloop(combat_fuel(), seed, round, a, b, na, nb, CSt{ba, bb, t0, 0n, Nil{}, Nil{}})
  fight_end(st, round, a, b, na, nb, ta, tb, ba, bb)

# Rounds
# ------

type P2 is Data:
  P2{a: Nat, b: Nat}

type FOut is Data:
  FOut{ps: List<&2, Player>, fs: List<&2, Fight>}

def seat_name(mode: Nat, +k: Nat) -> String:
  match mode:
    case 0n:
      get_or(String, ["You", "Mira", "Brask", "Vell"], k, "?")
    case 1n+m:
      "Seat " ++ Nat.show(k)

def seat_style(+k: Nat) -> String:
  get_or(String, ["tempo", "economy", "climber"], Nat.mod(k, 3n), "tempo")

def alive_ids(ps: List<&2, Player>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      +r = alive_ids(t)
      pick(List<&2, Nat>, p_alive(p), p_id(p) <> r, r)

def at(+l: List<&2, Nat>, +i: Nat) -> Nat:
  get_or(Nat, l, i, 0n)

def pairs4(m: Nat, +l: List<&2, Nat>) -> List<&2, P2>:
  match m:
    case 0n:
      [P2{at(l, 0n), at(l, 3n)}, P2{at(l, 1n), at(l, 2n)}]
    case 1n+r:
      pick(List<&2, P2>, nat_eq(r, 0n), [P2{at(l, 0n), at(l, 1n)}, P2{at(l, 2n), at(l, 3n)}], [P2{at(l, 0n), at(l, 2n)}, P2{at(l, 1n), at(l, 3n)}])

def pairs3(m: Nat, +l: List<&2, Nat>) -> List<&2, P2>:
  match m:
    case 0n:
      [P2{at(l, 1n), at(l, 2n)}]
    case 1n+r:
      pick(List<&2, P2>, nat_eq(r, 0n), [P2{at(l, 0n), at(l, 2n)}], [P2{at(l, 0n), at(l, 1n)}])

# the fixed pairing schedule for a round among the living seats
def pairings(+l: List<&2, Nat>, +round: Nat) -> List<&2, P2>:
  +n = len(Nat, l)
  +m = Nat.mod(round, 3n)
  pick(List<&2, P2>, nat_eq(n, 4n), pairs4(m, l),
    pick(List<&2, P2>, nat_eq(n, 3n), pairs3(m, l),
      pick(List<&2, P2>, nat_eq(n, 2n), [P2{at(l, 0n), at(l, 1n)}], Nil{})))

def opp_in(prs: List<&2, P2>, +k: Nat) -> Maybe<&2, Nat>:
  match prs:
    case Nil{}:
      None{}
    case P2{+a, +b} <> t:
      pick(Maybe<&2, Nat>, nat_eq(a, k), Some{b}, pick(Maybe<&2, Nat>, nat_eq(b, k), Some{a}, opp_in(t, k)))

def p_set_hp(p: Player, +v: Nat) -> Player:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, v, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays}

def damage_player(+ps: List<&2, Player>, +k: Nat, +d: Nat) -> List<&2, Player>:
  +p = pget(ps, k)
  pset(ps, k, p_set_hp(p, Econ.hp_after(p_hp(p), d)))

def apply_fight(+ps: List<&2, Player>, +f: Fight) -> List<&2, Player>:
  Fight{round, a, b, +res, dmg, ba, bb, log, evs} = f
  pick(List<&2, Player>, nat_eq(res, 0n), ps, damage_player(ps, pick(Nat, nat_eq(res, 1n), b, a), dmg))

def run_fights(prs: List<&2, P2>, +seed: U32, +round: Nat, +mode: Nat, +ps: List<&2, Player>, +fs: List<&2, Fight>) -> FOut:
  match prs:
    case Nil{}:
      FOut{ps, List.reverse(&2, Fight, fs)}
    case P2{+a, +b} <> t:
      +pa = pget(ps, a)
      +pb = pget(ps, b)
      +f = fight(seed, round, a, b, seat_name(mode, a), seat_name(mode, b), p_tier(pa), p_tier(pb), p_board(pa), p_board(pb))
      run_fights(t, seed, round, mode, apply_fight(ps, f), f <> fs)

# end of the recruit phase: ENDTURN abilities, board left to right
# (MAKE key [11, seat, round, pos, slot])
def grow_fin(fx: Fx, +p: Player) -> Player:
  Fx{nb, me, nh, ng, np} = fx
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, hp, ng, tier, upcost, invest, frozen, rolls, nb, shop, alive, out, nh, plays}

def grow_live(+seed: U32, +round: Nat, +p: Player) -> Player:
  Player{+id, hp, gold, tier, upcost, invest, frozen, rolls, +board, shop, alive, out, hand, plays} = p
  grow_fin(endturn(len(Mon, board), 0n, seed, [11n, id, round], Fx{board, mon_of(0n), hand, gold, plays}), p)

def grow_player(+seed: U32, +round: Nat, +p: Player) -> Player:
  pick(Player, p_alive(p), grow_live(seed, round, p), p)

def grow_all(ps: List<&2, Player>, +seed: U32, +round: Nat) -> List<&2, Player>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      grow_player(seed, round, p) <> grow_all(t, seed, round)

def elim_one(+round: Nat, +p: Player) -> Player:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  pick(Player, alive && nat_eq(hp, 0n), Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, False{}, round, hand, plays}, p)

def elim_all(ps: List<&2, Player>, +round: Nat) -> List<&2, Player>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      elim_one(round, p) <> elim_all(t, round)

# a frozen shop keeps its cards; empty slots (bought cards) are refilled
# from the round's fresh deterministic draw, up to shop_size()
def fill_shop(+kept: List<&2, Nat>, fresh: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, kept, List.take(&2, Nat, fresh, Nat.sub(shop_size(), len(Nat, kept))))

def next_round_live(+seed: U32, +r2: Nat, +p: Player) -> Player:
  Player{id, hp, gold, tier, upcost, invest, frozen, rolls, board, shop, alive, out, hand, plays} = p
  Player{id, hp, Econ.income(r2, invest, board_income(board)), tier, Econ.upgrade_cost_next(tier, upcost), invest, False{}, 0n, board, pick(List<&2, Nat>, frozen, fill_shop(shop, make_shop(seed, id, r2, 0n, tier)), make_shop(seed, id, r2, 0n, tier)), alive, out, hand, 0n}

# a new recruit phase: first any triple is assembled (copies an end-of-turn
# MAKE added), then income from the resulting board, the shop and upgrade cost
def next_round_player(+seed: U32, +r2: Nat, +p: Player) -> Player:
  pick(Player, p_alive(p), next_round_live(seed, r2, p_norm(p)), p)

def next_round_all(ps: List<&2, Player>, +seed: U32, +r2: Nat) -> List<&2, Player>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      next_round_player(seed, r2, p) <> next_round_all(t, seed, r2)


def first_alive(+mode: Nat, +ps: List<&2, Player>) -> Nat:
  pick(Nat, nat_eq(mode, 0n), 0n, get_or(Nat, alive_ids(ps), 0n, 0n))

def finish_round(fo: FOut, +seed: U32, +mode: Nat, +round: Nat, +hist: List<&2, Fight>) -> Game:
  FOut{ps2, +fs} = fo
  +ps3 = elim_all(ps2, round)
  +over = Nat.is_le(len(Nat, alive_ids(ps3)), 1n) || Nat.is_ge(round, max_rounds())
  +hist2 = List.append(&2, Fight, hist, fs)
  +ps4 = next_round_all(ps3, seed, 1n+round)
  pick(Game, over, Game{seed, mode, round, first_alive(mode, ps3), ps3, fs, hist2, True{}}, Game{seed, mode, 1n+round, first_alive(mode, ps4), ps4, fs, hist2, False{}})

def end_round(g: Game) -> Game:
  Game{+seed, +mode, +round, actor, players, fights, hist, done} = g
  +ps1 = grow_all(players, seed, round)
  finish_round(run_fights(pairings(alive_ids(ps1), round), seed, round, mode, ps1, Nil{}), seed, mode, round, hist)

def g_seed(g: Game) -> U32:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  seed

def g_mode(g: Game) -> Nat:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  mode

def g_round(g: Game) -> Nat:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  round

def g_actor(g: Game) -> Nat:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  actor

def g_players(g: Game) -> List<&2, Player>:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  players

def g_done(g: Game) -> Bool:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  done

def g_set_players(g: Game, +ps: List<&2, Player>) -> Game:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  Game{seed, mode, round, actor, ps, fights, hist, done}

def g_set_actor(g: Game, +k: Nat) -> Game:
  Game{seed, mode, round, actor, players, fights, hist, done} = g
  Game{seed, mode, round, k, players, fights, hist, done}

def bot_seat(+g: Game, +k: Nat) -> Game:
  +ps = g_players(g)
  +p = pget(ps, k)
  pick(Game, p_alive(p), g_set_players(g, pset(ps, k, bot_play(g_seed(g), g_round(g), p))), g)

def bots_all(seats: List<&2, Nat>, +g: Game) -> Game:
  match seats:
    case Nil{}:
      g
    case k <> t:
      bots_all(t, bot_seat(g, k))

# bots mode: once seat 0 is out, the bots play the remaining rounds
def auto_round(+g: Game) -> Game:
  +go = Bool.not(g_done(g)) && Bool.not(p_alive(pget(g_players(g), 0n)))
  pick(Game, go, end_round(bots_all([1n, 2n, 3n], g)), g)

def auto_rest(fuel: Nat, +g: Game) -> Game:
  match fuel:
    case 0n:
      g
    case 1n+f:
      auto_rest(f, auto_round(g))

def next_alive(ps: List<&2, Player>, +after: Nat) -> Maybe<&2, Nat>:
  match ps:
    case Nil{}:
      None{}
    case +p <> t:
      pick(Maybe<&2, Nat>, p_alive(p) && Nat.is_gt(p_id(p), after), Some{p_id(p)}, next_alive(t, after))

def manual_next(m: Maybe<&2, Nat>, +g: Game) -> Game:
  match m:
    case None{}:
      end_round(g)
    case Some{k}:
      g_set_actor(g, k)

def g_end(+g: Game) -> Game:
  pick(Game, nat_eq(g_mode(g), 0n), auto_rest(max_rounds(), end_round(bots_all([1n, 2n, 3n], g))), manual_next(next_alive(g_players(g), g_actor(g)), g))

def lift(r: PRes, +g: Game) -> GRes:
  match r:
    case PGood{p}:
      GGood{g_set_players(g, pset(g_players(g), g_actor(g), p))}
    case PBad{m}:
      GBad{"illegal_move", m}

def g_apply_go(done: Bool, a: Act, +g: Game) -> GRes:
  match done a:
    case True{} _:
      GBad{"game_over", "the game is finished"}
    case False{} End{}:
      GGood{g_end(g)}
    case False{} Auto{}:
      GGood{g_end(bot_seat(g, g_actor(g)))}
    case False{} a2:
      lift(p_apply(g_seed(g), g_round(g), pget(g_players(g), g_actor(g)), a2), g)

def g_apply(+g: Game, a: Act) -> GRes:
  g_apply_go(g_done(g), a, g)

def new_game(+seed: U32, +mode: Nat) -> Game:
  Game{seed, mode, 1n, 0n, [new_player(seed, 0n), new_player(seed, 1n), new_player(seed, 2n), new_player(seed, 3n)], Nil{}, Nil{}, False{}}

# Move parsing
# ------------

def all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      Char.is_digit(h) && all_digits(t)

# 1 or 2 decimal digits only, so no huge number is ever built
def small_nat(+s: String) -> Maybe<&2, Nat>:
  +n = String.length(s)
  pick(Maybe<&2, Nat>, Nat.is_ge(n, 1n) && Nat.is_le(n, 2n) && all_digits(s), Nat.read(s), None{})

def one_arg(rest: List<&2, String>) -> Maybe<&2, Nat>:
  match rest:
    case Nil{}:
      None{}
    case h <> t:
      match t:
        case Nil{}:
          small_nat(h)
        case h2 <> t2:
          None{}

# index action kinds: 0 buy, 1 sell, 2 play (only board units can be sold)
def act_of(k: Nat, +i: Nat) -> Act:
  match k:
    case 0n:
      Buy{i}
    case 1n+k1:
      pick(Act, nat_eq(k1, 0n), Sell{i}, Play{i})

def mk_one(mi: Maybe<&2, Nat>, +k: Nat) -> Maybe<&2, Act>:
  match mi:
    case None{}:
      None{}
    case Some{+i}:
      Some{act_of(k, i)}

def mk_two(mi: Maybe<&2, Nat>, mj: Maybe<&2, Nat>) -> Maybe<&2, Act>:
  match mi mj:
    case Some{i} Some{j}:
      Some{Swap{i, j}}
    case _ _:
      None{}

def two_arg(rest: List<&2, String>) -> Maybe<&2, Act>:
  match rest:
    case Nil{}:
      None{}
    case h <> t:
      match t:
        case Nil{}:
          None{}
        case h2 <> t2:
          match t2:
            case Nil{}:
              mk_two(small_nat(h), small_nat(h2))
            case h3 <> t3:
              None{}

def zero_arg(rest: List<&2, String>, +a: Act) -> Maybe<&2, Act>:
  match rest:
    case Nil{}:
      Some{a}
    case h <> t:
      None{}

def parse_cmd(+h: String, +rest: List<&2, String>) -> Maybe<&2, Act>:
  pick(Maybe<&2, Act>, String.eq(h, "buy"), mk_one(one_arg(rest), 0n),
  pick(Maybe<&2, Act>, String.eq(h, "sell"), mk_one(one_arg(rest), 1n),
  pick(Maybe<&2, Act>, String.eq(h, "play"), mk_one(one_arg(rest), 2n),
  pick(Maybe<&2, Act>, String.eq(h, "swap"), two_arg(rest),
  pick(Maybe<&2, Act>, String.eq(h, "roll"), zero_arg(rest, Roll{}),
  pick(Maybe<&2, Act>, String.eq(h, "freeze"), zero_arg(rest, Freeze{}),
  pick(Maybe<&2, Act>, String.eq(h, "upgrade"), zero_arg(rest, Upgrade{}),
  pick(Maybe<&2, Act>, String.eq(h, "invest"), zero_arg(rest, Invest{}),
  pick(Maybe<&2, Act>, String.eq(h, "end"), zero_arg(rest, End{}),
  pick(Maybe<&2, Act>, String.eq(h, "auto"), zero_arg(rest, Auto{}), None{}))))))))))

def parse_toks(ts: List<&2, String>) -> Maybe<&2, Act>:
  match ts:
    case Nil{}:
      None{}
    case h <> rest:
      parse_cmd(h, rest)

def parse_move(+m: String) -> Maybe<&2, Act>:
  pick(Maybe<&2, Act>, Nat.is_le(String.length(m), 16n), parse_toks(String.split(m, ':')), None{})

def act_str(a: Act) -> String:
  match a:
    case Buy{i}:
      "buy:" ++ Nat.show(i)
    case Play{i}:
      "play:" ++ Nat.show(i)
    case Sell{i}:
      "sell:" ++ Nat.show(i)
    case Swap{i, j}:
      "swap:" ++ Nat.show(i) ++ ":" ++ Nat.show(j)
    case Roll{}:
      "roll"
    case Freeze{}:
      "freeze"
    case Upgrade{}:
      "upgrade"
    case Invest{}:
      "invest"
    case End{}:
      "end"
    case Auto{}:
      "auto"

# Replay
# ------

type RErr is Data:
  RErr{code: String, msg: String, index: Nat, move: String}

type RSt is Data:
  RSt{g: Game, n: Nat, err: Maybe<&2, RErr>}

def rstep_res(r: GRes, +g: Game, +m: String, +n: Nat) -> RSt:
  match r:
    case GGood{g2}:
      RSt{g2, 1n+n, None{}}
    case GBad{c, msg}:
      RSt{g, n, Some{RErr{c, msg, n, m}}}

def rstep_parse(mp: Maybe<&2, Act>, +m: String, +g: Game, +n: Nat) -> RSt:
  match mp:
    case None{}:
      RSt{g, n, Some{RErr{"bad_move", "unknown move; expected buy:i, play:i, sell:i, swap:i:j, roll, freeze, upgrade, invest, end or auto", n, m}}}
    case Some{a}:
      rstep_res(g_apply(g, a), g, m, n)

def rstep_go(err: Maybe<&2, RErr>, +m: String, +g: Game, +n: Nat) -> RSt:
  match err:
    case Some{e}:
      RSt{g, n, Some{e}}
    case None{}:
      rstep_parse(parse_move(m), m, g, n)

def rstep(+m: String, st: RSt) -> RSt:
  RSt{g, n, err} = st
  rstep_go(err, m, g, n)

def replay_go(ms: List<&2, String>, st: RSt) -> RSt:
  match ms:
    case Nil{}:
      st
    case m <> t:
      replay_go(t, rstep(m, st))

def split_moves(+s: String) -> List<&2, String>:
  pick(List<&2, String>, String.is_empty(s), Nil{}, String.split(s, ','))

# over the cap: the initial state and a too_many_moves error at index 0;
# otherwise the replay. A match (not an eager pick) keeps the long branch
# from ever running when the transcript is refused.
def replay_cap(over: Bool, +seed: U32, +mode: Nat, ms: List<&2, String>) -> RSt:
  match over:
    case True{}:
      RSt{new_game(seed, mode), 0n, Some{RErr{"too_many_moves", "at most 1024 moves per request", 0n, ""}}}
    case False{}:
      replay_go(ms, RSt{new_game(seed, mode), 0n, None{}})

def replay(+seed: U32, +mode: Nat, +ms: List<&2, String>) -> RSt:
  replay_cap(Nat.is_gt(len(String, ms), max_moves()), seed, mode, ms)

# Ranking
# -------
# Living seats by HP (higher first), then eliminated seats by the round
# they fell (later first); ties keep the lower seat id first.

def p2_a(x: P2) -> Nat:
  P2{a, b} = x
  a

def p2_b(x: P2) -> Nat:
  P2{a, b} = x
  b

def rank_key(+p: Player) -> Nat:
  pick(Nat, p_alive(p), Nat.add(100n, p_hp(p)), p_out(p))

def rank_ins(+xs: List<&2, P2>, +x: P2) -> List<&2, P2>:
  match xs:
    case Nil{}:
      [x]
    case +h <> t:
      pick(List<&2, P2>, Nat.is_gt(p2_b(x), p2_b(h)), x <> h <> t, h <> rank_ins(t, x))

def rank_go(ps: List<&2, Player>, acc: List<&2, P2>) -> List<&2, P2>:
  match ps:
    case Nil{}:
      acc
    case +p <> t:
      rank_go(t, rank_ins(acc, P2{p_id(p), rank_key(p)}))

def map_p2a(xs: List<&2, P2>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      p2_a(h) <> map_p2a(t)

def ranking(+ps: List<&2, Player>) -> List<&2, Nat>:
  map_p2a(rank_go(ps, Nil{}))

# JSON
# ----

def esc_char(+c: Char) -> Char:
  +u = Char.to_u32(c)
  pick(Char, U32.is_lt(u, 32) || U32.is_gt(u, 126) || U32.is_eq(u, 34) || U32.is_eq(u, 92), '?', c)

def esc(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      SCon{esc_char(h), esc(t)}

def jq(s: String) -> String:
  "\"" ++ esc(s) ++ "\""

def jn(n: Nat) -> String:
  Nat.show(n)

def jb(b: Bool) -> String:
  pick(String, b, "true", "false")

def jarr(xs: List<&2, String>) -> String:
  "[" ++ String.join(xs, ",") ++ "]"

def jobj(xs: List<&2, String>) -> String:
  "{" ++ String.join(xs, ",") ++ "}"

def kv(k: String, v: String) -> String:
  "\"" ++ k ++ "\":" ++ v

def jmaybe(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "null"
    case Some{n}:
      jn(n)

def map_jq(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      jq(h) <> map_jq(t)

# the gold a board sale gives for sure: the refund plus the unit's own
# (effective) Sell: gain gold abilities; MAKE and other effects not counted
def sell_gold_go(xs: List<&2, Abil>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Abil{+trig, tgt, +eff, +a, h} = x
      Nat.add(pick(Nat, nat_eq(trig, 3n) && nat_eq(eff, 2n), a, 0n), sell_gold_go(t))

def mon_sell_gold(+m: Mon) -> Nat:
  Nat.add(sell_refund(), sell_gold_go(mon_abils(m)))

# a unit with its effective values: golden doubles baseAttack/baseHealth,
# Rally, Income and ability amounts (text); id is always the catalog id
def unit_card(+m: Mon, +k: Card) -> String:
  Mon{c, a, h, s, +g} = m
  Card{cid, name, tribe, tier, ca, ch, sh, gu, ar, ra, inc, abils} = k
  jobj([kv("id", jn(c)), kv("name", jq(name)), kv("tribe", jq(tribe_name(tribe))), kv("golden", jb(g)), kv("attack", jn(a)), kv("health", jn(h)), kv("baseAttack", jn(dbl(g, ca))), kv("baseHealth", jn(dbl(g, ch))), kv("tier", jn(tier)), kv("shield", jb(s)), kv("guard", jb(gu)), kv("armor", jn(ar)), kv("rally", jn(dbl(g, ra))), kv("income", jn(dbl(g, inc))), kv("sellGold", jn(mon_sell_gold(m))), kv("keywords", jarr(map_jq(card_keywords_g(g, k)))), kv("text", jq(card_text_g(g, k)))])

def unit_json(+m: Mon) -> String:
  unit_card(m, card(mon_cid(m)))

def map_unit(xs: List<&2, Mon>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      unit_json(h) <> map_unit(t)

def map_jn(xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      jn(h) <> map_jn(t)

def board_json(b: List<&2, Mon>) -> String:
  jarr(map_unit(b))

def shop_card_json(c: Nat) -> String:
  unit_json(mon_of(c))

def map_shop(xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      shop_card_json(h) <> map_shop(t)

def shop_json(s: List<&2, Nat>) -> String:
  jarr(map_shop(s))

def player_json(+mode: Nat, +round: Nat, +viewer: Nat, +p: Player) -> String:
  Player{+id, hp, gold, +tier, upcost, +invest, frozen, rolls, +board, shop, alive, out, +hand, plays} = p
  +me = nat_eq(id, viewer)
  +bot = nat_eq(mode, 0n) && Bool.not(nat_eq(id, 0n))
  jobj([kv("id", jn(id)), kv("name", jq(seat_name(mode, id))), kv("bot", jb(bot)), kv("style", jq(pick(String, bot, seat_style(id), "agent"))), kv("alive", jb(alive)), kv("hp", jn(hp)), kv("gold", pick(String, me, jn(gold), "null")), kv("income", jn(Econ.income(round, invest, board_income(board)))), kv("nextIncome", jn(Econ.income(1n+round, invest, board_income(board)))), kv("tier", jn(tier)), kv("upgradeCost", pick(String, Nat.is_lt(tier, max_tier()), jn(upcost), "null")), kv("investment", jn(invest)), kv("frozen", pick(String, me, jb(frozen), "null")), kv("board", board_json(board)), kv("hand", pick(String, me, board_json(hand), "null")), kv("handCount", jn(len(Mon, hand))), kv("plays", jn(plays)), kv("shop", pick(String, me, shop_json(shop), "null")), kv("ready", jb(alive && nat_eq(mode, 1n) && Nat.is_lt(id, viewer))), kv("eliminatedRound", pick(String, alive, "null", jn(out)))])

def players_json(ps: List<&2, Player>, +mode: Nat, +round: Nat, +viewer: Nat) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      player_json(mode, round, viewer, p) <> players_json(t, mode, round, viewer)

def winner_code(+res: Nat, +a: Nat, +b: Nat) -> String:
  pick(String, nat_eq(res, 0n), "-1", jn(pick(Nat, nat_eq(res, 1n), a, b)))

# compact unit snapshot inside combat events (names/text: /api/rules)
def snap_json(m: Mon) -> String:
  Mon{+c, a, h, s, g} = m
  jobj([kv("id", jn(c)), kv("attack", jn(a)), kv("health", jn(h)), kv("shield", jb(s)), kv("guard", jb(c_guard(c))), kv("golden", jb(g))])

def map_snap(xs: List<&2, Mon>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      snap_json(h) <> map_snap(t)

def snaps(xs: List<&2, Mon>) -> String:
  jarr(map_snap(xs))

def idx_or_gone(dead: Bool, +i: Nat) -> String:
  pick(String, dead, "-1", jn(i))

def reason_name(w: Nat) -> String:
  get_or(String, ["elimination", "empty", "fuel"], w, "?")

def ev_json(+a: Nat, +b: Nat, e: Ev) -> String:
  match e:
    case EvAtk{step, side, ti, ai2, ti2, ba, bb, aa, ab, +asb, +tsb, +ad, +td, ral, aatk, text}:
      jobj([kv("kind", jq("attack")), kv("step", jn(step)), kv("side", jq(pick(String, side, "a", "b"))), kv("attackerIndex", "0"), kv("targetIndex", jn(ti)), kv("attackerAfterIndex", idx_or_gone(ad, ai2)), kv("targetAfterIndex", idx_or_gone(td, ti2)), kv("rally", jn(ral)), kv("attackerAttack", jn(aatk)), kv("beforeA", snaps(ba)), kv("beforeB", snaps(bb)), kv("afterA", snaps(aa)), kv("afterB", snaps(ab)), kv("attackerShieldBroken", jb(asb)), kv("targetShieldBroken", jb(tsb)), kv("attackerDied", jb(ad)), kv("targetDied", jb(td)), kv("text", jq(text))])
    case EvEnd{step, +res, dmg, why, aa, ab, text}:
      jobj([kv("kind", jq("end")), kv("step", jn(step)), kv("winner", winner_code(res, a, b)), kv("damage", jn(dmg)), kv("finishReason", jq(reason_name(why))), kv("afterA", snaps(aa)), kv("afterB", snaps(ab)), kv("text", jq(text))])

def map_ev(xs: List<&2, Ev>, +a: Nat, +b: Nat) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      ev_json(a, b, h) <> map_ev(t, a, b)

def fight_json(f: Fight) -> String:
  Fight{+round, +a, +b, +res, +dmg, ba, bb, log, evs} = f
  jobj([kv("round", jn(round)), kv("a", jn(a)), kv("b", jn(b)), kv("winner", winner_code(res, a, b)), kv("damage", jn(dmg)), kv("aBoard", board_json(ba)), kv("bBoard", board_json(bb)), kv("log", jarr(map_jq(log))), kv("events", jarr(map_ev(evs, a, b)))])

# the viewer's most recent fight (detailed), even after bots fast-forward
def fight_has(+k: Nat, f: Fight) -> Bool:
  Fight{round, +a, +b, res, dmg, ba, bb, log, evs} = f
  nat_eq(a, k) || nat_eq(b, k)

def last_fight_go(xs: List<&2, Fight>, +k: Nat, best: Maybe<&2, Fight>) -> Maybe<&2, Fight>:
  match xs:
    case Nil{}:
      best
    case +f <> t:
      last_fight_go(t, k, pick(Maybe<&2, Fight>, fight_has(k, f), Some{f}, best))

def last_fight_json(m: Maybe<&2, Fight>) -> String:
  match m:
    case None{}:
      "null"
    case Some{f}:
      fight_json(f)

def hist_json(f: Fight) -> String:
  Fight{+round, +a, +b, +res, +dmg, ba, bb, log, evs} = f
  jobj([kv("round", jn(round)), kv("a", jn(a)), kv("b", jn(b)), kv("winner", winner_code(res, a, b)), kv("damage", jn(dmg))])

# Legal actions: every recruit candidate that p_apply accepts, plus end
# and auto, so the list agrees with the rules by construction.

type Cand is Data:
  Cand{a: Act}

def cands_one(ix: List<&2, Nat>, +k: Nat) -> List<&2, Act>:
  match ix:
    case Nil{}:
      Nil{}
    case +i <> t:
      act_of(k, i) <> cands_one(t, k)

def cands_j(js: List<&2, Nat>, +i: Nat) -> List<&2, Act>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      Swap{i, j} <> cands_j(t, i)

def cands_swap(ix: List<&2, Nat>, +n: Nat) -> List<&2, Act>:
  match ix:
    case Nil{}:
      Nil{}
    case +i <> t:
      List.append(&2, Act, cands_j(List.drop(&2, Nat, List.range(n), 1n+i), i), cands_swap(t, n))

def legal_filter(xs: List<&2, Act>, +seed: U32, +round: Nat, +p: Player) -> List<&2, Act>:
  match xs:
    case Nil{}:
      Nil{}
    case +a <> t:
      +r = legal_filter(t, seed, round, p)
      pick(List<&2, Act>, pres_ok(p_apply(seed, round, p, a)), a <> r, r)

def recruit_cands(+p: Player) -> List<&2, Act>:
  +nb = len(Mon, p_board(p))
  +ns = len(Nat, p_shop(p))
  +nh = len(Mon, p_hand(p))
  List.append(&2, Act, cands_one(List.range(ns), 0n), List.append(&2, Act, cands_one(List.range(nh), 2n), List.append(&2, Act, cands_one(List.range(nb), 1n), List.append(&2, Act, cands_swap(List.range(nb), nb), [Roll{}, Freeze{}, Upgrade{}, Invest{}]))))

# every recruit action p_apply accepts for p (End/Auto are always legal
# while the game runs and are added by legal_list)
def legal_acts(+seed: U32, +round: Nat, +p: Player) -> List<&2, Act>:
  legal_filter(recruit_cands(p), seed, round, p)

def map_act_str(xs: List<&2, Act>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> t:
      act_str(a) <> map_act_str(t)

def legal_list(+seed: U32, +round: Nat, +p: Player) -> List<&2, String>:
  List.append(&2, String, map_act_str(legal_acts(seed, round, p)), ["end", "auto"])

def legal_actions(+g: Game) -> List<&2, String>:
  pick(List<&2, String>, g_done(g), Nil{}, legal_list(g_seed(g), g_round(g), pget(g_players(g), g_actor(g))))

def err_json(e: Maybe<&2, RErr>) -> String:
  match e:
    case None{}:
      "null"
    case Some{RErr{code, msg, index, move}}:
      jobj([kv("code", jq(code)), kv("message", jq(msg)), kv("index", jn(index)), kv("move", jq(move))])

def costs_json() -> String:
  jobj([kv("buy", jn(buy_cost())), kv("roll", jn(roll_cost())), kv("invest", jn(invest_cost())), kv("sellRefund", jn(sell_refund())), kv("boardMax", "5"), kv("handMax", jn(max_hand())), kv("play", "0"), kv("shopSize", jn(shop_size())), kv("maxInvestment", jn(max_invest())), kv("maxTier", jn(max_tier())), kv("startHp", jn(start_hp())), kv("maxMoves", jn(max_moves()))])

def jopp(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "-1"
    case Some{n}:
      jn(n)

def opp_json(+g: Game) -> String:
  pick(String, g_done(g), "-1", jopp(opp_in(pairings(alive_ids(g_players(g)), g_round(g)), g_actor(g))))

def map_fight(xs: List<&2, Fight>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      fight_json(h) <> map_fight(t)

def map_hist(xs: List<&2, Fight>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      hist_json(h) <> map_hist(t)

def game_json_go(+g: Game, +n: Nat, +err: Maybe<&2, RErr>) -> String:
  Game{+seed, +mode, +round, +actor, +players, fights, +hist, +done} = g
  +rank = ranking(players)
  jobj([kv("schemaVersion", jn(protocol_version())), kv("protocolVersion", jn(protocol_version())), kv("seed", U32.show(seed)), kv("mode", jq(pick(String, nat_eq(mode, 0n), "bots", "manual"))), kv("round", jn(round)), kv("maxRounds", jn(max_rounds())), kv("phase", jq(pick(String, done, "finished", "recruit"))), kv("player", jn(actor)), kv("nextOpponent", opp_json(g)), kv("costs", costs_json()), kv("players", jarr(players_json(players, mode, round, actor))), kv("legalActions", jarr(map_jq(legal_actions(g)))), kv("combat", jarr(map_fight(fights))), kv("history", jarr(map_hist(hist))), kv("lastFight", last_fight_json(last_fight_go(hist, actor, None{}))), kv("winner", pick(String, done, jn(get_or(Nat, rank, 0n, 0n)), "null")), kv("rank", pick(String, done, jarr(map_jn(rank)), "null")), kv("error", err_json(err)), kv("movesApplied", jn(n))])

def game_json(st: RSt) -> String:
  RSt{g, n, err} = st
  game_json_go(g, n, err)

def rst_status(st: RSt) -> Nat:
  RSt{g, n, err} = st
  pick(Nat, Maybe.is_some(&2, RErr, err), 400n, 200n)

# ===== API (called by engine/main.bend) — keep at the end of the file =====

# JSON body {"error":{"code":..,"message":..}} for HTTP-level errors
def api_error(code: String, msg: String) -> String:
  jobj([kv("error", jobj([kv("code", jq(code)), kv("message", jq(msg))]))])

def seed_ok(+s: String) -> Bool:
  +n = String.length(s)
  Nat.is_ge(n, 1n) && all_digits(s) && (Nat.is_lt(n, 10n) || (nat_eq(n, 10n) && String.is_le(s, "4294967295")))

def parse_seed(+s: String) -> Maybe<&2, U32>:
  pick(Maybe<&2, U32>, seed_ok(s), U32.read(s), None{})

def parse_mode(+s: String) -> Maybe<&2, Nat>:
  pick(Maybe<&2, Nat>, String.is_empty(s) || String.eq(s, "bots"), Some{0n}, pick(Maybe<&2, Nat>, String.eq(s, "manual"), Some{1n}, None{}))

# over the cap the API answers an error body only (as the HTTP layer does)
def api_game_run(over: Bool, +seed: U32, +mode: Nat, +ms: List<&2, String>) -> Nat & String:
  match over:
    case True{}:
      (400n, api_error("too_many_moves", "at most 1024 moves per request"))
    case False{}:
      +st = replay(seed, mode, ms)
      (rst_status(st), game_json(st))

def api_game_go(ms: Maybe<&2, U32>, mm: Maybe<&2, Nat>, +moves: String) -> Nat & String:
  match ms mm:
    case None{} _:
      (400n, api_error("bad_request", "seed must be a decimal integer in 0..4294967295"))
    case Some{s} None{}:
      (400n, api_error("bad_request", "mode must be bots or manual"))
    case Some{seed} Some{mode}:
      +ms = split_moves(moves)
      api_game_run(Nat.is_gt(len(String, ms), max_moves()), seed, mode, ms)

# HTTP status and JSON body for GET /api/game. seed: decimal U32 text
# (required); mode: "bots" | "manual" | "" (bots); moves: the already
# URL-decoded comma-separated move list ("" means none).
def api_game(seed: String, mode: String, moves: String) -> Nat & String:
  api_game_go(parse_seed(seed), parse_mode(mode), moves)

def trig_name(t: Nat) -> String:
  get_or(String, ["play", "kinplay", "endturn", "sell"], t, "?")

def eff_name(e: Nat) -> String:
  get_or(String, ["stats", "statsPerHand", "gold", "make", "statsPerPlay"], e, "?")

def abil_json(x: Abil) -> String:
  Abil{trig, tgt, eff, a, h} = x
  jobj([kv("trigger", jq(trig_name(trig))), kv("target", jq(pick(String, nat_eq(tgt, 0n), "self", "kin"))), kv("effect", jq(eff_name(eff))), kv("a", jn(a)), kv("h", jn(h))])

def map_abil(xs: List<&2, Abil>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      abil_json(h) <> map_abil(t)

def card_rule_json(+k: Card) -> String:
  Card{cid, name, tribe, tier, atk, hp, sh, gu, ar, ra, inc, abils} = k
  jobj([kv("id", jn(cid)), kv("name", jq(name)), kv("tribe", jq(tribe_name(tribe))), kv("tier", jn(tier)), kv("attack", jn(atk)), kv("health", jn(hp)), kv("shield", jb(sh)), kv("guard", jb(gu)), kv("armor", jn(ar)), kv("rally", jn(ra)), kv("income", jn(inc)), kv("keywords", jarr(map_jq(card_keywords(k)))), kv("abilities", jarr(map_abil(abils))), kv("text", jq(card_text(k)))])

def map_card_rule(xs: List<&2, Card>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      card_rule_json(h) <> map_card_rule(t)

def rules_text() -> List<&2, String>:
  [ "4 seats, start at " ++ Nat.show(start_hp()) ++ " HP. At most " ++ Nat.show(max_rounds()) ++ " rounds; the game ends early when one seat is left."
  , "Each round: recruit phase, then every living seat fights its scheduled opponent."
  , "Gold resets every round to income = min(2 + round, 10) + investment + Income units on the board. Unspent gold is lost."
  , "buy:i costs 3 gold and puts shop card i at the right end of your hand (max 7 cards; a full hand cannot buy). Buying never touches the board, except when the new card completes a triple (see Golden)."
  , "play:i is free: hand card i resolves its Play abilities, then joins the right end of the board (max 5 units). Then each other card of its tribe that was already on the board resolves its After-you-play abilities once, left to right."
  , "sell:i sells board unit i for " ++ Nat.show(sell_refund()) ++ " gold, then its Sell abilities fire. Only board units can be sold; hand cards cannot. Your hand is private; other seats only see how many cards you hold."
  , "Golden: three regular copies of the same card in your hand and board assemble automatically into one golden card after a buy, play or sell and at the start of each recruit phase. Hand copies are used first; the golden card goes to the right end of your hand. Its attack and health are the three copies' totals minus one printed card (twice the printed stats plus every buff). A golden unit doubles its ability amounts (stats and gold), Rally and Income; its random-card abilities fire twice; Armor, Shield, Guard and the sell refund stay the same. Golden cards never merge again."
  , "Tribes: Ember, Tide and Stone. Neutral cards belong to no tribe: tribe abilities (other allies of a tribe, after you play a card of a tribe, random cards of a tribe) never affect, trigger on or create them."
  , "roll costs 1 gold and redraws 3 cards from tiers up to yours. freeze toggles keeping the current shop for next round; slots emptied by buying are refilled with fresh cards."
  , "upgrade raises your tier (1 to " ++ Nat.show(max_tier()) ++ "). Leaving tier 1/2/3/4 costs " ++ Nat.show(Econ.upgrade_base(1n)) ++ "/" ++ Nat.show(Econ.upgrade_base(2n)) ++ "/" ++ Nat.show(Econ.upgrade_base(3n)) ++ "/" ++ Nat.show(Econ.upgrade_base(4n)) ++ " gold; the cost drops by 1 each round you wait, but never below " ++ Nat.show(Econ.upgrade_floor(1n)) ++ "/" ++ Nat.show(Econ.upgrade_floor(2n)) ++ "/" ++ Nat.show(Econ.upgrade_floor(3n)) ++ "/" ++ Nat.show(Econ.upgrade_floor(4n)) ++ ". Higher tiers unlock stronger cards."
  , "invest costs 2 gold now for +1 income every later round (max 3 investments)."
  , "swap:i:j reorders your board. Units attack from the front; a surviving attacker goes to the back of its line."
  , "Combat: sides alternate; the side with more units starts (tie: seeded coin). Targets are seeded-random, but a Guard must be attacked first. Rally n: before each of its attacks a unit gains +n attack for the rest of the combat. A hit of 0 does nothing. A hit of 1 or more on a Shield breaks the Shield and does nothing else; otherwise Armor n reduces the hit by n. Both units deal damage simultaneously. Combat stops after " ++ Nat.show(combat_fuel()) ++ " attacks (draw). Combat never changes your real board."
  , "End of turn abilities fire at the end of every recruit phase, board left to right; each one sees the board as the abilities before it left it. Abilities never trigger other abilities."
  , "Ability counts: 'for each card in your hand' and 'for each card you played' count at most 4. During a play the played card has already left your hand and is not yet counted as played (it counts as 'played earlier' for later plays and at end of turn). 'Other X allies' never includes the source itself."
  , "The loser of a fight takes damage = winner tier + sum of tiers of the winner's surviving units, but at most " ++ Nat.show(damage_cap(0n)) ++ " + the round number (round 1: " ++ Nat.show(damage_cap(1n)) ++ ", round " ++ Nat.show(max_rounds()) ++ ": " ++ Nat.show(damage_cap(max_rounds())) ++ "). A draw deals no damage."
  , "Pairings rotate: with 4 seats round r pairs (0,1)(2,3), (0,2)(1,3), (0,3)(1,2) by r mod 3 over living seats in id order; with 3 seats one seat has a bye."
  , "Ranking: living seats by HP, then eliminated seats by elimination round (later is better); ties go to the lower seat id."
  ]

def upgrade_costs_json() -> String:
  jobj([kv("1", jn(Econ.upgrade_base(1n))), kv("2", jn(Econ.upgrade_base(2n))), kv("3", jn(Econ.upgrade_base(3n))), kv("4", jn(Econ.upgrade_base(4n)))])

# keyed by the CURRENT tier (1..4), like upgradeCosts: the lowest cost
# the per-round discount reaches while leaving that tier
def upgrade_floors_json() -> String:
  jobj([kv("1", jn(Econ.upgrade_floor(1n))), kv("2", jn(Econ.upgrade_floor(2n))), kv("3", jn(Econ.upgrade_floor(3n))), kv("4", jn(Econ.upgrade_floor(4n)))])

# plain-language keyword and trigger reference for clients (UI, agents);
# every entry restates a rule enforced above, it adds no mechanics
def glossary_entry(+term: String, +text: String) -> String:
  jobj([kv("term", jq(term)), kv("text", jq(text))])

def glossary_json() -> String:
  jarr(
    [ glossary_entry("Guard", "Enemies must attack a Guard unit while one is alive on its side.")
    , glossary_entry("Shield", "The first hit of 1 or more on this unit only breaks the Shield and deals no damage; a hit of 0 leaves the Shield intact.")
    , glossary_entry("Armor", "Armor n lowers every damaging hit on this unit by n (to a minimum of 0), unless a Shield absorbs it.")
    , glossary_entry("Rally", "Rally n: right before each of its attacks this unit gains +n attack for the rest of the combat.")
    , glossary_entry("Income", "Income n: when a new round starts, you get n more gold for this unit on your board.")
    , glossary_entry("Play", "Play: resolves when you move this card from your hand to the board, before it joins the board.")
    , glossary_entry("After you play", "After you play another card of this tribe: resolves for this unit already on your board, once per such play, after the played card joins the board.")
    , glossary_entry("End of turn", "End of turn: resolves when the recruit phase ends, board left to right, before combat.")
    , glossary_entry("Sell", "Sell: resolves when you sell this unit from the board. Only board units can be sold.")
    , glossary_entry("Other allies", "'Other X allies' are the units of tribe X (Ember, Tide or Stone) on your board except the source itself. Neutral units are never included.")
    , glossary_entry("Counts", "'For each card in your hand' or 'for each card you played' counts at most 4. Inside a play the played card is not counted.")
    , glossary_entry("Triple", "Three regular (non-golden) copies of the same card across your hand and board. They assemble automatically into one golden card after a buy, play or sell and at the start of a recruit phase; hand copies are used first.")
    , glossary_entry("Golden", "Three regular copies of a card assemble into a golden card: totals of the copies minus one printed card, and doubled ability amounts, Rally and Income (Armor unchanged).")
    , glossary_entry("Neutral", "Neutral cards belong to no tribe: tribe abilities never buff, trigger on or create them. They still count as cards played.")
    , glossary_entry("Damage cap", "The loser of a fight takes the winner's tier plus the tiers of the winner's surviving units, at most 3 + the round number.")
    ])

def api_rules() -> String:
  jobj([kv("schemaVersion", jn(protocol_version())), kv("protocolVersion", jn(protocol_version())), kv("game", jq("Bend Grounds")), kv("maxRounds", jn(max_rounds())), kv("seats", "4"), kv("costs", costs_json()), kv("upgradeCosts", upgrade_costs_json()), kv("upgradeFloors", upgrade_floors_json()), kv("damageCap", jobj([kv("base", jn(damage_cap(0n))), kv("perRound", jn(Nat.sub(damage_cap(1n), damage_cap(0n))))])), kv("tribes", jarr(map_jq(["Ember", "Tide", "Stone", "Neutral"]))), kv("cards", jarr(map_card_rule(card_list()))), kv("actions", jarr(map_jq(["buy:i", "play:i", "sell:i", "swap:i:j", "roll", "freeze", "upgrade", "invest", "end", "auto"]))), kv("modes", jobj([kv("bots", jq("moves act for seat 0; end lets bots 1-3 recruit, then combat resolves")), kv("manual", jq("moves act for the seat in player; end passes to the next living seat; after the last, combat resolves"))])), kv("botStyles", jarr(map_jq(["tempo", "economy", "climber"]))), kv("rules", jarr(map_jq(rules_text()))), kv("glossary", glossary_json())])

def api_health() -> String:
  "{\"ok\":true,\"engine\":\"bend2\",\"game\":\"Bend Grounds\",\"schemaVersion\":" ++ jn(protocol_version()) ++ ",\"protocolVersion\":" ++ jn(protocol_version()) ++ "}"
