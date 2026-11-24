# Bend Grounds economy helpers. Pure Nat functions used directly by the
# engine (engine/game.bend). LAWS.bend states laws about these; keep
# signatures stable (coordinate changes through docs/SPEC.md).
import Base

# spend(gold, cost): Some(gold - cost) when gold >= cost, None otherwise
def spend(gold: Nat, cost: Nat) -> Maybe<&2, Nat>:
  match gold cost:
    case g 0n:
      Some{g}
    case 0n 1n+c:
      None{}
    case 1n+g 1n+c:
      spend(g, c)

# min(a, cap)
def cap(a: Nat, c: Nat) -> Nat:
  match a c:
    case 0n c0:
      0n
    case 1n+p 0n:
      0n
    case 1n+p 1n+q:
      1n+cap(p, q)

# base income for a round (round starts at 1n): min(2 + round, 10)
def base_income(round: Nat) -> Nat:
  cap(2n+round, 10n)

# income = base(round) + investment + bonus (Purse Moth count)
def income(round: Nat, invest: Nat, bonus: Nat) -> Nat:
  Nat.add(Nat.add(base_income(round), invest), bonus)

# one gold off a cost, floor 0 (Nat.sub(c, 1)); the per-round step inside
# upgrade_cost_next
def decay(c: Nat) -> Nat:
  match c:
    case 0n:
      0n
    case 1n+p:
      p

# highest tier; a player at max_tier cannot upgrade further
def max_tier() -> Nat:
  5n

# max(a, b)
def nmax(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n b0:
      b0
    case 1n+p 0n:
      1n+p
    case 1n+p 1n+q:
      1n+nmax(p, q)

# base cost to LEAVE a tier, paid when the upgrade starts being offered:
# tier 1 -> 2 costs 5, 2 -> 3 costs 8, 3 -> 4 costs 11, 4 -> 5 costs 13;
# tier 0 (unused) and tier >= 5 (max tier) cost 0 / unavailable
def upgrade_base(tier: Nat) -> Nat:
  match tier:
    case 0n:
      0n
    case 1n:
      5n
    case 2n:
      8n
    case 3n:
      11n
    case 4n:
      13n
    case 5n+t:
      0n

# lowest cost the per-round discount can reach while leaving a tier:
# tier 1: 3, tier 2: 5, tier 3: 8, tier 4: 10; tier 0 and >= 5: 0
def upgrade_floor(tier: Nat) -> Nat:
  match tier:
    case 0n:
      0n
    case 1n:
      3n
    case 2n:
      5n
    case 3n:
      8n
    case 4n:
      10n
    case 5n+t:
      0n

# the stored upgrade cost after one more round passes at `tier`:
# for tiers 1..4, one gold cheaper but never below the tier's floor,
# max(upgrade_floor(tier), cost - 1); tier 0 and max tier (>= 5) always 0,
# whatever cost is passed in.
def upgrade_cost_next(tier: Nat, cost: Nat) -> Nat:
  match tier:
    case 0n:
      0n
    case 1n:
      nmax(3n, decay(cost))
    case 2n:
      nmax(5n, decay(cost))
    case 3n:
      nmax(8n, decay(cost))
    case 4n:
      nmax(10n, decay(cost))
    case 5n+t:
      0n

# the stored cost after n more rounds at `tier` (n-fold upgrade_cost_next);
# a forecast helper, same step the engine applies once per round
def cost_after(+tier: Nat, cost: Nat, n: Nat) -> Nat:
  match n:
    case 0n:
      cost
    case 1n+m:
      upgrade_cost_next(tier, cost_after(tier, cost, m))

# hp after taking damage, saturating at 0
def hp_after(hp: Nat, dmg: Nat) -> Nat:
  Nat.sub(hp, dmg)

# damage dealt by a combat winner: its tier plus the tiers of survivors
def damage(tier: Nat, survivors: List<&2, Nat>) -> Nat:
  match survivors:
    case Nil{}:
      tier
    case t <> ts:
      Nat.add(t, damage(tier, ts))

# board has room for another unit (board max 5)
def has_room(len: Nat) -> Bool:
  Nat.is_lt(len, 5n)
