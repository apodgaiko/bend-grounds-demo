# Bend Grounds: the proofs of LAWS.bend. Every Laws.x def below fills the
# law of the same name; the rest is a small kit of order lemmas on Base's
# Nat.is_le / Nat.is_lt. No holes, no @unsafe, no foreign code.
#
#   bun vendor/bend/bend2/main.ts PROOF.bend --verdict

import Base
import ./engine/econ.bend as Econ
import ./LAWS.bend as Laws

# Kit
# ---

# a type picked by a Bool: rewriting through it refutes False == True
def BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# from False == True, anything
def absurd(-P: Type, h: {False{} == True{} : Bool}) -> P:
  %h : BD(_, P, Unit)
  Unit{}

# 0 <= b
def le0(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# a <= b implies a <= 1 + b
def le_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, h)
    case 1n+ap 1n+bp:
      le_succ(ap, bp, h)

def le_trans(a: Nat, b: Nat, c: Nat,
  hab: {Nat.is_le(a, b) == True{} : Bool},
  hbc: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ c0:
      le0(c0)
    case 1n+ap 0n _:
      absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, hab)
    case 1n+ap 1n+bp 0n:
      absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, hbc)
    case 1n+ap 1n+bp 1n+cp:
      le_trans(ap, bp, cp, hab, hbc)

# a <= a + k
def le_add(a: Nat, k: Nat) -> {Nat.is_le(a, Nat.add(a, k)) == True{} : Bool}:
  match a:
    case 0n:
      le0(k)
    case 1n+p:
      le_add(p, k)

# b <= a + b
def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      le_refl(b)
    case 1n++p:
      le_succ(b, Nat.add(p, b), le_add_l(p, b))

# 1 + (a + b) == a + (1 + b)
def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a < b implies 1 + a <= b
def lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool})
  -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      le0(q)
    case 1n+p 0n:
      absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      lt_le(p, q, h)

# 1 + a <= b implies a < b
def le_lt(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool})
  -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      le_lt(p, q, h)

# cap is monotone in its first argument
def cap_mono(a: Nat, c: Nat) -> {Nat.is_le(Econ.cap(a, c), Econ.cap(1n+a, c)) == True{} : Bool}:
  match a c:
    case 0n c0:
      le0(Econ.cap(1n, c0))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cap_mono(p, q)

# equality is symmetric
def sym(-A: Type, -a: A, -b: A, e: {a == b : A}) -> {b == a : A}:
  %e : {_ == a : A}
  {==}

# a <= max(a, b)
def le_nmax_l(a: Nat, b: Nat) -> {Nat.is_le(a, Econ.nmax(a, b)) == True{} : Bool}:
  match a b:
    case 0n b0:
      le0(b0)
    case 1n+p 0n:
      le_refl(p)
    case 1n+p 1n+q:
      le_nmax_l(p, q)

# a <= c and b <= c imply max(a, b) <= c
def nmax_le(a: Nat, b: Nat, c: Nat,
  ha: {Nat.is_le(a, c) == True{} : Bool},
  hb: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(Econ.nmax(a, b), c) == True{} : Bool}:
  match a b c:
    case 0n b0 c0:
      hb
    case 1n+p 0n c0:
      ha
    case 1n+p 1n+q 0n:
      absurd({Nat.is_le(Econ.nmax(1n+p, 1n+q), 0n) == True{} : Bool}, ha)
    case 1n+p 1n+q 1n+r:
      nmax_le(p, q, r, ha, hb)

# a <= b implies max(a, b) == b
def nmax_eq_r(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool})
  -> {Econ.nmax(a, b) == b : Nat}:
  match a b:
    case 0n b0:
      {==}
    case 1n+p 0n:
      absurd({Econ.nmax(1n+p, 0n) == 0n : Nat}, h)
    case 1n+p 1n+q:
      %nmax_eq_r(p, q, h) : {1n+Econ.nmax(p, q) == 1n+_ : Nat}
      {==}

# Spending
# --------

def Laws.spend_pays(cost, rest):
  match cost:
    case 0n:
      match rest:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+c:
      Laws.spend_pays(c, rest)

def Laws.spend_rejects(gold, k):
  match gold:
    case 0n:
      {==}
    case 1n+g:
      Laws.spend_rejects(g, k)

def Laws.spend_le(gold, cost):
  match gold cost:
    case 0n 0n:
      {==}
    case 1n+g 0n:
      le_refl(g)
    case 0n 1n+c:
      {==}
    case 1n+g 1n+c:
      le_succ(Maybe.default(&2, Nat, Econ.spend(g, c), 0n), g, Laws.spend_le(g, c))

def Laws.spend_keeps_bound(gold, cost, max, h):
  le_trans(Maybe.default(&2, Nat, Econ.spend(gold, cost), 0n), gold, max,
    Laws.spend_le(gold, cost), h)

# Caps
# ----

def Laws.cap_le(a, c):
  match a c:
    case 0n c0:
      le0(c0)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Laws.cap_le(p, q)

def Laws.cap_below(a, c):
  match a c:
    case 0n c0:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Laws.cap_below(p, q)

def Laws.cap_keeps(a, k):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Laws.cap_keeps(p, k) : {1n+Econ.cap(p, Nat.add(p, k)) == 1n+_ : Nat}
      {==}

# Income
# ------

def Laws.base_income_le(round):
  Laws.cap_le(2n+round, 10n)

def Laws.base_income_ge(round):
  le0(Econ.cap(round, 8n))

def Laws.base_income_mono(round):
  cap_mono(round, 8n)

def Laws.income_invest(round, invest, bonus):
  %add_succ(Econ.base_income(round), invest)
    : {Nat.add(_, bonus) == 1n+Nat.add(Nat.add(Econ.base_income(round), invest), bonus) : Nat}
  {==}

def Laws.income_bonus(round, invest, bonus):
  %add_succ(Nat.add(Econ.base_income(round), invest), bonus)
    : {_ == 1n+Nat.add(Nat.add(Econ.base_income(round), invest), bonus) : Nat}
  {==}

def Laws.income_ge_base(round, invest, bonus):
  le_trans(Econ.base_income(round), Nat.add(Econ.base_income(round), invest),
    Nat.add(Nat.add(Econ.base_income(round), invest), bonus),
    le_add(Econ.base_income(round), invest),
    le_add(Nat.add(Econ.base_income(round), invest), bonus))

# Upgrade costs
# -------------

def Laws.decay_le(c):
  match c:
    case 0n:
      {==}
    case 1n++p:
      le_succ(p, p, le_refl(p))

def Laws.decay_step(c):
  {==}

def Laws.upgrade_bases():
  {==}

def Laws.upgrade_floors():
  {==}

def Laws.upgrade_base_le(tier):
  match tier:
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
    case 5n+t:
      {==}

def Laws.upgrade_base_top(k):
  {==}

def Laws.upgrade_floor_le_base(tier):
  match tier:
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
    case 5n+t:
      {==}

def Laws.upgrade_floor_le(tier):
  match tier:
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
    case 5n+t:
      {==}

# floor(tier) <= base_income(8 + k), which is 10 for every k
def floor_le_late_base(tier: Nat, k: Nat)
  -> {Nat.is_le(Econ.upgrade_floor(tier), Econ.base_income(8n+k)) == True{} : Bool}:
  match k:
    case 0n:
      Laws.upgrade_floor_le(tier)
    case 1n+p:
      Laws.upgrade_floor_le(tier)

def Laws.upgrade_floor_affordable(tier, k, invest, bonus):
  le_trans(Econ.upgrade_floor(tier), Econ.base_income(8n+k), Econ.income(8n+k, invest, bonus),
    floor_le_late_base(tier, k), Laws.income_ge_base(8n+k, invest, bonus))

def Laws.upgrade_next_top(k, c):
  {==}

def Laws.upgrade_next_ge_floor(tier, c):
  match tier:
    case 0n:
      {==}
    case 1n:
      le_nmax_l(3n, Econ.decay(c))
    case 2n:
      le_nmax_l(5n, Econ.decay(c))
    case 3n:
      le_nmax_l(8n, Econ.decay(c))
    case 4n:
      le_nmax_l(10n, Econ.decay(c))
    case 5n+t:
      {==}

def Laws.upgrade_next_le(tier, c, h):
  match tier:
    case 0n:
      le0(c)
    case 1n:
      nmax_le(3n, Econ.decay(c), c, h, Laws.decay_le(c))
    case 2n:
      nmax_le(5n, Econ.decay(c), c, h, Laws.decay_le(c))
    case 3n:
      nmax_le(8n, Econ.decay(c), c, h, Laws.decay_le(c))
    case 4n:
      nmax_le(10n, Econ.decay(c), c, h, Laws.decay_le(c))
    case 5n+t:
      le0(c)

def Laws.upgrade_next_step(u, hu, k):
  match u:
    case 0n:
      nmax_eq_r(3n, Nat.add(k, 3n), le_add_l(k, 3n))
    case 1n:
      nmax_eq_r(5n, Nat.add(k, 5n), le_add_l(k, 5n))
    case 2n:
      nmax_eq_r(8n, Nat.add(k, 8n), le_add_l(k, 8n))
    case 3n:
      nmax_eq_r(10n, Nat.add(k, 10n), le_add_l(k, 10n))
    case 4n+w:
      match w:
        case 0n:
          absurd({Econ.upgrade_cost_next(5n, 1n+Nat.add(k, 0n)) == Nat.add(k, 0n) : Nat}, hu)
        case 1n+v:
          absurd({Econ.upgrade_cost_next(6n+v, 1n+Nat.add(k, 0n)) == Nat.add(k, 0n) : Nat}, hu)

def Laws.upgrade_next_floor(tier):
  match tier:
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
    case 5n+t:
      {==}

# n+1 rounds from c == n rounds from the cost one round later
def cost_after_shift(+t: Nat, +c: Nat, +m: Nat)
  -> {Econ.cost_after(t, c, 1n+m) == Econ.cost_after(t, Econ.upgrade_cost_next(t, c), m) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+q:
      %cost_after_shift(t, c, q)
        : {Econ.upgrade_cost_next(t, Econ.cost_after(t, c, 1n+q)) == Econ.upgrade_cost_next(t, _) : Nat}
      {==}

# the floor stays the floor over any number of rounds
def cost_after_fix(+t: Nat, +n: Nat)
  -> {Econ.cost_after(t, Econ.upgrade_floor(t), n) == Econ.upgrade_floor(t) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %sym(Nat, Econ.cost_after(t, Econ.upgrade_floor(t), m), Econ.upgrade_floor(t), cost_after_fix(t, m))
        : {Econ.upgrade_cost_next(t, _) == Econ.upgrade_floor(t) : Nat}
      Laws.upgrade_next_floor(t)

def Laws.cost_after_ge_floor(tier, c, n, h):
  match n:
    case 0n:
      h
    case 1n+m:
      Laws.upgrade_next_ge_floor(tier, Econ.cost_after(tier, c, m))

def Laws.cost_after_le(tier, c, n, h):
  match n:
    case 0n:
      le_refl(c)
    case 1n+m:
      le_trans(Econ.upgrade_cost_next(tier, Econ.cost_after(tier, c, m)), Econ.cost_after(tier, c, m), c,
        Laws.upgrade_next_le(tier, Econ.cost_after(tier, c, m), Laws.cost_after_ge_floor(tier, c, m, h)),
        Laws.cost_after_le(tier, c, m, h))

def Laws.cost_after_reach(u, hu, k, n):
  match k:
    case 0n:
      cost_after_fix(1n+u, n)
    case 1n+j:
      %sym(Nat, Econ.cost_after(1n+u, 1n+Nat.add(j, Econ.upgrade_floor(1n+u)), 1n+Nat.add(j, n)), Econ.cost_after(1n+u, Econ.upgrade_cost_next(1n+u, 1n+Nat.add(j, Econ.upgrade_floor(1n+u))), Nat.add(j, n)), cost_after_shift(1n+u, 1n+Nat.add(j, Econ.upgrade_floor(1n+u)), Nat.add(j, n)))
        : {_ == Econ.upgrade_floor(1n+u) : Nat}
      %sym(Nat, Econ.upgrade_cost_next(1n+u, 1n+Nat.add(j, Econ.upgrade_floor(1n+u))), Nat.add(j, Econ.upgrade_floor(1n+u)), Laws.upgrade_next_step(u, hu, j))
        : {Econ.cost_after(1n+u, _, Nat.add(j, n)) == Econ.upgrade_floor(1n+u) : Nat}
      Laws.cost_after_reach(u, hu, j, n)

def Laws.cost_after_exact(u, hu, n, k):
  match n:
    case 0n:
      {==}
    case 1n+m:
      %sym(Nat, 1n+Nat.add(m, Nat.add(k, Econ.upgrade_floor(1n+u))), Nat.add(m, 1n+Nat.add(k, Econ.upgrade_floor(1n+u))), add_succ(m, Nat.add(k, Econ.upgrade_floor(1n+u))))
        : {Econ.upgrade_cost_next(1n+u, Econ.cost_after(1n+u, _, m)) == Nat.add(k, Econ.upgrade_floor(1n+u)) : Nat}
      %sym(Nat, Econ.cost_after(1n+u, Nat.add(m, 1n+Nat.add(k, Econ.upgrade_floor(1n+u))), m), 1n+Nat.add(k, Econ.upgrade_floor(1n+u)), Laws.cost_after_exact(u, hu, m, 1n+k))
        : {Econ.upgrade_cost_next(1n+u, _) == Nat.add(k, Econ.upgrade_floor(1n+u)) : Nat}
      Laws.upgrade_next_step(u, hu, k)

# Hit points
# ----------

def Laws.hp_after_le(hp, dmg):
  match hp dmg:
    case 0n _:
      {==}
    case 1n+a 0n:
      le_refl(a)
    case 1n+a 1n+b:
      le_succ(Nat.sub(a, b), a, Laws.hp_after_le(a, b))

def Laws.hp_after_exact(dmg, rest):
  match dmg:
    case 0n:
      match rest:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+d:
      Laws.hp_after_exact(d, rest)

def Laws.hp_after_floor(hp, k):
  match hp:
    case 0n:
      {==}
    case 1n+p:
      Laws.hp_after_floor(p, k)

# Combat damage
# -------------

def Laws.damage_ge_tier(tier, survivors):
  match survivors:
    case Nil{}:
      le_refl(tier)
    case t <> ts:
      +d = Econ.damage(tier, ts)
      le_trans(tier, d, Nat.add(t, d), Laws.damage_ge_tier(tier, ts), le_add_l(t, d))

def Laws.damage_survivor(tier, t, ts):
  {==}

# Board capacity
# --------------

def Laws.room_full(k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.room_keeps_cap(len, h):
  lt_le(len, 5n, h)

def Laws.room_open(len, h):
  le_lt(len, 5n, h)
