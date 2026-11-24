# Bend Grounds proof kit: generic lemmas over Base only (no engine import).
# Every def is a universally quantified lemma about Base's Nat, Bool and
# List; tests/engine_invariants.bend and tests/action_laws.bend import it.
# No holes, no axioms, no @unsafe.
#
#   bun vendor/bend/bend2/main.ts tests/proof_kit.bend --verdict

import Base

# Bool and equality
# -----------------

def bd(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# from False == True, anything
def ft_absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, %h : bd(_)
    Unit{})

def sym(-A: Type, -a: A, -b: A, e: {a == b : A}) -> {b == a : A}:
  %e : {_ == a : A}
  {==}

def tt_absurd(-A: Type, h: {True{} == False{} : Bool}) -> A:
  ft_absurd(A, sym(Bool, True{}, False{}, h))

# Boolean reflection: T(b) is Unit when b holds and Empty otherwise. It is
# Data, so a proof of it may be copied (equalities are Type and may not).
def T(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def to_T(-b: Bool, e: {b == True{} : Bool}) -> T(b):
  %sym(Bool, b, True{}, e) : T(_)
  Unit{}

def from_T(+b: Bool, w: T(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, w)

# a copyable conjunction
type Both<-A: Data, -B: Data> is Data:
  Both{l: A, r: B}

# a && b == True gives both halves
def and_l(+a: Bool, -b: Bool, h: {(a && b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ft_absurd({False{} == True{} : Bool}, h)

def and_r(+a: Bool, -b: Bool, h: {(a && b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ft_absurd({b == True{} : Bool}, h)

# Nat order
# ---------

def le0(c: Nat) -> {Nat.is_le(0n, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+r:
      {==}

def le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# x <= y implies x <= 1 + y
def le_step(x: Nat, y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+a 0n:
      ft_absurd({Nat.is_le(1n+a, 1n) == True{} : Bool}, h)
    case 1n+a 1n+b:
      le_step(a, b, h)

def le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      le0(c)
    case 1n+x 0n _:
      ft_absurd({Nat.is_le(1n+x, c) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      ft_absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      le_trans(x, y, z, h1, h2)

def lt0(q: Nat) -> {Nat.is_le(1n, 1n+q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+r:
      {==}

# n < m implies n + 1 <= m
def lt_succ_le(n: Nat, m: Nat, h: {Nat.is_lt(n, m) == True{} : Bool}) -> {Nat.is_le(1n+n, m) == True{} : Bool}:
  match n m:
    case 0n 0n:
      ft_absurd({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      lt0(q)
    case 1n+a 0n:
      ft_absurd({Nat.is_le(2n+a, 0n) == True{} : Bool}, h)
    case 1n+a 1n+b:
      lt_succ_le(a, b, h)

# nothing is below 0
def no_lt0(k: Nat, -A: Type, h: {Nat.is_lt(k, 0n) == True{} : Bool}) -> A:
  match k:
    case 0n:
      ft_absurd(A, h)
    case 1n+q:
      ft_absurd(A, h)

# x <= x + k
def le_add(a: Nat, k: Nat) -> {Nat.is_le(a, Nat.add(a, k)) == True{} : Bool}:
  match a:
    case 0n:
      le0(k)
    case 1n+p:
      le_add(p, k)

# Nat arithmetic
# --------------

def add_zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      sym(Nat, Nat.add(b, 0n), b, add_zero_r(b))
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# (x + a) + b == (x + b) + a: two additive buffs commute
def add_swap(+x: Nat, +a: Nat, +b: Nat) -> {Nat.add(Nat.add(x, a), b) == Nat.add(Nat.add(x, b), a) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(x, a), b), Nat.add(x, Nat.add(b, a)), Nat.add(Nat.add(x, b), a),
    Equal.trans(Nat, Nat.add(Nat.add(x, a), b), Nat.add(x, Nat.add(a, b)), Nat.add(x, Nat.add(b, a)),
      add_assoc(x, a, b),
      Equal.cong(Nat, Nat, y => Nat.add(x, y), Nat.add(a, b), Nat.add(b, a), add_comm(a, b))),
    sym(Nat, Nat.add(Nat.add(x, b), a), Nat.add(x, Nat.add(b, a)), add_assoc(x, b, a)))

# Lists
# -----

def len_set(-A: Data, xs: List<&2, A>, n: Nat, x: A) -> {List.length(&2, A, List.set(&2, A, xs, n, x)) == List.length(&2, A, xs) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      %len_set(A, t, p, x) : {1n+List.length(&2, A, List.set(&2, A, t, p, x)) == 1n+_ : Nat}
      {==}

def len_append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> {Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) == List.length(&2, A, List.append(&2, A, xs, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      %len_append(A, t, ys) : {1n+Nat.add(List.length(&2, A, t), List.length(&2, A, ys)) == 1n+_ : Nat}
      {==}

def is_some(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{v}:
      Unit

def none_some(-A: Data, -x: A, h: {None{} == Some{x} : Maybe<&2, A>}, -B: Type) -> B:
  Empty.absurd(B, %sym(Maybe<&2, A>, None{}, Some{x}, h) : is_some(A, _)
    Unit{})

# a present index is below the length
def get_lt(-A: Data, xs: List<&2, A>, i: Nat, -x: A, h: {List.get(&2, A, xs, i) == Some{x} : Maybe<&2, A>}) -> {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      none_some(A, x, h, {Nat.is_lt(i, 0n) == True{} : Bool})
    case y <> t 0n:
      {==}
    case y <> t 1n+p:
      get_lt(A, t, p, x, h)

# reading back what was just written
def get_set_eq(-A: Data, xs: List<&2, A>, i: Nat, +x: A, h: {Nat.is_lt(i, List.length(&2, A, xs)) == True{} : Bool}) -> {List.get(&2, A, List.set(&2, A, xs, i, x), i) == Some{x} : Maybe<&2, A>}:
  match xs i:
    case Nil{} _:
      no_lt0(i, {List.get(&2, A, List.set(&2, A, Nil{}, i, x), i) == Some{x} : Maybe<&2, A>}, h)
    case y <> t 0n:
      {==}
    case y <> t 1n+p:
      get_set_eq(A, t, p, x, h)

# writing one slot never changes another
def get_set_ne(-A: Data, xs: List<&2, A>, i: Nat, j: Nat, x: A, h: {Nat.is_eq(i, j) == False{} : Bool}) -> {List.get(&2, A, List.set(&2, A, xs, i, x), j) == List.get(&2, A, xs, j) : Maybe<&2, A>}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case y <> t 0n 0n:
      tt_absurd({List.get(&2, A, List.set(&2, A, y <> t, 0n, x), 0n) == List.get(&2, A, y <> t, 0n) : Maybe<&2, A>}, h)
    case y <> t 0n 1n+q:
      {==}
    case y <> t 1n+p 0n:
      {==}
    case y <> t 1n+p 1n+q:
      get_set_ne(A, t, p, q, x, h)

# take never yields more than asked
def len_take_le(-A: Data, xs: List<&2, A>, n: Nat) -> {Nat.is_le(List.length(&2, A, List.take(&2, A, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      le0(n)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      len_take_le(A, t, p)
