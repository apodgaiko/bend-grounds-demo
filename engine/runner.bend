# Bend Grounds fast runner: a persistent simulation process for tests,
# self-play and RL. Every rule, transition and observation is ./game.bend
# (pure, checked); this file only keeps games in memory between requests
# and speaks a line protocol on stdin/stdout.
#
# Protocol (docs/FAST-RUNNER.md): one request line in, exactly one
# response line out, "<status> <json>". Nothing else is ever written to
# stdout.
#
#   rules | health | quit
#   reset <env> <seed> <mode>    == api_game(seed, mode, "")
#   step <env> [<m1,m2,..>]      == api_game(seed, mode, T ++ batch)
#   observe <env>                == api_game(seed, mode, T)
#   close <env>
#
# T is the env's transcript of APPLIED moves. A step applies its moves in
# order with G.g_apply on the stored Game (no replay from the start); the
# first rejected move stops the batch and leaves the state as it was
# before that move, exactly the state the replay API reports.
#
# Only the read loop (`loop`, `next`) is @unsafe: a runner reads until
# end of input. The request handling below it is total.
import Base
import ./game.bend as G

# Limits
# ------

# bytes per request line (a 1024-move batch of 16-byte moves fits)
def line_max() -> U32:
  262144

# live envs per process
def env_cap() -> Nat:
  4096n

def runner_protocol() -> String:
  "fast-runner/1"

# Small helpers
# -------------

def pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# UTF-8 length of a String, in bytes
def utf8_len(s: String, acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{+c}, t}:
      +w = pick(U32, U32.is_lt(c, 128), 1, pick(U32, U32.is_lt(c, 2048), 2, pick(U32, U32.is_lt(c, 65536), 3, 4)))
      utf8_len(t, U32.add(acc, w))

# drops one trailing "\n" and then one trailing "\r"
def chomp_lf(+s: String) -> String:
  pick(String, String.ends_with(s, "\n"), String.take(s, Nat.sub(String.length(s), 1n)), s)

def chomp(+s: String) -> String:
  +a = chomp_lf(s)
  pick(String, String.ends_with(a, "\r"), String.take(a, Nat.sub(String.length(a), 1n)), a)

# env ids: 1 to 6 decimal digits
def env_id(+s: String) -> Maybe<&2, Nat>:
  +n = String.length(s)
  pick(Maybe<&2, Nat>, Nat.is_ge(n, 1n) && Nat.is_le(n, 6n) && G.all_digits(s), Nat.read(s), None{})

# Envs
# ----

type Env is Data:
  Env{id: Nat, g: G.Game, n: Nat}

def env_key(e: Env) -> Nat:
  Env{id, g, n} = e
  id

def env_find(es: List<&2, Env>, +k: Nat) -> Maybe<&2, Env>:
  match es:
    case Nil{}:
      None{}
    case +e <> t:
      pick(Maybe<&2, Env>, Nat.is_eq(env_key(e), k), Some{e}, env_find(t, k))

def env_drop(es: List<&2, Env>, +k: Nat) -> List<&2, Env>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> +t:
      pick(List<&2, Env>, Nat.is_eq(env_key(e), k), t, e <> env_drop(t, k))

def env_has(+es: List<&2, Env>, +k: Nat) -> Bool:
  Maybe.is_some(&2, Env, env_find(es, k))

def env_put(+es: List<&2, Env>, e: Env) -> List<&2, Env>:
  Env{+id, g, n} = e
  Env{id, g, n} <> env_drop(es, id)

# Responses
# ---------

type Out is Data:
  Out{code: Nat, body: String, envs: List<&2, Env>, quit: Bool}

def err(+code: Nat, c: String, m: String, envs: List<&2, Env>) -> Out:
  Out{code, G.api_error(c, m), envs, False{}}

def bad_command(envs: List<&2, Env>) -> Out:
  err(400n, "bad_command", "expected: rules | health | quit | reset ENV SEED MODE | step ENV [MOVES] | observe ENV | close ENV (ENV is 1-6 digits)", envs)

def unknown_env(envs: List<&2, Env>) -> Out:
  err(404n, "unknown_env", "no such env; reset it first", envs)

def ok_json() -> String:
  "{\"ok\":true}"

def api_out(r: Nat & String, es: List<&2, Env>) -> Out:
  (code, body) = r
  Out{code, body, es, False{}}

# reset: the answer is api_game(seed, mode, "") byte for byte; a bad seed
# or mode creates nothing and keeps an existing env untouched
def reset_go(ms: Maybe<&2, U32>, mm: Maybe<&2, Nat>, +k: Nat, +es: List<&2, Env>, seed_s: String, mode_s: String) -> Out:
  match ms mm:
    case Some{+seed} Some{+mode}:
      +g = G.new_game(seed, mode)
      +full = Bool.not(env_has(es, k)) && Nat.is_ge(List.length(&2, Env, es), env_cap())
      pick(Out, full, err(400n, "too_many_envs", "at most 4096 envs per runner; close one first", es), Out{200n, G.game_json_go(g, 0n, None{}), env_put(es, Env{k, g, 0n}), False{}})
    case _ _:
      api_out(G.api_game(seed_s, mode_s, ""), es)

def reset_id(mk: Maybe<&2, Nat>, +es: List<&2, Env>, +seed_s: String, +mode_s: String) -> Out:
  match mk:
    case None{}:
      bad_command(es)
    case Some{+k}:
      reset_go(G.parse_seed(seed_s), G.parse_mode(mode_s), k, es, seed_s, mode_s)

# step: G.replay_go from the stored state is the same left fold the replay
# API runs over the whole transcript, so the answer is api_game over
# T ++ batch. The committed state is the reported one: every move before
# a rejected move is kept, the rejected move and the rest are not.
def step_fin(st: G.RSt, +k: Nat, +es: List<&2, Env>) -> Out:
  G.RSt{+g, +n, +e} = st
  Out{pick(Nat, Maybe.is_some(&2, G.RErr, e), 400n, 200n), G.game_json_go(g, n, e), env_put(es, Env{k, g, n}), False{}}

def step_run(over: Bool, +g: G.Game, +n: Nat, +ms: List<&2, String>, +k: Nat, +es: List<&2, Env>) -> Out:
  match over:
    case True{}:
      err(400n, "too_many_moves", "at most 1024 moves per request", es)
    case False{}:
      step_fin(G.replay_go(ms, G.RSt{g, n, None{}}), k, es)

def step_env(me: Maybe<&2, Env>, +moves: String, +k: Nat, +es: List<&2, Env>) -> Out:
  match me:
    case None{}:
      unknown_env(es)
    case Some{Env{id, +g, +n}}:
      +ms = G.split_moves(moves)
      step_run(Nat.is_gt(Nat.add(n, G.len(String, ms)), G.max_moves()), g, n, ms, k, es)

def step_id(mk: Maybe<&2, Nat>, +moves: String, +es: List<&2, Env>) -> Out:
  match mk:
    case None{}:
      bad_command(es)
    case Some{+k}:
      step_env(env_find(es, k), moves, k, es)

def observe_env(me: Maybe<&2, Env>, +es: List<&2, Env>) -> Out:
  match me:
    case None{}:
      unknown_env(es)
    case Some{Env{id, g, n}}:
      Out{200n, G.game_json_go(g, n, None{}), es, False{}}

def observe_id(mk: Maybe<&2, Nat>, +es: List<&2, Env>) -> Out:
  match mk:
    case None{}:
      bad_command(es)
    case Some{+k}:
      observe_env(env_find(es, k), es)

def close_id(mk: Maybe<&2, Nat>, +es: List<&2, Env>) -> Out:
  match mk:
    case None{}:
      bad_command(es)
    case Some{+k}:
      pick(Out, env_has(es, k), Out{200n, ok_json(), env_drop(es, k), False{}}, unknown_env(es))

def health_json() -> String:
  "{\"ok\":true,\"runner\":\"" ++ runner_protocol() ++ "\",\"protocolVersion\":" ++ Nat.show(G.protocol_version()) ++ "}"

# Dispatch
# --------

# 0 rules, 1 health, 2 quit, 3 reset, 4 step, 5 observe, 6 close, 7 unknown
def cmd_id(+c: String) -> Nat:
  pick(Nat, String.eq(c, "rules"), 0n,
    pick(Nat, String.eq(c, "health"), 1n,
      pick(Nat, String.eq(c, "quit"), 2n,
        pick(Nat, String.eq(c, "reset"), 3n,
          pick(Nat, String.eq(c, "step"), 4n,
            pick(Nat, String.eq(c, "observe"), 5n,
              pick(Nat, String.eq(c, "close"), 6n, 7n)))))))

# argument shapes: the number of words after the command
def args_n(xs: List<&2, String>) -> Nat:
  List.length(&2, String, xs)

def arg(+xs: List<&2, String>, +i: Nat) -> String:
  G.get_or(String, xs, i, "")

def run_reset(+xs: List<&2, String>, +es: List<&2, Env>) -> Out:
  pick(Out, Nat.is_eq(args_n(xs), 3n), reset_id(env_id(arg(xs, 0n)), es, arg(xs, 1n), arg(xs, 2n)), bad_command(es))

def run_step(+xs: List<&2, String>, +es: List<&2, Env>) -> Out:
  +n = args_n(xs)
  pick(Out, Nat.is_eq(n, 1n) || Nat.is_eq(n, 2n), step_id(env_id(arg(xs, 0n)), arg(xs, 1n), es), bad_command(es))

def run_one_go(ok: Bool, +xs: List<&2, String>, +es: List<&2, Env>, +which: Nat) -> Out:
  match ok:
    case False{}:
      bad_command(es)
    case True{}:
      pick(Out, Nat.is_eq(which, 0n), observe_id(env_id(arg(xs, 0n)), es), close_id(env_id(arg(xs, 0n)), es))

def run_one(+xs: List<&2, String>, +es: List<&2, Env>, +which: Nat) -> Out:
  run_one_go(Nat.is_eq(args_n(xs), 1n), xs, es, which)

def run_bare_go(ok: Bool, +es: List<&2, Env>, which: Nat) -> Out:
  match ok:
    case False{}:
      bad_command(es)
    case True{}:
      match which:
        case 0n:
          Out{200n, G.api_rules(), es, False{}}
        case 1n+a:
          match a:
            case 0n:
              Out{200n, health_json(), es, False{}}
            case 1n+b:
              Out{200n, ok_json(), es, True{}}

def run_bare(+xs: List<&2, String>, +es: List<&2, Env>, +which: Nat) -> Out:
  run_bare_go(Nat.is_eq(args_n(xs), 0n), es, which)

def run_cmd(id: Nat, +xs: List<&2, String>, +es: List<&2, Env>) -> Out:
  match id:
    case 0n:
      run_bare(xs, es, 0n)
    case 1n+a:
      match a:
        case 0n:
          run_bare(xs, es, 1n)
        case 1n+b:
          match b:
            case 0n:
              run_bare(xs, es, 2n)
            case 1n+c:
              match c:
                case 0n:
                  run_reset(xs, es)
                case 1n+d:
                  match d:
                    case 0n:
                      run_step(xs, es)
                    case 1n+e:
                      match e:
                        case 0n:
                          run_one(xs, es, 0n)
                        case 1n+f:
                          match f:
                            case 0n:
                              run_one(xs, es, 1n)
                            case 1n+h:
                              bad_command(es)

def run_words(ws: List<&2, String>, +es: List<&2, Env>) -> Out:
  match ws:
    case Nil{}:
      bad_command(es)
    case +c <> t:
      run_cmd(cmd_id(c), t, es)

# one request line (without its line end) against the envs
def handle(+line: String, +es: List<&2, Env>) -> Out:
  run_words(String.split(line, ' '), es)

def show(+o: Out) -> String:
  Out{+code, +body, envs, quit} = o
  Nat.show(code) ++ " " ++ body

# IO loop
# -------

# what the loop does next: stop, or read again (drain: still inside an
# over-long line, whose remainder is skipped). The stdin handle travels
# beside it.
type Next is Data:
  Stop{}
  Go{envs: List<&2, Env>, drain: Bool}

def answer(f: File, +o: Out) -> IO(File & Next):
  Out{code, body, +envs, +quit} = o
  do IO<File & Next>:
    IO.print(show(o))
    return (f, pick(Next, quit, Stop{}, Go{envs, False{}}))

def too_long(f: File, +es: List<&2, Env>) -> IO(File & Next):
  do IO<File & Next>:
    IO.print("413 " ++ G.api_error("line_too_long", "a request line holds at most 262144 bytes"))
    return (f, Go{es, True{}})

def got_text(f: File, +s: String, +es: List<&2, Env>, long: Bool) -> IO(File & Next):
  match long:
    case True{}:
      too_long(f, es)
    case False{}:
      answer(f, handle(chomp(s), es))

# a line read: s is "" at end of input; it ends in "\n" unless it is the
# last line, or it is a prefix of an over-long line
def got_line_go(eof: Bool, drain: Bool, f: File, +s: String, +es: List<&2, Env>) -> IO(File & Next):
  match eof drain:
    case True{} _:
      IO.pure(File & Next, (f, Stop{}))
    case False{} True{}:
      IO.pure(File & Next, (f, Go{es, Bool.not(String.ends_with(s, "\n"))}))
    case False{} False{}:
      got_text(f, s, es, Bool.and(Bool.not(String.ends_with(s, "\n")), U32.is_ge(utf8_len(s, 0), line_max())))

def got_line(f: File, +s: String, +es: List<&2, Env>, +drain: Bool) -> IO(File & Next):
  got_line_go(String.is_empty(s), drain, f, s, es)

def got(r: File & Result<&1, &1, U32 & String, String>, +es: List<&2, Env>, +drain: Bool) -> IO(File & Next):
  (f, res) = r
  match res:
    case Done{s}:
      got_line(f, s, es, drain)
    case Fail{e}:
      do IO<File & Next>:
        IO.print_err("runner: cannot read stdin")
        return (f, Stop{})

@unsafe
def loop(f: File, es: List<&2, Env>, drain: Bool) -> IO(Unit):
  do IO<Unit>:
    r : File & Result<&1, &1, U32 & String, String> <- File.read_line(f, line_max())
    nx : File & Next <- got(r, es, drain)
    next(nx)

@unsafe
def next(nx: File & Next) -> IO(Unit):
  (f, n) = nx
  match n:
    case Stop{}:
      IO.exit(0)
    case Go{es, drain}:
      loop(f, es, drain)

def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    loop(f, Nil{}, False{})
