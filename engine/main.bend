# Bend Grounds: the native HTTP server and command line.
#
# Every rule lives in ./game.bend (pure, checked). This file is only the
# transport: it reads one bounded HTTP request per connection, routes it
# through an exact path whitelist, URL-decodes the query, hands the
# decoded text to the engine and writes one response with an exact
# Content-Length, then closes the connection. Only the accept loop is
# @unsafe (a server runs until killed); request parsing is total.
#
#   ./build/server                    serve http://127.0.0.1:8765
#   ./build/server serve 9000         serve on another port
#   ./build/server game 42 bots buy:0,play:0,end
#   ./build/server rules | health
import Base
import ./game.bend as G

# Limits
# ------

# the whole request head (request line + headers) must fit in this many
# bytes; a longer request is refused, never cut down to a prefix
def req_cap() -> U32:
  65536

# reads per request, and how long each may wait (ms)
def read_fuel() -> Nat:
  32n

def read_wait() -> U32:
  3000

# the only API protocol version served, taken from the game itself
# (G.protocol_version, also announced as protocolVersion in every body);
# /api/game accepts an optional `v` query parameter that must equal this
# (absent means this version)
def api_version() -> String:
  Nat.show(G.protocol_version())

# moves in one transcript (the engine enforces the same cap with a full
# state; this is the transport backstop)
def move_cap() -> U32:
  1024

# no digit run in moves may be longer than this; the engine bounds move
# indexes further, but nothing that long ever reaches it
def digit_cap() -> U32:
  9

def port_default() -> U32:
  8765

# Small helpers
# -------------

def pick(-A: Type, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def u32_in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

def bytes_len(bs: List<&2, U32>, acc: U32) -> U32:
  match bs:
    case Nil{}:
      acc
    case b <> t:
      bytes_len(t, U32.inc(acc))

# UTF-8 length of a String, in bytes, for Content-Length
def utf8_len(s: String, acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{+c}, t}:
      +w = pick(U32, U32.is_lt(c, 128), 1, pick(U32, U32.is_lt(c, 2048), 2, pick(U32, U32.is_lt(c, 65536), 3, 4)))
      utf8_len(t, U32.add(acc, w))

# Scanning the request head
# -------------------------

# how much of "\r\n\r\n" has just been seen (4 = all of it)
def crlf_sel(st: Nat, +cr: Bool, +lf: Bool) -> Nat:
  match st:
    case 0n:
      pick(Nat, cr, 1n, 0n)
    case 1n+a:
      match a:
        case 0n:
          pick(Nat, lf, 2n, pick(Nat, cr, 1n, 0n))
        case 1n+b2:
          match b2:
            case 0n:
              pick(Nat, cr, 3n, 0n)
            case 1n+c:
              match c:
                case 0n:
                  pick(Nat, lf, 4n, pick(Nat, cr, 1n, 0n))
                case 1n+d:
                  4n

def crlf_next(st: Nat, +b: U32) -> Nat:
  crlf_sel(st, U32.is_eq(b, 13), U32.is_eq(b, 10))

def head_done_go(bs: List<&2, U32>, +st: Nat) -> Bool:
  match bs:
    case Nil{}:
      Nat.is_eq(st, 4n)
    case b <> t:
      head_done_go(t, crlf_next(st, b))

def head_done(bs: List<&2, U32>) -> Bool:
  head_done_go(bs, 0n)

# the bytes of the request line (up to the first CR or LF), reversed
def first_line_go(bs: List<&2, U32>, +stop: Bool, +acc: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      acc
    case +b <> t:
      +now = Bool.or(stop, Bool.or(U32.is_eq(b, 13), U32.is_eq(b, 10)))
      first_line_go(t, now, pick(List<&2, U32>, now, acc, b <> acc))

# Some text if every byte is printable ASCII (32..126)
def ascii_go(bs: List<&2, U32>, +ok: Bool, acc: String) -> Maybe<&2, String>:
  match bs:
    case Nil{}:
      pick(Maybe<&2, String>, ok, Some{acc}, None{})
    case +b <> t:
      ascii_go(t, Bool.and(ok, u32_in(b, 32, 126)), SCon{Chr{b}, acc})

# the request line as text: first_line_go leaves it reversed, and
# ascii_go reverses it back while checking it
def request_line(bs: List<&2, U32>) -> Maybe<&2, String>:
  ascii_go(first_line_go(bs, False{}, Nil{}), True{}, SNil{})

# String helpers
# --------------

type Cut is Data:
  Cut{found: Bool, before: String, after: String}

def cut_step(c: Cut, +x: U32, +sep: U32) -> Cut:
  Cut{found, +before, +after} = c
  match found:
    case True{}:
      Cut{True{}, before, SCon{Chr{x}, after}}
    case False{}:
      pick(Cut, U32.is_eq(x, sep), Cut{True{}, before, after}, Cut{False{}, SCon{Chr{x}, before}, after})

def cut_fin(c: Cut) -> String & Maybe<&2, String>:
  Cut{found, before, after} = c
  match found:
    case True{}:
      (String.reverse(before), Some{String.reverse(after)})
    case False{}:
      (String.reverse(before), None{})

def cut_go(s: String, +sep: U32, c: Cut) -> Cut:
  match s:
    case SNil{}:
      c
    case SCon{Chr{+x}, t}:
      cut_go(t, sep, cut_step(c, x, sep))

# (before, Some after) at the first sep, or (s, None) when sep is absent
def cut(s: String, +sep: U32) -> String & Maybe<&2, String>:
  cut_fin(cut_go(s, sep, Cut{False{}, SNil{}, SNil{}}))

def hex_val(+x: U32) -> Maybe<&2, U32>:
  pick(Maybe<&2, U32>, u32_in(x, 48, 57), Some{U32.sub(x, 48)},
    pick(Maybe<&2, U32>, u32_in(x, 97, 102), Some{U32.sub(x, 87)},
      pick(Maybe<&2, U32>, u32_in(x, 65, 70), Some{U32.sub(x, 55)}, None{})))

# Percent-decoding of one query value. '+' is a space. Every decoded
# character must be printable ASCII; anything else (a bad or cut escape,
# a control byte, UTF-8) fails the whole value.
type Dec is Data:
  DNorm{}
  DPct{}
  DPct2{hi: U32}
  DFail{}

def dec_char(+v: U32, +acc: String) -> Dec & String:
  pick(Dec & String, u32_in(v, 32, 126), (DNorm{}, SCon{Chr{v}, acc}), (DFail{}, acc))

def dec_lo(hi: U32, m: Maybe<&2, U32>, acc: String) -> Dec & String:
  match m:
    case Some{lo}:
      dec_char(U32.add(U32.mul(hi, 16), lo), acc)
    case None{}:
      (DFail{}, acc)

def dec_hi(m: Maybe<&2, U32>, acc: String) -> Dec & String:
  match m:
    case Some{hi}:
      (DPct2{hi}, acc)
    case None{}:
      (DFail{}, acc)

def dec_step(st: Dec, +x: U32, +acc: String) -> Dec & String:
  match st:
    case DNorm{}:
      pick(Dec & String, U32.is_eq(x, 37), (DPct{}, acc),
        pick(Dec & String, U32.is_eq(x, 43), (DNorm{}, SCon{Chr{32}, acc}), dec_char(x, acc)))
    case DPct{}:
      dec_hi(hex_val(x), acc)
    case DPct2{hi}:
      dec_lo(hi, hex_val(x), acc)
    case DFail{}:
      (DFail{}, acc)

def dec_fin(st: Dec, acc: String) -> Maybe<&2, String>:
  match st:
    case DNorm{}:
      Some{String.reverse(acc)}
    case _:
      None{}

def dec_fin_p(p: Dec & String) -> Maybe<&2, String>:
  (st, acc) = p
  dec_fin(st, acc)

def dec_step_p(p: Dec & String, +x: U32) -> Dec & String:
  (st, acc) = p
  dec_step(st, x, acc)

def dec_go(s: String, p: Dec & String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      dec_fin_p(p)
    case SCon{Chr{+x}, t}:
      dec_go(t, dec_step_p(p, x))

def url_decode(s: String) -> Maybe<&2, String>:
  dec_go(s, (DNorm{}, SNil{}))

# Query parameters
# ----------------

# a query parameter: absent, present once with its decoded value, or bad
# (repeated, or undecodable)
type Param is Data:
  PNone{}
  PSome{v: String}
  PBad{}

def param_add(p: Param, m: Maybe<&2, String>) -> Param:
  match p m:
    case PNone{} Some{v}:
      PSome{v}
    case _ _:
      PBad{}

type Query is Data:
  Query{seed: Param, mode: Param, moves: Param, ver: Param}

# 0 seed, 1 mode, 2 moves, 3 v (protocol version), 4 anything else
# (ignored: a cache-buster, say)
def key_id(+k: String) -> Nat:
  pick(Nat, String.eq(k, "seed"), 0n,
    pick(Nat, String.eq(k, "mode"), 1n,
      pick(Nat, String.eq(k, "moves"), 2n,
        pick(Nat, String.eq(k, "v"), 3n, 4n))))

def q_put(q: Query, id: Nat, m: Maybe<&2, String>) -> Query:
  Query{seed, mode, moves, ver} = q
  match id:
    case 0n:
      Query{param_add(seed, m), mode, moves, ver}
    case 1n+a:
      match a:
        case 0n:
          Query{seed, param_add(mode, m), moves, ver}
        case 1n+b:
          match b:
            case 0n:
              Query{seed, mode, param_add(moves, m), ver}
            case 1n+c:
              match c:
                case 0n:
                  Query{seed, mode, moves, param_add(ver, m)}
                case 1n+d:
                  Query{seed, mode, moves, ver}

def q_pair(q: Query, kv: String & Maybe<&2, String>) -> Query:
  (k, mv) = kv
  match mv:
    case None{}:
      q_put(q, key_id(k), Some{""})
    case Some{v}:
      q_put(q, key_id(k), url_decode(v))

def q_part(+q: Query, +p: String) -> Query:
  pick(Query, String.is_empty(p), q, q_pair(q, cut(p, 61)))

def q_parts(xs: List<&2, String>, +q: Query) -> Query:
  match xs:
    case Nil{}:
      q
    case p <> t:
      q_parts(t, q_part(q, p))

def parse_query(s: String) -> Query:
  q_parts(String.split(s, '&'), Query{PNone{}, PNone{}, PNone{}, PNone{}})

# Transport checks on moves
# -------------------------

def commas(s: String, +acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{+x}, t}:
      commas(t, pick(U32, U32.is_eq(x, 44), U32.inc(acc), acc))

# the longest run of decimal digits
def digit_run(s: String, +run: U32, +best: U32) -> U32:
  match s:
    case SNil{}:
      best
    case SCon{Chr{+x}, t}:
      +r = pick(U32, u32_in(x, 48, 57), U32.inc(run), 0)
      digit_run(t, r, pick(U32, U32.is_gt(r, best), r, best))

# Responses
# ---------

type Resp is Data:
  RText{code: Nat, ctype: String, extra: String, body: String}
  RFile{path: String, ctype: String}

def json_type() -> String:
  "application/json; charset=utf-8"

def rjson(code: Nat, body: String) -> Resp:
  RText{code, json_type(), "", body}

def rerr(code: Nat, err: String, msg: String) -> Resp:
  rjson(code, G.api_error(err, msg))

def status_text(+code: Nat) -> String:
  pick(String, Nat.is_eq(code, 200n), "OK",
    pick(String, Nat.is_eq(code, 400n), "Bad Request",
      pick(String, Nat.is_eq(code, 404n), "Not Found",
        pick(String, Nat.is_eq(code, 405n), "Method Not Allowed",
          pick(String, Nat.is_eq(code, 408n), "Request Timeout",
            pick(String, Nat.is_eq(code, 431n), "Request Header Fields Too Large", "Internal Server Error"))))))

def head_text(+code: Nat, ctype: String, extra: String, len: U32) -> String:
  "HTTP/1.1 " ++ Nat.show(code) ++ " " ++ status_text(code) ++ "\r\nContent-Type: " ++ ctype ++ "\r\nContent-Length: " ++ U32.show(len) ++ "\r\nConnection: close\r\nCache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\n" ++ extra ++ "\r\n"

# Routing
# -------

def param_text(p: Param) -> String:
  match p:
    case PSome{v}:
      v
    case _:
      ""

def game_call(r: Nat & String) -> Resp:
  (code, body) = r
  rjson(code, body)

# transport backstops; everything finer is the engine's call
def game_checked(many: Bool, long: Bool, seed: String, mode: String, moves: String) -> Resp:
  match many long:
    case True{} _:
      rerr(400n, "too_many_moves", "a transcript holds at most 1024 moves")
    case False{} True{}:
      rerr(400n, "bad_move", "a move index is far too long")
    case False{} False{}:
      game_call(G.api_game(seed, mode, moves))

def game_moves(seed: String, mode: String, +moves: String) -> Resp:
  game_checked(U32.is_ge(commas(moves, 0), move_cap()), U32.is_gt(digit_run(moves, 0, 0), digit_cap()), seed, mode, moves)

def game_with(seed: Param, mode: Param, moves: Param) -> Resp:
  match seed mode moves:
    case PBad{} _ _:
      rerr(400n, "bad_request", "seed: repeated, or not printable ASCII")
    case _ PBad{} _:
      rerr(400n, "bad_request", "mode: repeated, or not printable ASCII")
    case _ _ PBad{}:
      rerr(400n, "bad_request", "moves: repeated, or not printable ASCII")
    case _ _ _:
      game_moves(param_text(seed), param_text(mode), param_text(moves))

# the protocol version is checked before anything else: absent or
# exactly api_version() is served; any other value (an older protocol
# included), an empty or undecodable value, or a repeated `v` gets an
# error-only 400 unsupported_version
def ver_ok(v: Param) -> Bool:
  match v:
    case PNone{}:
      True{}
    case PSome{s}:
      String.eq(s, api_version())
    case PBad{}:
      False{}

def game_versioned(ok: Bool, seed: Param, mode: Param, moves: Param) -> Resp:
  match ok:
    case True{}:
      game_with(seed, mode, moves)
    case False{}:
      rerr(400n, "unsupported_version", "v: this server speaks protocol version " ++ api_version() ++ " only (send v=" ++ api_version() ++ " once, or omit v)")

def route_query(q: Query) -> Resp:
  Query{seed, mode, moves, ver} = q
  game_versioned(ver_ok(ver), seed, mode, moves)

def route_game(q: Maybe<&2, String>) -> Resp:
  match q:
    case None{}:
      game_with(PNone{}, PNone{}, PNone{})
    case Some{s}:
      route_query(parse_query(s))

def html_type() -> String:
  "text/html; charset=utf-8"

# the exact path whitelist: 0 game, 1 health, 2 rules, 3 index,
# 4 app.js, 5 style.css, 6 anything else
def path_id(+p: String) -> Nat:
  pick(Nat, String.eq(p, "/api/game"), 0n,
    pick(Nat, String.eq(p, "/api/health"), 1n,
      pick(Nat, String.eq(p, "/api/rules"), 2n,
        pick(Nat, Bool.or(String.eq(p, "/"), String.eq(p, "/index.html")), 3n,
          pick(Nat, String.eq(p, "/app.js"), 4n,
            pick(Nat, String.eq(p, "/style.css"), 5n, 6n))))))

def route_id(id: Nat, q: Maybe<&2, String>) -> Resp:
  match id:
    case 0n:
      route_game(q)
    case 1n+a:
      match a:
        case 0n:
          rjson(200n, G.api_health())
        case 1n+b:
          match b:
            case 0n:
              rjson(200n, G.api_rules())
            case 1n+c:
              match c:
                case 0n:
                  RFile{"web/index.html", html_type()}
                case 1n+d:
                  match d:
                    case 0n:
                      RFile{"web/app.js", "text/javascript; charset=utf-8"}
                    case 1n+e:
                      match e:
                        case 0n:
                          RFile{"web/style.css", "text/css; charset=utf-8"}
                        case 1n+f:
                          rerr(404n, "not_found", "no such path")

def route_target(t: String & Maybe<&2, String>) -> Resp:
  (path, q) = t
  route_id(path_id(path), q)

def route_method(get: Bool, target: String) -> Resp:
  match get:
    case True{}:
      route_target(cut(target, 63))
    case False{}:
      RText{405n, json_type(), "Allow: GET\r\n", G.api_error("method_not_allowed", "only GET is served")}

def bad_line() -> Resp:
  rerr(400n, "bad_request", "malformed request line")

def route_version(ok: Bool, +meth: String, target: String) -> Resp:
  match ok:
    case True{}:
      route_method(String.eq(meth, "GET"), target)
    case False{}:
      bad_line()

# exactly METHOD SP TARGET SP HTTP/1.x
def route_words(ws: List<&2, String>) -> Resp:
  match ws:
    case meth <> t1:
      match t1:
        case target <> t2:
          match t2:
            case +ver <> t3:
              match t3:
                case Nil{}:
                  route_version(String.starts_with(ver, "HTTP/1."), meth, target)
                case x <> t4:
                  bad_line()
            case Nil{}:
              bad_line()
        case Nil{}:
          bad_line()
    case Nil{}:
      bad_line()

def route_line(m: Maybe<&2, String>) -> Resp:
  match m:
    case None{}:
      rerr(400n, "bad_request", "the request line must be printable ASCII")
    case Some{line}:
      route_words(String.split(line, ' '))

# the response to one complete request head
def route(bs: List<&2, U32>) -> Resp:
  route_line(request_line(bs))

# Reading a request
# -----------------

type Got is Data:
  GotHead{bs: List<&2, U32>}
  GotBig{}
  GotLate{}
  GotEnd{}

def got_check(done: Bool, big: Bool, s: Socket, all: List<&2, U32>, next: Socket -> List<&2, U32> -> IO(Socket & Got)) -> IO(Socket & Got):
  match done big:
    case True{} _:
      IO.pure(Socket & Got, (s, GotHead{all}))
    case False{} True{}:
      IO.pure(Socket & Got, (s, GotBig{}))
    case False{} False{}:
      next(s, all)

def got_more(s: Socket, +all: List<&2, U32>, next: Socket -> List<&2, U32> -> IO(Socket & Got)) -> IO(Socket & Got):
  got_check(head_done(all), U32.is_ge(bytes_len(all, 0), req_cap()), s, all, next)

def got_step(sr: Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, Unit>, acc: List<&2, U32>, next: Socket -> List<&2, U32> -> IO(Socket & Got)) -> IO(Socket & Got):
  (s, p) = sr
  match p:
    case Ready{Done{Some{chunk}}}:
      got_more(s, List.append(&2, U32, acc, chunk), next)
    case Ready{Done{None{}}}:
      IO.pure(Socket & Got, (s, GotEnd{}))
    case Ready{Fail{e}}:
      IO.pure(Socket & Got, (s, GotEnd{}))
    case Wait{u}:
      IO.pure(Socket & Got, (s, GotLate{}))

# at most read_fuel() reads, each waiting at most read_wait() ms, and
# never more than req_cap() bytes in all
def read_head(fuel: Nat, s: Socket, +acc: List<&2, U32>) -> IO(Socket & Got):
  match fuel:
    case 0n:
      IO.pure(Socket & Got, (s, GotLate{}))
    case 1n+f:
      +room = U32.sub(req_cap(), bytes_len(acc, 0))
      do IO<Socket & Got>:
        sr : Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, Unit> <- TCP.try_recv_bytes(s, room, read_wait())
        got_step(sr, acc, s2 => a2 => read_head(f, s2, a2))

# Writing a response
# ------------------

def sent_close(m: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  (s, r) = m
  Socket.close(s)

def send_text(s: Socket, +code: Nat, ctype: String, extra: String, +body: String) -> IO(Unit):
  do IO<Unit>:
    m : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send(s, head_text(code, ctype, extra, utf8_len(body, 0)) ++ body)
    sent_close(m)

def sent_head(m: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>, body: List<&2, U32>) -> IO(Unit):
  (s, r) = m
  match r:
    case Done{u}:
      do IO<Unit>:
        m2 : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send_bytes(s, body)
        sent_close(m2)
    case Fail{e}:
      Socket.close(s)

def send_bytes(s: Socket, ctype: String, +body: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    m : Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit> <- TCP.send(s, head_text(200n, ctype, "", bytes_len(body, 0)))
    sent_head(m, body)

def send_missing(s: Socket) -> IO(Unit):
  send_text(s, 404n, json_type(), "", G.api_error("not_found", "asset missing; run from the project root"))

def file_read(s: Socket, fr: File & Result<&1, &1, U32 & String, List<&2, U32>>, ctype: String) -> IO(Unit):
  (f, r) = fr
  match r:
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        send_bytes(s, ctype, bs)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        send_missing(s)

def file_sized(s: Socket, fs: File & Result<&1, &1, U32 & String, U32>, ctype: String) -> IO(Unit):
  (f, r) = fs
  match r:
    case Done{n}:
      do IO<Unit>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, U32.add(n, 1))
        file_read(s, fr, ctype)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        send_missing(s)

def file_opened(s: Socket, r: Result<&1, &1, U32 & String, File>, ctype: String) -> IO(Unit):
  match r:
    case Done{f}:
      do IO<Unit>:
        fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        file_sized(s, fs, ctype)
    case Fail{e}:
      send_missing(s)

def respond(s: Socket, r: Resp) -> IO(Unit):
  match r:
    case RText{code, ctype, extra, body}:
      send_text(s, code, ctype, extra, body)
    case RFile{path, ctype}:
      do IO<Unit>:
        fo : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
        file_opened(s, fo, ctype)

def http_got(g: Socket & Got) -> IO(Unit):
  (s, got) = g
  match got:
    case GotHead{bs}:
      respond(s, route(bs))
    case GotBig{}:
      respond(s, rerr(431n, "request_too_large", "the request head exceeds 65536 bytes"))
    case GotLate{}:
      respond(s, rerr(408n, "request_timeout", "the request head did not arrive in time"))
    case GotEnd{}:
      Socket.close(s)

def http_talk(s: Socket) -> IO(Unit):
  do IO<Unit>:
    g : Socket & Got <- read_head(read_fuel(), s, Nil{})
    http_got(g)

# Serving
# -------

def accepted(m: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Listener):
  (l, r) = m
  match r:
    case Done{s}:
      do IO<Listener>:
        IO.spawn(Unit, http_talk(s))
        return l
    case Fail{e}:
      IO.pure(Listener, l)

@unsafe
def serve(l: Listener) -> IO(Unit):
  do IO<Unit>:
    m  : Listener & Result<&1, &1, U32 & String, Socket> <- TCP.accept(l)
    l2 : Listener <- accepted(m)
    serve(l2)

def serve_on(+port: U32) -> IO(Unit):
  do IO<Unit>:
    l : Listener <- IO.try(Listener, TCP.listen("127.0.0.1", port))
    IO.print("Bend Grounds serving http://127.0.0.1:" ++ U32.show(port))
    serve(l)

# Command line
# ------------

def usage() -> String:
  "usage: server [serve [PORT]] | game SEED [MODE [MOVES]] | rules | health"

def cli_out(r: Nat & String) -> IO(Unit):
  (code, body) = r
  do IO<Unit>:
    IO.print(body)
    IO.exit(pick(U32, Nat.is_eq(code, 200n), 0, 1))

def cli_fail() -> IO(Unit):
  do IO<Unit>:
    IO.print_err(usage())
    IO.exit(2)

# game SEED [MODE [MOVES]]
def cli_game(xs: List<String>) -> IO(Unit):
  match xs:
    case seed <> t1:
      match t1:
        case Nil{}:
          cli_out(G.api_game(seed, "", ""))
        case mode <> t2:
          match t2:
            case Nil{}:
              cli_out(G.api_game(seed, mode, ""))
            case moves <> t3:
              match t3:
                case Nil{}:
                  cli_out(G.api_game(seed, mode, moves))
                case x <> t4:
                  cli_fail()
    case Nil{}:
      cli_fail()

def cli_port(m: Maybe<&2, U32>) -> IO(Unit):
  match m:
    case Some{n}:
      serve_on(n)
    case None{}:
      cli_fail()

def cli_serve(xs: List<String>) -> IO(Unit):
  match xs:
    case Nil{}:
      serve_on(port_default())
    case p <> t:
      match t:
        case Nil{}:
          cli_port(U32.read(p))
        case x <> t2:
          cli_fail()

# 0 serve, 1 game, 2 rules, 3 health, 4 unknown
def cmd_id(+c: String) -> Nat:
  pick(Nat, String.eq(c, "serve"), 0n,
    pick(Nat, String.eq(c, "game"), 1n,
      pick(Nat, String.eq(c, "rules"), 2n,
        pick(Nat, String.eq(c, "health"), 3n, 4n))))

def cli_cmd(id: Nat, xs: List<String>) -> IO(Unit):
  match id:
    case 0n:
      cli_serve(xs)
    case 1n+a:
      match a:
        case 0n:
          cli_game(xs)
        case 1n+b:
          match b:
            case 0n:
              IO.print(G.api_rules())
            case 1n+c:
              match c:
                case 0n:
                  IO.print(G.api_health())
                case 1n+d:
                  cli_fail()

def cli(xs: List<String>) -> IO(Unit):
  match xs:
    case Nil{}:
      serve_on(port_default())
    case c <> t:
      cli_cmd(cmd_id(c), t)

def cli_args(xs: List<String>) -> IO(Unit):
  match xs:
    case Nil{}:
      serve_on(port_default())
    case prog <> t:
      cli(t)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    cli_args(args)
