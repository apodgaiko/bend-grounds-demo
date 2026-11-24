# Bend Grounds CLI: replays one game transcript and prints the JSON.
#   build/cli <seed> <mode> <moves>      e.g. build/cli 7 bots buy:0,end
#   build/cli rules
import Base
import ./game.bend as G

def cli_run(args: List<String>) -> IO(Unit):
  match args:
    case Nil{}:
      IO.print("usage: cli <seed> <mode> <moves> | cli rules")
    case a <> t:
      match t:
        case Nil{}:
          IO.print(G.api_rules())
        case b <> t2:
          match t2:
            case Nil{}:
              IO.print(Pair.snd(Nat, String, G.api_game(a, b, "")))
            case c <> t3:
              IO.print(Pair.snd(Nat, String, G.api_game(a, b, c)))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    cli_run(List.tail(&1, String, args))
