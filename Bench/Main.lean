import Bench.Cases

/-!
# `lake exe bench`

Runs the verified algorithms on growing inputs and compares the growth of the running time
with the proved bounds.  Usage:

    lake exe bench [--quick] [--list] [--csv FILE | --no-csv] [FILTER …]

A `FILTER` selects the cases whose problem or name contains it (case-insensitive), e.g.
`lake exe bench factoring` or `lake exe bench nussMul karatsuba`.
-/

open Bench

def parseArgs : List String → Options → Except String (Options × Bool)
  | [], o => .ok (o, false)
  | "--quick" :: r, o => parseArgs r { o with quick := true, target := 30000000, maxRun := 1000000000 }
  | "--list" :: _, o => .ok (o, true)
  | "--no-csv" :: r, o => parseArgs r { o with csv := none }
  | "--csv" :: f :: r, o => parseArgs r { o with csv := some f }
  | a :: r, o =>
    if a.startsWith "--" then .error s!"unknown option {a}"
    else parseArgs r { o with filters := o.filters ++ [a] }

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok (o, true) =>
    for c in allCases.filter (selected o) do
      IO.println s!"{padR c.problem 38} {padR c.name 36} {c.ref}"
    return 0
  | .ok (o, false) =>
    IO.println "# Benchmarks of the verified algorithms"
    runAll o allCases
    return 0
