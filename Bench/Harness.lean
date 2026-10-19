/-!
# Benchmark harness

A benchmark `Case` runs one verified algorithm on inputs of growing size and fits the growth
of its running time against the bound proved for it:

* `Growth.poly e`: time `∝ sizeᵉ` (up to logarithmic factors); the fitted exponent is the
  slope of `log time` against `log size`;
* `Growth.exp α`: time `∝ 2^(α · size)`, where `size` is a bit length (factoring, discrete
  logarithms); the fitted exponent is the slope of `log₂ time` against `size`.

The fit uses the larger half of the sizes, where the asymptotics dominate.  Inputs are
prepared outside the timed region and read from an `IO.Ref` inside it, so the compiler
cannot hoist the computation out of the timing loop; every result is hashed into the
checksum, so it cannot be discarded.
-/

namespace Bench

/-- The expected growth of the running time in the size parameter. -/
inductive Growth where
  | poly (e : Float)
  | exp (α : Float)

structure Case where
  /-- the problem the algorithm solves (the grouping of the report) -/
  problem : String
  /-- the Lean function -/
  name : String
  /-- where it is in the book -/
  ref : String
  /-- what the size parameter is -/
  param : String
  /-- the bound that is proved (or, for heuristic algorithms, expected) -/
  bound : String
  growth : Growth
  sizes : List Nat
  /-- prepare the inputs of a size; the result is the action to time -/
  prepare : Nat → IO (IO UInt64)

/-- An action that applies `f` to `input`, read from a reference so that each run recomputes it. -/
def task {α β : Type} [Hashable β] (input : α) (f : α → β) : IO (IO UInt64) := do
  let r ← IO.mkRef input
  pure do
    let x ← r.get
    pure (hash (f x))

/-! ## Timing -/

/-- Average nanoseconds per run, repeating until `target` nanoseconds have passed. -/
def measure (act : IO UInt64) (target : Nat) : IO (Float × UInt64) := do
  let mut runs := 0
  let mut total := 0
  let mut acc : UInt64 := 0
  repeat
    let t₀ ← IO.monoNanosNow
    let h ← act
    let t₁ ← IO.monoNanosNow
    runs := runs + 1
    total := total + (t₁ - t₀)
    acc := acc ^^^ h
    if total ≥ target then break
  return (total.toFloat / runs.toFloat, acc)

/-! ## Formatting -/

/-- `x` rounded to `d` decimals. -/
def fmt (x : Float) (d : Nat := 2) : String :=
  if x.isNaN then "–" else
  let p := (10 : Float) ^ d.toFloat
  let r := (x * p).round / p
  let s := toString r
  -- `toString` of a `Float` prints many digits; cut after `d` decimals
  match s.splitOn "." with
  | [i, f] =>
    let t := (f.take d).toString
    if d = 0 then i else i ++ "." ++ t.pushn '0' (d - t.length)
  | _ => s

/-- A duration in nanoseconds, with a unit. -/
def fmtTime (ns : Float) : String :=
  if ns < 1e3 then fmt ns 0 ++ " ns"
  else if ns < 1e6 then fmt (ns / 1e3) 1 ++ " µs"
  else if ns < 1e9 then fmt (ns / 1e6) 1 ++ " ms"
  else fmt (ns / 1e9) 2 ++ " s"

def padL (s : String) (n : Nat) : String := "".pushn ' ' (n - s.length) ++ s
def padR (s : String) (n : Nat) : String := s.pushn ' ' (n - s.length)

/-! ## Fitting -/

/-- The least-squares slope of `ys` against `xs`. -/
def slope (pts : List (Float × Float)) : Float :=
  let n := pts.length.toFloat
  let sx := (pts.map (·.1)).foldl (· + ·) 0
  let sy := (pts.map (·.2)).foldl (· + ·) 0
  let sxx := (pts.map fun p ↦ p.1 * p.1).foldl (· + ·) 0
  let sxy := (pts.map fun p ↦ p.1 * p.2).foldl (· + ·) 0
  let d := n * sxx - sx * sx
  if pts.length < 2 || d == 0 then 0.0 / 0.0 else (n * sxy - sx * sy) / d

/-- The coordinates in which the growth is a straight line. -/
def Growth.coords : Growth → Nat → Float → Float × Float
  | .poly _, s, t => (Float.log s.toFloat, Float.log t)
  | .exp _, s, t => (s.toFloat, Float.log2 t)

def Growth.expected : Growth → Float
  | .poly e => e
  | .exp α => α

def Growth.describe : Growth → String
  | .poly e => "size^" ++ fmt e 2
  | .exp α => "2^(" ++ fmt α 2 ++ "·bits)"

/-- The tolerance for "as expected": logarithmic factors raise a fitted polynomial exponent
somewhat. -/
def Growth.tolerance : Growth → Float
  | .poly _ => 0.35
  | .exp _ => 0.08

/-- The fitted exponent, on the larger half of the points (at least three). -/
def fitExponent (g : Growth) (rows : List (Nat × Float)) : Float :=
  let k := max 3 ((rows.length + 1) / 2)
  let tail := rows.drop (rows.length - k)
  slope (tail.map fun (s, t) ↦ g.coords s t)

/-- `≈` as expected; `▲` grows faster than the bound (look at the implementation); `▼`
grows slower (the bound is pessimistic for these sizes, e.g. GMP's fast products). -/
def verdict (g : Growth) (fitted : Float) : String :=
  if fitted.isNaN then "?"
  else if fitted > g.expected + g.tolerance then "▲"
  else if fitted < g.expected - g.tolerance then "▼"
  else "≈"

/-! ## Running -/

structure Options where
  /-- nanoseconds of repetitions per point -/
  target : Nat := 200000000
  /-- stop a case after a point slower than this (nanoseconds per run) -/
  maxRun : Nat := 3000000000
  /-- drop the largest sizes -/
  quick : Bool := false
  filters : List String := []
  csv : Option System.FilePath := some "bench/results.csv"

structure Result where
  case : Case
  rows : List (Nat × Float)
  fitted : Float

/-- Run one case and print its table. -/
def runCase (o : Options) (c : Case) : IO (Result × UInt64) := do
  IO.println s!"\n### {c.name} ({c.ref})"
  IO.println s!"{c.param}; bound {c.bound}; expected growth {c.growth.describe}"
  IO.println s!"{padL "size" 10} {padL "time/run" 12} {padL "local exp." 11}"
  let sizes := if o.quick then c.sizes.take (max 3 (c.sizes.length - 2)) else c.sizes
  let mut rows : Array (Nat × Float) := #[]
  let mut acc : UInt64 := 0
  for s in sizes do
    let act ← c.prepare s
    let (t, h) ← measure act o.target
    acc := acc ^^^ h
    let local_ := match rows.back? with
      | some (s', t') =>
        let (x₁, y₁) := c.growth.coords s' t'
        let (x₂, y₂) := c.growth.coords s t
        fmt ((y₂ - y₁) / (x₂ - x₁)) 2
      | none => ""
    IO.println s!"{padL (toString s) 10} {padL (fmtTime t) 12} {padL local_ 11}"
    (← IO.getStdout).flush
    rows := rows.push (s, t)
    if t > o.maxRun.toFloat then
      IO.println s!"{padL "" 10} (stopping: slower than {fmtTime o.maxRun.toFloat} per run)"
      break
  let fitted := fitExponent c.growth rows.toList
  IO.println s!"fitted exponent {fmt fitted 2} (expected {fmt c.growth.expected 2}) \
    {verdict c.growth fitted}"
  return (⟨c, rows.toList, fitted⟩, acc)

def selected (o : Options) (c : Case) : Bool :=
  o.filters.isEmpty || o.filters.any fun f ↦
    let f := f.toLower
    ((c.problem.toLower.splitOn f).length > 1) || ((c.name.toLower.splitOn f).length > 1)

/-- The summary, grouped by problem. -/
def summary (rs : List Result) : IO Unit := do
  IO.println "\n## Summary\n"
  IO.println "| problem | algorithm | bound | expected | fitted | |"
  IO.println "|---|---|---|---|---|---|"
  for r in rs do
    IO.println s!"| {r.case.problem} | `{r.case.name}` | {r.case.bound} | \
      {fmt r.case.growth.expected 2} | {fmt r.fitted 2} | {verdict r.case.growth r.fitted} |"
  IO.println "\n≈ as expected · ▲ grows faster than the bound · ▼ grows slower \
    (e.g. GMP's subquadratic products)"

def writeCsv (path : System.FilePath) (rs : List Result) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  let lines := rs.flatMap fun r ↦ r.rows.map fun (s, t) ↦
    s!"{r.case.problem},{r.case.name},{s},{t}"
  IO.FS.writeFile path ("problem,algorithm,size,ns\n" ++ "\n".intercalate lines ++ "\n")

def runAll (o : Options) (cases : List Case) : IO Unit := do
  let cs := cases.filter (selected o)
  let mut results := #[]
  let mut acc : UInt64 := 0
  let mut problem := ""
  for c in cs do
    if c.problem != problem then
      problem := c.problem
      IO.println s!"\n## {problem}"
    let (r, h) ← runCase o c
    results := results.push r
    acc := acc ^^^ h
  summary results.toList
  if let some p := o.csv then
    writeCsv p results.toList
    IO.println s!"\nraw timings written to {p}"
  IO.println s!"(checksum {acc})"

end Bench
