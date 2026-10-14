import Mathlib.Tactic.Basic

/-!
# The `cost_simps` simp set

The bookkeeping lemmas of counted computations (`Counted.lean`), together with lemmas such
as "this helper costs nothing", are tagged `@[cost_simps]`; the `cost_simp` and
`cost_unfold` tactics simplify with exactly this set.  (A simp attribute must be declared
in a file before the one that first uses it.)
-/

register_simp_attr cost_simps

open Lean in
/-- `@[cost_free]` marks a function of this project that does no big-number arithmetic
(comparisons, additions, shifts, list or array bookkeeping), so that `counted_def` may call
it without charging anything.  A call of any other project function that has no counted
version is an error. -/
initialize costFreeAttr : TagAttribute ←
  registerTagAttribute `cost_free "a function that `counted_def` may call free of charge"
