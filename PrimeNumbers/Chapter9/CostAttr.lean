import Mathlib.Tactic.Basic

/-!
# The `cost_simps` simp set

The bookkeeping lemmas of counted computations (`Counted.lean`) are tagged `@[cost_simps]`; the `cost_simp` and
`cost_unfold` tactics simplify with exactly this set.  (A simp attribute must be declared
in a file before the one that first uses it.)
-/

register_simp_attr cost_simps
