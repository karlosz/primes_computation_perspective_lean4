import Mathlib

/-!
# Assumed theorems

Deep results that the book states without proof and that are not (yet) in Mathlib.

They are **not axioms**.  Each is a definition of a proposition, `Assumed.X : Prop`, and a
theorem that relies on it takes it as an explicit hypothesis, e.g.
`theorem foo (h : Assumed.Mertens c) : …`.  So nothing here can make the development
inconsistent, every dependence is visible in the statement, and when one of these is
eventually proved (here or in Mathlib) the hypotheses are discharged without touching the
theorems that use them.

Heuristic assumptions specific to one algorithm are stated in the same style next to that
algorithm, e.g. `Chapter5.RhoCollision` for the Pollard rho method.
-/

namespace PrimeNumbers.Assumed

/-- **Theorem 1.4.2 (Mertens)**, in the upper-bound form used for running times:
`∑_{p ≤ x} 1/p ≤ ln ln x + c` for all `x ≥ 2`.  (Mertens' theorem says the difference
tends to the constant `B = 0.26149…`, so this holds for a suitable `c`.) -/
def Mertens (c : ℝ) : Prop :=
  ∀ x : ℕ, 2 ≤ x → ∑ p ∈ Nat.primesBelow (x + 1), (1 / (p : ℝ)) ≤ Real.log (Real.log x) + c

/-- **Theorem 1.1.4 (Hadamard and de la Vallée Poussin), the prime number theorem**:
`π(x) ∼ x / ln x`. -/
def PrimeNumberTheorem : Prop :=
  Filter.Tendsto (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) Filter.atTop
    (nhds 1)

/-- **Theorem 1.2.1 (Brun)**: the sum of the reciprocals of the twin primes converges. -/
def Brun : Prop :=
  Summable fun p : ℕ ↦ if p.Prime ∧ (p + 2).Prime then (1 / (p : ℝ)) else 0

end PrimeNumbers.Assumed
