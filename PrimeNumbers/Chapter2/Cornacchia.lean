import PrimeNumbers.Chapter2.SquareRoot

/-!
# §2.3.4 Representation by quadratic forms

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.3.4.

* `cornacchia` — Algorithm 2.3.12 (Cornacchia–Smith): represent `p = x² + d y²`.
* `cornacchia_sound` — every answer the algorithm returns is a genuine representation.

**Not yet proved:** completeness, i.e. that the algorithm finds a representation whenever
one exists.  The book itself calls that proof "a little painful" and defers to the
literature.  Algorithm 2.3.13 (the variant for `4p = x² + |D| y²`) is not formalized yet.
-/

namespace PrimeNumbers.Chapter2

/-- **Algorithm 2.3.12, step 4 [Euclid chain]**:
```
while (b > c) (a, b) = (b, a mod b);
```
Returns the final `b`. -/
def cornacchiaChain (a b c : ℕ) : ℕ :=
  if c < b then cornacchiaChain b (a % b) c else b
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

theorem cornacchiaChain_le (a b c : ℕ) : cornacchiaChain a b c ≤ c := by
  fun_induction cornacchiaChain a b c with
  | case1 a b h ih => exact ih
  | case2 a b h => omega

/-- **Algorithm 2.3.12, step 5 [Final report]**, for the `b` produced by the Euclid chain:
```
t = p - b²;
if (t ≢ 0 (mod d)) return { };
if (t/d not a square) return { };
return (±b, ±√(t/d));
```
-/
def cornacchiaReport (p d b : ℕ) : Option (ℕ × ℕ) :=
  let t := p - b * b
  if t % d = 0 then
    let y := Nat.sqrt (t / d)
    if y * y = t / d then some (b, y) else none
  else none

/-- **Algorithm 2.3.12 (Represent `p` as `x² + d y²`: Cornacchia–Smith method).**
Given an odd prime `p` and a positive integer `d` not divisible by `p`, this algorithm
either reports that `p = x² + d y²` has no integral solution (`none`), or returns a
solution `(x, y)`.
```
1. if ((-d/p) == -1) return { };
2. x₀ = √(-d) mod p;   if (2 x₀ < p) x₀ = p - x₀;
3. (a, b) = (p, x₀);   c = ⌊√p⌋;
4. while (b > c) (a, b) = (b, a mod b);
5. t = p - b²;
   if (t ≢ 0 (mod d)) return { };
   if (t/d not a square) return { };
   return (±b, ±√(t/d));
```
-/
def cornacchia (p d : ℕ) : Option (ℕ × ℕ) :=
  if jacobi (-(d : ℤ)) p = -1 then none            -- 1. [Test for solvability]
  else
    let x₀ := (sqrtMod p ((-(d : ℤ) : ℤ) : ZMod p)).val   -- 2. [Initial square root]
    let x₀ := if 2 * x₀ < p then p - x₀ else x₀
    let c := Nat.sqrt p                            -- 3. [Initialize Euclid chain]
    let b := cornacchiaChain p x₀ c                -- 4. [Euclid chain]
    cornacchiaReport p d b                         -- 5. [Final report]

theorem cornacchiaReport_sound {p d b x y : ℕ} (hb : b * b ≤ p)
    (h : cornacchiaReport p d b = some (x, y)) : x ^ 2 + d * y ^ 2 = p := by
  simp only [cornacchiaReport] at h
  split_ifs at h with h₁ h₂
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  -- `d ∣ t = p - b²` and `y² = t / d`
  have : d * (Nat.sqrt ((p - b * b) / d)) ^ 2 = p - b * b := by
    rw [sq, h₂, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h₁)]
  rw [this, sq]
  omega

/-- **Soundness of Algorithm 2.3.12.**  If the algorithm returns `(x, y)`, then indeed
`x² + d y² = p`.  (This needs no hypothesis on `p` or `d` at all.) -/
theorem cornacchia_sound {p d x y : ℕ} (h : cornacchia p d = some (x, y)) :
    x ^ 2 + d * y ^ 2 = p := by
  simp only [cornacchia] at h
  split_ifs at h
  -- the chain stops at `b ≤ ⌊√p⌋`, so `b² ≤ p`
  all_goals
    exact cornacchiaReport_sound
      ((Nat.mul_self_le_mul_self (cornacchiaChain_le ..)).trans (Nat.sqrt_le p)) h

end PrimeNumbers.Chapter2
