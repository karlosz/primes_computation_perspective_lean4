import Mathlib

/-!
# §2.3.1 Quadratic residues

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.3.1.

The Legendre symbol (Definition 2.3.2) is Mathlib's `legendreSym p a`, and the Jacobi
symbol (Definition 2.3.3) is Mathlib's `jacobiSym a m`, written `J(a | m)`.

* `theorem_2_3_4_*` — Theorem 2.3.4, relations (2.6)–(2.11), in the book's form.
* `jacobi`          — Algorithm 2.3.5, computing the Jacobi symbol by reciprocity,
                      with `jacobi_eq : jacobi a m = J(a | m)` for odd `m`.
-/

namespace PrimeNumbers.Chapter2

open scoped NumberTheorySymbols
open jacobiSym

/-! ## Theorem 2.3.4 (Relations for Legendre and Jacobi symbols) -/

/-- **(2.6) Euler's test for quadratic residues**: `(a/p) ≡ a^((p-1)/2) (mod p)`.
(For odd `p`, `p / 2 = (p - 1) / 2`.) -/
theorem theorem_2_3_4_euler (p : ℕ) [Fact p.Prime] (a : ℤ) :
    (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) :=
  legendreSym.eq_pow p a

/-- **(2.7)** `(ab/m) = (a/m)(b/m)`. -/
theorem theorem_2_3_4_mul_left (a b : ℤ) (m : ℕ) : J(a * b | m) = J(a | m) * J(b | m) :=
  jacobiSym.mul_left a b m

/-- **(2.8)** `(a/mn) = (a/m)(a/n)`. -/
theorem theorem_2_3_4_mul_right (a : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    J(a | m * n) = J(a | m) * J(a | n) :=
  jacobiSym.mul_right' a hm hn

/-- **(2.9)** `(-1/m) = (-1)^((m-1)/2)` for odd `m`. -/
theorem theorem_2_3_4_neg_one {m : ℕ} (hm : Odd m) : J(-1 | m) = (-1) ^ ((m - 1) / 2) := by
  have h2 : m % 2 = 1 := Nat.odd_iff.mp hm
  rw [jacobiSym.at_neg_one hm, ZMod.χ₄_eq_neg_one_pow h2, show (m - 1) / 2 = m / 2 by omega]

/-- **(2.10)** `(2/m) = (-1)^((m²-1)/8)` for odd `m`. -/
theorem theorem_2_3_4_two {m : ℕ} (hm : Odd m) : J(2 | m) = (-1) ^ ((m ^ 2 - 1) / 8) := by
  rw [jacobiSym.at_two hm, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : m % 2 = 1 := Nat.odd_iff.mp hm
  -- write `m = 8k + r` with `r ∈ {1, 3, 5, 7}` and compute `(m² - 1)/8` explicitly
  obtain ⟨k, hk⟩ : ∃ k, m = 8 * k + m % 8 := ⟨m / 8, (Nat.div_add_mod m 8).symm⟩
  have key : ∀ r c : ℕ, r ^ 2 = 8 * c + 1 → m % 8 = r →
      (m ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + k * r) + c := by
    intro r c hc hr
    rw [hr] at hk
    have : m ^ 2 - 1 = 8 * (2 * (4 * k ^ 2 + k * r) + c) :=
      Nat.sub_eq_of_eq_add (by rw [hk]; linear_combination hc)
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcases : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
  rcases hcases with h | h | h | h
  · simp [h, h2, key 1 0 rfl h, pow_mul]
  · simp [h, h2, key 3 1 rfl h, pow_add, pow_mul]
  · simp [h, h2, key 5 3 rfl h, pow_add, pow_mul]
  · simp [h, h2, key 7 6 rfl h, pow_add, pow_mul]

/-- **(2.11) Law of quadratic reciprocity**: `(m/n)(n/m) = (-1)^((m-1)(n-1)/4)` for
coprime odd `m, n`. -/
theorem theorem_2_3_4_reciprocity {m n : ℕ} (hm : Odd m) (hn : Odd n) (hmn : m.Coprime n) :
    J(m | n) * J(n | m) = (-1) ^ ((m - 1) * (n - 1) / 4) := by
  obtain ⟨i, rfl⟩ := hm
  obtain ⟨j, rfl⟩ := hn
  have hexp : (2 * i + 1 - 1) * (2 * j + 1 - 1) / 4 = (2 * i + 1) / 2 * ((2 * j + 1) / 2) := by
    rw [show (2 * i + 1 - 1) * (2 * j + 1 - 1) = 4 * (i * j) by simp; ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
    congr 1 <;> omega
  have hsq : J((2 * j + 1 : ℕ) | 2 * i + 1) ^ 2 = 1 :=
    jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hmn.symm)
  rw [hexp, jacobiSym.quadratic_reciprocity ⟨i, rfl⟩ ⟨j, rfl⟩, mul_assoc, ← sq, hsq, mul_one]

/-! ## Algorithm 2.3.5 (Calculation of Legendre/Jacobi symbol) -/

/-- The inner loop of Algorithm 2.3.5:
```
while (a even) { a = a/2;  if (m mod 8 ∈ {3,5}) t = -t; }
```
(entered with `a ≠ 0`). Returns the new `(a, t)`. -/
def jacobiHalve (a m : ℕ) (t : ℤ) : ℕ × ℤ :=
  if a ≠ 0 ∧ a % 2 = 0 then
    jacobiHalve (a / 2) m (if m % 8 = 3 ∨ m % 8 = 5 then -t else t)
  else (a, t)
termination_by a
decreasing_by omega

theorem jacobiHalve_fst_le (a m : ℕ) (t : ℤ) : (jacobiHalve a m t).1 ≤ a := by
  fun_induction jacobiHalve a m t with
  | case1 a t h ih => simp only [dite_eq_ite] at ih; omega
  | case2 => exact le_rfl

theorem jacobiHalve_fst_pos {a : ℕ} (ha : a ≠ 0) (m : ℕ) (t : ℤ) : (jacobiHalve a m t).1 ≠ 0 := by
  fun_induction jacobiHalve a m t with
  | case1 a t h ih => exact ih (by omega)
  | case2 => exact ha

theorem jacobiHalve_fst_odd {a : ℕ} (ha : a ≠ 0) (m : ℕ) (t : ℤ) :
    (jacobiHalve a m t).1 % 2 = 1 := by
  fun_induction jacobiHalve a m t with
  | case1 a t h ih => exact ih (by omega)
  | case2 a t h => simp only; omega

/-- The inner loop preserves the quantity `t · (a/m)`: this is relation (2.10). -/
theorem jacobiHalve_spec (a : ℕ) {m : ℕ} (hm : m % 2 = 1) (t : ℤ) :
    (jacobiHalve a m t).2 * J((jacobiHalve a m t).1 | m) = t * J(a | m) := by
  fun_induction jacobiHalve a m t with
  | case1 a t h ih =>
    simp only [dite_eq_ite] at ih
    rw [ih, ← even_odd (a := a) (mod_cast h.2) hm, Int.natCast_ediv]
    split_ifs <;> simp
  | case2 => rfl

/-- The outer loop of Algorithm 2.3.5:
```
while (a ≠ 0) {
  while (a even) { a = a/2;  if (m mod 8 ∈ {3,5}) t = -t; }
  (a, m) = (m, a);                            // Swap variables.
  if (a ≡ m ≡ 3 (mod 4)) t = -t;
  a = a mod m;
}
if (m == 1) return t;
return 0;
```
-/
def jacobiLoop (a m : ℕ) (t : ℤ) : ℤ :=
  if a = 0 then
    if m = 1 then t else 0
  else
    let r := jacobiHalve a m t
    jacobiLoop (m % r.1) r.1 (if r.1 % 4 = 3 ∧ m % 4 = 3 then -r.2 else r.2)
termination_by a
decreasing_by
  have := jacobiHalve_fst_le a m t
  have := Nat.mod_lt m (Nat.pos_of_ne_zero (jacobiHalve_fst_pos ‹a ≠ 0› m t))
  omega

/-- **Algorithm 2.3.5.**  Given a positive odd integer `m` and an integer `a`, returns
the Jacobi symbol `(a/m)`, which for `m` an odd prime is also the Legendre symbol. -/
def jacobi (a : ℤ) (m : ℕ) : ℤ :=
  jacobiLoop (a % m).toNat m 1

/-- Loop invariant of Algorithm 2.3.5: `t · (a/m)` is preserved by each pass.  The swap
step is the reciprocity law (2.11). -/
theorem jacobiLoop_eq (a : ℕ) {m : ℕ} (hm : m % 2 = 1) (t : ℤ) :
    jacobiLoop a m t = t * J(a | m) := by
  fun_induction jacobiLoop a m t with
  | case1 t => simp
  | case2 m t hm1 =>
    have : J(((0 : ℕ) : ℤ) | m) = 0 := by exact_mod_cast jacobiSym.zero_left (by omega)
    rw [this, mul_zero]
  | case3 a m t ha r ih =>
    have hr : r.1 % 2 = 1 := jacobiHalve_fst_odd ha m t
    simp only [dite_eq_ite] at ih
    rw [ih hr, Int.natCast_mod, ← jacobiSym.mod_left, ← jacobiHalve_spec a hm t,
      ← quadratic_reciprocity_if hr hm]
    split_ifs <;> simp [r]

/-- **Correctness of Algorithm 2.3.5**: for odd `m`, `jacobi a m` is the Jacobi symbol. -/
theorem jacobi_eq (a : ℤ) {m : ℕ} (hm : Odd m) : jacobi a m = J(a | m) := by
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm.pos
  rw [jacobi, jacobiLoop_eq _ (Nat.odd_iff.mp hm), one_mul,
    Int.toNat_of_nonneg (Int.emod_nonneg _ hm0.ne'), ← jacobiSym.mod_left]

/-- For an odd prime `p`, Algorithm 2.3.5 computes the Legendre symbol. -/
theorem jacobi_eq_legendreSym (a : ℤ) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    jacobi a p = legendreSym p a := by
  rw [jacobi_eq a ((Fact.out : p.Prime).odd_of_ne_two hp), jacobiSym.legendreSym.to_jacobiSym]

end PrimeNumbers.Chapter2
