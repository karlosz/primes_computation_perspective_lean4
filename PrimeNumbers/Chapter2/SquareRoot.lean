import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter2.Jacobi

/-!
# §2.3.2 Square roots

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.3.2.

* `tonelli`  — the general (`p ≡ 1 (mod 8)`) branch of Algorithm 2.3.8 (Tonelli), which as
               the book remarks handles every odd prime; `tonelli_sq`.
* `sqrtMod`  — Algorithm 2.3.8 in full, with the shortcuts for `p ≡ 3, 5, 7 (mod 8)`;
               `sqrtMod_sq`.
* `cipolla`  — Algorithm 2.3.9 (Cipolla), square roots via arithmetic in `F_{p²}`;
               `cipolla_sq`.

The algorithms compute in `ZMod p` ("all arithmetic is modulo `p`") using the powering
ladder of Algorithm 2.1.5.  At run time `ZMod p` is `Fin p` over arbitrary-precision
naturals, so this is as fast as explicit `mod p` arithmetic on `ℕ`.
-/

namespace PrimeNumbers.Chapter2

open scoped NumberTheorySymbols

/-! ## Euler's criterion (2.6), in the two forms used below -/

section Euler

variable {p : ℕ} [Fact p.Prime]

/-- If `a ≢ 0` is a square mod `p` then `a^((p-1)/2) = 1`. -/
theorem pow_half_eq_one {a : ZMod p} (ha0 : a ≠ 0) (ha : IsSquare a) : a ^ (p / 2) = 1 :=
  (ZMod.euler_criterion p ha0).mp ha

/-- If `d` is not a square mod `p` then `d^((p-1)/2) = -1`. -/
theorem pow_half_eq_neg_one {d : ZMod p} (hd : ¬IsSquare d) : d ^ (p / 2) = -1 := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hd (IsSquare.zero)
  exact (ZMod.pow_div_two_eq_neg_one_or_one p hd0).resolve_left
    fun h ↦ hd ((ZMod.euler_criterion p hd0).mpr h)

end Euler

/-! ## Algorithm 2.3.8 (Square roots (mod p)), Tonelli -/

/-- "Represent `n = 2^s t`, with `t` odd": returns `(s, t)`. -/
counted_def oddPart (n : ℕ) : ℕ × ℕ :=
  if n ≠ 0 ∧ n % 2 = 0 then
    let r := oddPart (n / 2)
    (r.1 + 1, r.2)
  else (0, n)
termination_by n
decreasing_by omega

/-- Splitting off the powers of two is free: tests and halvings are shifts. -/
@[cost_simps] theorem oddPart_cost (C : Chapter9.CostModel) (n : ℕ) :
    Chapter9.CostM.cost C (oddPart.counted n) = 0 := by
  fun_induction oddPart n with
  | case1 n h r ih => cost_unfold oddPart.counted; exact ih
  | case2 n h => cost_unfold oddPart.counted

theorem oddPart_spec {n : ℕ} (hn : n ≠ 0) :
    n = 2 ^ (oddPart n).1 * (oddPart n).2 ∧ (oddPart n).2 % 2 = 1 := by
  fun_induction oddPart n with
  | case1 n h r ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    refine ⟨?_, ih₂⟩
    have : n = 2 * (n / 2) := by omega
    rw [this, ih₁]
    simp only [r]
    ring
  | case2 n h => simp only [pow_zero, one_mul, true_and]; omega

/-- The loop of Algorithm 2.3.8, started at `i = 1` as the book permits
("One may start at `i = 1`"):
```
for (i ≤ ... < s) { if ((A D^m)^(2^(s-1-i)) ≡ -1 (mod p)) m = m + 2^i; }
```
-/
counted_def tonelliLoop {p : ℕ} (A D : ZMod p) (s i m : ℕ) : ℕ :=
  if i < s then
    if power (A * power D m) (2 ^ (s - 1 - i)) = -1 then tonelliLoop A D s (i + 1) (m + 2 ^ i)
    else tonelliLoop A D s (i + 1) m
  else m
termination_by s - i
decreasing_by all_goals omega

/-- **Algorithm 2.3.8, step 2 [Case `p ≡ 1 (mod 8)`].**  Given `a` and a quadratic
nonresidue `d` modulo `p`:
```
Represent p - 1 = 2^s t, with t odd;
A = a^t mod p;
D = d^t mod p;
m = 0;
for (0 ≤ i < s) { if ((A D^m)^(2^(s-1-i)) ≡ -1 (mod p)) m = m + 2^i; }
x = a^((t+1)/2) D^(m/2) mod p;
return x;
```
-/
counted_def tonelli {p : ℕ} (a d : ZMod p) : ZMod p :=
  let st := oddPart (p - 1)
  let s := st.1
  let t := st.2
  let A := power a t
  let D := power d t
  let m := tonelliLoop A D s 1 0
  power a ((t + 1) / 2) * power D (m / 2)

/-- Deterministic stand-in for the book's "find a random integer with property `P`":
try `d, d + 1, …` (at most `fuel` candidates) and return the first that passes. -/
counted_def searchFrom (P : ℕ → Bool) : (fuel d : ℕ) → ℕ
  | 0, d => d
  | fuel + 1, d => if P d then d else searchFrom P fuel (d + 1)

theorem searchFrom_spec (P : ℕ → Bool) (fuel d : ℕ) (h : ∃ e, d ≤ e ∧ e < d + fuel ∧ P e) :
    P (searchFrom P fuel d) := by
  induction fuel generalizing d with
  | zero => obtain ⟨e, h₁, h₂, -⟩ := h; omega
  | succ fuel ih =>
    rw [searchFrom]
    split_ifs with hd
    · exact hd
    · obtain ⟨e, h₁, h₂, h₃⟩ := h
      have : e ≠ d := by rintro rfl; exact hd h₃
      exact ih (d + 1) ⟨e, by omega, by omega, h₃⟩

/-- A quadratic nonresidue modulo the odd prime `p`: the least `d ≥ 2` with `(d/p) = -1`,
tested with Algorithm 2.3.5.  (The book picks `d` at random; half of all residues work.) -/
counted_def findNonresidue (p : ℕ) : ℕ :=
  searchFrom (fun d ↦ jacobi d p = -1) p 2

/-- **Algorithm 2.3.8 (Square roots (mod p)).**  Given an odd prime `p` and `a` with
`(a/p) = 1`, returns a solution `x` to `x² ≡ a (mod p)`.
```
if (p ≡ 3, 7 (mod 8)) { x = a^((p+1)/4) mod p;  return x; }
if (p ≡ 5 (mod 8)) {
  x = a^((p+3)/8) mod p;
  c = x² mod p;                                  // Then c ≡ ±a (mod p).
  if (c ≠ a mod p) x = x 2^((p-1)/4) mod p;
  return x;
}
[Case p ≡ 1 (mod 8)]  …
```
-/
counted_def sqrtMod (p : ℕ) (a : ZMod p) : ZMod p :=
  if p % 8 = 3 ∨ p % 8 = 7 then
    power a ((p + 1) / 4)
  else if p % 8 = 5 then
    let x := power a ((p + 3) / 8)
    if x * x ≠ a then x * power 2 ((p - 1) / 4) else x
  else
    tonelli a (findNonresidue p : ℕ)

section Correctness

variable {p : ℕ} [Fact p.Prime]

/-- Loop invariant of Algorithm 2.3.8.  Entering pass `i` we have `m` even and
`(A D^m)^(2^(s-i)) = 1`; so on exit (`i = s`) we have `A D^m = 1`, as the book notes
("Now we have `A D^m ≡ 1 (mod p)`"). -/
theorem tonelliLoop_spec {A D : ZMod p} {s : ℕ} (hD : D ^ 2 ^ (s - 1) = -1) (i m : ℕ)
    (hi : 1 ≤ i) (his : i ≤ s) (hm : Even m) (h : (A * D ^ m) ^ 2 ^ (s - i) = 1) :
    Even (tonelliLoop A D s i m) ∧ A * D ^ tonelliLoop A D s i m = 1 := by
  fun_induction tonelliLoop A D s i m with
  | case1 i m hlt hz ih =>
    -- the test fired: `(A D^m)^(2^(s-1-i)) = -1`, and `D^(2^i · 2^(s-1-i)) = -1` fixes it
    simp only [power_eq] at hz
    refine ih (by omega) (by omega) (hm.add (Nat.even_pow.mpr ⟨even_two, by omega⟩)) ?_
    have hexp : 2 ^ i * 2 ^ (s - 1 - i) = 2 ^ (s - 1) := by rw [← pow_add]; congr 1; omega
    rw [show s - (i + 1) = s - 1 - i by omega, pow_add, ← mul_assoc, mul_pow, hz, ← pow_mul,
      hexp, hD]
    norm_num
  | case2 i m hlt hz ih =>
    -- the test did not fire: the square root `(A D^m)^(2^(s-1-i))` of `1` must be `1`
    simp only [power_eq] at hz
    refine ih (by omega) (by omega) hm ?_
    have hsq : ((A * D ^ m) ^ 2 ^ (s - 1 - i)) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ, show s - 1 - i + 1 = s - i by omega, h]
    rw [show s - (i + 1) = s - 1 - i by omega]
    exact (sq_eq_one_iff.mp hsq).resolve_right hz
  | case3 i m hlt =>
    obtain rfl : i = s := by omega
    exact ⟨hm, by simpa using h⟩

/-- **Correctness of Algorithm 2.3.8, general case.**  For an odd prime `p`, a square
`a` and a nonresidue `d` modulo `p`, `tonelli a d` is a square root of `a`. -/
theorem tonelli_sq (hp : p ≠ 2) {a d : ZMod p} (ha : IsSquare a) (hd : ¬IsSquare d) :
    tonelli a d ^ 2 = a := by
  have hpp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp
  -- `p - 1 = 2^s t` with `t` odd and `s ≥ 1`
  obtain ⟨hst, ht⟩ := oddPart_spec (n := p - 1) (by have := hpp.two_le; omega)
  simp only [tonelli, power_eq]
  generalize (oddPart (p - 1)).1 = s at hst ⊢
  generalize (oddPart (p - 1)).2 = t at hst ht ⊢
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := by
    rcases s with _ | s
    · simp at hst; omega
    · exact ⟨s, rfl⟩
  have hhalf : p / 2 = t * 2 ^ s := by
    have : p - 1 = 2 * (t * 2 ^ s) := by rw [hst]; ring
    omega
  have ht2 : (t + 1) / 2 * 2 = t + 1 := by omega
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [zero_pow (show (t + 1) / 2 ≠ 0 by omega)]
  -- by Euler's criterion, `A = a^t` has `A^(2^(s-1)) = 1` and `D = d^t` has `D^(2^(s-1)) = -1`
  have hA : (a ^ t) ^ 2 ^ s = 1 := by rw [← pow_mul, ← hhalf, pow_half_eq_one ha0 ha]
  have hD : (d ^ t) ^ 2 ^ s = -1 := by rw [← pow_mul, ← hhalf, pow_half_eq_neg_one hd]
  obtain ⟨hm, hAD⟩ := tonelliLoop_spec (A := a ^ t) (D := d ^ t) (s := s + 1) (by simpa using hD)
    1 0 le_rfl (by omega) Even.zero (by simpa using hA)
  generalize tonelliLoop (a ^ t) (d ^ t) (s + 1) 1 0 = m at hm hAD
  -- `x² = a^(t+1) D^m = a · (A D^m) = a`
  have hm2 : m / 2 * 2 = m := Nat.div_mul_cancel hm.two_dvd
  calc (a ^ ((t + 1) / 2) * (d ^ t) ^ (m / 2)) ^ 2
      = a ^ ((t + 1) / 2 * 2) * (d ^ t) ^ (m / 2 * 2) := by rw [mul_pow, ← pow_mul, ← pow_mul]
    _ = a * (a ^ t * (d ^ t) ^ m) := by rw [ht2, hm2, pow_succ]; ring
    _ = a := by rw [hAD, mul_one]

/-- For an odd prime `p`, `findNonresidue p` is a quadratic nonresidue. -/
theorem findNonresidue_spec (hp : p ≠ 2) : ¬IsSquare ((findNonresidue p : ℕ) : ZMod p) := by
  have hpp : p.Prime := Fact.out
  have key : ∀ e : ℕ, jacobi e p = -1 ↔ ¬IsSquare ((e : ℕ) : ZMod p) := fun e ↦ by
    rw [jacobi_eq_legendreSym _ p hp, legendreSym.eq_neg_one_iff]
    norm_cast
  rw [← key]
  -- a nonsquare `x` exists; it is neither `0` nor `1`, so its residue lies in `[2, p-1]`
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  refine of_decide_eq_true (searchFrom_spec (fun d ↦ jacobi d p = -1) p 2
    ⟨x.val, ?_, by have := x.val_lt; omega, ?_⟩)
  · have h0 : x.val ≠ 0 := fun h ↦ hx ((ZMod.val_eq_zero x).mp h ▸ IsSquare.zero)
    have h1 : x.val ≠ 1 := fun h ↦ hx (by
      have : x = 1 := by rw [← ZMod.natCast_zmod_val x, h, Nat.cast_one]
      exact this ▸ IsSquare.one)
    omega
  · rw [decide_eq_true_iff]
    rwa [key, ZMod.natCast_zmod_val]

/-- **Correctness of Algorithm 2.3.8.**  For an odd prime `p` and a square `a` modulo `p`
(i.e. `(a/p) = 1`, or `a ≡ 0`), `sqrtMod p a` is a solution of `x² ≡ a (mod p)`. -/
theorem sqrtMod_sq (hp : p ≠ 2) {a : ZMod p} (ha : IsSquare a) : sqrtMod p a ^ 2 = a := by
  have hpp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp
  unfold sqrtMod
  simp only [power_eq]
  split_ifs with h37 h5 hc
  · -- `p ≡ 3 (mod 4)`: `x² = a^((p+1)/2) = a · a^((p-1)/2) = a`
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [zero_pow (show (p + 1) / 4 ≠ 0 by omega)]
    rw [← pow_mul, show (p + 1) / 4 * 2 = p / 2 + 1 by omega, pow_succ, pow_half_eq_one ha0 ha,
      one_mul]
  · -- `p ≡ 5 (mod 8)` and `x² = -a`: multiply by a square root `2^((p-1)/4)` of `-1`
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp [zero_pow (show (p + 3) / 8 ≠ 0 by omega)] at hc
    -- `x² = a · a^((p-1)/4)` and `a^((p-1)/4) = ±1`
    have hx : a ^ ((p + 3) / 8) * a ^ ((p + 3) / 8) = a * a ^ ((p - 1) / 4) := by
      rw [← pow_add, show (p + 3) / 8 + (p + 3) / 8 = (p - 1) / 4 + 1 by omega, pow_succ, mul_comm]
    have hquarter : (a ^ ((p - 1) / 4)) ^ 2 = 1 := by
      rw [← pow_mul, show (p - 1) / 4 * 2 = p / 2 by omega, pow_half_eq_one ha0 ha]
    have hneg : a ^ ((p - 1) / 4) = -1 := by
      refine (sq_eq_one_iff.mp hquarter).resolve_left fun h ↦ hc ?_
      rw [hx, h, mul_one]
    -- `2` is a nonresidue for `p ≡ 5 (mod 8)`
    have h2 : (2 : ZMod p) ^ (p / 2) = -1 :=
      pow_half_eq_neg_one fun h ↦ by have := (ZMod.exists_sq_eq_two_iff hp).mp h; omega
    calc (a ^ ((p + 3) / 8) * 2 ^ ((p - 1) / 4)) ^ 2
        = a ^ ((p + 3) / 8) * a ^ ((p + 3) / 8) * 2 ^ ((p - 1) / 4 * 2) := by
          rw [pow_mul]; ring
      _ = a := by rw [hx, hneg, show (p - 1) / 4 * 2 = p / 2 by omega, h2]; ring
  · -- `p ≡ 5 (mod 8)` and `x² = a` already
    rw [sq]
    exact not_not.mp hc
  · exact tonelli_sq hp ha (findNonresidue_spec hp)

end Correctness

/-! ## Algorithm 2.3.9 (Square roots (mod p) via `F_{p²}` arithmetic), Cipolla -/

/-- The field `F_{p²} = F_p(ω)` with `ω² = w`, for a nonresidue `w`: pairs `(x, y) = x + yω`
with the book's multiplication rule `(x, y) * (u, v) = (xu + yvw, xv + yu)`. -/
abbrev Fp2 (p : ℕ) (w : ZMod p) : Type := QuadraticAlgebra (ZMod p) w 0

/-- A product in `F_{p²}`, `(a + bω)(c + dω) = (ac + w bd) + (ad + bc)ω`: five products of
residues modulo `p`. -/
instance (p : ℕ) (w : ZMod p) : Chapter9.MulCost (Fp2 p w) :=
  ⟨fun C _ _ => 5 * C.mulMod p.size⟩

/-- **Algorithm 2.3.9 (Cipolla).**  Given an odd prime `p`, a quadratic residue `a`
modulo `p`, and `t` such that `t² - a` is a quadratic nonresidue (the book finds `t` at
random, testing with Algorithm 2.3.5):
```
x = (t + √(t² - a))^((p+1)/2);                    // Use F_{p²} arithmetic.
return x;
```
The arithmetic is that of `Fp2 p (t² - a)` (Mathlib's `QuadraticAlgebra`).  The result
lies in `F_p`, so we return its first coordinate. -/
counted_def cipolla {p : ℕ} (a t : ZMod p) : ZMod p :=
  (power (⟨t, 1⟩ : Fp2 p (t * t - a)) ((p + 1) / 2)).re

section Correctness

variable {p : ℕ} [Fact p.Prime]

open QuadraticAlgebra in
/-- **Correctness of Algorithm 2.3.9.**  For an odd prime `p`, a square `a` modulo `p`
and `t` with `t² - a` a nonresidue, `cipolla a t` is a square root of `a`.

Following the book: with `ω² = t² - a` a nonresidue, Frobenius gives
`(t + ω)^p = t - ω`, hence `(t + ω)^(p+1) = t² - ω² = a`, so
`x = (t + ω)^((p+1)/2)` satisfies `x² = a`; and `x` must lie in `F_p`. -/
theorem cipolla_sq (hp : p ≠ 2) {a t : ZMod p} (ha : IsSquare a) (ht : ¬IsSquare (t * t - a)) :
    cipolla a t ^ 2 = a := by
  have hpp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := hpp.eq_two_or_odd.resolve_left hp
  simp only [cipolla, power_eq]
  generalize hw : t * t - a = w at ht ⊢
  -- `K = F_p(ω)` has characteristic `p`
  have : CharP (Fp2 p w) p :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective p
  let C : ZMod p →+* Fp2 p w := algebraMap (ZMod p) (Fp2 p w)
  have hC : ∀ r, C r = ⟨r, 0⟩ := fun _ ↦ rfl
  have hz : (⟨t, 1⟩ : Fp2 p w) = C t + ω := by ext <;> simp [hC]
  have hωω : (ω : Fp2 p w) * ω = C w := by ext <;> simp [hC]
  -- `ω^p = ω · (ω²)^((p-1)/2) = -ω` by Euler's criterion
  have hωp : (ω : Fp2 p w) ^ p = -ω := by
    have hp2 : p = 2 * (p / 2) + 1 := by omega
    calc (ω : Fp2 p w) ^ p = ω ^ (2 * (p / 2) + 1) := congrArg (fun n ↦ (ω : Fp2 p w) ^ n) hp2
      _ = C (w ^ (p / 2)) * ω := by rw [pow_succ, pow_mul, sq, hωω, ← map_pow]
      _ = -ω := by rw [pow_half_eq_neg_one ht]; simp
  -- Frobenius: `(t + ω)^p = t - ω`
  have hfrob : (C t + ω) ^ p = C t - ω := by
    rw [add_pow_char, hωp, ← map_pow, ZMod.pow_card, sub_eq_add_neg]
  -- hence `(t + ω)^(p+1) = t² - ω² = a`
  have hnorm : (C t + ω) ^ (p + 1) = C a := by
    have ha' : a = t * t - w := by rw [← hw]; ring
    rw [pow_succ, hfrob, ha', map_sub, map_mul, ← hωω]
    ring
  rw [hz]
  generalize hx : (C t + ω) ^ ((p + 1) / 2) = x
  have hxx : x * x = C a := by
    rw [← hx, ← pow_add, show (p + 1) / 2 + (p + 1) / 2 = p + 1 by omega, hnorm]
  -- compare coordinates in `x² = a`
  have hre : x.re * x.re + w * x.im * x.im = a := by
    simpa [hC] using congrArg QuadraticAlgebra.re hxx
  have him : x.re * x.im + x.im * x.re = 0 := by
    simpa [hC] using congrArg QuadraticAlgebra.im hxx
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    have := hpp.two_le
    omega
  have hprod : x.re * x.im = 0 := by
    have : 2 * (x.re * x.im) = 0 := by linear_combination him
    exact (mul_eq_zero.mp this).resolve_left h2
  rcases mul_eq_zero.mp hprod with hre0 | him0
  · -- `x.re = 0` would make `ω² = a / x.im²` a square: impossible
    exfalso
    have hre' : w * x.im * x.im = a := by rw [hre0] at hre; linear_combination hre
    have hi : x.im ≠ 0 := by
      rintro h
      apply ht
      rw [← hw, show a = 0 by rw [← hre', h]; ring, sub_zero]
      exact ⟨t, rfl⟩
    obtain ⟨r, hr⟩ := ha
    refine ht ⟨r * x.im⁻¹, Eq.symm ?_⟩
    calc r * x.im⁻¹ * (r * x.im⁻¹) = r * r * (x.im⁻¹ * x.im⁻¹) := by ring
      _ = w * x.im * x.im * (x.im⁻¹ * x.im⁻¹) := by rw [← hr, ← hre']
      _ = w * (x.im * x.im⁻¹) * (x.im * x.im⁻¹) := by ring
      _ = w := by rw [mul_inv_cancel₀ hi]; ring
  · -- `x.im = 0`, so `x ∈ F_p` and `x² = a`
    rw [him0] at hre
    linear_combination hre

/-- Step 1 of Algorithm 2.3.9 [Find a certain quadratic nonresidue]: the least `t ≥ 0`
with `((t² - a)/p) = -1`.  (The book picks `t` at random.) -/
counted_def findCipolla (p a : ℕ) : ℕ :=
  searchFrom (fun t ↦ jacobi ((t : ℤ) * t - a) p = -1) p 0

/-- **Algorithm 2.3.9 (Cipolla)**, both steps. -/
counted_def cipollaSqrt (p : ℕ) (a : ZMod p) : ZMod p :=
  cipolla a (findCipolla p a.val : ℕ)

/-- For a nonzero square `a` there is a `t` with `t² - a` a nonresidue: with `a = r²` and
`u` any nonresidue, `t = r (1 + u)/(1 - u)` gives `t² - a = (2r/(1 - u))² u`. -/
theorem exists_sq_sub_not_isSquare (hp : p ≠ 2) {a : ZMod p} (ha : IsSquare a) (ha0 : a ≠ 0) :
    ∃ t : ZMod p, ¬IsSquare (t * t - a) := by
  obtain ⟨r, rfl⟩ := ha
  have hr : r ≠ 0 := fun h ↦ ha0 (by rw [h, mul_zero])
  obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have hu1 : 1 - u ≠ 0 := fun h ↦ hu (by
    rw [show u = 1 by linear_combination -h]; exact IsSquare.one)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpp : p.Prime := Fact.out
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    have := hpp.two_le
    omega
  set c := 2 * r * (1 - u)⁻¹ with hc
  have hc0 : c ≠ 0 := mul_ne_zero (mul_ne_zero h2 hr) (inv_ne_zero hu1)
  refine ⟨r * (1 + u) * (1 - u)⁻¹, fun ⟨s, hs⟩ ↦ hu ⟨s * c⁻¹, ?_⟩⟩
  have key : r * (1 + u) * (1 - u)⁻¹ * (r * (1 + u) * (1 - u)⁻¹) - r * r = c * c * u := by
    rw [hc]; field_simp; ring
  rw [key] at hs
  calc u = c * c * u * (c⁻¹ * c⁻¹) := by field_simp
    _ = s * c⁻¹ * (s * c⁻¹) := by rw [hs]; ring

/-- The search of step 1 of Algorithm 2.3.9 succeeds. -/
theorem findCipolla_spec (hp : p ≠ 2) {a : ZMod p} (ha : IsSquare a) (ha0 : a ≠ 0) :
    ¬IsSquare (((findCipolla p a.val : ℕ) : ZMod p) * (findCipolla p a.val : ℕ) - a) := by
  have key : ∀ t : ℕ, jacobi ((t : ℤ) * t - a.val) p = -1 ↔
      ¬IsSquare ((t : ZMod p) * t - a) := fun t ↦ by
    rw [jacobi_eq_legendreSym _ p hp, legendreSym.eq_neg_one_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := exists_sq_sub_not_isSquare hp ha ha0
  rw [← key]
  refine of_decide_eq_true (searchFrom_spec (fun t ↦ jacobi ((t : ℤ) * t - a.val) p = -1) p 0
    ⟨t.val, Nat.zero_le _, by have := t.val_lt; omega, ?_⟩)
  rw [decide_eq_true_iff, key, ZMod.natCast_zmod_val]
  exact ht

/-- **Correctness of Algorithm 2.3.9, both steps.**  For an odd prime `p` and a square
`a` modulo `p`, `cipollaSqrt p a` is a square root of `a`. -/
theorem cipollaSqrt_sq (hp : p ≠ 2) {a : ZMod p} (ha : IsSquare a) (ha0 : a ≠ 0) :
    cipollaSqrt p a ^ 2 = a :=
  cipolla_sq hp ha (findCipolla_spec hp ha ha0)

end Correctness

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Tonelli: number of modular multiplications -/

/-- The modular multiplications made by `tonelliLoop A D s i m`: per pass, the power
`D^m`, one product, and the power `(A D^m)^(2^(s-1-i))`. -/
def tonelliLoopMults {p : ℕ} (A D : ZMod p) (s i m : ℕ) : ℕ :=
  if i < s then
    if power (A * power D m) (2 ^ (s - 1 - i)) = -1 then
      tonelliLoopMults A D s (i + 1) (m + 2 ^ i) + (powMults m + 1 + powMults (2 ^ (s - 1 - i)))
    else tonelliLoopMults A D s (i + 1) m + (powMults m + 1 + powMults (2 ^ (s - 1 - i)))
  else 0
termination_by s - i
decreasing_by all_goals omega

/-- The modular multiplications made by `tonelli a d`: the powers `a^t`, `d^t`, the loop,
and the final `a^((t+1)/2) · D^(m/2)`. -/
def tonelliMults {p : ℕ} (a d : ZMod p) : ℕ :=
  let st := oddPart (p - 1)
  let m := tonelliLoop (power a st.2) (power d st.2) st.1 1 0
  2 * powMults st.2 + tonelliLoopMults (power a st.2) (power d st.2) st.1 1 0 +
    (powMults ((st.2 + 1) / 2) + powMults (m / 2) + 1)

/-- In the Tonelli loop the exponent `m` stays below `2^i`, hence below `2^s`. -/
theorem tonelliLoop_lt {p : ℕ} (A D : ZMod p) (s i m : ℕ) (hm : m < 2 ^ i) (his : i ≤ s) :
    tonelliLoop A D s i m < 2 ^ s := by
  fun_induction tonelliLoop A D s i m with
  | case1 i m hlt hz ih => exact ih (by rw [pow_succ]; omega) (by omega)
  | case2 i m hlt hz ih => exact ih (by rw [pow_succ]; omega) (by omega)
  | case3 i m hlt => exact hm.trans_le (Nat.pow_le_pow_right (by norm_num) his)

theorem powMults_le_of_lt_two_pow {m i : ℕ} (hm : m < 2 ^ i) : powMults m ≤ 2 * i := by
  have h₁ := powMults_le m
  have h₂ : Nat.log 2 m ≤ Nat.log 2 (2 ^ i) := Nat.log_mono_right hm.le
  rw [Nat.log_pow (by norm_num)] at h₂
  omega

theorem tonelliLoopMults_le {p : ℕ} (A D : ZMod p) (s i m : ℕ) (hm : m < 2 ^ i)
    (his : i ≤ s) : tonelliLoopMults A D s i m ≤ (s - i) * (4 * s + 1) := by
  have hpass : ∀ i m : ℕ, i < s → m < 2 ^ i →
      powMults m + 1 + powMults (2 ^ (s - 1 - i)) ≤ 4 * s + 1 := by
    intro i m hi hm
    have h₁ := powMults_le_of_lt_two_pow hm
    have h₂ := powMults_le (2 ^ (s - 1 - i))
    rw [Nat.log_pow (by norm_num)] at h₂
    omega
  fun_induction tonelliLoopMults A D s i m with
  | case1 i m hlt hz ih =>
    have ih := ih (by rw [pow_succ]; omega) (by omega)
    have := hpass i m hlt hm
    rw [show s - i = s - (i + 1) + 1 by omega, add_mul, one_mul]
    omega
  | case2 i m hlt hz ih =>
    have ih := ih (by rw [pow_succ]; omega) (by omega)
    have := hpass i m hlt hm
    rw [show s - i = s - (i + 1) + 1 by omega, add_mul, one_mul]
    omega
  | case3 i m hlt => omega

/-- **Complexity of Tonelli's algorithm 2.3.8.**  With `p - 1 = 2^s t`, the algorithm makes
at most `6 log₂ t + 4s² + 1` multiplications modulo `p` — the book's
"`O(s² + ln t)` modular operations".  Each costs at most `C.mulMod (size p)` bit
operations (`mul_add_divMod_le`), so with grammar-school arithmetic the worst case
(`s` large) is `O(ln⁴ p)` and the typical case (`s` small) is `O(ln³ p)`. -/
theorem tonelliMults_le {p : ℕ} (a d : ZMod p) :
    tonelliMults a d ≤
      6 * Nat.log 2 (oddPart (p - 1)).2 + 4 * (oddPart (p - 1)).1 ^ 2 + 1 := by
  simp only [tonelliMults]
  generalize (oddPart (p - 1)).1 = s
  generalize (oddPart (p - 1)).2 = t
  generalize power a t = A
  generalize power d t = D
  have h₁ := powMults_le t
  have h₂ := powMults_le ((t + 1) / 2)
  have h₃ : Nat.log 2 ((t + 1) / 2) ≤ Nat.log 2 t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · exact Nat.log_mono_right (by omega)
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · -- `s = 0`: the loop does not run and `m = 0`
    have h₄ : tonelliLoopMults A D 0 1 0 = 0 := by rw [tonelliLoopMults]; simp
    have h₅ : tonelliLoop A D 0 1 0 = 0 := by rw [tonelliLoop]; simp
    have h₆ : powMults (0 / 2) = 0 := by rw [powMults]; simp
    rw [h₄, h₅, h₆, show (0 : ℕ) ^ 2 = 0 by norm_num]
    omega
  · have h₄ := tonelliLoopMults_le A D s 1 0 (by norm_num) hs
    have h₅ : powMults (tonelliLoop A D s 1 0 / 2) ≤ 2 * s :=
      powMults_le_of_lt_two_pow ((Nat.div_le_self _ _).trans_lt
        (tonelliLoop_lt A D s 1 0 (by norm_num) hs))
    have h₆ : (s - 1) * (4 * s + 1) + 2 * s ≤ 4 * s ^ 2 := by
      obtain ⟨c, rfl⟩ : ∃ c, s = c + 1 := ⟨s - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      nlinarith
    omega

/-! ### Bit operations of the modular square root -/

/-- The loop's bit operations are its multiplications modulo `p`. -/
theorem tonelliLoop_cost (C : CostModel) {p : ℕ} (A D : ZMod p) (s i m : ℕ) :
    costOf C (tonelliLoop A D s i m) = tonelliLoopMults A D s i m * C.mulMod p.size := by
  have hK : ∀ a b : ZMod p, MulCost.mulCost C a b = C.mulMod p.size := fun _ _ ↦ rfl
  fun_induction tonelliLoop A D s i m with
  | case1 i m hlt hz ih =>
    cost_unfold tonelliLoop.counted
    rw [tonelliLoopMults, if_pos hlt, if_pos hz, power_cost C hK, power_cost C hK, ih]
    ring
  | case2 i m hlt hz ih =>
    cost_unfold tonelliLoop.counted
    rw [tonelliLoopMults, if_pos hlt, if_neg hz, power_cost C hK, power_cost C hK, ih]
    ring
  | case3 i m hlt =>
    cost_unfold tonelliLoop.counted
    rw [tonelliLoopMults, if_neg hlt, zero_mul]

/-- **The bit operations of Tonelli's algorithm** are its multiplications modulo `p`, each a
product of residues and a reduction (`C.mulMod (size p)`). -/
theorem tonelli_cost (C : CostModel) {p : ℕ} (a d : ZMod p) :
    costOf C (tonelli a d) = tonelliMults a d * C.mulMod p.size := by
  have hK : ∀ a b : ZMod p, MulCost.mulCost C a b = C.mulMod p.size := fun _ _ ↦ rfl
  cost_unfold tonelli.counted
  rw [tonelliMults, power_cost C hK, power_cost C hK, tonelliLoop_cost, power_cost C hK,
    power_cost C hK]
  ring

/-- **Bit complexity of Tonelli's algorithm, grammar-school arithmetic**: with
`p - 1 = 2^s t` and `k` the bit length of `p`, at most
`(6 log₂ t + 4s² + 1)(2k² + k)` bit operations — `O(ln⁴ p)` in the worst case (`s ≈ k`)
and `O(ln³ p)` when `s` is bounded, as the book states. -/
theorem tonelliCost_school_le {p : ℕ} (a d : ZMod p) :
    costOf school (tonelli a d) ≤
      (6 * Nat.log 2 (oddPart (p - 1)).2 + 4 * (oddPart (p - 1)).1 ^ 2 + 1) *
        (2 * p.size ^ 2 + p.size) := by
  rw [tonelli_cost, school_mulMod]
  exact Nat.mul_le_mul_right _ (tonelliMults_le a d)

theorem oddPart_snd_le (n : ℕ) : (oddPart n).2 ≤ n := by
  fun_induction oddPart n with
  | case1 n h r ih => exact ih.trans (Nat.div_le_self _ _)
  | case2 n h => exact le_rfl

/-- The modular multiplications made by `sqrtMod p a` (Algorithm 2.3.8), not counting the
search for a nonresidue in the case `p ≡ 1 (mod 8)`. -/
def sqrtModMults (p : ℕ) (a : ZMod p) : ℕ :=
  if p % 8 = 3 ∨ p % 8 = 7 then powMults ((p + 1) / 4)
  else if p % 8 = 5 then powMults ((p + 3) / 8) + 1 + (powMults ((p - 1) / 4) + 1)
  else tonelliMults a (findNonresidue p : ℕ)

/-- **The bit operations of Algorithm 2.3.8** are its multiplications modulo `p`, and in the
case `p ≡ 1 (mod 8)` the search for a nonresidue. -/
theorem sqrtMod_cost_le (C : CostModel) (p : ℕ) (a : ZMod p) :
    costOf C (sqrtMod p a) ≤ sqrtModMults p a * C.mulMod p.size + costOf C (findNonresidue p) := by
  have hK : ∀ a b : ZMod p, MulCost.mulCost C a b = C.mulMod p.size := fun _ _ ↦ rfl
  cost_unfold sqrtMod.counted
  unfold sqrtModMults
  simp only [power_cost C hK, tonelli_cost]
  split_ifs <;> nlinarith [Nat.zero_le (costOf C (findNonresidue p))]

/-- **Complexity of Algorithm 2.3.8**: at most `6 log₂ p + 4s² + 2` multiplications modulo
`p`, where `2^s` is the power of two in `p - 1`; so `O(ln p)` multiplications, i.e.
`O(ln³ p)` bit operations, in the cases `p ≡ 3, 5, 7 (mod 8)`. -/
theorem sqrtModMults_le (p : ℕ) (a : ZMod p) :
    sqrtModMults p a ≤ 6 * Nat.log 2 p + 4 * (oddPart (p - 1)).1 ^ 2 + 2 := by
  have hlog : ∀ m, m ≤ p → powMults m ≤ 2 * Nat.log 2 p := fun m hm ↦
    (powMults_le m).trans (Nat.mul_le_mul_left 2 (Nat.log_mono_right hm))
  unfold sqrtModMults
  split_ifs with h₁ h₂
  · have := hlog ((p + 1) / 4) (by omega)
    omega
  · have := hlog ((p + 3) / 8) (by omega)
    have := hlog ((p - 1) / 4) (by omega)
    omega
  · have h := tonelliMults_le a (findNonresidue p : ℕ)
    have ht : Nat.log 2 (oddPart (p - 1)).2 ≤ Nat.log 2 p :=
      Nat.log_mono_right ((oddPart_snd_le _).trans (Nat.sub_le p 1))
    omega

end RunningTime

end PrimeNumbers.Chapter2
