import PrimeNumbers.Chapter9.BitCost
import Mathlib

/-!
# §3.1 Trial division

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 3.1.

* `trialDivision`       — Algorithm 3.1.1: the multiset (here: list) of the primes dividing
                          `n`, with multiplicity.  This is the book's first *factoring*
                          algorithm.
* `trialDivision_spec`  — the output consists of primes and multiplies to `n`;
* `trialDivision_perm`  — hence it is the prime factorization of `n` (a permutation of
                          Mathlib's `Nat.primeFactorsList n`).
* `isPrimeTD`           — the resulting primality test, with `isPrimeTD_iff`.
-/

namespace PrimeNumbers.Chapter3

/-- The inner loop of Algorithm 3.1.1:
```
while (d | N) { N = N/d;  F = F ∪ {d}; }
```
Returns the new `(N, F)`. -/
def divideOut (d N : ℕ) (F : List ℕ) : ℕ × List ℕ :=
  if 1 < d ∧ 0 < N ∧ d ∣ N then divideOut d (N / d) (d :: F) else (N, F)
termination_by N
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem divideOut_fst_le (d N : ℕ) (F : List ℕ) : (divideOut d N F).1 ≤ N := by
  fun_induction divideOut d N F with
  | case1 N F h ih => exact ih.trans (Nat.div_le_self _ _)
  | case2 => exact le_rfl

/-- **Algorithm 3.1.1, step 2 [Main division loop]**:
```
while (d² ≤ N) {
  while (d | N) { N = N/d;  F = F ∪ {d}; }
  d = d + 2;
}
if (N == 1) return F;
return F ∪ {N};
```
-/
def trialLoop (d N : ℕ) (F : List ℕ) : List ℕ :=
  if d * d ≤ N then
    let r := divideOut d N F
    trialLoop (d + 2) r.1 r.2
  else if N = 1 then F
  else N :: F
termination_by N + 2 - d
decreasing_by
  have h₁ : d ≤ d * d := Nat.le_mul_self d
  have h₂ := divideOut_fst_le d N F
  omega

/-- **Algorithm 3.1.1 (Trial division).**  Given an integer `n > 1`, produces the
multiset `F` of the primes that divide `n`. -/
def trialDivision (n : ℕ) : List ℕ :=
  let r := divideOut 2 n []       -- 1. [Divide by 2]
  trialLoop 3 r.1 r.2             -- 2. [Main division loop]

/-- The inner loop: `N · ∏F` is unchanged, `d` no longer divides the new `N`, and every
element added to `F` is `d` (and then `d` divided the old `N`). -/
theorem divideOut_spec {d N : ℕ} (hd : 1 < d) (hN : 0 < N) (F : List ℕ) :
    (divideOut d N F).1 * (divideOut d N F).2.prod = N * F.prod ∧
      0 < (divideOut d N F).1 ∧ (divideOut d N F).1 ∣ N ∧ ¬d ∣ (divideOut d N F).1 ∧
      ∀ x ∈ (divideOut d N F).2, x ∈ F ∨ (x = d ∧ d ∣ N) := by
  fun_induction divideOut d N F with
  | case1 N F h ih =>
    have hdvd : d ∣ N := h.2.2
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ih (Nat.div_pos (Nat.le_of_dvd hN hdvd) (by omega))
    refine ⟨?_, h₂, h₃.trans (Nat.div_dvd_of_dvd hdvd), h₄, fun x hx ↦ ?_⟩
    · rw [h₁, List.prod_cons, ← mul_assoc, Nat.div_mul_cancel hdvd]
    · rcases h₅ x hx with hmem | ⟨rfl, -⟩
      · rcases List.mem_cons.mp hmem with rfl | hF
        · exact Or.inr ⟨rfl, hdvd⟩
        · exact Or.inl hF
      · exact Or.inr ⟨rfl, hdvd⟩
  | case2 N F h =>
    exact ⟨rfl, hN, dvd_rfl, fun hdvd ↦ h ⟨hd, hN, hdvd⟩, fun x hx ↦ Or.inl hx⟩

/-- A number `> 1` all of whose prime factors are `≥ d` is prime as soon as it is `< d²`,
and any divisor `d` of it is prime. -/
theorem prime_of_dvd_of_forall_le {d N : ℕ} (hd : 1 < d) (hdvd : d ∣ N)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ N → d ≤ q) : d.Prime := by
  have h := hmin d.minFac (Nat.minFac_prime (by omega)) ((Nat.minFac_dvd d).trans hdvd)
  have : d.minFac = d := le_antisymm (Nat.minFac_le (by omega)) h
  exact this ▸ Nat.minFac_prime (by omega)

/-- Loop invariant of Algorithm 3.1.1: `N` has no prime factor below the odd trial
divisor `d`, and `F` consists of primes.  On exit, the cofactor `N` is `1` or a prime. -/
theorem trialLoop_spec {d N : ℕ} (F : List ℕ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hN : 0 < N)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ N → d ≤ q) (hF : ∀ x ∈ F, x.Prime) :
    (trialLoop d N F).prod = N * F.prod ∧ ∀ x ∈ trialLoop d N F, x.Prime := by
  fun_induction trialLoop d N F with
  | case1 d N F hle r ih =>
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := divideOut_spec (by omega : 1 < d) hN F
    refine h₁ ▸ ih (by omega) (by omega) h₂ (fun q hq hqr ↦ ?_) (fun x hx ↦ ?_)
    · -- prime factors of the new `N` are `≥ d`, are not `d`, and are not the even `d + 1`
      have hqd : d ≤ q := hmin q hq (hqr.trans h₃)
      have hne : q ≠ d := by rintro rfl; exact h₄ hqr
      have hne' : q ≠ d + 1 := by
        rintro rfl
        have := hq.eq_two_or_odd
        omega
      omega
    · rcases h₅ x hx with hxF | ⟨rfl, hdvd⟩
      · exact hF x hxF
      · exact prime_of_dvd_of_forall_le (by omega) hdvd hmin
  | case2 d F hlt => simpa using hF
  | case3 d N F hlt hN1 =>
    -- `1 < N < d²` and `N` has no prime factor below `d`: `N` is prime
    have hNp : N.Prime := by
      by_contra hnp
      have h₁ := Nat.minFac_sq_le_self hN hnp
      have h₂ := hmin N.minFac (Nat.minFac_prime hN1) (Nat.minFac_dvd N)
      have h₃ : d * d ≤ N.minFac ^ 2 := by rw [sq]; exact Nat.mul_le_mul h₂ h₂
      omega
    refine ⟨by simp, fun x hx ↦ ?_⟩
    rcases List.mem_cons.mp hx with rfl | hxF
    · exact hNp
    · exact hF x hxF

/-- **Correctness of Algorithm 3.1.1**: the output consists of primes whose product is `n`. -/
theorem trialDivision_spec {n : ℕ} (hn : 0 < n) :
    (trialDivision n).prod = n ∧ ∀ p ∈ trialDivision n, p.Prime := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := divideOut_spec (by norm_num : 1 < 2) hn []
  have := trialLoop_spec (d := 3) (divideOut 2 n []).2 le_rfl (by norm_num) h₂
    (fun q hq hqr ↦ by
      have : q ≠ 2 := by rintro rfl; exact h₄ hqr
      have := hq.two_le
      omega)
    (fun x hx ↦ by
      rcases h₅ x hx with hx | ⟨rfl, -⟩
      · simp at hx
      · exact Nat.prime_two)
  rw [h₁] at this
  simpa [trialDivision] using this

/-- **Algorithm 3.1.1 computes the prime factorization**: its output is, up to order,
Mathlib's list `Nat.primeFactorsList n` of the prime factors of `n` with multiplicity. -/
theorem trialDivision_perm {n : ℕ} (hn : 0 < n) :
    (trialDivision n).Perm n.primeFactorsList :=
  Nat.primeFactorsList_unique (trialDivision_spec hn).1 (trialDivision_spec hn).2

/-- Primality by trial division: `n` is prime iff its factorization is `{n}`. -/
def isPrimeTD (n : ℕ) : Bool := trialDivision n = [n]

theorem isPrimeTD_iff {n : ℕ} (hn : 1 < n) : isPrimeTD n = true ↔ n.Prime := by
  rw [isPrimeTD, decide_eq_true_iff]
  constructor
  · intro h
    exact (trialDivision_spec (n := n) (by omega)).2 n (by rw [h]; simp)
  · intro hp
    have := trialDivision_perm (n := n) (by omega)
    rw [Nat.primeFactorsList_prime hp] at this
    exact List.perm_singleton.mp this

/-! ## Running time -/

/-- The number of passes of the main loop of Algorithm 3.1.1, following `trialLoop`. -/
def trialSteps (d N : ℕ) (F : List ℕ) : ℕ :=
  if d * d ≤ N then
    let r := divideOut d N F
    trialSteps (d + 2) r.1 r.2 + 1
  else 0
termination_by N + 2 - d
decreasing_by
  have h₁ : d ≤ d * d := Nat.le_mul_self d
  have h₂ := divideOut_fst_le d N F
  omega

/-- Algorithm 3.1.1 makes at most `(√N + 2 - d)/2` passes of its main loop: about `√n / 2`
trial divisors in the worst case, which is the book's `O(√n)` bound for trial division. -/
theorem two_mul_trialSteps_le (d N : ℕ) (F : List ℕ) :
    2 * trialSteps d N F ≤ Nat.sqrt N + 2 - d := by
  fun_induction trialSteps d N F with
  | case1 d N F hle r ih =>
    have h₁ : d ≤ Nat.sqrt N := Nat.le_sqrt.mpr hle
    have h₂ : Nat.sqrt r.1 ≤ Nat.sqrt N := Nat.sqrt_le_sqrt (divideOut_fst_le d N F)
    omega
  | case2 d N F hlt => omega

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Bit operations -/

/-- The number of divisions made by the inner loop `divideOut d N F`: one divisibility
test per pass, and one more division `N / d` each time the test succeeds. -/
def divideOutOps (d N : ℕ) (F : List ℕ) : ℕ :=
  if 1 < d ∧ 0 < N ∧ d ∣ N then divideOutOps d (N / d) (d :: F) + 2 else 1
termination_by N
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The bit operations of `divideOut d N F`: each of its divisions, at operand size. -/
def divideOutCost (C : CostModel) (d N : ℕ) (F : List ℕ) : ℕ :=
  if 1 < d ∧ 0 < N ∧ d ∣ N then
    divideOutCost C d (N / d) (d :: F) + 2 * C.divMod N.size d.size
  else C.divMod N.size d.size
termination_by N
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The number of divisions made by the main loop `trialLoop d N F`. -/
def trialOps (d N : ℕ) (F : List ℕ) : ℕ :=
  if d * d ≤ N then
    let r := divideOut d N F
    trialOps (d + 2) r.1 r.2 + divideOutOps d N F
  else 0
termination_by N + 2 - d
decreasing_by
  have h₁ : d ≤ d * d := Nat.le_mul_self d
  have h₂ := divideOut_fst_le d N F
  omega

/-- The bit operations of `trialLoop d N F`.  (The test `d² ≤ N` multiplies two numbers of
at most half the length of `N`; it is dominated by the division in the same pass and is
not counted.) -/
def trialCost (C : CostModel) (d N : ℕ) (F : List ℕ) : ℕ :=
  if d * d ≤ N then
    let r := divideOut d N F
    trialCost C (d + 2) r.1 r.2 + divideOutCost C d N F
  else 0
termination_by N + 2 - d
decreasing_by
  have h₁ : d ≤ d * d := Nat.le_mul_self d
  have h₂ := divideOut_fst_le d N F
  omega

/-- The bit operations of `trialDivision n` (Algorithm 3.1.1). -/
def trialDivisionCost (C : CostModel) (n : ℕ) : ℕ :=
  let r := divideOut 2 n []
  divideOutCost C 2 n [] + trialCost C 3 r.1 r.2

/-- Each successful division at least halves `N`: so the divisions of one inner loop
number at most `2 (log₂ N - log₂ N') + 1`, where `N'` is the cofactor left. -/
theorem divideOutOps_add_le (d N : ℕ) (F : List ℕ) :
    divideOutOps d N F + 2 * Nat.log 2 (divideOut d N F).1 ≤ 2 * Nat.log 2 N + 1 := by
  fun_induction divideOutOps d N F with
  | case1 N F h ih =>
    have hdN : d ≤ N := Nat.le_of_dvd h.2.1 h.2.2
    have h₁ : Nat.log 2 (N / d) ≤ Nat.log 2 (N / 2) :=
      Nat.log_mono_right (Nat.div_le_div_left (by omega) (by norm_num))
    have h₂ : Nat.log 2 (N / 2) = Nat.log 2 N - 1 := Nat.log_div_base 2 N
    have h₃ : 0 < Nat.log 2 N := Nat.log_pos (by norm_num) (by omega)
    rw [divideOut]
    simp only [h, and_self, ↓reduceIte]
    omega
  | case2 N F h =>
    rw [divideOut]
    simp only [h, ↓reduceIte]
    omega

/-- All divisions of the main loop: at most `2 log₂ N` successful ones in total, plus one
failed test per pass. -/
theorem trialOps_le (d N : ℕ) (F : List ℕ) :
    trialOps d N F ≤ 2 * Nat.log 2 N + trialSteps d N F := by
  fun_induction trialOps d N F with
  | case1 d N F hle r ih =>
    have h := divideOutOps_add_le d N F
    have hs : trialSteps d N F = trialSteps (d + 2) r.1 r.2 + 1 := by
      rw [trialSteps]; simp [hle, r]
    simp only [r] at ih hs ⊢
    omega
  | case2 d N F hlt => omega

section Bound

variable (C : CostModel) {n B : ℕ}
  (hB : ∀ a b : ℕ, a ≤ n.size → b ≤ n.size → C.divMod a b ≤ B)
include hB

theorem divideOutCost_le {d N : ℕ} (hd : d ≤ n) (hN : N ≤ n) (F : List ℕ) :
    divideOutCost C d N F ≤ divideOutOps d N F * B := by
  have hdiv : ∀ N' ≤ n, C.divMod N'.size d.size ≤ B := fun N' hN' ↦
    hB _ _ (Nat.size_le_size hN') (Nat.size_le_size hd)
  fun_induction divideOutCost C d N F with
  | case1 N F h ih =>
    have ih := ih ((Nat.div_le_self _ _).trans hN)
    have := hdiv N hN
    rw [divideOutOps]
    simp only [h, and_self, ↓reduceIte, add_mul]
    omega
  | case2 N F h =>
    rw [divideOutOps]
    simpa [h] using hdiv N hN

theorem trialCost_le {d N : ℕ} (hN : N ≤ n) (F : List ℕ) :
    trialCost C d N F ≤ trialOps d N F * B := by
  fun_induction trialCost C d N F with
  | case1 d N F hle r ih =>
    have hdN : d ≤ N := (Nat.le_mul_self d).trans hle
    have ih := ih ((divideOut_fst_le d N F).trans hN)
    have := divideOutCost_le C hB (hdN.trans hN) hN F
    rw [trialOps]
    simp only [hle, ↓reduceIte, add_mul, r] at ih ⊢
    omega
  | case2 d N F hlt => simp

/-- **Bit complexity of trial division**, for any cost model: at most
`2 log₂ n + √n/2 + 1` divisions, each of numbers no longer than `n`. -/
theorem trialDivisionCost_le (hn : 2 ≤ n) :
    trialDivisionCost C n ≤ (2 * Nat.log 2 n + Nat.sqrt n / 2 + 1) * B := by
  have h₁ := divideOutCost_le C hB hn le_rfl []
  have h₂ := trialCost_le C hB (divideOut_fst_le 2 n []) (d := 3) (divideOut 2 n []).2
  have h₃ := divideOutOps_add_le 2 n []
  have h₄ := trialOps_le 3 (divideOut 2 n []).1 (divideOut 2 n []).2
  have h₅ := two_mul_trialSteps_le 3 (divideOut 2 n []).1 (divideOut 2 n []).2
  have h₆ : Nat.sqrt (divideOut 2 n []).1 ≤ Nat.sqrt n :=
    Nat.sqrt_le_sqrt (divideOut_fst_le 2 n [])
  have hops : divideOutOps 2 n [] + trialOps 3 (divideOut 2 n []).1 (divideOut 2 n []).2 ≤
      2 * Nat.log 2 n + Nat.sqrt n / 2 + 1 := by omega
  calc trialDivisionCost C n
      ≤ divideOutOps 2 n [] * B +
          trialOps 3 (divideOut 2 n []).1 (divideOut 2 n []).2 * B := by
        simp only [trialDivisionCost]; omega
    _ = (divideOutOps 2 n [] + trialOps 3 (divideOut 2 n []).1 (divideOut 2 n []).2) * B := by
        ring
    _ ≤ _ := Nat.mul_le_mul_right B hops

end Bound

/-- **Bit complexity of trial division, grammar-school arithmetic.**  Algorithm 3.1.1
factors a `k`-bit number `n` in at most `(2 log₂ n + √n/2 + 1) · k (k + 1)` bit
operations, i.e. `O(√n ln² n)`. -/
theorem trialDivisionCost_school_le {n : ℕ} (hn : 2 ≤ n) :
    trialDivisionCost school n ≤
      (2 * Nat.log 2 n + Nat.sqrt n / 2 + 1) * ((n.size + 1) * n.size) :=
  trialDivisionCost_le school (fun a b ha hb ↦ Nat.mul_le_mul (by omega) hb) hn

end RunningTime

end PrimeNumbers.Chapter3
