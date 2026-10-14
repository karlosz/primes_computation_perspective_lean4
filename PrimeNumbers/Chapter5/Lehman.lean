import PrimeNumbers.Chapter9.CountedLib
import PrimeNumbers.Chapter5.Fermat
import PrimeNumbers.Chapter2.Euclid

/-!
# §5.1.2 Lehman method

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.1.2.

* `lehman`          — Algorithm 5.1.2 (Lehman method).
* `lehman_sound`           — for `n ≥ 576`, a returned `d` is a nontrivial divisor of `n`.
* `theorem_5_1_3_complete` — if the algorithm returns nothing, `n > 1` is prime.  The
  proof follows the book: `n = p q` with `n^{1/3} < p ≤ q`, Dirichlet's approximation
  theorem (`dirichlet_approximation`, from Mathlib) applied to `p/q` (`lehman_approx`),
  and the resulting `a = u q + v p` lies in the scanned range
  (`lehmanWitness_of_composite`).
* `lehmanPassBound_le_cuberoot` — step [Loop] makes at most `4 n^{1/3} + 2` passes.

Two deviations from the book, both noted where they occur: `k` runs to `⌊n^{1/3}⌋ + 1`
(one further than printed; the book's own inequality gives only `k < n^{1/3} + 1`), and
soundness is proved for `n ≥ 576` rather than `n > 21`.
-/

namespace PrimeNumbers.Chapter5

/-- Search upward for `⌊n^(1/e)⌋`: the largest `c` (within `fuel` steps) with `c^e ≤ n`. -/
counted_def rootLoop (e n : ℕ) : (c fuel : ℕ) → ℕ
  | c, 0 => c
  | c, fuel + 1 => if (c + 1) ^ e ≤ n then rootLoop e n (c + 1) fuel else c

/-- `⌊n^(1/e)⌋`. -/
counted_def iroot (e n : ℕ) : ℕ := rootLoop e n 0 n

theorem rootLoop_pow_le {e n c : ℕ} (hc : c ^ e ≤ n) (fuel : ℕ) :
    rootLoop e n c fuel ^ e ≤ n := by
  induction fuel generalizing c with
  | zero => exact hc
  | succ fuel ih =>
    rw [rootLoop]
    split_ifs with h
    · exact ih h
    · exact hc

theorem iroot_pow_le {e : ℕ} (he : e ≠ 0) (n : ℕ) : iroot e n ^ e ≤ n :=
  rootLoop_pow_le (by simp [he]) n

/-- **Algorithm 5.1.2, step 1 [Trial division]**: a divisor `d` of `n` with `2 ≤ d ≤ c`. -/
counted_def smallDivisor (n : ℕ) : (d fuel : ℕ) → Option ℕ
  | _, 0 => none
  | d, fuel + 1 => if n % d = 0 then some d else smallDivisor n (d + 1) fuel

/-- The inner loop of Algorithm 5.1.2, for `a, a + 1, …` (`fuel` values):
```
if b = √(a² - 4kn) is an integer return gcd(a + b, n);
```
-/
counted_def lehmanInner (n k a : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 =>
    let t := a * a - 4 * k * n
    let b := Nat.sqrt t
    if b * b = t then some (Nat.gcd (a + b) n) else lehmanInner n k (a + 1) fuel

/-- The outer loop of Algorithm 5.1.2, for `k, k + 1, …` (`fuel` values):
```
for (2√(kn) ≤ a ≤ 2√(kn) + n^(1/6)/(4√k)) { … }
```
-/
counted_def lehmanOuter (n r6 : ℕ) : (k fuel : ℕ) → Option ℕ
  | _, 0 => none
  | k, fuel + 1 =>
    match lehmanInner n k (ceilSqrt (4 * k * n)) (r6 / (4 * Nat.sqrt k) + 2) with
    | some d => some d
    | none => lehmanOuter n r6 (k + 1) fuel

/-- **Algorithm 5.1.2 (Lehman method).**  Given an integer `n > 21`, either provides a
nontrivial factor of `n` or reports nothing (the book: "proves `n` prime").
```
1. Check whether n has a nontrivial divisor d ≤ n^(1/3), and if so, return d;
2. for (1 ≤ k ≤ n^(1/3)) { for (2√(kn) ≤ a ≤ 2√(kn) + n^(1/6)/(4√k)) { … } }
   return "n is prime";
```
**One deviation from the book**: `k` runs up to `⌊n^(1/3)⌋ + 1`, one further than printed.
The book's proof of Theorem 5.1.3 bounds the `k` it needs by `k < n^(1/3) + 1`, which for
integers gives `k ≤ ⌊n^(1/3)⌋ + 1`, not `k ≤ n^(1/3)`; the extra value makes the
completeness theorem below true as proved. -/
counted_def lehman (n : ℕ) : Option ℕ :=
  let c := iroot 3 n
  match smallDivisor n 2 (c - 1) with
  | some d => some d
  | none => lehmanOuter n (iroot 6 n) 1 (c + 1)

/-! ## Soundness -/

theorem smallDivisor_some {n d fuel r : ℕ} (h : smallDivisor n d fuel = some r) :
    d ≤ r ∧ r < d + fuel ∧ r ∣ n := by
  induction fuel generalizing d with
  | zero => simp [smallDivisor] at h
  | succ fuel ih =>
    rw [smallDivisor] at h
    split_ifs at h with hd
    · obtain rfl := Option.some.inj h
      exact ⟨le_rfl, by omega, Nat.dvd_of_mod_eq_zero hd⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih h
      exact ⟨by omega, by omega, h₃⟩

theorem lehmanInner_some {n k a fuel d : ℕ} (h : lehmanInner n k a fuel = some d) :
    ∃ a' b, a ≤ a' ∧ a' < a + fuel ∧ a' * a' - 4 * k * n = b * b ∧ d = Nat.gcd (a' + b) n := by
  induction fuel generalizing a with
  | zero => simp [lehmanInner] at h
  | succ fuel ih =>
    simp only [lehmanInner] at h
    split_ifs at h with hsq
    · exact ⟨a, _, le_rfl, by omega, hsq.symm, (Option.some.inj h).symm⟩
    · obtain ⟨a', b, h₁, h₂, h₃, h₄⟩ := ih h
      exact ⟨a', b, by omega, by omega, h₃, h₄⟩

theorem lehmanOuter_some {n r6 k fuel d : ℕ} (h : lehmanOuter n r6 k fuel = some d) :
    ∃ k', k ≤ k' ∧ k' < k + fuel ∧
      lehmanInner n k' (ceilSqrt (4 * k' * n)) (r6 / (4 * Nat.sqrt k') + 2) = some d := by
  induction fuel generalizing k with
  | zero => simp [lehmanOuter] at h
  | succ fuel ih =>
    rw [lehmanOuter] at h
    split at h
    · rename_i d' hd'
      obtain rfl := Option.some.inj h
      exact ⟨k, le_rfl, by omega, hd'⟩
    · obtain ⟨k', h₁, h₂, h₃⟩ := ih h
      exact ⟨k', by omega, by omega, h₃⟩

/-- **Soundness of Algorithm 5.1.2**: for `n ≥ 576`, a returned `d` is a nontrivial
divisor of `n`. -/
theorem lehman_sound {n d : ℕ} (hn : 576 ≤ n) (h : lehman n = some d) :
    d ∣ n ∧ 1 < d ∧ d < n := by
  have hc3 : iroot 3 n ^ 3 ≤ n := iroot_pow_le (by norm_num) n
  have hr6 : iroot 6 n ^ 6 ≤ n := iroot_pow_le (by norm_num) n
  simp only [lehman] at h
  generalize iroot 3 n = c at hc3 h
  generalize iroot 6 n = r6 at hr6 h
  -- `c³ ≤ n` forces `c < n`, and `r6⁶ ≤ n` forces `64 r6 ≤ n`
  have hcn : c < n := by
    by_contra hge
    have : n * 1 * 1 ≤ c * c * c := by
      have h1 : 1 ≤ c := by omega
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) h1) h1
    have : c ^ 3 = c * c * c := by ring
    nlinarith
  have hr6n : 64 * r6 ≤ n := by
    rcases Nat.lt_or_ge r6 3 with hlt | hge
    · omega
    · have h5 : 3 ^ 5 ≤ r6 ^ 5 := Nat.pow_le_pow_left hge 5
      have : r6 ^ 6 = r6 * r6 ^ 5 := by ring
      nlinarith
  split at h
  · -- found by trial division
    rename_i d' hd'
    obtain rfl := Option.some.inj h
    obtain ⟨h₁, h₂, h₃⟩ := smallDivisor_some hd'
    exact ⟨h₃, by omega, by omega⟩
  · -- found in the main loop: `a² - 4kn = b²`
    obtain ⟨k, hk1, hkc, hinner⟩ := lehmanOuter_some h
    obtain ⟨a, b, ha₁, ha₂, hsq, rfl⟩ := lehmanInner_some hinner
    have hkn : 0 < 4 * k * n := by positivity
    have hna : 4 * k * n ≤ a * a :=
      (le_ceilSqrt_mul_self _).trans (Nat.mul_le_mul ha₁ ha₁)
    have haa : a * a = 4 * k * n + b * b := by omega
    have hba : b ≤ a := by
      by_contra hlt
      have : a * a < b * b := Nat.mul_lt_mul'' (by omega) (by omega)
      omega
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | h0
      · simp at hna; omega
      · exact h0
    -- `64 k ≤ n`, because `k ≤ c + 1` and `c³ ≤ n`
    have hk64 : 64 * k ≤ n := by
      rcases Nat.lt_or_ge k 10 with hlt | hge
      · omega
      · have hc9 : 9 ≤ c := by omega
        have h₁ : 81 ≤ c * c := Nat.mul_le_mul hc9 hc9
        have h₂ : c ^ 3 = c * (c * c) := by ring
        nlinarith
    -- hence `⌈√(4kn)⌉ ≤ n/4 + 1`
    have ha₀ : ceilSqrt (4 * k * n) ≤ n / 4 + 1 := by
      refine ceilSqrt_le ?_
      have h4 : n < 4 * (n / 4 + 1) := by omega
      nlinarith
    -- so `a + b ≤ 2a < n`
    have hfuel : r6 / (4 * Nat.sqrt k) ≤ r6 := Nat.div_le_self _ _
    have hab : a + b < n := by omega
    have hdvd : Nat.gcd (a + b) n ∣ n := Nat.gcd_dvd_right _ _
    have hlt : Nat.gcd (a + b) n < n :=
      (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)).trans_lt hab
    refine ⟨hdvd, ?_, hlt⟩
    -- if `gcd(a + b, n) = 1` then `n ∣ a - b < n`, so `a = b` and `4kn = 0`
    by_contra hd1
    have hpos : 0 < Nat.gcd (a + b) n := Nat.gcd_pos_of_pos_right _ (by omega)
    have hcop : Nat.Coprime n (a + b) := by
      rw [Nat.coprime_comm]; exact (by omega : Nat.gcd (a + b) n = 1)
    have hfac : (a + b) * (a - b) = 4 * k * n := by
      rw [← Nat.mul_self_sub_mul_self_eq]; omega
    have hn_dvd : n ∣ (a + b) * (a - b) := ⟨4 * k, by rw [hfac]; ring⟩
    have := hcop.dvd_of_dvd_mul_left hn_dvd
    have hzero : a - b = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    rw [hzero, mul_zero] at hfac
    omega

/-! ## Running time -/

/-- **The number of passes of step [Loop] of Algorithm 5.1.2**, bounded by the fuel of each
inner loop: `∑_{k} (⌊n^{1/6}⌋ / (4⌊√k⌋) + 2)` over the `k` tried.  Each pass costs two
multiplications, one integer square root and (once) a gcd; this is the sum the book bounds
by `O(n^{1/3})`.  Step [Trial division] adds at most `⌊n^{1/3}⌋` divisions. -/
def lehmanPassBound (r6 k fuel : ℕ) : ℕ :=
  ∑ i ∈ Finset.range fuel, (r6 / (4 * Nat.sqrt (k + i)) + 2)

theorem lehmanPassBound_succ (r6 k fuel : ℕ) :
    lehmanPassBound r6 k (fuel + 1) =
      (r6 / (4 * Nat.sqrt k) + 2) + lehmanPassBound r6 (k + 1) fuel := by
  rw [lehmanPassBound, Finset.sum_range_succ', add_zero, add_comm, lehmanPassBound]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by rw [add_right_comm, add_assoc]

/-! ## Completeness, reduced to the existence statement of Theorem 5.1.3 -/

/-- **The existence statement in the proof of Theorem 5.1.3**: some `k ≤ n^{1/3}` and some
`a` in the range scanned for that `k` have `a² - 4kn` a perfect square.

The book proves: if `n` is composite with no divisor in `[2, n^{1/3}]`, then `n = p q`
with primes `n^{1/3} < p ≤ q`, and by Dirichlet's approximation theorem there are `u, v`
with `k = u v ≤ n^{1/3}` and `|u q - v p| < n^{1/3}`; then `a = u q + v p` works.  That
derivation is **not formalized**; `LehmanWitness n` is what it produces. -/
def LehmanWitness (n : ℕ) : Prop :=
  ∃ k a b, 1 ≤ k ∧ k ≤ iroot 3 n + 1 ∧ ceilSqrt (4 * k * n) ≤ a ∧
    a < ceilSqrt (4 * k * n) + (iroot 6 n / (4 * Nat.sqrt k) + 2) ∧ a * a - 4 * k * n = b * b

theorem lehmanInner_isSome {n k a fuel : ℕ}
    (h : ∃ a' b, a ≤ a' ∧ a' < a + fuel ∧ a' * a' - 4 * k * n = b * b) :
    (lehmanInner n k a fuel).isSome := by
  induction fuel generalizing a with
  | zero => obtain ⟨a', b, h₁, h₂, -⟩ := h; omega
  | succ fuel ih =>
    simp only [lehmanInner]
    split_ifs with hsq
    · rfl
    · obtain ⟨a', b, h₁, h₂, h₃⟩ := h
      have hne : a' ≠ a := by
        rintro rfl
        exact hsq (by rw [h₃, Nat.sqrt_eq])
      exact ih ⟨a', b, by omega, by omega, h₃⟩

theorem lehmanOuter_isSome {n r6 k fuel : ℕ}
    (h : ∃ k', k ≤ k' ∧ k' < k + fuel ∧
      (lehmanInner n k' (ceilSqrt (4 * k' * n)) (r6 / (4 * Nat.sqrt k') + 2)).isSome) :
    (lehmanOuter n r6 k fuel).isSome := by
  induction fuel generalizing k with
  | zero => obtain ⟨k', h₁, h₂, -⟩ := h; omega
  | succ fuel ih =>
    rw [lehmanOuter]
    split
    · rfl
    · rename_i hnone
      obtain ⟨k', h₁, h₂, h₃⟩ := h
      have hne : k' ≠ k := by
        rintro rfl
        rw [hnone] at h₃
        exact absurd h₃ (by simp)
      exact ih ⟨k', by omega, by omega, h₃⟩

/-- If the existence statement holds, Algorithm 5.1.2 returns an answer. -/
theorem lehman_isSome_of_witness {n : ℕ} (h : LehmanWitness n) : (lehman n).isSome := by
  obtain ⟨k, a, b, hk1, hkc, ha₁, ha₂, hsq⟩ := h
  simp only [lehman]
  split
  · rfl
  · exact lehmanOuter_isSome ⟨k, hk1, by omega, lehmanInner_isSome ⟨a, b, ha₁, ha₂, hsq⟩⟩

theorem smallDivisor_none {n d fuel : ℕ} (h : smallDivisor n d fuel = none) :
    ∀ r, d ≤ r → r < d + fuel → ¬r ∣ n := by
  induction fuel generalizing d with
  | zero => intro r h₁ h₂; omega
  | succ fuel ih =>
    rw [smallDivisor] at h
    split_ifs at h with hd
    intro r h₁ h₂ hr
    rcases Nat.eq_or_lt_of_le h₁ with rfl | hlt
    · exact hd (Nat.mod_eq_zero_of_dvd hr)
    · exact ih h r (by omega) (by omega) hr

/-- **Completeness of Algorithm 5.1.2, modulo the existence statement.**  Suppose that for
composite `n` without a divisor in `[2, n^{1/3}]` the existence statement `LehmanWitness n`
holds (this is the part of the proof of Theorem 5.1.3 that is not formalized).  Then if
the algorithm returns nothing, `n` is prime. -/
theorem lehman_none_prime {n : ℕ}
    (hex : ¬n.Prime → (∀ d, 2 ≤ d → d ≤ iroot 3 n → ¬d ∣ n) → LehmanWitness n)
    (h : lehman n = none) : n.Prime := by
  by_contra hnp
  have hsmall : smallDivisor n 2 (iroot 3 n - 1) = none := by
    simp only [lehman] at h
    split at h
    · exact absurd h (by simp)
    · assumption
  have hwit := hex hnp fun d h₁ h₂ ↦ smallDivisor_none hsmall d h₁ (by omega)
  have := lehman_isSome_of_witness hwit
  rw [h] at this
  exact absurd this (by simp)

/-! ## Closed form of the running time -/

/-- `∑_{k=1}^{c} 1/√k ≤ 2√c`. -/
theorem sum_inv_sqrt_le (c : ℕ) :
    ∑ i ∈ Finset.range c, (1 / Real.sqrt ((i : ℝ) + 1)) ≤ 2 * Real.sqrt c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ]
    have ha : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
    have hb : (0 : ℝ) < Real.sqrt ((c : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have ha2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt (by positivity)
    have hb2 : Real.sqrt ((c : ℝ) + 1) ^ 2 = c + 1 := Real.sq_sqrt (by positivity)
    have hstep : 1 / Real.sqrt ((c : ℝ) + 1) ≤
        2 * Real.sqrt ((c : ℝ) + 1) - 2 * Real.sqrt c := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (Real.sqrt ((c : ℝ) + 1) - Real.sqrt c)]
    push_cast
    linarith

/-- `⌊√k⌋ ≥ √k / 2` for `k ≥ 1`. -/
theorem sqrt_le_two_mul_natSqrt {k : ℕ} (hk : 1 ≤ k) :
    Real.sqrt k ≤ 2 * (Nat.sqrt k : ℝ) := by
  have h1 : 1 ≤ Nat.sqrt k := Nat.le_sqrt.mpr (by omega)
  have h2 : (k : ℝ) ≤ ((Nat.sqrt k : ℝ) + 1) ^ 2 := by
    have := (Nat.lt_succ_sqrt' k).le
    exact_mod_cast this
  have h3 : Real.sqrt k ≤ (Nat.sqrt k : ℝ) + 1 :=
    (Real.sqrt_le_sqrt h2).trans_eq (Real.sqrt_sq (by positivity))
  have h4 : (1 : ℝ) ≤ Nat.sqrt k := by exact_mod_cast h1
  linarith

/-- **Closed form for the running time of Algorithm 5.1.2**: with `c = ⌊n^{1/3}⌋` and
`r6 = ⌊n^{1/6}⌋`, step [Loop] makes at most `r6 √c + 2c` passes.  Since `r6⁶ ≤ n` and
`c³ ≤ n` this is at most `n^{1/3} + 2 n^{1/3}`: the book's `O(n^{1/3})`. -/
theorem lehmanPassBound_le_closed (r6 c : ℕ) :
    (lehmanPassBound r6 1 c : ℝ) ≤ r6 * Real.sqrt c + 2 * c := by
  have h₁ : (lehmanPassBound r6 1 c : ℝ) ≤
      ((∑ i ∈ Finset.range c, (r6 / (4 * Nat.sqrt (1 + i)) + 2) : ℕ) : ℝ) := le_rfl
  have hterm : ∀ i ∈ Finset.range c,
      (((r6 / (4 * Nat.sqrt (1 + i)) + 2 : ℕ)) : ℝ) ≤
        (r6 : ℝ) / 2 * (1 / Real.sqrt ((i : ℝ) + 1)) + 2 := by
    intro i _
    have hs : 1 ≤ Nat.sqrt (1 + i) := Nat.le_sqrt.mpr (by omega)
    have hspos : (0 : ℝ) < Nat.sqrt (1 + i) := by exact_mod_cast hs
    have hrt : (0 : ℝ) < Real.sqrt ((i : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h2 := sqrt_le_two_mul_natSqrt (k := 1 + i) (by omega)
    rw [show ((1 + i : ℕ) : ℝ) = (i : ℝ) + 1 by push_cast; ring] at h2
    have hdiv : ((r6 / (4 * Nat.sqrt (1 + i)) : ℕ) : ℝ) ≤ (r6 : ℝ) / (4 * Nat.sqrt (1 + i)) := by
      have := Nat.cast_div_le (α := ℝ) (m := r6) (n := 4 * Nat.sqrt (1 + i))
      simpa using this
    have hcmp : (r6 : ℝ) / (4 * Nat.sqrt (1 + i)) ≤
        (r6 : ℝ) / 2 * (1 / Real.sqrt ((i : ℝ) + 1)) := by
      rw [div_mul_div_comm, mul_one]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg r6) (by positivity) (by linarith)
    push_cast
    linarith
  have h₂ := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h₂
  have h₃ := sum_inv_sqrt_le c
  have hr : (0 : ℝ) ≤ (r6 : ℝ) / 2 := by positivity
  have h₄ := mul_le_mul_of_nonneg_left h₃ hr
  push_cast at h₁ h₂ ⊢
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h₂
  nlinarith

/-! ## The existence step of Theorem 5.1.3 -/

/-- **Dirichlet's approximation theorem** ([Hardy and Wright, Theorem 36], as used in the
book): for real `ξ` and `N ≥ 1` there are integers `j` and `0 < v ≤ N` with
`|v ξ - j| ≤ 1/(N + 1)`.  This is in Mathlib. -/
theorem dirichlet_approximation (ξ : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ j v : ℤ, 0 < v ∧ v ≤ N ∧ |v * ξ - j| ≤ 1 / (N + 1) :=
  Real.exists_int_int_abs_mul_sub_le ξ hN

/-- The approximation used in the proof of Theorem 5.1.3.  Let `0 < p ≤ q` and let `t` be
the real cube root of `p q`, with `t < p`.  Then there are positive integers `u, v` with
`u v < t + 1` and `|u q - v p| < t`.

Proof (the book's): apply Dirichlet's theorem to `p/q` with the bound
`B = √(t q / p)` (the book's `n^{1/6} √(q/p)`); then `q / B = t` and `B² p / q = t`. -/
theorem lehman_approx {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) {t : ℝ} (ht0 : 0 < t)
    (ht : t ^ 3 = (p : ℝ) * q) (htp : t < p) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ ((u * v : ℕ) : ℝ) < t + 1 ∧ |(u : ℝ) * q - v * p| < t := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hQ : (0 : ℝ) < q := by exact_mod_cast hp.trans_le hpq
  have hPQ : (p : ℝ) ≤ q := by exact_mod_cast hpq
  -- `t ≥ 1`
  have ht1 : 1 ≤ t := by
    by_contra hlt
    have h₁ : t ^ 3 < 1 := pow_lt_one₀ ht0.le (by linarith) (by norm_num)
    have h₂ : (1 : ℝ) ≤ (p : ℝ) * q := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp
      nlinarith
    linarith
  -- the bound `B`, with `B² = t q / p` and `t B = q`
  set B := Real.sqrt (t * q / p) with hB
  have hB2 : B ^ 2 = t * q / p := Real.sq_sqrt (by positivity)
  have hB0 : 0 < B := Real.sqrt_pos.mpr (by positivity)
  have hB1 : 1 ≤ B := by
    have h₁ : (1 : ℝ) ≤ t * q / p := by
      rw [le_div_iff₀ hP]; nlinarith
    have : (1 : ℝ) ≤ B ^ 2 := by rw [hB2]; exact h₁
    nlinarith
  have htB : t * B = q := by
    have hsq : (t * B) ^ 2 = (q : ℝ) ^ 2 := by
      rw [mul_pow, hB2, show t ^ 2 * (t * (q : ℝ) / p) = t ^ 3 * q / p by ring, ht]
      field_simp
    nlinarith [sq_nonneg (t * B - q), mul_pos ht0 hB0]
  -- Dirichlet with `N = ⌊B⌋`
  have hN : 0 < ⌊B⌋₊ := Nat.floor_pos.mpr hB1
  have hNle : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB0.le
  have hNlt : B < (⌊B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one B
  obtain ⟨j, v, hv0, hvN, habs⟩ := dirichlet_approximation ((p : ℝ) / q) hN
  have hv0' : (0 : ℝ) < v := by exact_mod_cast hv0
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv0
  have hvN' : (v : ℝ) ≤ ⌊B⌋₊ := by exact_mod_cast hvN
  have hN1 : (0 : ℝ) < (⌊B⌋₊ : ℝ) + 1 := by positivity
  -- `|v p - j q| < t`
  have hdiff : |(v : ℝ) * p - j * q| < t := by
    have h₁ : (v : ℝ) * ((p : ℝ) / q) - j = ((v : ℝ) * p - j * q) / q := by field_simp
    rw [h₁, abs_div, abs_of_pos hQ, div_le_iff₀ hQ] at habs
    have h₂ : 1 / ((⌊B⌋₊ : ℝ) + 1) * q < t := by
      rw [← htB, show 1 / ((⌊B⌋₊ : ℝ) + 1) * (t * B) = t * (B / ((⌊B⌋₊ : ℝ) + 1)) by ring]
      exact mul_lt_of_lt_one_right ht0 ((div_lt_one hN1).mpr hNlt)
    linarith
  -- `j ≥ 1`: otherwise `|v p - j q| ≥ p > t`
  have hj : 0 < j := by
    by_contra hle
    have hj0 : (j : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hle
    have h₁ : (j : ℝ) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hj0 hQ.le
    have h₂ : (p : ℝ) ≤ v * p := le_mul_of_one_le_left hP.le hv1
    linarith [le_abs_self ((v : ℝ) * p - j * q)]
  -- `j v < t + 1`
  have hprod : (j : ℝ) * v < t + 1 := by
    have h₁ : (j : ℝ) ≤ v * ((p : ℝ) / q) + 1 / ((⌊B⌋₊ : ℝ) + 1) := by
      linarith [(abs_le.mp habs).2, neg_abs_le ((v : ℝ) * ((p : ℝ) / q) - j),
        (abs_le.mp habs).1]
    have h₂ : (v : ℝ) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hv0'.le (hvN'.trans hNle) 2
    have h₃ : (v : ℝ) ^ 2 * ((p : ℝ) / q) ≤ t := by
      calc (v : ℝ) ^ 2 * ((p : ℝ) / q) ≤ B ^ 2 * ((p : ℝ) / q) :=
            mul_le_mul_of_nonneg_right h₂ (by positivity)
        _ = t := by rw [hB2]; field_simp
    have h₄ : (v : ℝ) / ((⌊B⌋₊ : ℝ) + 1) < 1 := (div_lt_one hN1).mpr (by linarith)
    have h₅ : (j : ℝ) * v ≤ (v * ((p : ℝ) / q) + 1 / ((⌊B⌋₊ : ℝ) + 1)) * v :=
      mul_le_mul_of_nonneg_right h₁ hv0'.le
    have h₆ : (v * ((p : ℝ) / q) + 1 / ((⌊B⌋₊ : ℝ) + 1)) * v =
        (v : ℝ) ^ 2 * ((p : ℝ) / q) + (v : ℝ) / ((⌊B⌋₊ : ℝ) + 1) := by ring
    linarith
  -- back to natural numbers
  have hjn : ((j.toNat : ℕ) : ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg hj.le
  have hvn : ((v.toNat : ℕ) : ℝ) = v := by exact_mod_cast Int.toNat_of_nonneg hv0.le
  refine ⟨j.toNat, v.toNat, by omega, by omega, ?_, ?_⟩
  · push_cast; rw [hjn, hvn]; exact hprod
  · rw [hjn, hvn, abs_sub_comm]; exact hdiff

/-! ### `iroot` is the integer root -/

theorem le_rootLoop (e n c fuel : ℕ) : c ≤ rootLoop e n c fuel := by
  induction fuel generalizing c with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [rootLoop]
    split_ifs
    · exact (Nat.le_succ c).trans (ih (c + 1))
    · exact le_rfl

theorem le_rootLoop_of_pow_le {e n c fuel m : ℕ} (hcm : c ≤ m) (hm : m ^ e ≤ n)
    (hfuel : m ≤ c + fuel) : m ≤ rootLoop e n c fuel := by
  induction fuel generalizing c with
  | zero => exact hfuel.trans (by simp [rootLoop])
  | succ fuel ih =>
    rw [rootLoop]
    split_ifs with h
    · rcases Nat.eq_or_lt_of_le hcm with rfl | hlt
      · exact (Nat.le_succ c).trans (le_rootLoop e n (c + 1) fuel)
      · exact ih hlt (by omega)
    · by_contra hlt
      exact h ((Nat.pow_le_pow_left (by omega : c + 1 ≤ m) e).trans hm)

/-- `iroot e n` is the largest `m` with `m^e ≤ n`. -/
theorem le_iroot {e n m : ℕ} (he : e ≠ 0) (hm : m ^ e ≤ n) : m ≤ iroot e n :=
  le_rootLoop_of_pow_le (Nat.zero_le m) hm (by
    have := Nat.le_self_pow he m
    omega)

theorem lt_iroot_succ_pow {e : ℕ} (he : e ≠ 0) (n : ℕ) : n < (iroot e n + 1) ^ e := by
  by_contra hle
  have := le_iroot he (not_lt.mp hle)
  omega

/-! ### From a composite `n` to the witness -/

/-- **The existence step of Theorem 5.1.3.**  If `n > 1` is composite and has no divisor
in `[2, ⌊n^{1/3}⌋]`, then some `k ≤ ⌊n^{1/3}⌋ + 1` and some `a` in the range scanned for
that `k` have `a² - 4kn` a perfect square.

Following the book: `n = p q` with `n^{1/3} < p ≤ q`; `lehman_approx` gives `u, v` with
`k = u v < n^{1/3} + 1` and `b = |u q - v p| < n^{1/3}`; then `a = u q + v p` has
`a² - 4kn = b²`, and `a - ⌈2√(kn)⌉ ≤ b² / (4√(kn)) < n^{1/6} / (4√k)`. -/
theorem lehmanWitness_of_composite {n : ℕ} (hn : 1 < n) (hnp : ¬n.Prime)
    (hno : ∀ d, 2 ≤ d → d ≤ iroot 3 n → ¬d ∣ n) : LehmanWitness n := by
  unfold LehmanWitness
  have hc : n < (iroot 3 n + 1) ^ 3 := lt_iroot_succ_pow (by norm_num) n
  have hr : n < (iroot 6 n + 1) ^ 6 := lt_iroot_succ_pow (by norm_num) n
  generalize iroot 3 n = c at hno hc ⊢
  generalize iroot 6 n = r6 at hr ⊢
  -- `n = p q` with `c < p ≤ q`
  have hpp := Nat.minFac_prime (by omega : n ≠ 1)
  obtain ⟨q, hnpq⟩ := Nat.minFac_dvd n
  set p := n.minFac with hp_def
  have hcp : c < p := by
    by_contra hle
    exact hno p hpp.two_le (not_lt.mp hle) (Nat.minFac_dvd n)
  have hpq : p ≤ q := by
    have h₁ := Nat.minFac_sq_le_self (by omega) hnp
    rw [sq, ← hp_def] at h₁
    by_contra hlt
    have : p * q < p * p := Nat.mul_lt_mul_of_pos_left (by omega) hpp.pos
    omega
  -- the real cube root `t` of `n`
  set t : ℝ := (n : ℝ) ^ (((3 : ℕ) : ℝ)⁻¹) with ht_def
  have ht3 : t ^ 3 = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ht0 : 0 < t := Real.rpow_pos_of_pos hn0 _
  have htc : t < (c : ℝ) + 1 := by
    by_contra hle
    have h₁ : ((c : ℝ) + 1) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by positivity) (not_lt.mp hle) 3
    rw [ht3] at h₁
    have : (c + 1) ^ 3 ≤ n := by exact_mod_cast h₁
    omega
  have htp : t < p := by
    have : (c : ℝ) + 1 ≤ p := by exact_mod_cast hcp
    linarith
  obtain ⟨u, v, hu, hv, hprod, hdiff⟩ := lehman_approx hpp.pos hpq ht0
    (by rw [ht3, hnpq]; push_cast; ring) htp
  -- `k = u v ≤ c + 1`
  have hk1 : 1 ≤ u * v := Nat.mul_pos hu hv
  have hkc : u * v ≤ c + 1 := by
    by_contra hgt
    have : ((c + 2 : ℕ) : ℝ) ≤ ((u * v : ℕ) : ℝ) := by exact_mod_cast (by omega : c + 2 ≤ u * v)
    push_cast at this hprod
    linarith
  -- `b = |u q - v p| < t`
  set b := ((u : ℤ) * q - v * p).natAbs with hb_def
  have hbR : (b : ℝ) = |(u : ℝ) * q - v * p| := by
    have h := Int.natCast_natAbs ((u : ℤ) * q - v * p)
    have h' : ((b : ℤ) : ℝ) = ((|(u : ℤ) * q - v * p| : ℤ) : ℝ) := by rw [← h]
    push_cast at h'
    exact h'
  have hbt : (b : ℝ) < t := hbR ▸ hdiff
  -- `a = u q + v p` has `a² = 4kn + b²`
  have hid : (u * q + v * p) * (u * q + v * p) = 4 * (u * v) * n + b * b := by
    have hb2 : ((b : ℤ) * b) = ((u : ℤ) * q - v * p) * ((u : ℤ) * q - v * p) :=
      Int.natAbs_mul_self' _
    zify
    rw [hb2, hnpq]
    push_cast
    ring
  set a := u * q + v * p with ha_def
  set k := u * v with hk_def
  have ha₀ : ceilSqrt (4 * k * n) ≤ a := ceilSqrt_le (by omega)
  have hs1 : 1 ≤ Nat.sqrt k := Nat.le_sqrt.mpr (by omega)
  have hs2 : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
  obtain ⟨E, hE⟩ : ∃ E, a = ceilSqrt (4 * k * n) + E := ⟨a - ceilSqrt (4 * k * n), by omega⟩
  have hceil := le_ceilSqrt_mul_self (4 * k * n)
  generalize ha₀def : ceilSqrt (4 * k * n) = a₀ at ha₀ hE hceil
  -- `2 E a₀ ≤ b²`
  have h2E : 2 * E * a₀ ≤ b * b := by
    rw [hE] at hid
    nlinarith
  -- `(4 s E)² n ≤ b⁴`
  have hnat : (4 * Nat.sqrt k * E) ^ 2 * n ≤ (b * b) ^ 2 := by
    calc (4 * Nat.sqrt k * E) ^ 2 * n
        = 4 * E ^ 2 * (4 * (Nat.sqrt k * Nat.sqrt k) * n) := by ring
      _ ≤ 4 * E ^ 2 * (4 * k * n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs2))
      _ ≤ 4 * E ^ 2 * (a₀ * a₀) := Nat.mul_le_mul_left _ hceil
      _ = (2 * E * a₀) ^ 2 := by ring
      _ ≤ (b * b) ^ 2 := Nat.pow_le_pow_left h2E 2
  -- in the reals: `b⁴ < t⁴ = t n`, hence `(4 s E)² < t` and `(4 s E)⁶ < n`
  have hlt6 : (4 * Nat.sqrt k * E) ^ 6 < n := by
    have hb4 : ((b : ℝ) * b) ^ 2 < t * n := by
      have h₁ : (b : ℝ) ^ 4 < t ^ 4 := pow_lt_pow_left₀ hbt (Nat.cast_nonneg b) (by norm_num)
      have h₂ : t ^ 4 = t * n := by rw [← ht3]; ring
      calc ((b : ℝ) * b) ^ 2 = (b : ℝ) ^ 4 := by ring
        _ < t ^ 4 := h₁
        _ = t * n := h₂
    have hreal : ((4 * Nat.sqrt k * E : ℕ) : ℝ) ^ 2 * n ≤ ((b : ℝ) * b) ^ 2 := by
      exact_mod_cast hnat
    have hsq : ((4 * Nat.sqrt k * E : ℕ) : ℝ) ^ 2 < t := by
      have := lt_of_le_of_lt hreal hb4
      exact lt_of_mul_lt_mul_right this hn0.le
    have h6 : (((4 * Nat.sqrt k * E : ℕ) : ℝ) ^ 2) ^ 3 < t ^ 3 :=
      pow_lt_pow_left₀ hsq (by positivity) (by norm_num)
    rw [ht3, ← pow_mul] at h6
    exact_mod_cast h6
  have hlt : 4 * Nat.sqrt k * E < r6 + 1 :=
    lt_of_pow_lt_pow_left₀ 6 (Nat.zero_le _) (hlt6.trans hr)
  have hEle : E ≤ r6 / (4 * Nat.sqrt k) := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    rw [mul_comm]
    omega
  exact ⟨k, a, b, hk1, hkc, by rw [ha₀def]; exact ha₀, by rw [ha₀def]; omega,
    by rw [hid, Nat.add_sub_cancel_left]⟩

/-- **Theorem 5.1.3, completeness of the Lehman method**: if Algorithm 5.1.2 returns
nothing then `n > 1` is prime.  (Unconditional; `k` runs to `⌊n^{1/3}⌋ + 1`, see `lehman`.) -/
theorem theorem_5_1_3_complete {n : ℕ} (hn : 1 < n) (h : lehman n = none) : n.Prime :=
  lehman_none_prime (fun hnp hno ↦ lehmanWitness_of_composite hn hnp hno) h

/-- **Running time of Algorithm 5.1.2, in closed form**: step [Loop] makes at most
`4 n^{1/3} + 2` passes — the book's `O(n^{1/3})`. -/
theorem lehmanPassBound_le_cuberoot {n : ℕ} (hn : 1 ≤ n) :
    (lehmanPassBound (iroot 6 n) 1 (iroot 3 n + 1) : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 3 : ℝ) + 2 := by
  have hc3 : iroot 3 n ^ 3 ≤ n := iroot_pow_le (by norm_num) n
  have hr6 : iroot 6 n ^ 6 ≤ n := iroot_pow_le (by norm_num) n
  have h := lehmanPassBound_le_closed (iroot 6 n) (iroot 3 n + 1)
  generalize iroot 3 n = c at hc3 h
  generalize iroot 6 n = r6 at hr6 h
  rw [show (1 / 3 : ℝ) = (((3 : ℕ) : ℝ)⁻¹) by norm_num]
  set x : ℝ := (n : ℝ) ^ (((3 : ℕ) : ℝ)⁻¹) with hx_def
  have hx3 : x ^ 3 = n := Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by norm_num)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 < x := Real.rpow_pos_of_pos (by linarith) _
  have hx1 : 1 ≤ x := by
    by_contra hlt
    have : x ^ 3 < 1 := pow_lt_one₀ hx0.le (by linarith) (by norm_num)
    linarith
  have hcR : (c : ℝ) ^ 3 ≤ x ^ 3 := by rw [hx3]; exact_mod_cast hc3
  have hrR : (r6 : ℝ) ^ 6 ≤ x ^ 3 := by rw [hx3]; exact_mod_cast hr6
  -- `c ≤ x`, `r6 ≤ x` and `r6 √c ≤ x`
  have hc : (c : ℝ) ≤ x := le_of_pow_le_pow_left₀ (by norm_num) hx0.le hcR
  have hr : (r6 : ℝ) ≤ x := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) hx0.le (hrR.trans ?_)
    calc x ^ 3 = x ^ 3 * 1 := by ring
      _ ≤ x ^ 3 * x ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hx1) (by positivity)
      _ = x ^ 6 := by ring
  have hsc : Real.sqrt c ^ 2 = c := Real.sq_sqrt (Nat.cast_nonneg c)
  have hrc : (r6 : ℝ) * Real.sqrt c ≤ x := by
    refine le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) hx0.le ?_
    calc ((r6 : ℝ) * Real.sqrt c) ^ 6 = (r6 : ℝ) ^ 6 * (Real.sqrt c ^ 2) ^ 3 := by ring
      _ = (r6 : ℝ) ^ 6 * (c : ℝ) ^ 3 := by rw [hsc]
      _ ≤ x ^ 3 * x ^ 3 := mul_le_mul hrR hcR (by positivity) (by positivity)
      _ = x ^ 6 := by ring
  -- `√(c + 1) ≤ √c + 1`
  have hsqrt : Real.sqrt ((c + 1 : ℕ) : ℝ) ≤ Real.sqrt c + 1 := by
    rw [show Real.sqrt c + 1 = Real.sqrt ((Real.sqrt c + 1) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    nlinarith [Real.sqrt_nonneg (c : ℝ)]
  have hr0 : (0 : ℝ) ≤ r6 := Nat.cast_nonneg r6
  have hmul : (r6 : ℝ) * Real.sqrt ((c + 1 : ℕ) : ℝ) ≤ r6 * (Real.sqrt c + 1) :=
    mul_le_mul_of_nonneg_left hsqrt hr0
  push_cast at h hmul ⊢
  linarith

/-! ## Bit operations -/

section BitCost

open PrimeNumbers.Chapter9 PrimeNumbers.Chapter2

/-- The cost charged for `⌈√m⌉`: a square root and a squaring. -/
theorem ceilSqrt_counted_cost (C : CostModel) (m : ℕ) :
    costOf C (ceilSqrt m) = costOf C (Nat.sqrt m) + C.mul (Nat.sqrt m).size (Nat.sqrt m).size := by
  cost_unfold ceilSqrt.counted

section Bounds

/-! The bounds assume bounds on the primitive operations — multiplications `≤ M`, integer
square roots `≤ S`, divisions `≤ D`, on numbers up to `A` (square roots of numbers up to
`A²`) — and the final gcd `≤ G`; which operations the loops perform is read off the code. -/

variable (C : CostModel) {n A M S D G : ℕ}
  (hM : ∀ a b, a ≤ A → b ≤ A → C.mul a.size b.size ≤ M)
  (hS : ∀ t, t ≤ A * A → costOf C (Nat.sqrt t) ≤ S)
  (hG : ∀ a b, a ≤ A → b ≤ A → costOf C (Nat.gcd (a + b) n) ≤ G)

include hM hS hG in
/-- The inner loop costs at most `3M + S` per pass (at most `fuel` passes: the squaring
`a²`, the product `4k · n`, the square root `b` and the check `b²`), plus the final gcd if
it succeeds. -/
theorem lehmanInnerCost_le {k : ℕ} (h4k : 4 * k ≤ A) (hn : n ≤ A)
    (a fuel : ℕ) (h : a + fuel ≤ A + 1) :
    costOf C (lehmanInner n k a fuel) ≤
      fuel * (3 * M + S) + if (lehmanInner n k a fuel).isSome then G else 0 := by
  induction fuel generalizing a with
  | zero => cost_unfold lehmanInner.counted
  | succ fuel ih =>
    have haA : a ≤ A := by omega
    have hb : Nat.sqrt (a * a - 4 * k * n) ≤ a := by
      have := Nat.sqrt_le_sqrt (Nat.sub_le (a * a) (4 * k * n))
      rwa [Nat.sqrt_eq] at this
    have h₁ := hM a a haA haA
    have h₂ := hM (4 * k) n h4k hn
    have h₃ := hM _ _ (hb.trans haA) (hb.trans haA)
    have h₄ := hS (a * a - 4 * k * n) ((Nat.sub_le _ _).trans (Nat.mul_le_mul haA haA))
    have ih := ih (a + 1) (by omega)
    have hgcd := hG a _ haA (hb.trans haA)
    cost_unfold lehmanInner.counted
    simp only [lehmanInner]
    split_ifs at ih ⊢ <;> (try simp only [Option.isSome_some, not_true_eq_false] at *) <;>
      nlinarith

include hM hS hG in
/-- **Bit complexity of step [Loop] of the Lehman method**, for any cost model: at most
`3M + S` per pass, with the passes bounded by `lehmanPassBound`; `2M + 2S + D` per value of
`k` (the product `4k · n`, `⌈√(4kn)⌉`, `⌊√k⌋` and one division); and the final gcd. -/
theorem lehmanCost_le {r6 : ℕ}
    (hD : ∀ a b, a ≤ A → b ≤ A → C.divMod a.size b.size ≤ D) (hr6 : r6 ≤ A) (hn : n ≤ A)
    (k fuel : ℕ)
    (hA : ∀ k', k ≤ k' → k' < k + fuel →
      ceilSqrt (4 * k' * n) + (r6 / (4 * Nat.sqrt k') + 2) ≤ A + 1 ∧ 4 * k' * n ≤ A ∧
        4 * k' ≤ A) :
    costOf C (lehmanOuter n r6 k fuel) ≤
      lehmanPassBound r6 k fuel * (3 * M + S) + fuel * (2 * M + 2 * S + D) + G := by
  induction fuel generalizing k with
  | zero => cost_unfold lehmanOuter.counted
  | succ fuel ih =>
    obtain ⟨hk₁, hk₂, hk₃⟩ := hA k le_rfl (by omega)
    have h₁ := lehmanInnerCost_le C hM hS hG hk₃ hn
      (ceilSqrt (4 * k * n)) (r6 / (4 * Nat.sqrt k) + 2) hk₁
    have h₂ := ih (k + 1) (fun k' hk₁ hk₂ ↦ hA k' (by omega) (by omega))
    -- the work for this `k`
    have hs : Nat.sqrt (4 * k * n) ≤ A := (Nat.sqrt_le_self _).trans hk₂
    have hsk : 4 * Nat.sqrt k ≤ A := by have := Nat.sqrt_le_self k; omega
    have e₁ := hM (4 * k) n hk₃ hn
    have e₂ := hS (4 * k * n) (hk₂.trans (Nat.le_mul_self A))
    have e₃ := hM _ _ hs hs
    have e₄ := hS k ((show k ≤ A by omega).trans (Nat.le_mul_self A))
    have e₅ := hD r6 (4 * Nat.sqrt k) hr6 hsk
    have hceil := ceilSqrt_counted_cost C (4 * k * n)
    cost_unfold lehmanOuter.counted
    rw [lehmanPassBound_succ]
    rcases hm : lehmanInner n k (ceilSqrt (4 * k * n)) (r6 / (4 * Nat.sqrt k) + 2) with _ | d
    · simp only [hm, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero] at h₁ ⊢
      cost_simp
      nlinarith
    · simp only [hm, Option.isSome_some, ↓reduceIte] at h₁ ⊢
      cost_simp
      nlinarith

end Bounds

/-- **Bit complexity of the Lehman method, grammar-school arithmetic**, with integer square
roots by Algorithm 9.2.11.  With `A = 4 (⌊n^{1/3}⌋ + 1) n + n + 2` of `K` bits
(`K ≈ (4/3) log₂ n`), step [Loop] costs at most
`(4 n^{1/3} + 2) · (3K² + schoolSqrt (2K)) + (n^{1/3} + 1) · (2K² + 2 schoolSqrt (2K) +
(K + 1) K) + (K + 1)(3K + 5)` bit operations: `O(n^{1/3} ln³ n)`. -/
theorem lehmanCost_school_le {n : ℕ} (hn : 1 ≤ n) :
    let K := (4 * (iroot 3 n + 1) * n + n + 2).size
    (costOf school (lehmanOuter n (iroot 6 n) 1 (iroot 3 n + 1)) : ℝ) ≤
      (4 * (n : ℝ) ^ (1 / 3 : ℝ) + 2) * (3 * (K * K) + schoolSqrt (2 * K) : ℕ) +
        ((n : ℝ) ^ (1 / 3 : ℝ) + 1) *
          (2 * (K * K) + 2 * schoolSqrt (2 * K) + (K + 1) * K : ℕ) +
        ((K + 1) * (3 * K + 5) : ℕ) := by
  intro K
  set A := 4 * (iroot 3 n + 1) * n + n + 2 with hAdef
  have hr6 : iroot 6 n ≤ n :=
    (Nat.le_self_pow (by norm_num) _).trans (iroot_pow_le (by norm_num) n)
  have hc3 : iroot 3 n ≤ n :=
    (Nat.le_self_pow (by norm_num) _).trans (iroot_pow_le (by norm_num) n)
  have hsz : ∀ x ≤ A, x.size ≤ K := fun x hx ↦ Nat.size_le_size hx
  have hkn : ∀ k', k' < 1 + (iroot 3 n + 1) → 4 * k' * n ≤ 4 * (iroot 3 n + 1) * n :=
    fun k' hk ↦ Nat.mul_le_mul_right n (Nat.mul_le_mul_left 4 (by omega))
  have hcost := lehmanCost_le school (A := A) (n := n) (r6 := iroot 6 n)
    (M := K * K) (S := schoolSqrt (2 * K)) (D := (K + 1) * K) (G := (K + 1) * (3 * K + 5))
    (fun a b ha hb ↦ Nat.mul_le_mul (hsz a ha) (hsz b hb))
    (fun t ht ↦ (sqrt_counted_cost_school_le t).trans (schoolSqrt_mono (by
      have := Nat.size_le_size ht
      have := size_mul_le A A
      have hK : A.size = K := rfl
      omega)))
    (fun a b ha hb ↦ by
      rw [gcd_counted_cost]
      refine (euclidBitCost_school_le_of_le (N := 2 * A) (by omega) (by omega)).trans ?_
      have : (2 * A).size ≤ K + 1 := by
        rw [show K = A.size from rfl, Nat.size_le, pow_succ]
        have := Nat.lt_size_self A
        omega
      nlinarith)
    (fun a b ha hb ↦ (Nat.mul_le_mul (by have := hsz a ha; omega) (hsz b hb) :
      (a.size - b.size + 1) * b.size ≤ _))
    (by omega) (by omega) 1 (iroot 3 n + 1)
    (fun k' hk₁ hk₂ ↦ by
      have h₁ : ceilSqrt (4 * k' * n) ≤ 4 * k' * n := ceilSqrt_le (Nat.le_mul_self _)
      have h₂ := hkn k' hk₂
      have h₃ : iroot 6 n / (4 * Nat.sqrt k') ≤ iroot 6 n := Nat.div_le_self _ _
      refine ⟨by omega, by omega, by nlinarith⟩)
  have hpasses := lehmanPassBound_le_cuberoot hn
  have hc : (iroot 3 n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h3 : (iroot 3 n : ℝ) ^ (3 : ℕ) ≤ n := by exact_mod_cast iroot_pow_le (by norm_num) n
    rw [show (1 / 3 : ℝ) = (((3 : ℕ) : ℝ)⁻¹) by norm_num]
    exact (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)).mpr
      (by exact_mod_cast h3)
  have hcost' : (costOf school (lehmanOuter n (iroot 6 n) 1 (iroot 3 n + 1)) : ℝ) ≤
      (lehmanPassBound (iroot 6 n) 1 (iroot 3 n + 1) : ℝ) *
          (3 * (K * K) + schoolSqrt (2 * K) : ℕ) +
        ((iroot 3 n + 1 : ℕ) : ℝ) * (2 * (K * K) + 2 * schoolSqrt (2 * K) + (K + 1) * K : ℕ) +
        ((K + 1) * (3 * K + 5) : ℕ) := by
    exact_mod_cast hcost
  have hW0 : (0 : ℝ) ≤ ((3 * (K * K) + schoolSqrt (2 * K) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hV0 : (0 : ℝ) ≤ ((2 * (K * K) + 2 * schoolSqrt (2 * K) + (K + 1) * K : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  refine hcost'.trans ?_
  push_cast [Nat.cast_add] at hc ⊢
  gcongr

end BitCost

end PrimeNumbers.Chapter5
