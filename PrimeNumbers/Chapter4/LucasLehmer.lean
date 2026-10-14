import PrimeNumbers.Chapter9.CountedDef
import PrimeNumbers.Chapter9.BitCost
import Mathlib

/-!
# §4.2 The `n + 1` test: Lucas–Lehmer

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 4.2.

* `lucasLehmer`     — Algorithm 4.2.7 (Lucas–Lehmer test for Mersenne primes).
* `lucasLehmer_iff` — Theorem 4.2.6 for this very function: it returns `true` exactly
                      when `2^p - 1` is prime.  The number theory is Mathlib's
                      (`lucas_lehmer_sufficiency`, `lucas_lehmer_necessity`); what is proved
                      here is that the loop below computes Mathlib's sequence `sMod`.

Not formalized: the general Lucas-sequence `n + 1` tests (Theorems 4.2.2–4.2.5,
4.2.8–4.2.10) and Algorithm 4.2.11 (divisors in residue classes).
-/

namespace PrimeNumbers.Chapter4

open LucasLehmer

/-- **Algorithm 4.2.7, step 2 [Compute Lucas–Lehmer sequence]** (`k` passes remaining):
```
v = (v² - 2) mod (2^p - 1);
```
with `M = 2^p - 1`.  On naturals, `v² - 2` is computed as `v² + M - 2`. -/
counted_def lucasLehmerLoop (M v : ℕ) : ℕ → ℕ
  | 0 => v
  | k + 1 => lucasLehmerLoop M ((v * v + M - 2) % M) k

/-- **Algorithm 4.2.7 (Lucas–Lehmer test for Mersenne primes).**  Given an odd prime `p`,
decides whether `2^p - 1` is prime.
```
v = 4;
for (k ∈ [1, p - 2]) v = (v² - 2) mod (2^p - 1);
if (v == 0) return YES;
return NO;
```
-/
counted_def lucasLehmer (p : ℕ) : Bool :=
  lucasLehmerLoop (2 ^ p - 1) 4 (p - 2) = 0

/-- The loop computes Mathlib's Lucas–Lehmer sequence `sMod p`. -/
theorem lucasLehmerLoop_eq {p : ℕ} (hp : 3 ≤ p) (k i v : ℕ) (hv : (v : ℤ) = sMod p i) :
    (lucasLehmerLoop (2 ^ p - 1) v k : ℤ) = sMod p (i + k) := by
  have h8 : 2 ^ 3 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  have hM : ((2 ^ p - 1 : ℕ) : ℤ) = 2 ^ p - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  induction k generalizing i v with
  | zero => simpa [lucasLehmerLoop] using hv
  | succ k ih =>
    rw [lucasLehmerLoop, ih (i + 1) _ ?_, add_right_comm, add_assoc]
    rw [sMod, ← hv, Int.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul, hM]
    rw [show (v : ℤ) * v + (2 ^ p - 1) - ((2 : ℕ) : ℤ) = (v : ℤ) ^ 2 - 2 + (2 ^ p - 1) by
      push_cast; ring, Int.add_emod_right]

/-- **Theorem 4.2.6 (Lucas–Lehmer test for Mersenne primes), for Algorithm 4.2.7.**
For `p ≥ 3` (in particular for every odd prime `p`), `lucasLehmer p` returns `true` if
and only if `M_p = 2^p - 1` is prime. -/
theorem lucasLehmer_iff {p : ℕ} (hp : 3 ≤ p) : lucasLehmer p = true ↔ (2 ^ p - 1).Prime := by
  have h8 : 2 ^ 3 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  -- the starting value: `sMod p 0 = 4 mod M = 4`
  have h4 : ((4 : ℕ) : ℤ) = sMod p 0 := by
    have : (4 : ℤ) < 2 ^ p - 1 := by
      have : ((2 ^ p : ℕ) : ℤ) = 2 ^ p := by norm_num
      omega
    rw [sMod, Int.emod_eq_of_lt (by norm_num) this]; rfl
  have hloop := lucasLehmerLoop_eq hp (p - 2) 0 4 h4
  rw [zero_add] at hloop
  have hres : lucasLehmer p = true ↔ LucasLehmerTest p := by
    rw [LucasLehmerTest, residue_eq_zero_iff_sMod_eq_zero p (by omega), ← hloop, lucasLehmer,
      decide_eq_true_iff]
    exact_mod_cast Iff.rfl
  rw [hres]
  exact ⟨lucas_lehmer_sufficiency p (by omega), lucas_lehmer_necessity p hp⟩

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-! ### Bit operations -/

theorem lucasLehmerCost_le (C : CostModel) {M v : ℕ} (hv : v < M) (k : ℕ) :
    costOf C (lucasLehmerLoop M v k) ≤ k * C.mulMod M.size := by
  induction k generalizing v with
  | zero => cost_unfold lucasLehmerLoop.counted; simp
  | succ k ih =>
    have ih := ih (v := (v * v + M - 2) % M) (Nat.mod_lt _ (by omega))
    -- `v² + M - 2 < M²`, so it has at most `2 size M` bits
    have hlt : v * v + M - 2 < M * M := by
      obtain ⟨c, rfl⟩ : ∃ c, M = c + 1 := ⟨M - 1, by omega⟩
      have h₁ : v * v ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
      have h₂ : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by ring
      omega
    have hsize : (v * v + M - 2).size ≤ 2 * M.size := by
      have := size_le_of_lt hlt
      have := size_mul_le M M
      omega
    have h₁ : C.mul v.size v.size ≤ C.mul M.size M.size :=
      C.mul_mono (size_le_of_lt hv) (size_le_of_lt hv)
    have h₂ := C.divMod_mono M.size hsize
    cost_unfold lucasLehmerLoop.counted
    simp only [add_mul, one_mul, CostModel.mulMod] at ih ⊢
    omega

/-- **Bit complexity of the Lucas–Lehmer test, grammar-school arithmetic**: deciding the
primality of `2^p - 1` takes at most `(p - 2)(2p² + p)` bit operations, i.e. `O(p³)`. -/
theorem lucasLehmerCost_school_le {p : ℕ} (hp : 3 ≤ p) :
    costOf school (lucasLehmerLoop (2 ^ p - 1) 4 (p - 2)) ≤ (p - 2) * (2 * p ^ 2 + p) := by
  have h8 : 2 ^ 3 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  refine (lucasLehmerCost_le school (by omega) (p - 2)).trans (Nat.mul_le_mul_left _ ?_)
  have hsize : (2 ^ p - 1).size ≤ p := Nat.size_le.mpr (by omega)
  rw [school_mulMod]
  nlinarith [Nat.pow_le_pow_left hsize 2]

end RunningTime

end PrimeNumbers.Chapter4
