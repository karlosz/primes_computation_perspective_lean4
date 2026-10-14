import PrimeNumbers.Chapter9.CountedDef

/-!
# Counted versions of library functions

Library functions that do big-number arithmetic are charged, when an algorithm written with
`counted_def` calls them, through a counted version.  Some are given in `Counted.lean` (list
combinators, `List.prod`, array writes); the ones here are written with `counted_def`
itself, mirroring the library's implementation, and proved equal to it.  Algorithm files
import this file (and through it `counted_def`).
-/

namespace PrimeNumbers.Chapter9

/-- `Nat.log.go`, Mathlib's implementation of `Nat.log` by repeated squaring of the base. -/
counted_def logGo (n : ℕ) : (b fuel : ℕ) → ℕ × ℕ
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then (n, 0)
    else
      match logGo n (b * b) fuel with
      | (q, e) => if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

theorem logGo_eq (n b fuel : ℕ) : logGo n b fuel = Nat.log.go n b fuel := by
  induction fuel generalizing b with
  | zero => rw [logGo, Nat.log.go]
  | succ fuel ih => rw [logGo, Nat.log.go, ih]

/-- `⌊log_b n⌋`, as Mathlib computes it. -/
counted_def ilog (b n : ℕ) : ℕ := if b ≤ 1 then 0 else (logGo n b n).2

theorem ilog_eq (b n : ℕ) : ilog b n = Nat.log b n := by
  rw [ilog, Nat.log, logGo_eq]

/-- A call of `Nat.log` in a `counted_def` is charged as Mathlib's implementation. -/
def _root_.Nat.log.counted {m : Type → Type} [Monad m] [NatArith m] (b n : ℕ) : m ℕ :=
  ilog.counted b n

theorem logGo_fst_le (n b fuel : ℕ) : (logGo n b fuel).1 ≤ n := by
  induction fuel generalizing b with
  | zero => simp [logGo]
  | succ fuel ih =>
    rw [logGo]
    split_ifs
    · exact le_rfl
    · have := ih (b * b)
      rcases h : logGo n (b * b) fuel with ⟨q, e⟩
      rw [h] at this
      simp only
      split_ifs
      · exact this
      · exact (Nat.div_le_self _ _).trans this

/-- Each level of `logGo` squares the base once and divides once, by numbers `≤ n` (each
such operation costing at most `W`); there are at most `k` levels when `n < b^(2^k)`. -/
theorem logGo_cost_le (C : CostModel) {n W : ℕ}
    (hW : ∀ a c, a ≤ n.size → c ≤ n.size → C.mul a c ≤ W ∧ C.divMod a c ≤ W) (fuel : ℕ) :
    ∀ (b k : ℕ), 2 ≤ b → n < b ^ 2 ^ k → costOf C (logGo n b fuel) ≤ k * (2 * W) := by
  induction fuel with
  | zero => intro b k _ _; cost_unfold logGo.counted
  | succ fuel ih =>
    intro b k hb hk
    by_cases hnb : n < b
    · cost_unfold logGo.counted
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hk; omega
        · omega⟩
      have ih := ih (b * b) k (by nlinarith)
        (by rw [← pow_two, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]; exact hk)
      have hq := logGo_fst_le n (b * b) fuel
      have hbn := Nat.size_le_size (not_lt.mp hnb)
      cost_unfold logGo.counted
      rcases h : logGo n (b * b) fuel with ⟨q, e⟩
      rw [h] at hq
      simp only at hq
      have hW₁ := (hW b.size b.size hbn hbn).1
      have hW₂ := (hW q.size b.size (Nat.size_le_size hq) hbn).2
      simp only [cost_simps]
      split_ifs <;> nlinarith

/-- The charge for `Nat.log b n` (`b ≥ 2`): at most `size n` levels, each a squaring and a
division of numbers `≤ n`. -/
theorem ilog_cost_le (C : CostModel) {b n W : ℕ} (hb : 2 ≤ b)
    (hW : ∀ a c, a ≤ n.size → c ≤ n.size → C.mul a c ≤ W ∧ C.divMod a c ≤ W) :
    costOf C (Nat.log b n) ≤ n.size * (2 * W) := by
  show CostM.cost C (ilog.counted b n) ≤ _
  cost_unfold ilog.counted
  refine logGo_cost_le C hW n b n.size hb ?_
  calc n < 2 ^ n.size := Nat.lt_size_self n
    _ ≤ b ^ n.size := Nat.pow_le_pow_left hb _
    _ ≤ b ^ 2 ^ n.size := Nat.pow_le_pow_right (by omega) (Nat.lt_two_pow_self).le

end PrimeNumbers.Chapter9
