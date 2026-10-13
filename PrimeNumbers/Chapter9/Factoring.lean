import PrimeNumbers.Chapter9.BitCost
import PrimeNumbers.Chapter5.PollardRho
import PrimeNumbers.Chapter5.PollardPMinusOne

/-!
# Bit complexity of the factoring algorithms of Chapter 5

Using the cost model of `Chapter9/BitCost.lean`; `k` is the bit length of `n`.

* `pollardRhoCost_le` — for any cost model, `fuel` passes of Pollard rho (Algorithm 5.2.1)
  cost at most `fuel · (3 · mulMod + gcd)`: "3 modular multiplications and a gcd" per pass.
  `pollardRhoCost_school_le`: at most `fuel · (9k² + 4k)` bit operations.
  With `pollardRhoLoop_isSome` (`fuel = p` always suffices) this is a rigorous
  `O(p ln² n)`; the heuristic running time is `O(√p ln² n)`.
* `pm1Cost_le` — for any cost model, Pollard `p - 1` (Algorithm 5.4.1) with bound `B`
  costs at most `pm1Steps B` modular powers with exponents `≤ B`, plus one gcd, where
  `pm1Steps B = ∑_{p ≤ B} a_p ≤ π(B) log₂ B` (`pm1Steps_le`).
  `pm1Cost_school_le`: at most `pm1Steps B · (4 log₂ B + 1)(k + 1)² + k(3k + 1)`.

The cost of finding the primes up to `B` (step 1 of Algorithm 5.4.1) is not included.
-/

namespace PrimeNumbers.Chapter9

open PrimeNumbers.Chapter2 PrimeNumbers.Chapter5

/-! ## Pollard rho (Algorithm 5.2.1) -/

/-- The bit operations of one evaluation `F(x) = (x² + a) mod n`. -/
def rhoFCost (C : CostModel) (n a x : ℕ) : ℕ :=
  C.mul x.size x.size + C.divMod (x * x + a).size n.size

/-- The bit operations of `pollardRhoLoop n a U V fuel`: three evaluations of `F` and one
gcd per pass. -/
def pollardRhoCost (C : CostModel) (n a : ℕ) (U V : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
    let U' := rhoF n a U
    let V₁ := rhoF n a V
    let V' := rhoF n a V₁
    rhoFCost C n a U + rhoFCost C n a V + rhoFCost C n a V₁ +
      euclidBitCost C n (absDiff U' V') +
      if euclid n (absDiff U' V') = 1 then pollardRhoCost C n a U' V' fuel else 0

/-- One evaluation of `F` on a residue costs at most one modular multiplication. -/
theorem rhoFCost_le (C : CostModel) {n a x : ℕ} (ha : a < n) (hx : x < n) :
    rhoFCost C n a x ≤ C.mulMod n.size := by
  have hlt : x * x + a < n * n := by
    obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
    have h₁ : x * x ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
    have h₂ : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by ring
    omega
  have hsize : (x * x + a).size ≤ 2 * n.size := by
    have := size_le_of_lt hlt
    have := size_mul_le n n
    omega
  exact Nat.add_le_add (C.mul_mono (size_le_of_lt hx) (size_le_of_lt hx))
    (C.divMod_mono _ hsize)

theorem absDiff_lt {n u v : ℕ} (hu : u < n) (hv : v < n) : absDiff u v < n := by
  unfold absDiff; split_ifs <;> omega

/-- **Bit complexity of Pollard rho**, for any cost model: each pass costs at most three
modular multiplications and one gcd with `n` (bounded by `G`). -/
theorem pollardRhoCost_le (C : CostModel) {n a G : ℕ} (ha : a < n)
    (hG : ∀ d < n, euclidBitCost C n d ≤ G) {U V : ℕ} (hU : U < n) (hV : V < n) (fuel : ℕ) :
    pollardRhoCost C n a U V fuel ≤ fuel * (3 * C.mulMod n.size + G) := by
  have hn : 0 < n := by omega
  induction fuel generalizing U V with
  | zero => simp [pollardRhoCost]
  | succ fuel ih =>
    have hF : ∀ x, rhoF n a x < n := fun x ↦ Nat.mod_lt _ hn
    have h₁ := rhoFCost_le C ha hU
    have h₂ := rhoFCost_le C ha hV
    have h₃ := rhoFCost_le C ha (hF V)
    have h₄ := hG _ (absDiff_lt (hF U) (hF (rhoF n a V)))
    have ih := ih (hF U) (hF (rhoF n a V))
    simp only [pollardRhoCost, add_mul, one_mul]
    split_ifs <;> omega

/-- **Bit complexity of Pollard rho, grammar-school arithmetic**: at most `9k² + 4k` bit
operations per pass of [Factor search]. -/
theorem pollardRhoCost_school_le {n a U V : ℕ} (ha : a < n) (hU : U < n) (hV : V < n)
    (fuel : ℕ) :
    pollardRhoCost school n a U V fuel ≤ fuel * (9 * n.size ^ 2 + 4 * n.size) := by
  refine (pollardRhoCost_le school ha
    (fun d hd ↦ euclidBitCost_school_le' hd le_rfl) hU hV fuel).trans (le_of_eq ?_)
  rw [school_mulMod]
  ring

/-! ## Pollard `p - 1` (Algorithm 5.4.1) -/

/-- The bit operations of `ladder n p c j`: `j` modular powers with exponent `p`. -/
def ladderCost (C : CostModel) (n p : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => powModCost C c p n + ladderCost C n p (powMod c p n) j

/-- The bit operations of the power ladders over a list of primes. -/
def laddersCost (C : CostModel) (n B : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: L, c =>
    ladderCost C n p c (Nat.log p B) + laddersCost C n B L (ladder n p c (Nat.log p B))

/-- The bit operations of `pollardPMinusOne n B c` (steps 2 and 3). -/
def pm1Cost (C : CostModel) (n B c : ℕ) : ℕ :=
  laddersCost C n B (primesUpTo B) c + euclidBitCost C n ((ladders n B c + n - 1) % n)

/-- The number of modular powers in step 2: `∑_{p ≤ B} a_p`. -/
def pm1Steps (B : ℕ) : ℕ := ((primesUpTo B).map fun p ↦ Nat.log p B).sum

/-- `pm1Steps B ≤ π(B) · log₂ B`. -/
theorem pm1Steps_le (B : ℕ) : pm1Steps B ≤ (primesUpTo B).length * Nat.log 2 B := by
  have := List.sum_le_length_nsmul ((primesUpTo B).map fun p ↦ Nat.log p B) (Nat.log 2 B)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact Nat.log_anti_left (by norm_num) (mem_primesUpTo.mp hp).1.two_le)
  simpa [pm1Steps] using this

theorem ladder_lt {n p c : ℕ} (hc : c < n) (j : ℕ) : ladder n p c j < n := by
  induction j generalizing c with
  | zero => exact hc
  | succ j ih => exact ih (powMod_lt _ _ (by omega))

section

variable (C : CostModel) {n B : ℕ}

/-- The cost of one modular power with exponent at most `B`. -/
def powBound (C : CostModel) (n B : ℕ) : ℕ :=
  C.divMod n.size n.size + Nat.log 2 B * (2 * C.mulMod n.size)

theorem ladderCost_le {p c : ℕ} (hp : p ≤ B) (hc : c < n) (j : ℕ) :
    ladderCost C n p c j ≤ j * powBound C n B := by
  induction j generalizing c with
  | zero => simp [ladderCost]
  | succ j ih =>
    have h₁ : powModCost C c p n ≤ powBound C n B :=
      (powModCost_le C hc p).trans (Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (Nat.log_mono_right hp)) _)
    have ih := ih (c := powMod c p n) (powMod_lt _ _ (by omega))
    simp only [ladderCost, add_mul, one_mul]
    omega

theorem laddersCost_le (L : List ℕ) (hL : ∀ p ∈ L, p ≤ B) {c : ℕ} (hc : c < n) :
    laddersCost C n B L c ≤ (L.map fun p ↦ Nat.log p B).sum * powBound C n B := by
  induction L generalizing c with
  | nil => simp [laddersCost]
  | cons p L ih =>
    have h₁ := ladderCost_le C (hL p (by simp)) hc (Nat.log p B)
    have ih := ih (fun q hq ↦ hL q (by simp [hq])) (ladder_lt (p := p) hc (Nat.log p B))
    simp only [laddersCost, List.map_cons, List.sum_cons, add_mul]
    omega

/-- **Bit complexity of Pollard `p - 1`**, for any cost model: `pm1Steps B` modular powers
with exponents at most `B`, and one gcd with `n` (bounded by `G`). -/
theorem pm1Cost_le {G c : ℕ} (hG : ∀ d < n, euclidBitCost C n d ≤ G) (hc : c < n) :
    pm1Cost C n B c ≤ pm1Steps B * powBound C n B + G := by
  have h₁ := laddersCost_le C (primesUpTo B) (fun p hp ↦ (mem_primesUpTo.mp hp).2) hc
  have h₂ := hG _ (Nat.mod_lt (ladders n B c + n - 1) (by omega : 0 < n))
  simp only [pm1Cost, pm1Steps]
  omega

end

/-- **Bit complexity of Pollard `p - 1`, grammar-school arithmetic**: at most
`pm1Steps B · (4 log₂ B + 1)(k + 1)² + k(3k + 1)` bit operations. -/
theorem pm1Cost_school_le {n B c : ℕ} (hc : c < n) :
    pm1Cost school n B c ≤
      pm1Steps B * ((4 * Nat.log 2 B + 1) * (n.size + 1) ^ 2) + n.size * (3 * n.size + 1) := by
  refine (pm1Cost_le school (fun d hd ↦ euclidBitCost_school_le' hd le_rfl) hc).trans ?_
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
  rw [powBound, school_mulMod]
  have : school.divMod n.size n.size = n.size := by simp [school]
  rw [this]
  nlinarith [Nat.zero_le (Nat.log 2 B), Nat.zero_le n.size,
    Nat.zero_le (Nat.log 2 B * n.size)]

end PrimeNumbers.Chapter9
