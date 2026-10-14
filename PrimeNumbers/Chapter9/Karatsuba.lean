import PrimeNumbers.Chapter9.BitCost

/-!
# §9.5.1 Karatsuba multiplication, and a sub-quadratic cost model

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 9.5.1.

Karatsuba's method multiplies two `2h`-bit numbers `x = a 2^h + b`, `y = c 2^h + d` with
three `h`-bit multiplications: `ac`, `bd` and `(a - b)(c - d)`, using
`ad + bc = ac + bd - (a - b)(c - d)`.  (This "subtractive" form keeps all three factors
below `2^h`, so the recursion stays on powers of two.)

* `karatsuba` — the recursive algorithm on numbers below `2^(2^j)`; `karatsuba_eq` proves
  it computes `x y`.
* `karatsubaCost` — its bit-operation count: three half-size products plus `c · 2^j` bit
  operations of additions, subtractions and shifts at each level;
  `karatsubaCost_le` proves `karatsubaCost j ≤ (2c + 1) · 3^j`, i.e. `O(N^(log₂ 3))` for
  `N = 2^j`-bit inputs.
* `karatsubaModel` — a `CostModel` whose multiplication cost is that bound, so every
  general running-time theorem of the project (`powModCost_le`, `pollardRhoCost_le`, …)
  now also holds with Karatsuba multiplication.  Division in this model is still
  grammar-school; fast division (Newton reciprocation, §9.2.2) is not yet formalized.

The faster methods of §9.5 — Toom–Cook (Algorithms 9.5.1–9.5.2), FFT multiplication
(Algorithm 9.5.12), Schönhage's method (Algorithm 9.5.23), Nussbaumer convolution
(Algorithm 9.5.25) — are the next candidates for cost models.
-/

namespace PrimeNumbers.Chapter9

/-- `|a - b|` on naturals. -/
def natDist (a b : ℕ) : ℕ := if b ≤ a then a - b else b - a

/-- **Karatsuba multiplication** of `x, y < 2^(2^j)`. -/
def karatsuba : ℕ → ℕ → ℕ → ℕ
  | 0, x, y => x * y
  | j + 1, x, y =>
    let h := 2 ^ j
    let a := x / 2 ^ h
    let b := x % 2 ^ h
    let c := y / 2 ^ h
    let d := y % 2 ^ h
    let p₁ := karatsuba j a c
    let p₂ := karatsuba j b d
    let p₃ := karatsuba j (natDist a b) (natDist c d)
    -- `ad + bc = ac + bd - (a - b)(c - d)`, the sign of `(a - b)(c - d)` decided by comparisons
    let mid := if (b ≤ a ↔ d ≤ c) then p₁ + p₂ - p₃ else p₁ + p₂ + p₃
    (p₁ <<< (2 * h)) + (mid <<< h) + p₂

theorem natDist_lt {a b n : ℕ} (ha : a < n) (hb : b < n) : natDist a b < n := by
  unfold natDist; split_ifs <;> omega

/-- The middle coefficient: `ac + bd ∓ |a - b| |c - d| = ad + bc`. -/
theorem karatsuba_mid (a b c d : ℕ) :
    (if (b ≤ a ↔ d ≤ c) then a * c + b * d - natDist a b * natDist c d
      else a * c + b * d + natDist a b * natDist c d) = a * d + b * c := by
  unfold natDist
  by_cases hab : b ≤ a <;> by_cases hcd : d ≤ c <;> simp only [hab, hcd, iff_true,
    iff_false, not_true_eq_false, ↓reduceIte]
  · have : (a - b) * (c - d) + (a * d + b * c) = a * c + b * d := by
      zify [hab, hcd]; ring
    omega
  · have : a * c + b * d + (a - b) * (d - c) = a * d + b * c := by
      zify [hab, (by omega : c ≤ d)]; ring
    exact this
  · have : a * c + b * d + (b - a) * (c - d) = a * d + b * c := by
      zify [(by omega : a ≤ b), hcd]; ring
    exact this
  · have : (b - a) * (d - c) + (a * d + b * c) = a * c + b * d := by
      zify [(by omega : a ≤ b), (by omega : c ≤ d)]; ring
    omega

/-- **Correctness of Karatsuba multiplication.** -/
theorem karatsuba_eq (j : ℕ) {x y : ℕ} (hx : x < 2 ^ 2 ^ j) (hy : y < 2 ^ 2 ^ j) :
    karatsuba j x y = x * y := by
  induction j generalizing x y with
  | zero => rfl
  | succ j ih =>
    have hh : 2 ^ 2 ^ (j + 1) = 2 ^ 2 ^ j * 2 ^ 2 ^ j := by rw [pow_succ, pow_mul, sq]
    have hpos : 0 < 2 ^ 2 ^ j := by positivity
    have ha : x / 2 ^ 2 ^ j < 2 ^ 2 ^ j := (Nat.div_lt_iff_lt_mul hpos).mpr (hh ▸ hx)
    have hc : y / 2 ^ 2 ^ j < 2 ^ 2 ^ j := (Nat.div_lt_iff_lt_mul hpos).mpr (hh ▸ hy)
    have hb : x % 2 ^ 2 ^ j < 2 ^ 2 ^ j := Nat.mod_lt _ hpos
    have hd : y % 2 ^ 2 ^ j < 2 ^ 2 ^ j := Nat.mod_lt _ hpos
    simp only [karatsuba, ih ha hc, ih hb hd, ih (natDist_lt ha hb) (natDist_lt hc hd),
      karatsuba_mid, Nat.shiftLeft_eq]
    conv_rhs => rw [← Nat.div_add_mod x (2 ^ 2 ^ j), ← Nat.div_add_mod y (2 ^ 2 ^ j)]
    rw [show 2 ^ (2 * 2 ^ j) = 2 ^ 2 ^ j * 2 ^ 2 ^ j by rw [two_mul, pow_add]]
    ring

/-! ## Running time -/

/-- The bit operations of `karatsuba j`: one bit product at the bottom; three half-size
products and `c · 2^j` bit operations of linear work (splitting, comparisons,
subtractions, shifts and additions) at level `j`. -/
def karatsubaCost (c : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => 3 * karatsubaCost c j + c * 2 ^ (j + 1)

/-- **Karatsuba is `O(N^(log₂ 3))`**: `karatsubaCost c j ≤ (2c + 1) 3^j - 2c 2^j`. -/
theorem karatsubaCost_le (c j : ℕ) :
    karatsubaCost c j + 2 * c * 2 ^ j ≤ (2 * c + 1) * 3 ^ j := by
  induction j with
  | zero => simp [karatsubaCost]; omega
  | succ j ih =>
    simp only [karatsubaCost, pow_succ]
    nlinarith

theorem karatsubaCost_mono (c : ℕ) : Monotone (karatsubaCost c) := by
  refine monotone_nat_of_le_succ fun j ↦ ?_
  simp only [karatsubaCost]
  have : karatsubaCost c j ≤ 3 * karatsubaCost c j := by omega
  omega

/-- **A sub-quadratic cost model**: multiplying numbers of at most `a` and `b` bits is
charged as Karatsuba multiplication at the next power of two `2^⌈log₂ max a b⌉`, with `c`
bit operations of linear work per bit per level (`c = 16` is ample).  Division is charged
as in the grammar-school model. -/
def karatsubaModel (c : ℕ) : CostModel where
  mul a b := karatsubaCost c (Nat.clog 2 (max a b))
  divMod a b := (a - b + 1) * b
  mul_mono h₁ h₂ := karatsubaCost_mono c (Nat.clog_mono_right 2 (max_le_max h₁ h₂))
  divMod_mono b h := Nat.mul_le_mul_right b (by omega)

/-- In the Karatsuba model, multiplying two `k`-bit numbers costs at most
`(2c + 1) · 3^⌈log₂ k⌉ ≤ 3 (2c + 1) k^(log₂ 3)`. -/
theorem karatsubaModel_mul_le (c k : ℕ) :
    (karatsubaModel c).mul k k ≤ (2 * c + 1) * 3 ^ Nat.clog 2 k := by
  have := karatsubaCost_le c (Nat.clog 2 k)
  simp only [karatsubaModel, max_self]
  omega

end PrimeNumbers.Chapter9
