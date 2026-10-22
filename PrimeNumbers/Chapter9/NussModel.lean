import PrimeNumbers.Chapter9.BitCost
import Mathlib.Data.Nat.Size
import Mathlib.Order.MinMax

/-!
# A quasi-linear cost model

`nussModel` charges `360000 N (log₂ N + 3)⁴` bit operations for a product of `N`-bit numbers.
Nussbaumer multiplication achieves it (`nussMul_cost_le`, in `NussbaumerCost.lean`); analyses
that only need the model (e.g. §5.5) import this file alone.
-/

namespace PrimeNumbers.Chapter9

/-- **A quasi-linear cost model**: multiplying numbers of at most `N` bits costs
`360000 N (log₂ N + 3)⁴` bit operations, which Nussbaumer multiplication achieves
(`nussMul_cost_le`); division and linear operations stay schoolbook. -/
def nussModel : CostModel where
  mul a b := 360000 * max a b * ((max a b).size + 3) ^ 4
  divMod a b := (a - b + 1) * b
  addRate := 1
  unit := 1
  mul_mono h₁ h₂ := by
    have h := max_le_max h₁ h₂
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h)
      (Nat.pow_le_pow_left (by have := Nat.size_le_size h; omega) _)
  divMod_mono b h := Nat.mul_le_mul_right b (by omega)

theorem nussModel_mul (a b : ℕ) :
    nussModel.mul a b = 360000 * max a b * ((max a b).size + 3) ^ 4 := rfl

end PrimeNumbers.Chapter9
