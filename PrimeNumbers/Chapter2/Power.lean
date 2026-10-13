import Mathlib

/-!
# §2.1.2 Powers

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.1.2.

* `pow`     — Algorithm 2.1.5, the recursive powering algorithm in a semigroup;
              `pow_eq` shows `pow x n = x ^ n`.
* `powMod`  — the same algorithm for `x^n mod m`, with a modular reduction in each
              branch as the book prescribes; `powMod_eq` shows `powMod x n m = x^n % m`.
* `euler_2_2`, `fermat_little`, `inverse_2_3` — relations (2.2), (2.3).
-/

namespace PrimeNumbers.Chapter2

/-! ## Algorithm 2.1.5 (Recursive powering algorithm) -/

/-- **Algorithm 2.1.5.**  Given `x` in a semigroup and a positive integer `n`, compute `xⁿ`.
```
pow(x, n) {
  if (n == 1) return x;
  if (n even) return pow(x, n/2)^2;
  return x * pow(x, (n-1)/2)^2;
}
```
Only a multiplication is required of the type `M`.  (For the out-of-spec input `n = 0`
the function returns `x`.) -/
def pow {M : Type*} [Mul M] (x : M) (n : ℕ) : M :=
  if n ≤ 1 then x
  else if n % 2 = 0 then
    let y := pow x (n / 2)
    y * y                       -- Even branch.
  else
    let y := pow x ((n - 1) / 2)
    x * (y * y)                 -- Odd branch.
termination_by n
decreasing_by all_goals omega

/-- **Correctness of Algorithm 2.1.5**: `pow x n = xⁿ` for every positive `n`. -/
theorem pow_eq {M : Type*} [Monoid M] (x : M) {n : ℕ} (hn : 0 < n) : pow x n = x ^ n := by
  fun_induction pow x n with
  | case1 n h =>
    obtain rfl : n = 1 := by omega
    simp
  | case2 n h heven y ih =>
    have hn2 : n = n / 2 + n / 2 := by omega
    rw [show y = x ^ (n / 2) from ih (by omega), ← pow_add, ← hn2]
  | case3 n h hodd y ih =>
    have hn2 : n = ((n - 1) / 2 + (n - 1) / 2) + 1 := by omega
    rw [show y = x ^ ((n - 1) / 2) from ih (by omega), ← pow_add, ← pow_succ', ← hn2]

/-- Algorithm 2.1.5 respects any multiplicative relation `R` between the semigroup `M` it
runs in and a monoid `N`: if `x` is related to `x'` then `pow x n` is related to `x' ^ n`.
This is how powering in a *representation* (say, lists of coefficients reduced modulo `f`)
is shown to compute powers in the structure represented. -/
theorem pow_rel {M N : Type*} [Mul M] [Monoid N] (R : M → N → Prop)
    (hmul : ∀ a b a' b', R a a' → R b b' → R (a * b) (a' * b')) {x : M} {x' : N} (hx : R x x')
    {n : ℕ} (hn : 0 < n) : R (pow x n) (x' ^ n) := by
  fun_induction pow x n with
  | case1 n h =>
    obtain rfl : n = 1 := by omega
    simpa using hx
  | case2 n h heven y ih =>
    have hn2 : n = n / 2 + n / 2 := by omega
    rw [hn2, pow_add]
    exact hmul _ _ _ _ (ih (by omega)) (ih (by omega))
  | case3 n h hodd y ih =>
    have hn2 : n = ((n - 1) / 2 + (n - 1) / 2) + 1 := by omega
    rw [hn2, pow_succ', pow_add]
    exact hmul _ _ _ _ hx (hmul _ _ _ _ (ih (by omega)) (ih (by omega)))

/-- Algorithm 2.1.5 extended to the exponent `n = 0` when the semigroup has an identity.
This is the powering routine used by the later algorithms of the chapter. -/
def power {M : Type*} [Mul M] [One M] (x : M) (n : ℕ) : M :=
  if n = 0 then 1 else pow x n

@[simp]
theorem power_eq {M : Type*} [Monoid M] (x : M) (n : ℕ) : power x n = x ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [power]
  · simp [power, hn.ne', pow_eq x hn]

/-- **Algorithm 2.1.5 for `xⁿ mod m`**: "the required modular reductions are to occur for
each branch (even, odd) of the algorithm".  Extended to `n = 0` by `x⁰ = 1`. -/
def powMod (x n m : ℕ) : ℕ :=
  if n = 0 then 1 % m
  else if n = 1 then x % m
  else if n % 2 = 0 then
    let y := powMod x (n / 2) m
    y * y % m                   -- Even branch.
  else
    let y := powMod x ((n - 1) / 2) m
    x * (y * y % m) % m         -- Odd branch.
termination_by n
decreasing_by all_goals omega

/-- **Correctness of modular powering**: `powMod x n m = xⁿ mod m`. -/
theorem powMod_eq (x n m : ℕ) : powMod x n m = x ^ n % m := by
  fun_induction powMod x n m with
  | case1 => simp
  | case2 => simp
  | case3 n h0 h1 heven y ih =>
    have hn2 : n = n / 2 + n / 2 := by omega
    rw [show y = x ^ (n / 2) % m from ih, ← Nat.mul_mod, ← pow_add, ← hn2]
  | case4 n h0 h1 hodd y ih =>
    have hn2 : n = ((n - 1) / 2 + (n - 1) / 2) + 1 := by omega
    rw [show y = x ^ ((n - 1) / 2) % m from ih, ← Nat.mul_mod, ← pow_add, Nat.mul_mod_mod,
      ← pow_succ', ← hn2]

theorem powMod_lt (x n : ℕ) {m : ℕ} (hm : 0 < m) : powMod x n m < m :=
  powMod_eq x n m ▸ Nat.mod_lt _ hm

/-- `powMod` computes powers in `ZMod m`. -/
theorem cast_powMod (x n m : ℕ) : (powMod x n m : ZMod m) = (x : ZMod m) ^ n := by
  rw [powMod_eq, ZMod.natCast_mod, Nat.cast_pow]

/-! ## Relations (2.2) and (2.3) -/

/-- **Relation (2.2) (Euler).**  `a^φ(m) ≡ 1 (mod m)` whenever `a, m` are coprime. -/
theorem euler_2_2 {a m : ℕ} (h : a.Coprime m) : a ^ m.totient ≡ 1 [MOD m] :=
  Nat.ModEq.pow_totient h

/-- **Fermat's little theorem**: `a^(p-1) ≡ 1 (mod p)` for prime `p ∤ a`. -/
theorem fermat_little {a p : ℕ} (hp : p.Prime) (h : ¬p ∣ a) : a ^ (p - 1) ≡ 1 [MOD p] := by
  simpa [Nat.totient_prime hp] using euler_2_2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).symm

/-- **Relation (2.3).**  The "easy inverse": `a⁻¹ mod m = a^(φ(m)-1) mod m`, here in the
form that `powMod a (φ(m) - 1) m` is an inverse of `a` modulo `m`. -/
theorem inverse_2_3 {a m : ℕ} (hm : 0 < m) (h : a.Coprime m) :
    a * powMod a (m.totient - 1) m ≡ 1 [MOD m] := by
  have hφ : 0 < m.totient := Nat.totient_pos.mpr hm
  calc a * powMod a (m.totient - 1) m
      ≡ a * a ^ (m.totient - 1) [MOD m] := by
        rw [powMod_eq]; exact (Nat.mod_modEq _ _).mul_left _
    _ = a ^ m.totient := by rw [← pow_succ', Nat.sub_add_cancel hφ]
    _ ≡ 1 [MOD m] := euler_2_2 h

end PrimeNumbers.Chapter2
