import PrimeNumbers.Chapter2.SquareRoot
import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power

/-!
# Exercise 2.36: square roots modulo a composite of known factorization

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.3.2,
Exercise 2.36 (and Algorithm 2.3.11, Hensel lifting).

Given the factorization `m = ∏ pᵢ^eᵢ`, all solutions of `x² ≡ a (mod m)`:

* `unitRoots` — modulo `p^e` for `p ∤ a`: for odd `p`, a square root modulo `p`
  (`sqrtMod`, Algorithm 2.3.8, after Euler's criterion) lifted by Hensel's method
  (`henselSqrt`, Algorithm 2.3.11 for `x² - a`), and its negative; for `p = 2` the digits
  of the roots found one at a time (`digitRoots`);
* `rootsPrimePow` — modulo `p^e` for any `a`: with `a ≡ p^k y`, `p ∤ y` (`stripP`), the
  multiples of `p^⌈e/2⌉` if `p^e ∣ a`, none if `k` is odd, else `p^{k/2}` times the lifts
  of the roots of `y` modulo `p^{e-k}` (`sq_val`: a root has valuation `k/2`); the work is
  proportional to the number of roots;
* `rootsMod` — modulo `m`, by the Chinese remainder theorem (`crtPair`, Theorem 2.1.6).

`rootsMod_spec`: the list returned is exactly the set of roots in `[0, m)`.
-/

namespace PrimeNumbers.Chapter2

/-- **One step of Hensel lifting (Algorithm 2.3.11) for `x² - a`**: from `r² ≡ a (mod q)`,
`q = p^k`, `k ≥ 1`, with `p ∤ 2r`, the root `r + q y ≡ r (mod q)` modulo `q p`, where
`y ≡ -c (2r)⁻¹ (mod p)` and `c = (r² - a)/q mod p`. -/
counted_def henselSqrt (a p q r : ℕ) : ℕ :=
  let qp := q * p
  let c := (r * r + qp - a % qp) % qp / q
  let y := (p - c * modInv (2 * r % p) p % p) % p
  (r + q * y) % qp

/-- Hensel lifting `k` times: from a root `r` modulo `q`, the modulus `q p^k` and the root
modulo it. -/
counted_def henselLoop (a p : ℕ) : (q r k : ℕ) → ℕ × ℕ
  | q, r, 0 => (q, r)
  | q, r, k + 1 => henselLoop a p (q * p) (henselSqrt a p q r) k

/-- The roots modulo `q p` lying over the root `r` modulo `q`: the candidates `r + q j`,
`j < p`, that are roots. -/
counted_def liftDigit (a p q r : ℕ) : List ℕ :=
  ((List.range p).map fun j ↦ r + q * j).filter fun t ↦ t * t % (q * p) = a % (q * p)

/-- The roots modulo `p^e`, digit by digit: the modulus and the roots. -/
counted_def digitRoots (a p : ℕ) : ℕ → ℕ × List ℕ
  | 0 => (1, [0])
  | e + 1 =>
    let (q, rs) := digitRoots a p e
    (q * p, rs.flatMap fun r ↦ liftDigit a p q r)

/-- **The roots of `x² ≡ a (mod p^e)`** (`e ≥ 1`), with the modulus `p^e`, for `p ∤ a`: for
odd `p`, none if `a` is a nonresidue modulo `p` (Euler's criterion), else `±` the Hensel lift
of the square root modulo `p`; for `p = 2` digit by digit.  (Correct for any `a`, but fast
only for `p ∤ a`.) -/
counted_def unitRoots (a p e : ℕ) : ℕ × List ℕ :=
  if p % 2 = 1 ∧ a % p ≠ 0 then
    if powMod a (p / 2) p = 1 then
      let r := (sqrtMod p (a : ZMod p)).val
      let (q, t) := henselLoop a p p r (e - 1)
      (q, [t, q - t])
    else (p ^ e, [])
  else digitRoots a p e

/-- `x = p^k y` with `k ≤ e`, and `p ∤ y` unless `k = e`. -/
counted_def stripP (p : ℕ) : (x e : ℕ) → ℕ × ℕ
  | x, 0 => (0, x)
  | x, e + 1 =>
    if x % p = 0 then
      let (k, y) := stripP p (x / p) e
      (k + 1, y)
    else (0, x)

/-- **The roots of `x² ≡ a (mod p^e)`** (`e ≥ 1`), with the modulus `p^e`.  With
`a ≡ p^k y (mod p^e)`, `p ∤ y`: if `k = e` (`p^e ∣ a`), the multiples of `p^⌈e/2⌉`; if `k`
is odd, none; otherwise `p^{k/2} (s + p^{e-k} j)` for the roots `s` of `y` modulo `p^{e-k}`
(`unitRoots`) and `j < p^{k/2}`.  The work is proportional to the number of roots. -/
counted_def rootsPrimePow (a p e : ℕ) : ℕ × List ℕ :=
  let q := p ^ e
  let (k, y) := stripP p (a % q) e
  if k = e then (q, (List.range (p ^ (e / 2))).map fun j ↦ p ^ ((e + 1) / 2) * j)
  else if k % 2 = 1 then (q, [])
  else
    let (m, S) := unitRoots y p (e - k)
    let h := p ^ (k / 2)
    (q, S.flatMap fun s ↦ (List.range h).map fun j ↦ h * (s + m * j))

/-- **The Chinese remainder theorem for two moduli (Theorem 2.1.6)**: the `t < m₁ m₂` with
`t ≡ r (mod m₁)` and `t ≡ s (mod m₂)`, for coprime `m₁, m₂` and `r < m₁`. -/
counted_def crtPair (r m₁ s m₂ : ℕ) : ℕ :=
  r + m₁ * ((s + m₂ - r % m₂) % m₂ * modInv (m₁ % m₂) m₂ % m₂)

/-- **Exercise 2.36: the square roots of `a` modulo `m = ∏ p^e`**, given the factorization
as the pairs `(p, e)` (distinct primes, `e ≥ 1`): the modulus `m` and the roots in
`[0, m)`. -/
counted_def rootsMod (a : ℕ) : List (ℕ × ℕ) → ℕ × List ℕ
  | [] => (1, [0])
  | (p, e) :: fs =>
    let (m, rs) := rootsMod a fs
    let (q, ss) := rootsPrimePow a p e
    (m * q, ss.flatMap fun s ↦ rs.map fun r ↦ crtPair r m s q)


/-! ### Correctness -/

/-- `t` is a square root of `a` modulo `m` in `[0, m)`. -/
def IsSqrtMod (a m t : ℕ) : Prop := t < m ∧ t * t % m = a % m

theorem crtPair_spec {r m₁ s m₂ : ℕ} (hcop : Nat.Coprime m₁ m₂) (hm₂ : 0 < m₂) (hr : r < m₁) :
    crtPair r m₁ s m₂ < m₁ * m₂ ∧ crtPair r m₁ s m₂ % m₁ = r ∧
      crtPair r m₁ s m₂ % m₂ = s % m₂ := by
  unfold crtPair
  set y := (s + m₂ - r % m₂) % m₂ * modInv (m₁ % m₂) m₂ % m₂
  have hy : y < m₂ := Nat.mod_lt _ hm₂
  refine ⟨by nlinarith, by simp [Nat.mod_eq_of_lt hr], ?_⟩
  -- modulo `m₂`: `r + m₁ (s - r) m₁⁻¹ ≡ s`
  have hinv := mul_modInv_modEq (x := m₁ % m₂) (m := m₂)
    (by rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact hcop)
  apply (ZMod.natCast_eq_natCast_iff' _ _ m₂).1
  have hle : r % m₂ ≤ s + m₂ := by have := Nat.mod_lt r hm₂; omega
  have hinv' := (ZMod.natCast_eq_natCast_iff _ _ m₂).2 hinv
  push_cast [Nat.cast_sub hle, ZMod.natCast_mod] at hinv' ⊢
  simp only [y, ZMod.natCast_mod]
  push_cast [Nat.cast_sub hle, ZMod.natCast_mod]
  rw [ZMod.natCast_self, add_zero]
  linear_combination ((s : ZMod m₂) - r) * hinv'

/-- The roots modulo `m q`, `m, q` coprime, are the combinations of the roots modulo `m` and
modulo `q`. -/
theorem isSqrtMod_mul_iff {a m q t : ℕ} (hcop : Nat.Coprime m q) (hq : 0 < q) :
    IsSqrtMod a (m * q) t ↔
      ∃ r s, IsSqrtMod a m r ∧ IsSqrtMod a q s ∧ t = crtPair r m s q := by
  constructor
  · rintro ⟨ht, hsq⟩
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp at ht
      · exact h
    have hmod : t * t ≡ a [MOD m * q] := hsq
    refine ⟨t % m, t % q, ⟨Nat.mod_lt _ hm, ?_⟩, ⟨Nat.mod_lt _ hq, ?_⟩, ?_⟩
    · have := Nat.ModEq.of_mul_right q hmod
      simpa [Nat.ModEq, Nat.mul_mod] using this
    · have := Nat.ModEq.of_mul_left m hmod
      simpa [Nat.ModEq, Nat.mul_mod] using this
    · obtain ⟨c₁, c₂, c₃⟩ := crtPair_spec (s := t % q) hcop hq (Nat.mod_lt t hm)
      have h₁ : crtPair (t % m) m (t % q) q ≡ t [MOD m] := by
        simp only [Nat.ModEq, c₂]
      have h₂ : crtPair (t % m) m (t % q) q ≡ t [MOD q] := by
        simp only [Nat.ModEq, c₃, Nat.mod_mod]
      have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h₁, h₂⟩
      exact (Nat.ModEq.eq_of_lt_of_lt this c₁ ht).symm
  · rintro ⟨r, s, ⟨hr, hr'⟩, ⟨hs, hs'⟩, rfl⟩
    obtain ⟨c₁, c₂, c₃⟩ := crtPair_spec (s := s) hcop hq hr
    refine ⟨c₁, ?_⟩
    apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
    constructor
    · show _ % m = _ % m; rw [Nat.mul_mod, c₂, ← hr', Nat.mul_mod]
    · show _ % q = _ % q; rw [Nat.mul_mod, c₃, Nat.mod_eq_of_lt hs, ← hs', Nat.mul_mod]


theorem mem_liftDigit {a p q r t : ℕ} :
    t ∈ liftDigit a p q r ↔ (∃ j < p, t = r + q * j) ∧ t * t % (q * p) = a % (q * p) := by
  simp [liftDigit, eq_comm]

/-- A root modulo `q p` is a root modulo `q` plus `q` times a digit. -/
theorem isSqrtMod_mul_digit {a p q t : ℕ} (hq : 0 < q) :
    IsSqrtMod a (q * p) t ↔ IsSqrtMod a q (t % q) ∧ t / q < p ∧
      t * t % (q * p) = a % (q * p) := by
  constructor
  · rintro ⟨ht, hsq⟩
    refine ⟨⟨Nat.mod_lt _ hq, ?_⟩, Nat.div_lt_of_lt_mul (by linarith), hsq⟩
    have : t * t ≡ a [MOD q] := Nat.ModEq.of_mul_right p hsq
    simpa [Nat.ModEq, Nat.mul_mod] using this
  · rintro ⟨-, hd, hsq⟩
    refine ⟨?_, hsq⟩
    have := Nat.div_add_mod t q
    nlinarith [Nat.mod_lt t hq]

theorem digitRoots_spec (a p : ℕ) (hp : 0 < p) (e : ℕ) :
    (digitRoots a p e).1 = p ^ e ∧ ∀ t, t ∈ (digitRoots a p e).2 ↔ IsSqrtMod a (p ^ e) t := by
  induction e with
  | zero => simp [digitRoots, IsSqrtMod, Nat.mod_one]
  | succ e ih =>
    simp only [digitRoots]
    generalize digitRoots a p e = R at ih ⊢
    obtain ⟨q, rs⟩ := R
    obtain ⟨rfl, h₂⟩ := ih
    have hq : 0 < p ^ e := by positivity
    refine ⟨by rw [pow_succ], fun t ↦ ?_⟩
    simp only [List.mem_flatMap, mem_liftDigit]
    rw [pow_succ, isSqrtMod_mul_digit hq]
    constructor
    · rintro ⟨r, hr, ⟨j, hj, rfl⟩, hsq⟩
      have hr₁ := ((h₂ r).1 hr).1
      have hm : (r + p ^ e * j) % p ^ e = r := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr₁]
      have hd : (r + p ^ e * j) / p ^ e = j := by
        rw [Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hr₁, zero_add]
      exact ⟨by rw [hm]; exact (h₂ r).1 hr, by rw [hd]; exact hj, hsq⟩
    · rintro ⟨hr, hd, hsq⟩
      exact ⟨t % p ^ e, (h₂ _).2 hr, ⟨t / p ^ e, hd, (Nat.mod_add_div t _).symm⟩, hsq⟩


/-- **Hensel lifting is correct**: from a root `r` modulo `q` (`p ∣ q`, `p ∤ 2r`), the root
`t ≡ r (mod q)` modulo `q p`. -/
theorem henselSqrt_spec {a p q r : ℕ} (hp : p.Prime) (hq : 0 < q) (hpq : p ∣ q)
    (hr : r * r % q = a % q) (hpr : ¬p ∣ 2 * r) :
    henselSqrt a p q r < q * p ∧ henselSqrt a p q r * henselSqrt a p q r % (q * p) =
      a % (q * p) ∧ henselSqrt a p q r % q = r % q := by
  have hp0 := hp.pos
  have hqp : 0 < q * p := by positivity
  unfold henselSqrt
  set X := (r * r + q * p - a % (q * p)) % (q * p) with hX
  set c := X / q
  set z := modInv (2 * r % p) p
  set y := (p - c * z % p) % p
  have hle : a % (q * p) ≤ r * r + q * p := by have := Nat.mod_lt a hqp; omega
  -- `q ∣ X` and `X ≡ r² - a (mod q p)`
  have hXq : q ∣ X := by
    rw [hX, Nat.dvd_mod_iff (dvd_mul_right q p)]
    apply (Nat.modEq_iff_dvd' hle).1
    calc a % (q * p) ≡ a [MOD q] := Nat.mod_mod_of_dvd a (dvd_mul_right q p)
      _ ≡ r * r [MOD q] := hr.symm
      _ ≡ r * r + q * p [MOD q] := by simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  have hXc : X = q * c := (Nat.mul_div_cancel' hXq).symm
  have h₁ : ((q * p : ℕ) : ℤ) ∣ (r * r - a : ℤ) - q * c := by
    set M : ℤ := ((q * p : ℕ) : ℤ)
    have hqc : ((q : ℤ) * c) = X := by exact_mod_cast hXc.symm
    rw [hqc, hX, Int.natCast_mod, Nat.cast_sub hle, Int.natCast_mod]
    push_cast
    apply Int.ModEq.dvd
    have hM : M ≡ 0 [ZMOD M] := by simp [Int.ModEq]
    calc ((r : ℤ) * r + M - a % M) % M ≡ r * r + M - a % M [ZMOD M] := Int.mod_modEq _ _
      _ ≡ r * r + 0 - a [ZMOD M] :=
        Int.ModEq.sub (Int.ModEq.add_left _ hM) (Int.mod_modEq _ _)
      _ = r * r - a := by ring
  -- `p ∣ c + 2 r y`: `y ≡ -c (2r)⁻¹ (mod p)`
  have hz : 2 * r % p * z ≡ 1 [MOD p] :=
    mul_modInv_modEq ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
      (by rwa [Nat.dvd_mod_iff dvd_rfl]))))
  have h₂ : (p : ℤ) ∣ c + 2 * r * y := by
    have hcz : c * z % p ≤ p := (Nat.mod_lt _ hp0).le
    have : ((c + 2 * r * y : ℕ) : ZMod p) = 0 := by
      have hz' := (ZMod.natCast_eq_natCast_iff _ _ p).2 hz
      simp only [y, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hz' ⊢
      push_cast [Nat.cast_sub hcz, ZMod.natCast_mod, ZMod.natCast_self]
      linear_combination (-(c : ZMod p)) * hz'
    have := (ZMod.natCast_eq_zero_iff _ _).1 this
    exact_mod_cast this
  have h₃ : ((q * p : ℕ) : ℤ) ∣ (q : ℤ) * q * y * y := by
    obtain ⟨k, rfl⟩ := hpq
    exact ⟨k * y * y, by push_cast; ring⟩
  have hdvd : ((q * p : ℕ) : ℤ) ∣ ((r + q * y : ℕ) : ℤ) * (r + q * y : ℕ) - a := by
    obtain ⟨k, hk⟩ := h₂
    have h₂' : ((q * p : ℕ) : ℤ) ∣ q * (c + 2 * r * y) := ⟨k, by rw [hk]; push_cast; ring⟩
    convert dvd_add (dvd_add h₁ h₂') h₃ using 1
    push_cast; ring
  have hmod : (r + q * y) * (r + q * y) ≡ a [MOD q * p] :=
    (Int.natCast_modEq_iff.1 (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (by
      simpa using hdvd))))
  refine ⟨Nat.mod_lt _ hqp, ?_, ?_⟩
  · rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]; exact hmod
  · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right q p), Nat.add_mul_mod_self_left]


theorem henselLoop_spec {a p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∀ {q r : ℕ}, 0 < q → p ∣ q → r < q → r * r % q = a % q → ¬p ∣ 2 * r →
      (henselLoop a p q r k).1 = q * p ^ k ∧ (henselLoop a p q r k).2 < (henselLoop a p q r k).1 ∧
      (henselLoop a p q r k).2 * (henselLoop a p q r k).2 % (henselLoop a p q r k).1 =
        a % (henselLoop a p q r k).1 ∧
      (henselLoop a p q r k).2 % p = r % p := by
  induction k with
  | zero => intro q r _ _ hrq hr _; exact ⟨by simp [henselLoop], hrq, hr, rfl⟩
  | succ k ih =>
    intro q r hq hpq _ hr hpr
    obtain ⟨t₁, t₂, t₃⟩ := henselSqrt_spec (a := a) hp hq hpq hr hpr
    have htp : henselSqrt a p q r % p = r % p := by
      rw [← Nat.mod_mod_of_dvd _ hpq, t₃, Nat.mod_mod_of_dvd _ hpq]
    have hpt : ¬p ∣ 2 * henselSqrt a p q r := by
      rwa [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, htp, ← Nat.mul_mod, ← Nat.dvd_iff_mod_eq_zero]
    obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      ih (Nat.mul_pos hq hp.pos) (dvd_mul_of_dvd_left hpq p) t₁ t₂ hpt
    exact ⟨by simp only [henselLoop, h₁]; ring, h₂, h₃, by simp only [henselLoop, h₄, htp]⟩

/-- **Lifts are unique away from `p ∣ 2t`**: two roots modulo `p^e` that agree modulo the odd
prime `p` agree. -/
theorem eq_of_mul_self_mod {p e w t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hw : w < p ^ e)
    (ht : t < p ^ e) (hsq : w * w % p ^ e = t * t % p ^ e) (hmod : w % p = t % p)
    (hpt : ¬p ∣ t) : w = t := by
  have hcop : Nat.Coprime (p ^ e) (w + t) := by
    refine Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h ↦ hpt ?_)
    have h2 : p ∣ 2 * t := by
      rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
      rw [two_mul, ← (Nat.ModEq.add_right t hmod : (w + t) % p = (t + t) % p)]; exact h
    exact ((Nat.Prime.dvd_mul hp).1 h2).resolve_left fun h ↦ hp2
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  rcases le_total t w with h | h
  · have hd : p ^ e ∣ (w - t) * (w + t) := by
      rw [mul_comm, ← Nat.mul_self_sub_mul_self_eq]
      exact (Nat.modEq_iff_dvd' (Nat.mul_self_le_mul_self h)).1 hsq.symm
    have := hcop.dvd_of_dvd_mul_right hd
    have := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega
  · have hd : p ^ e ∣ (t - w) * (t + w) := by
      rw [mul_comm, ← Nat.mul_self_sub_mul_self_eq]
      exact (Nat.modEq_iff_dvd' (Nat.mul_self_le_mul_self h)).1 hsq
    have := (add_comm w t ▸ hcop).dvd_of_dvd_mul_right hd
    have := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega


/-- A root modulo `p^e` (`e ≥ 1`) is a root modulo `p`. -/
theorem zmod_sq_of_isSqrtMod {a p e w : ℕ} (he : 1 ≤ e) (h : IsSqrtMod a (p ^ e) w) :
    ((w : ZMod p)) ^ 2 = a := by
  have : w * w ≡ a [MOD p] :=
    Nat.ModEq.of_dvd (dvd_pow_self p (by omega)) h.2
  rw [sq, ← Nat.cast_mul]; exact (ZMod.natCast_eq_natCast_iff _ _ _).2 this

theorem unitRoots_spec {a p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (unitRoots a p e).1 = p ^ e ∧
      ∀ t, t ∈ (unitRoots a p e).2 ↔ IsSqrtMod a (p ^ e) t := by
  have := Fact.mk hp
  unfold unitRoots
  split_ifs with h₁ h₂
  · -- `p` odd, `p ∤ a`, `a` a residue: `±` the Hensel lift of `√a mod p`
    have hp2 : p ≠ 2 := by rintro rfl; simp at h₁
    have ha0 : (a : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]; exact h₁.2
    have hsq : IsSquare (a : ZMod p) := by
      rw [ZMod.euler_criterion p ha0]
      rw [powMod_eq] at h₂
      have := (ZMod.natCast_eq_natCast_iff' (a ^ (p / 2)) 1 p).2 (by
        rw [h₂, Nat.one_mod_eq_one.2 hp.one_lt.ne'])
      push_cast at this; exact this
    set r := (sqrtMod p (a : ZMod p)).val
    have hrp : r < p := ZMod.val_lt _
    have hr2 : (r : ZMod p) ^ 2 = a := by
      simp only [r, ZMod.natCast_val, ZMod.cast_id', id]; exact sqrtMod_sq hp2 hsq
    have hrr : r * r % p = a % p := by
      have := hr2; rw [sq, ← Nat.cast_mul] at this
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 this
    have hpr : ¬p ∣ r := fun h ↦ ha0 (by
      rw [← hr2, (ZMod.natCast_eq_zero_iff _ _).2 h]; ring)
    have hpr2 : ¬p ∣ 2 * r := fun h ↦ ((Nat.Prime.dvd_mul hp).1 h).elim
      (fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)) hpr
    obtain ⟨l₁, l₂, l₃, l₄⟩ :=
      henselLoop_spec (a := a) hp (e - 1) hp.pos dvd_rfl hrp hrr hpr2
    dsimp only
    generalize henselLoop a p p r (e - 1) = L at l₁ l₂ l₃ l₄ ⊢
    obtain ⟨q, t⟩ := L
    simp only at l₁ l₂ l₃ l₄ ⊢
    have hq : q = p ^ e := by rw [l₁, ← pow_succ']; congr 1; omega
    subst hq
    have hpt : ¬p ∣ t := by rwa [Nat.dvd_iff_mod_eq_zero, l₄, ← Nat.dvd_iff_mod_eq_zero]
    have ht0 : 0 < t := Nat.pos_of_ne_zero fun h ↦ hpt (h ▸ dvd_zero p)
    have hpe : p ∣ p ^ e := dvd_pow_self p (by omega)
    -- `p^e - t ≡ -t`
    have hneg : ∀ m, m ∣ p ^ e → ((p ^ e - t : ℕ) : ZMod m) = -t := fun m hm ↦ by
      rw [Nat.cast_sub l₂.le, (ZMod.natCast_eq_zero_iff _ _).2 hm, zero_sub]
    have hpt' : ¬p ∣ p ^ e - t := fun h ↦ hpt (by
      simpa [Nat.sub_sub_self l₂.le] using Nat.dvd_sub hpe h)
    have hroot' : IsSqrtMod a (p ^ e) (p ^ e - t) := by
      refine ⟨by omega, ?_⟩
      apply (ZMod.natCast_eq_natCast_iff' _ _ (p ^ e)).1
      have := (ZMod.natCast_eq_natCast_iff' _ _ (p ^ e)).2 l₃
      push_cast at this ⊢
      rw [hneg _ dvd_rfl]; linear_combination this
    refine ⟨rfl, fun w ↦ ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨l₂, l₃⟩
      · exact hroot'
    · have hw₁ := zmod_sq_of_isSqrtMod he hw
      have ht₁ := zmod_sq_of_isSqrtMod he ⟨l₂, l₃⟩
      have hsq : w * w % p ^ e = t * t % p ^ e := hw.2.trans l₃.symm
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hw₁.trans ht₁.symm) with h | h
      · have := eq_of_mul_self_mod hp hp2 hw.1 l₂ hsq
          ((ZMod.natCast_eq_natCast_iff' _ _ _).1 h) hpt
        simp [this]
      · have := eq_of_mul_self_mod hp hp2 hw.1 hroot'.1 (hw.2.trans hroot'.2.symm)
          ((ZMod.natCast_eq_natCast_iff' _ _ _).1 (by rw [h, hneg _ hpe])) hpt'
        simp [this]
  · -- `a` a nonresidue modulo the odd prime `p ∤ a`: no roots
    refine ⟨rfl, fun t ↦ ⟨by simp, fun ht ↦ ?_⟩⟩
    have hp2 : p ≠ 2 := by rintro rfl; simp at h₁
    have ha0 : (a : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]; exact h₁.2
    have hsq : IsSquare (a : ZMod p) := ⟨t, by rw [← zmod_sq_of_isSqrtMod he ht, sq]⟩
    rw [ZMod.euler_criterion p ha0] at hsq
    exfalso; apply h₂
    rw [powMod_eq]
    have := (ZMod.natCast_eq_natCast_iff' (a ^ (p / 2)) 1 p).1 (by push_cast; exact hsq)
    rw [this, Nat.one_mod_eq_one.2 hp.one_lt.ne']
  · exact digitRoots_spec a p hp.pos e


theorem stripP_spec (p : ℕ) (e : ℕ) : ∀ x : ℕ,
    x = p ^ (stripP p x e).1 * (stripP p x e).2 ∧ (stripP p x e).1 ≤ e ∧
      ((stripP p x e).1 < e → ¬p ∣ (stripP p x e).2) := by
  induction e with
  | zero => intro x; simp [stripP]
  | succ e ih =>
    intro x
    rw [stripP]
    split_ifs with h
    · obtain ⟨h₁, h₂, h₃⟩ := ih (x / p)
      dsimp only
      refine ⟨?_, by omega, fun hk ↦ h₃ (by omega)⟩
      rw [pow_succ, mul_comm (p ^ _) p, mul_assoc, ← h₁, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)]
    · exact ⟨by simp, by omega, fun _ ↦ fun hd ↦ h (Nat.mod_eq_zero_of_dvd hd)⟩

/-- `p^m ∣ p^j s` with `p ∤ s` iff `m ≤ j`. -/
theorem pow_dvd_pow_mul_iff {p m j s : ℕ} (hp : p.Prime) (hs : ¬p ∣ s) :
    p ^ m ∣ p ^ j * s ↔ m ≤ j := by
  constructor
  · intro h
    by_contra hc; push Not at hc
    have : p ^ (j + 1) ∣ p ^ j * s := (pow_dvd_pow p hc).trans h
    rw [pow_succ] at this
    exact hs (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos j) this)
  · intro h; exact (pow_dvd_pow p h).trans (dvd_mul_right _ _)

/-- **The valuation of a root**: if `r² ≡ p^k y (mod p^e)` with `p ∤ y` and `k < e`, then
`k` is even and `r = p^{k/2} s` with `p ∤ s` and `s² ≡ y (mod p^{e-k})`. -/
theorem sq_val {p e k y r : ℕ} (hp : p.Prime) (hk : k < e) (hy : ¬p ∣ y)
    (hr : r * r % p ^ e = p ^ k * y % p ^ e) :
    k % 2 = 0 ∧ ∃ s, ¬p ∣ s ∧ r = p ^ (k / 2) * s ∧ s * s % p ^ (e - k) = y % p ^ (e - k) := by
  -- `r ≠ 0`
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : p ^ e ∣ p ^ k * y := Nat.dvd_of_mod_eq_zero (by simpa using hr.symm)
    exact absurd ((pow_dvd_pow_mul_iff hp hy).1 this) (by omega)
  obtain ⟨j, s, hs, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr0 p hp.ne_one
  have hss : ¬p ∣ s * s := fun h ↦ hs ((Nat.Prime.dvd_mul hp).1 h |>.elim id id)
  have hrr : p ^ j * s * (p ^ j * s) = p ^ (2 * j) * (s * s) := by ring
  -- the valuations of both sides agree below `e`
  have hmod : p ^ (2 * j) * (s * s) ≡ p ^ k * y [MOD p ^ e] := by rw [← hrr]; exact hr
  have key : ∀ m ≤ e, (p ^ m ∣ p ^ (2 * j) * (s * s) ↔ p ^ m ∣ p ^ k * y) := fun m hm ↦ by
    have hpm : p ^ m ∣ p ^ e := pow_dvd_pow p hm
    exact hmod.dvd_iff hpm
  have h2j : 2 * j = k := by
    rcases lt_trichotomy (2 * j) k with h | h | h
    · have := (key (2 * j + 1) (by omega)).2 ((pow_dvd_pow_mul_iff hp hy).2 (by omega))
      exact absurd ((pow_dvd_pow_mul_iff hp hss).1 this) (by omega)
    · exact h
    · have := (key (k + 1) (by omega)).1 ((pow_dvd_pow_mul_iff hp hss).2 (by omega))
      exact absurd ((pow_dvd_pow_mul_iff hp hy).1 this) (by omega)
  refine ⟨by omega, s, hs, by rw [show k / 2 = j by omega], ?_⟩
  -- cancel `p^k`
  have hpe : p ^ e = p ^ k * p ^ (e - k) := by rw [← pow_add]; congr 1; omega
  rw [h2j, hpe] at hmod
  exact Nat.ModEq.mul_left_cancel' (pow_ne_zero k hp.ne_zero) hmod

theorem rootsPrimePow_spec {a p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (rootsPrimePow a p e).1 = p ^ e ∧
      ∀ t, t ∈ (rootsPrimePow a p e).2 ↔ IsSqrtMod a (p ^ e) t := by
  unfold rootsPrimePow; dsimp only
  have hq0 : 0 < p ^ e := pow_pos hp.pos e
  have hlt : a % p ^ e < p ^ e := Nat.mod_lt _ hq0
  obtain ⟨hx, hke, hpy⟩ := stripP_spec p e (a % p ^ e)
  generalize stripP p (a % p ^ e) e = KY at hx hke hpy ⊢
  obtain ⟨k, y⟩ := KY
  simp only at hx hke hpy ⊢
  have hpky : p ^ k * y % p ^ e = p ^ k * y := Nat.mod_eq_of_lt (by rw [← hx]; exact hlt)
  split_ifs with h₁ h₂
  · -- `p^e ∣ a`: the multiples of `p^⌈e/2⌉`
    subst h₁
    have ha0 : a % p ^ k = 0 := by
      rcases Nat.eq_zero_or_pos y with hy | hy
      · rw [hx, hy, mul_zero]
      · exfalso; have := Nat.le_mul_of_pos_right (p ^ k) hy; omega
    refine ⟨rfl, fun t ↦ ?_⟩
    simp only [List.mem_map, List.mem_range, IsSqrtMod, ha0]
    have hc : p ^ ((k + 1) / 2) * p ^ (k / 2) = p ^ k := by rw [← pow_add]; congr 1; omega
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨by rw [← hc]; exact Nat.mul_lt_mul_of_pos_left hj (pow_pos hp.pos _), ?_⟩
      apply Nat.mod_eq_zero_of_dvd
      exact (pow_dvd_pow p (show k ≤ 2 * ((k + 1) / 2) by omega)).trans
        ⟨j * j, by rw [pow_mul']; ring⟩
    · rintro ⟨ht, hsq⟩
      rcases Nat.eq_zero_or_pos t with rfl | htp
      · exact ⟨0, pow_pos hp.pos _, by simp⟩
      obtain ⟨i, s', hs', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd htp.ne' p hp.ne_one
      have hss : ¬p ∣ s' * s' := fun h ↦ hs' ((Nat.Prime.dvd_mul hp).1 h |>.elim id id)
      have hdiv : p ^ k ∣ p ^ (2 * i) * (s' * s') := by
        rw [show p ^ (2 * i) * (s' * s') = p ^ i * s' * (p ^ i * s') by ring]
        exact Nat.dvd_of_mod_eq_zero hsq
      have hik := (pow_dvd_pow_mul_iff hp hss).1 hdiv
      refine ⟨p ^ (i - (k + 1) / 2) * s', ?_, ?_⟩
      · have : p ^ ((k + 1) / 2) * (p ^ (i - (k + 1) / 2) * s') < p ^ ((k + 1) / 2) * p ^ (k / 2) := by
          rw [hc, ← mul_assoc, ← pow_add, show (k + 1) / 2 + (i - (k + 1) / 2) = i by omega]
          exact ht
        exact Nat.lt_of_mul_lt_mul_left this
      · rw [← mul_assoc, ← pow_add, show (k + 1) / 2 + (i - (k + 1) / 2) = i by omega]
  · -- odd valuation: no roots
    refine ⟨rfl, fun t ↦ ⟨by simp, fun ⟨_, hsq⟩ ↦ ?_⟩⟩
    have := (sq_val (r := t) hp (show k < e by omega) (hpy (by omega))
      (by rw [hsq, hx, hpky])).1
    omega
  · -- even valuation `k < e`: `p^{k/2} (s + p^{e-k} j)`
    have hke' : k < e := by omega
    have hpy' := hpy hke'
    obtain ⟨u₁, u₂⟩ := unitRoots_spec (a := y) hp (show 1 ≤ e - k by omega)
    generalize unitRoots y p (e - k) = MS at u₁ u₂ ⊢
    obtain ⟨m, S⟩ := MS
    simp only at u₁ u₂ ⊢
    subst u₁
    have hk2 : p ^ (k / 2) * p ^ (k / 2) = p ^ k := by rw [← pow_add]; congr 1; omega
    have hpe : p ^ k * p ^ (e - k) = p ^ e := by rw [← pow_add]; congr 1; omega
    have hm0 : 0 < p ^ (e - k) := pow_pos hp.pos _
    have hh0 : 0 < p ^ (k / 2) := pow_pos hp.pos _
    refine ⟨trivial, fun t ↦ ?_⟩
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, u₂]
    constructor
    · rintro ⟨s, ⟨hs, hss⟩, j, hj, rfl⟩
      constructor
      · have : s + p ^ (e - k) * j < p ^ (e - k) * p ^ (k / 2) := by nlinarith
        calc p ^ (k / 2) * (s + p ^ (e - k) * j) < p ^ (k / 2) * (p ^ (e - k) * p ^ (k / 2)) :=
              Nat.mul_lt_mul_of_pos_left this hh0
          _ = p ^ e := by rw [← hpe, ← hk2]; ring
      · rw [hx]
        have h₁ : (s + p ^ (e - k) * j) * (s + p ^ (e - k) * j) ≡ y [MOD p ^ (e - k)] := by
          have : (s + p ^ (e - k) * j) * (s + p ^ (e - k) * j) ≡ s * s [MOD p ^ (e - k)] := by
            simp [Nat.ModEq, Nat.add_mul_mod_self_left, Nat.mul_mod, Nat.add_mod]
          exact this.trans hss
        have h₂ := Nat.ModEq.mul_left' (p ^ k) h₁
        rw [hpe] at h₂
        rw [show p ^ (k / 2) * (s + p ^ (e - k) * j) * (p ^ (k / 2) * (s + p ^ (e - k) * j)) =
          p ^ k * ((s + p ^ (e - k) * j) * (s + p ^ (e - k) * j)) by rw [← hk2]; ring]
        rw [h₂, hpky]
    · rintro ⟨ht, hsq⟩
      obtain ⟨-, s', -, rfl, hs'⟩ := sq_val hp hke' hpy' (by rw [hsq, hx, hpky])
      refine ⟨s' % p ^ (e - k), ⟨Nat.mod_lt _ hm0, ?_⟩, s' / p ^ (e - k), ?_,
        by rw [Nat.mod_add_div]⟩
      · rw [← Nat.mul_mod, ← hs']
      · have : p ^ (k / 2) * s' < p ^ (k / 2) * (p ^ (e - k) * p ^ (k / 2)) := by
          rw [show p ^ (k / 2) * (p ^ (e - k) * p ^ (k / 2)) = p ^ e by rw [← hpe, ← hk2]; ring]
          exact ht
        exact Nat.div_lt_of_lt_mul (Nat.lt_of_mul_lt_mul_left this)

/-- A factorization: distinct primes, with positive exponents. -/
def IsFactorization (fs : List (ℕ × ℕ)) : Prop :=
  (fs.map Prod.fst).Nodup ∧ ∀ pe ∈ fs, pe.1.Prime ∧ 1 ≤ pe.2

/-- The number `∏ p^e` of a factorization. -/
def factorProd (fs : List (ℕ × ℕ)) : ℕ := (fs.map fun pe ↦ pe.1 ^ pe.2).prod

theorem coprime_factorProd {p e : ℕ} {fs : List (ℕ × ℕ)} (hp : p.Prime)
    (hfs : ∀ pe ∈ fs, pe.1.Prime) (hnot : p ∉ fs.map Prod.fst) :
    Nat.Coprime (factorProd fs) (p ^ e) := by
  unfold factorProd
  refine Nat.Coprime.pow_right _ (Nat.coprime_list_prod_left_iff.2 fun x hx ↦ ?_)
  obtain ⟨⟨q, k⟩, hq, rfl⟩ := List.mem_map.1 hx
  refine Nat.Coprime.pow_left _ ((Nat.coprime_primes (hfs _ hq) hp).2 fun h ↦ hnot ?_)
  exact List.mem_map.2 ⟨(q, k), hq, h⟩

/-- **Exercise 2.36 is correct**: given a factorization of `m`, `rootsMod` returns `m` and
exactly the square roots of `a` modulo `m` in `[0, m)`. -/
theorem rootsMod_spec (a : ℕ) {fs : List (ℕ × ℕ)} (h : IsFactorization fs) :
    (rootsMod a fs).1 = factorProd fs ∧
      ∀ t, t ∈ (rootsMod a fs).2 ↔ IsSqrtMod a (factorProd fs) t := by
  induction fs with
  | nil => simp [rootsMod, factorProd, IsSqrtMod, Nat.mod_one]
  | cons pe fs ih =>
    obtain ⟨p, e⟩ := pe
    obtain ⟨hnd, hpe⟩ := h
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp, he⟩ := hpe (p, e) (by simp)
    obtain ⟨h₁, h₂⟩ := ih ⟨hnd.2, fun x hx ↦ hpe x (by simp [hx])⟩
    obtain ⟨k₁, k₂⟩ := rootsPrimePow_spec (a := a) hp he
    have hcop := coprime_factorProd (e := e) hp (fun x hx ↦ (hpe x (by simp [hx])).1) hnd.1
    have hf : factorProd ((p, e) :: fs) = factorProd fs * p ^ e := by
      simp [factorProd, mul_comm]
    simp only [rootsMod]
    generalize rootsMod a fs = R at h₁ h₂ ⊢
    generalize rootsPrimePow a p e = Q at k₁ k₂ ⊢
    obtain ⟨m, rs⟩ := R
    obtain ⟨q, ss⟩ := Q
    simp only at h₁ h₂ k₁ k₂ ⊢
    subst h₁ k₁
    refine ⟨hf.symm, fun t ↦ ?_⟩
    rw [hf, isSqrtMod_mul_iff hcop (pow_pos hp.pos e)]
    simp only [List.mem_flatMap, List.mem_map, h₂, k₂]
    constructor
    · rintro ⟨s, hs, r, hr, rfl⟩; exact ⟨r, s, hr, hs, rfl⟩
    · rintro ⟨r, s, hr, hs, rfl⟩; exact ⟨s, hs, r, hr, rfl⟩

end PrimeNumbers.Chapter2
