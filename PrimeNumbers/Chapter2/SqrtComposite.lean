import PrimeNumbers.Chapter2.SquareRoot
import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power

/-!
# Exercise 2.36: square roots modulo a composite of known factorization

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 2.3.2,
Exercise 2.36 (and Algorithm 2.3.11, Hensel lifting).

Given the factorization `m = ∏ pᵢ^eᵢ`, all solutions of `x² ≡ a (mod m)`:

* `rootsPrimePow` — modulo a prime power `p^e`: for odd `p ∤ a`, a square root modulo `p`
  (`sqrtMod`, Algorithm 2.3.8, after Euler's criterion) lifted by Hensel's method
  (`henselSqrt`, Algorithm 2.3.11 for `x² - a`), and its negative; otherwise (`p ∣ a` or
  `p = 2`) the digits of the roots found one at a time (`digitRoots`);
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

/-- **The roots of `x² ≡ a (mod p^e)`** (`e ≥ 1`), with the modulus `p^e`: for odd `p ∤ a`,
none if `a` is a nonresidue modulo `p` (Euler's criterion), else `±` the Hensel lift of
the square root modulo `p`; otherwise digit by digit. -/
counted_def rootsPrimePow (a p e : ℕ) : ℕ × List ℕ :=
  if p % 2 = 1 ∧ a % p ≠ 0 then
    if powMod a (p / 2) p = 1 then
      let r := (sqrtMod p (a : ZMod p)).val
      let (q, t) := henselLoop a p p r (e - 1)
      (q, [t, q - t])
    else (p ^ e, [])
  else digitRoots a p e

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

theorem rootsPrimePow_spec {a p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (rootsPrimePow a p e).1 = p ^ e ∧
      ∀ t, t ∈ (rootsPrimePow a p e).2 ↔ IsSqrtMod a (p ^ e) t := by
  have := Fact.mk hp
  unfold rootsPrimePow
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
