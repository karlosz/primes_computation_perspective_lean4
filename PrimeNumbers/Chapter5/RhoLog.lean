import PrimeNumbers.Chapter2.Euclid
import PrimeNumbers.Chapter2.Power
import PrimeNumbers.Chapter5.PollardRho

/-!
# §5.2.2 Pollard rho method for discrete logarithms

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 5.2.2.

* `rhoLog` — the rho method for the discrete logarithm of `t` to the base `g` in `Z_p^*`,
  where `g` has order `N`: iterate a pseudorandom map on triples `(x, a, b)` with
  `x = g^a t^b`, find `x_i = x_{2i}` by Floyd's method, and solve
  `(b_i - b_{2i}) l ≡ a_{2i} - a_i (mod N)`.
* `rhoLog_sound` — a returned `l` satisfies `g^l ≡ t (mod p)`.

Soundness is obtained by *checking* the candidate (`g^l mod p == t`) before returning it —
one extra modular power, which any careful implementation performs.  The book describes
the method in prose (there is no numbered algorithm); the three-way split by `x mod 3` is
the classical choice of pseudorandom map.

* `rhoLogStep_inv`, `iterate_rhoLogStep_inv` — the walk keeps `x = g^a t^b`.
* `pow_rhoLogSolve` — at any collision with `gcd(b - B, N) = 1`, the candidate is a
  discrete logarithm of `t` (so the check passes).
* `exists_rhoLog_collision` — the walk has `x_i = x_{2i}` for some `1 ≤ i ≤ p`.
* `rhoLogWalkCost_le` — each pass costs three modular multiplications.

**Not proved:** that a collision occurs after `O(√N)` steps (the same random-map
heuristic as for factoring), and that the collision found has `gcd(b - B, N) = 1`
(automatic for prime `N` unless `b ≡ B`).
-/

namespace PrimeNumbers.Chapter5

open PrimeNumbers.Chapter2

/-- One step of the pseudorandom walk on `(x, a, b)` with `x = g^a t^b`:
`x ↦ t x`, `x²` or `g x` according to `x mod 3`; the exponents are kept modulo `N`. -/
def rhoLogStep (p N g t : ℕ) (s : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (x, a, b) := s
  if x % 3 = 0 then (x * x % p, 2 * a % N, 2 * b % N)
  else if x % 3 = 1 then (t * x % p, a, (b + 1) % N)
  else (g * x % p, (a + 1) % N, b)

/-- From a collision `g^a t^b = g^A t^B`, the candidate logarithm
`l = (A - a) (b - B)⁻¹ mod N`. -/
def rhoLogSolve (N a b A B : ℕ) : ℕ :=
  (A + N - a % N) % N * modInv ((b + N - B % N) % N) N % N

/-- Floyd's cycle search for the walk; on a collision, return the candidate if it checks. -/
def rhoLogLoop (p N g t : ℕ) : (u v : ℕ × ℕ × ℕ) → ℕ → Option ℕ
  | _, _, 0 => none
  | u, v, fuel + 1 =>
    let u' := rhoLogStep p N g t u
    let v' := rhoLogStep p N g t (rhoLogStep p N g t v)
    if u'.1 = v'.1 then
      let l := rhoLogSolve N u'.2.1 u'.2.2 v'.2.1 v'.2.2
      if powMod g l p = t % p then some l else none
    else rhoLogLoop p N g t u' v' fuel

/-- **Pollard rho for discrete logarithms** in `Z_p^*`: `g` of order `N`, target `t`. -/
def rhoLog (p N g t fuel : ℕ) : Option ℕ :=
  rhoLogLoop p N g t (1 % p, 0, 0) (1 % p, 0, 0) fuel

theorem rhoLogLoop_sound {p N g t : ℕ} {u v : ℕ × ℕ × ℕ} {fuel l : ℕ}
    (h : rhoLogLoop p N g t u v fuel = some l) : powMod g l p = t % p := by
  induction fuel generalizing u v with
  | zero => simp [rhoLogLoop] at h
  | succ fuel ih =>
    simp only [rhoLogLoop] at h
    split_ifs at h with h₁ h₂
    · obtain rfl := Option.some.inj h
      exact h₂
    · exact ih h

/-- **Soundness of the rho method for discrete logarithms**: a returned `l` satisfies
`g^l ≡ t (mod p)`. -/
theorem rhoLog_sound {p N g t fuel l : ℕ} (h : rhoLog p N g t fuel = some l) :
    g ^ l ≡ t [MOD p] := by
  have := rhoLogLoop_sound h
  rwa [powMod_eq] at this

/-! ## The walk invariant and the candidate -/

section Invariant

variable {p N g t : ℕ}

/-- `G^(m mod N) = G^m` when `G^N = 1`. -/
theorem pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {G : M} {N : ℕ} (hG : G ^ N = 1) (m : ℕ) :
    G ^ (m % N) = G ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m N, pow_add, pow_mul, hG, one_pow, mul_one]

/-- The walk invariant: `x = g^a t^b` in `Z_p`. -/
def RhoLogInv (p g t : ℕ) (s : ℕ × ℕ × ℕ) : Prop :=
  (s.1 : ZMod p) = (g : ZMod p) ^ s.2.1 * (t : ZMod p) ^ s.2.2

/-- One step of the walk preserves `x = g^a t^b`, provided `g^N = t^N = 1`. -/
theorem rhoLogStep_inv (hg : (g : ZMod p) ^ N = 1) (ht : (t : ZMod p) ^ N = 1)
    {s : ℕ × ℕ × ℕ} (hs : RhoLogInv p g t s) : RhoLogInv p g t (rhoLogStep p N g t s) := by
  obtain ⟨x, a, b⟩ := s
  simp only [RhoLogInv] at hs ⊢
  simp only [rhoLogStep]
  split_ifs
  · simp only [ZMod.natCast_mod, Nat.cast_mul, pow_mod_of_pow_eq_one hg,
      pow_mod_of_pow_eq_one ht, hs]
    ring
  · simp only [ZMod.natCast_mod, Nat.cast_mul, pow_mod_of_pow_eq_one ht, hs]
    ring
  · simp only [ZMod.natCast_mod, Nat.cast_mul, pow_mod_of_pow_eq_one hg, hs]
    ring

theorem iterate_rhoLogStep_inv (hg : (g : ZMod p) ^ N = 1) (ht : (t : ZMod p) ^ N = 1)
    {s : ℕ × ℕ × ℕ} (hs : RhoLogInv p g t s) (i : ℕ) :
    RhoLogInv p g t ((rhoLogStep p N g t)^[i] s) := by
  induction i with
  | zero => exact hs
  | succ i ih => rw [Function.iterate_succ_apply']; exact rhoLogStep_inv hg ht ih

/-- **The candidate is a discrete logarithm.**  Suppose `g` has order `N` modulo `p` and
`t = g^l`.  If `g^a t^b = g^A t^B` and `b - B` is invertible modulo `N`, then
`l' = (A - a)(b - B)⁻¹ mod N` satisfies `g^(l') = t`.

Indeed `a + l b ≡ A + l B (mod N)`, so `l (b - B) ≡ A - a`, i.e. `l ≡ l' (mod N)`. -/
theorem pow_rhoLogSolve {l a b A B : ℕ} (hN : 0 < N) (hord : orderOf (g : ZMod p) = N)
    (ht : (t : ZMod p) = (g : ZMod p) ^ l)
    (hcol : (g : ZMod p) ^ a * (t : ZMod p) ^ b = (g : ZMod p) ^ A * (t : ZMod p) ^ B)
    (hcop : Nat.Coprime ((b + N - B % N) % N) N) :
    (g : ZMod p) ^ rhoLogSolve N a b A B = (t : ZMod p) := by
  have : NeZero N := ⟨hN.ne'⟩
  -- powers of `g` agree iff the exponents agree modulo `N` (`g` is a unit of order `N`)
  have key : ∀ m m' : ℕ, (g : ZMod p) ^ m = (g : ZMod p) ^ m' ↔ m ≡ m' [MOD N] := by
    have hGN : (g : ZMod p) ^ N = 1 := hord ▸ pow_orderOf_eq_one (g : ZMod p)
    have hu : ((Units.ofPowEqOne (g : ZMod p) N hGN hN.ne' : (ZMod p)ˣ) : ZMod p) = g :=
      Units.val_ofPowEqOne _ _ _ _
    have hordu : orderOf (Units.ofPowEqOne (g : ZMod p) N hGN hN.ne') = N := by
      rw [← orderOf_units, hu, hord]
    intro m m'
    rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
      pow_eq_pow_iff_modEq, hordu]
  -- exponents: `a + l b ≡ A + l B (mod N)`
  rw [ht, ← pow_mul, ← pow_add, ← pow_mul, ← pow_add, key,
    ← ZMod.natCast_eq_natCast_iff] at hcol
  push_cast at hcol
  -- `d = b - B` and `e = A - a` in `Z_N`
  have hBN : B % N ≤ N := (Nat.mod_lt B hN).le
  have haN : a % N ≤ N := (Nat.mod_lt a hN).le
  have hd : (((b + N - B % N) % N : ℕ) : ZMod N) = (b : ZMod N) - B := by
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
      ZMod.natCast_mod, add_zero]
  have he : (((A + N - a % N) % N : ℕ) : ZMod N) = (A : ZMod N) - a := by
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self,
      ZMod.natCast_mod, add_zero]
  have hinv : (((b + N - B % N) % N : ℕ) : ZMod N) *
      (modInv ((b + N - B % N) % N) N : ZMod N) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (mul_modInv_modEq hcop)
    simpa using this
  -- `l' ≡ l (mod N)`
  have hl : ((rhoLogSolve N a b A B : ℕ) : ZMod N) = (l : ZMod N) := by
    rw [rhoLogSolve, ZMod.natCast_mod, Nat.cast_mul, he]
    have h1 : (l : ZMod N) * ((b : ZMod N) - B) = (A : ZMod N) - a := by
      linear_combination hcol
    rw [← h1, mul_assoc, ← hd, hinv, mul_one]
  rw [ht, key, ← ZMod.natCast_eq_natCast_iff]
  exact hl

/-- The `x`-coordinate of the walk is itself a walk: the next `x` depends only on `x`. -/
theorem rhoLogStep_fst (s : ℕ × ℕ × ℕ) :
    (rhoLogStep p N g t s).1 = (rhoLogStep p N g t (s.1, 0, 0)).1 := by
  obtain ⟨x, a, b⟩ := s
  simp only [rhoLogStep]
  split_ifs <;> rfl

theorem iterate_rhoLogStep_fst (s : ℕ × ℕ × ℕ) (i : ℕ) :
    ((rhoLogStep p N g t)^[i] s).1 =
      (fun x ↦ (rhoLogStep p N g t (x, 0, 0)).1)^[i] s.1 := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply, rhoLogStep_fst]

/-- **A collision exists**: for `p > 0` the walk has `x_i = x_{2i}` for some `1 ≤ i ≤ p`
(Floyd cycle-finding, as for factoring).  The heuristic claim is that `i = O(√N)`. -/
theorem exists_rhoLog_collision (hp : 0 < p) (s : ℕ × ℕ × ℕ) (hs : s.1 < p) :
    ∃ i, 1 ≤ i ∧ i ≤ p ∧
      ((rhoLogStep p N g t)^[i] s).1 = ((rhoLogStep p N g t)^[2 * i] s).1 := by
  obtain ⟨i, h₁, h₂, h₃⟩ := exists_iterate_eq_iterate_two_mul
    (fun x ↦ (rhoLogStep p N g t (x, 0, 0)).1)
    (fun x ↦ by simp only [rhoLogStep]; split_ifs <;> exact Nat.mod_lt _ hp) hs
  exact ⟨i, h₁, h₂, by rw [iterate_rhoLogStep_fst, iterate_rhoLogStep_fst, h₃]⟩

/-- The loop of `rhoLog` holds `u = S⁽ᵏ⁾(s₀)`, `v = S⁽²ᵏ⁾(s₀)`; if a later pass `i ≤ k + fuel`
has an `x`-collision, and every `x`-collision yields a candidate that passes the check,
the loop returns. -/
theorem rhoLogLoop_isSome_of (s₀ : ℕ × ℕ × ℕ) (k fuel : ℕ)
    (hcheck : ∀ i, ((rhoLogStep p N g t)^[i] s₀).1 = ((rhoLogStep p N g t)^[2 * i] s₀).1 →
      powMod g (rhoLogSolve N ((rhoLogStep p N g t)^[i] s₀).2.1
        ((rhoLogStep p N g t)^[i] s₀).2.2 ((rhoLogStep p N g t)^[2 * i] s₀).2.1
        ((rhoLogStep p N g t)^[2 * i] s₀).2.2) p = t % p)
    (hex : ∃ i, k < i ∧ i ≤ k + fuel ∧
      ((rhoLogStep p N g t)^[i] s₀).1 = ((rhoLogStep p N g t)^[2 * i] s₀).1) :
    (rhoLogLoop p N g t ((rhoLogStep p N g t)^[k] s₀) ((rhoLogStep p N g t)^[2 * k] s₀)
      fuel).isSome := by
  induction fuel generalizing k with
  | zero => obtain ⟨i, h₁, h₂, -⟩ := hex; omega
  | succ fuel ih =>
    have hu : rhoLogStep p N g t ((rhoLogStep p N g t)^[k] s₀) =
        (rhoLogStep p N g t)^[k + 1] s₀ := (Function.iterate_succ_apply' _ _ _).symm
    have hv : rhoLogStep p N g t (rhoLogStep p N g t ((rhoLogStep p N g t)^[2 * k] s₀)) =
        (rhoLogStep p N g t)^[2 * (k + 1)] s₀ := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
    simp only [rhoLogLoop, hu, hv]
    split_ifs with hcol hchk
    · rfl
    · exact absurd (hcheck (k + 1) hcol) hchk
    · obtain ⟨i, h₁, h₂, h₃⟩ := hex
      have hne : i ≠ k + 1 := by rintro rfl; exact hcol h₃
      exact ih (k + 1) ⟨i, by omega, by omega, h₃⟩

/-- **The rho method for discrete logarithms, assembled.**  Let `g` have order `N > 0`
modulo `p`, and `t ≡ g^l`.  Suppose that at every collision of the walk the difference
`b - B` of the `t`-exponents is invertible modulo `N` (for prime `N`: `b ≢ B`; this is the
part left to chance).  Then within `p` passes `rhoLog` returns a discrete logarithm of
`t`.  Under the random-map heuristic (`RhoCollision`-style hypotheses) the number of passes
is `O(√N)` instead of `p`. -/
theorem rhoLog_isSome {l : ℕ} (hp : 0 < p) (hN : 0 < N) (hord : orderOf (g : ZMod p) = N)
    (ht : (t : ZMod p) = (g : ZMod p) ^ l)
    (hcop : ∀ i, ((rhoLogStep p N g t)^[i] (1 % p, 0, 0)).1 =
        ((rhoLogStep p N g t)^[2 * i] (1 % p, 0, 0)).1 →
      Nat.Coprime ((((rhoLogStep p N g t)^[i] (1 % p, 0, 0)).2.2 + N -
        ((rhoLogStep p N g t)^[2 * i] (1 % p, 0, 0)).2.2 % N) % N) N)
    {fuel : ℕ} (hfuel : p ≤ fuel) : (rhoLog p N g t fuel).isSome := by
  have hgN : (g : ZMod p) ^ N = 1 := hord ▸ pow_orderOf_eq_one _
  have htN : (t : ZMod p) ^ N = 1 := by rw [ht, ← pow_mul, mul_comm, pow_mul, hgN, one_pow]
  have hinv0 : RhoLogInv p g t (1 % p, 0, 0) := by simp [RhoLogInv]
  obtain ⟨i, h₁, h₂, h₃⟩ := exists_rhoLog_collision (N := N) (g := g) (t := t) hp
    (1 % p, 0, 0) (Nat.mod_lt 1 hp)
  have := rhoLogLoop_isSome_of (p := p) (N := N) (g := g) (t := t) (1 % p, 0, 0) 0 fuel
    (fun i hcol ↦ by
      have hu := iterate_rhoLogStep_inv hgN htN hinv0 i
      have hv := iterate_rhoLogStep_inv hgN htN hinv0 (2 * i)
      have hcolZ : (g : ZMod p) ^ ((rhoLogStep p N g t)^[i] (1 % p, 0, 0)).2.1 *
          (t : ZMod p) ^ ((rhoLogStep p N g t)^[i] (1 % p, 0, 0)).2.2 =
          (g : ZMod p) ^ ((rhoLogStep p N g t)^[2 * i] (1 % p, 0, 0)).2.1 *
          (t : ZMod p) ^ ((rhoLogStep p N g t)^[2 * i] (1 % p, 0, 0)).2.2 := by
        rw [← hu, ← hv, hcol]
      have hsol := pow_rhoLogSolve hN hord ht hcolZ (hcop i hcol)
      rw [← cast_powMod] at hsol
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hsol
      rwa [Nat.mod_eq_of_lt (powMod_lt _ _ hp)] at this)
    ⟨i, h₁, by omega, h₃⟩
  simpa [rhoLog] using this

end Invariant

/-! ## Running time -/

section RunningTime

open PrimeNumbers.Chapter9

/-- The bit operations of one step of the walk: one multiplication of residues modulo `p`
and its reduction.  (The exponents are updated by additions and doublings modulo `N`,
which are linear.) -/
def rhoLogStepCost (C : CostModel) (p g t : ℕ) (s : ℕ × ℕ × ℕ) : ℕ :=
  if s.1 % 3 = 0 then C.mul s.1.size s.1.size + C.divMod (s.1 * s.1).size p.size
  else if s.1 % 3 = 1 then C.mul t.size s.1.size + C.divMod (t * s.1).size p.size
  else C.mul g.size s.1.size + C.divMod (g * s.1).size p.size

/-- The bit operations of the walk in `rhoLogLoop`: three steps per pass. -/
def rhoLogWalkCost (C : CostModel) (p N g t : ℕ) : (u v : ℕ × ℕ × ℕ) → ℕ → ℕ
  | _, _, 0 => 0
  | u, v, fuel + 1 =>
    let u' := rhoLogStep p N g t u
    let v₁ := rhoLogStep p N g t v
    let v' := rhoLogStep p N g t v₁
    rhoLogStepCost C p g t u + rhoLogStepCost C p g t v + rhoLogStepCost C p g t v₁ +
      if u'.1 = v'.1 then 0 else rhoLogWalkCost C p N g t u' v' fuel

theorem rhoLogStepCost_le (C : CostModel) {p g t : ℕ} (hg : g < p) (ht : t < p)
    {s : ℕ × ℕ × ℕ} (hs : s.1 < p) : rhoLogStepCost C p g t s ≤ C.mulMod p.size := by
  unfold rhoLogStepCost
  split_ifs
  · exact mul_add_divMod_le C hs hs
  · exact mul_add_divMod_le C ht hs
  · exact mul_add_divMod_le C hg hs

theorem rhoLogStep_fst_lt {p N g t : ℕ} (hp : 0 < p) (s : ℕ × ℕ × ℕ) :
    (rhoLogStep p N g t s).1 < p := by
  obtain ⟨x, a, b⟩ := s
  simp only [rhoLogStep]
  split_ifs <;> exact Nat.mod_lt _ hp

/-- **Bit complexity of the rho method for discrete logarithms**: each pass of the walk
costs three modular multiplications.  (At the collision there is in addition one modular
inverse modulo `N` and one modular power, bounded by `modInvCost_school_le` and
`powModCost_le`.) -/
theorem rhoLogWalkCost_le (C : CostModel) {p N g t : ℕ} (hg : g < p) (ht : t < p)
    {u v : ℕ × ℕ × ℕ} (hu : u.1 < p) (hv : v.1 < p) (fuel : ℕ) :
    rhoLogWalkCost C p N g t u v fuel ≤ fuel * (3 * C.mulMod p.size) := by
  have hp : 0 < p := by omega
  induction fuel generalizing u v with
  | zero => simp [rhoLogWalkCost]
  | succ fuel ih =>
    have h₁ := rhoLogStepCost_le C hg ht hu
    have h₂ := rhoLogStepCost_le C hg ht hv
    have h₃ := rhoLogStepCost_le C hg ht (rhoLogStep_fst_lt (N := N) (g := g) (t := t) hp v)
    have ih := ih (rhoLogStep_fst_lt (N := N) (g := g) (t := t) hp u)
      (rhoLogStep_fst_lt (N := N) (g := g) (t := t) hp
        (rhoLogStep p N g t v))
    simp only [rhoLogWalkCost, add_mul, one_mul]
    split_ifs <;> omega

end RunningTime

end PrimeNumbers.Chapter5
