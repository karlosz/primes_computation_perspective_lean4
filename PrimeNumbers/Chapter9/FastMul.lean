import PrimeNumbers.Chapter2.Poly
import PrimeNumbers.Chapter9.BitCost

/-!
# §9.6.1 Fast polynomial multiplication: binary segmentation

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Algorithm 9.6.1.

Binary segmentation (Kronecker substitution) multiplies polynomials with one *integer*
multiplication: pack the coefficients into the integers `x(2^b)`, `y(2^b)`, multiply,
and unpack the base-`2^b` digits of the product.  The integer multiplication is Lean's
`Nat.mul`, which is GMP's (Karatsuba / Toom–Cook / FFT internally): so the fast integer
arithmetic of §9.5 is used through the existing primitive rather than re-implemented.

* `pack`, `unpack` — divide-and-conquer conversions between coefficient lists and
  `Nat.ofDigits (2^b)` (Mathlib), so that each costs `O(N log D)` bit operations instead of
  the `O(N D)` of Horner's rule; `pack_eq`, `unpack_ofDigits`.
* `mulNat` — Algorithm 9.6.1 over `ℕ`; `mulNat_eq` proves it equals schoolbook
  `Poly.mul` whenever the product's coefficients fit in `b` bits, and
  `coeff_mul_le` gives a `b` that suffices.
* `mulMod` — multiplication in `Z_n[t]` by binary segmentation; `toPolynomial_mulMod`.
* `mulNatCost_le` — the cost is one multiplication of `b·D`-bit integers, `C.mul (bD) (bD)`.
-/

namespace PrimeNumbers.Chapter9

open Polynomial PrimeNumbers.Chapter2 PrimeNumbers.Chapter2.Poly

/-- `Nat.ofDigits` is evaluation of the coefficient list. -/
theorem ofDigits_eq_eval (B : ℕ) (L : List ℕ) :
    Nat.ofDigits B L = (toPolynomial L).eval B := by
  induction L with
  | nil => simp
  | cons c L ih => simp [Nat.ofDigits_cons, ih]

/-- Pack a coefficient list into the integer `L(2^b)`, splitting the list in halves. -/
counted_def pack (b : ℕ) (L : List ℕ) : ℕ :=
  if L.length ≤ 1 then Nat.ofDigits (2 ^ b) L
  else pack b (L.take (L.length / 2)) + (pack b (L.drop (L.length / 2)) <<< (b * (L.length / 2)))
termination_by L.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

theorem pack_eq (b : ℕ) (L : List ℕ) : pack b L = Nat.ofDigits (2 ^ b) L := by
  fun_induction pack b L with
  | case1 L h => rfl
  | case2 L h ih₁ ih₂ =>
    conv_rhs => rw [← List.take_append_drop (L.length / 2) L, Nat.ofDigits_append]
    rw [ih₁, ih₂, Nat.shiftLeft_eq, List.length_take, min_eq_left (Nat.div_le_self _ _),
      ← pow_mul]
    ring

/-- Unpack the `count` base-`2^b` digits of `N`, splitting in halves. -/
counted_def unpack (b N count : ℕ) : List ℕ :=
  if count = 0 then []
  else if count = 1 then [N]
  else unpack b (N % 2 ^ (b * (count / 2))) (count / 2) ++
    unpack b (N >>> (b * (count / 2))) (count - count / 2)
termination_by count
decreasing_by all_goals omega

theorem unpack_ofDigits {b : ℕ} (hb : 0 < b) (L : List ℕ) (hL : ∀ x ∈ L, x < 2 ^ b) :
    unpack b (Nat.ofDigits (2 ^ b) L) L.length = L := by
  have hB : 1 < 2 ^ b := Nat.one_lt_two_pow hb.ne'
  induction hlen : L.length using Nat.strong_induction_on generalizing L with
  | _ count ih =>
    rw [unpack]
    split_ifs with h0 h1
    · subst h0; exact (List.length_eq_zero_iff.mp hlen).symm
    · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (h1 ▸ hlen)
      simp
    · -- `L = L₁ ++ L₂` and `N = N₁ + 2^(b h) N₂` with `N₁ < 2^(b h)`
      set h := count / 2 with hh
      have hL₁ : (L.take h).length = h := by rw [List.length_take]; omega
      have hL₂ : (L.drop h).length = count - h := by rw [List.length_drop]; omega
      have hsplit : Nat.ofDigits (2 ^ b) L =
          Nat.ofDigits (2 ^ b) (L.take h) + 2 ^ (b * h) * Nat.ofDigits (2 ^ b) (L.drop h) := by
        conv_lhs => rw [← List.take_append_drop h L, Nat.ofDigits_append]
        rw [hL₁, ← pow_mul]
      have hlt : Nat.ofDigits (2 ^ b) (L.take h) < 2 ^ (b * h) := by
        have := Nat.ofDigits_lt_base_pow_length (l := L.take h) hB
          (fun x hx ↦ hL x (List.mem_of_mem_take hx))
        rwa [hL₁, ← pow_mul] at this
      have hmod : Nat.ofDigits (2 ^ b) L % 2 ^ (b * h) = Nat.ofDigits (2 ^ b) (L.take h) := by
        rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      have hdiv : Nat.ofDigits (2 ^ b) L >>> (b * h) = Nat.ofDigits (2 ^ b) (L.drop h) := by
        rw [Nat.shiftRight_eq_div_pow, hsplit, Nat.add_mul_div_left _ _ (by positivity),
          Nat.div_eq_of_lt hlt, zero_add]
      have e₁ := ih h (by omega) (L.take h) (fun x hx ↦ hL x (List.mem_of_mem_take hx)) hL₁
      have e₂ := ih (count - h) (by omega) (L.drop h)
        (fun x hx ↦ hL x (List.mem_of_mem_drop hx)) hL₂
      rw [hmod, hdiv, e₁, e₂, List.take_append_drop]

/-! ## Algorithm 9.6.1 over `ℕ` -/

theorem length_mul_nat {f g : List ℕ} (hf : f ≠ []) (hg : g ≠ []) :
    (mul f g).length = f.length + g.length - 1 := by
  induction f with
  | nil => exact absurd rfl hf
  | cons a f ih =>
    have hgl := List.length_pos_iff.mpr hg
    rcases f with _ | ⟨c, f⟩
    · simp [mul, length_add]; omega
    · have := ih (by simp)
      simp only [mul, length_add, length_smul, List.length_cons] at this ⊢
      omega

/-- **Algorithm 9.6.1 (binary segmentation)** for coefficient lists over `ℕ`:
`x(t) y(t)` is read off the base-`2^b` digits of the integer product `x(2^b) · y(2^b)`. -/
counted_def mulNat (b : ℕ) (f g : List ℕ) : List ℕ :=
  if f = [] ∨ g = [] then mul f g
  else unpack b (pack b f * pack b g) (f.length + g.length - 1)

/-- **Correctness of binary segmentation**: if every coefficient of the product is below
`2^b`, the result is exactly the schoolbook product. -/
theorem mulNat_eq {b : ℕ} (hb : 0 < b) (f g : List ℕ) (hbound : ∀ c ∈ mul f g, c < 2 ^ b) :
    mulNat b f g = mul f g := by
  unfold mulNat
  split_ifs with h
  · rfl
  · push Not at h
    have hprod : pack b f * pack b g = Nat.ofDigits (2 ^ b) (mul f g) := by
      rw [pack_eq, pack_eq, ofDigits_eq_eval, ofDigits_eq_eval, ofDigits_eq_eval,
        toPolynomial_mul, eval_mul]
    rw [hprod, ← length_mul_nat h.1 h.2]
    exact unpack_ofDigits hb _ hbound

theorem add_le_bound {X Y : List ℕ} {BX BY : ℕ} (hX : ∀ c ∈ X, c ≤ BX) (hY : ∀ c ∈ Y, c ≤ BY) :
    ∀ c ∈ add X Y, c ≤ BX + BY := by
  induction X generalizing Y with
  | nil => intro c hc; simp only [add] at hc; have := hY c hc; omega
  | cons x X ih =>
    cases Y with
    | nil => intro c hc; simp only [add] at hc; have := hX c hc; omega
    | cons y Y =>
      intro c hc
      simp only [add, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact Nat.add_le_add (hX x (by simp)) (hY y (by simp))
      · exact ih (fun c h ↦ hX c (by simp [h])) (fun c h ↦ hY c (by simp [h])) c hc

/-- The coefficients of `x y` are at most `len(x) · A · A'` when those of `x`, `y` are at
most `A`, `A'`: so `b = size (len(x) A A') + 1` bits suffice. -/
theorem coeff_mul_le {f g : List ℕ} {A A' : ℕ} (hf : ∀ x ∈ f, x ≤ A) (hg : ∀ y ∈ g, y ≤ A') :
    ∀ c ∈ mul f g, c ≤ f.length * (A * A') := by
  induction f with
  | nil => simp [mul]
  | cons a f ih =>
    intro c hc
    simp only [mul] at hc
    have h₁ : ∀ c ∈ smul a g, c ≤ A * A' := by
      intro c hc
      simp only [smul, List.mem_map] at hc
      obtain ⟨y, hy, rfl⟩ := hc
      exact Nat.mul_le_mul (hf a (by simp)) (hg y hy)
    have h₂ : ∀ c ∈ (0 :: mul f g), c ≤ f.length * (A * A') := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Nat.zero_le _
      · exact ih (fun x hx ↦ hf x (by simp [hx])) c hc
    have := add_le_bound h₁ h₂ c hc
    simp only [List.length_cons]
    nlinarith

/-- Binary segmentation with a sufficient `b` chosen automatically. -/
counted_def mulNatAuto (f g : List ℕ) : List ℕ :=
  mulNat ((f.length * (f.sum * g.sum)).size + 1) f g

theorem mulNatAuto_eq (f g : List ℕ) : mulNatAuto f g = mul f g := by
  refine mulNat_eq (Nat.succ_pos _) f g fun c hc ↦ ?_
  have h := coeff_mul_le (fun x hx ↦ List.le_sum_of_mem hx) (fun y hy ↦ List.le_sum_of_mem hy)
    c hc
  have h₁ := Nat.lt_size_self (f.length * (f.sum * g.sum))
  have h₂ : 2 ^ (f.length * (f.sum * g.sum)).size ≤ 2 ^ ((f.length * (f.sum * g.sum)).size + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## Multiplication in `Z_n[t]` -/

theorem toPolynomial_map_natCast {R : Type} [CommSemiring R] (L : List ℕ) :
    toPolynomial (L.map (Nat.cast : ℕ → R)) = (toPolynomial L).map (Nat.castRingHom R) := by
  induction L with
  | nil => simp
  | cons c L ih => simp [ih]

/-- **Polynomial multiplication in `Z_n[t]` by binary segmentation**: lift the coefficients
to `[0, n)`, multiply over `ℕ` with one integer multiplication, reduce. -/
counted_def mulMod (n : ℕ) (f g : Chapter2.Poly (ZMod n)) : Chapter2.Poly (ZMod n) :=
  (mulNatAuto (f.map ZMod.val) (g.map ZMod.val)).map (Nat.cast : ℕ → ZMod n)

theorem toPolynomial_mulMod {n : ℕ} [NeZero n] (f g : Chapter2.Poly (ZMod n)) :
    toPolynomial (mulMod n f g) = toPolynomial f * toPolynomial g := by
  have hlift : ∀ h : Chapter2.Poly (ZMod n),
      (toPolynomial (h.map ZMod.val)).map (Nat.castRingHom (ZMod n)) = toPolynomial h := by
    intro h
    rw [← toPolynomial_map_natCast, List.map_map]
    congr 1
    conv_rhs => rw [← List.map_id h]
    exact List.map_congr_left fun x _ ↦ ZMod.natCast_zmod_val x
  rw [mulMod, toPolynomial_map_natCast, mulNatAuto_eq, toPolynomial_mul, Polynomial.map_mul,
    hlift, hlift]

/-! ## Running time -/

/-- `L(2^b)` has at most `b · len L` bits when the coefficients are below `2^b`. -/
theorem size_pack_le {b : ℕ} (hb : 0 < b) {L : List ℕ} (hL : ∀ x ∈ L, x < 2 ^ b) :
    (pack b L).size ≤ b * L.length := by
  rw [Nat.size_le, pack_eq, pow_mul]
  exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow hb.ne') hL

/-- **Cost of Algorithm 9.6.1**: one multiplication of a `b·len(x)`-bit by a `b·len(y)`-bit
integer (packing and unpacking are shifts and additions, `O(N log D)` bit operations, not
charged).  With grammar-school integer multiplication this is no faster than schoolbook
polynomial multiplication; with the fast integer multiplication of §9.5 (which GMP uses)
it is quasi-linear in `b D`. -/
theorem mulNatCost_le (C : CostModel) {b : ℕ} (hb : 0 < b) {f g : List ℕ}
    (hf : ∀ x ∈ f, x < 2 ^ b) (hg : ∀ y ∈ g, y < 2 ^ b) :
    C.mul (pack b f).size (pack b g).size ≤ C.mul (b * f.length) (b * g.length) :=
  C.mul_mono (size_pack_le hb hf) (size_pack_le hb hg)

end PrimeNumbers.Chapter9
