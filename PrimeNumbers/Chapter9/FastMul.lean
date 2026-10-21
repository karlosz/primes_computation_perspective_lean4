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
  let n := L.length
  if n ≤ 1 then L.headD 0
  else
    let h := n / 2
    pack b (L.take h) + (pack b (L.drop h) <<< (b * h))
termination_by L.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

theorem pack_eq (b : ℕ) (L : List ℕ) : pack b L = Nat.ofDigits (2 ^ b) L := by
  fun_induction pack b L with
  | case1 L n hn =>
    have hn' : L.length ≤ 1 := hn
    match L, hn' with
    | [], _ => rfl
    | [c], _ => simp
  | case2 L n hn h ih₁ ih₂ =>
    conv_rhs => rw [← List.take_append_drop (L.length / 2) L, Nat.ofDigits_append]
    rw [ih₁, ih₂, Nat.shiftLeft_eq, List.length_take, min_eq_left (Nat.div_le_self _ _),
      ← pow_mul]
    ring

/-- Unpack the `count` base-`2^b` digits of `N`, splitting in halves. -/
counted_def unpack (b N count : ℕ) : List ℕ :=
  if count = 0 then []
  else if count = 1 then [N]
  else
    let h := count / 2
    let s := b * h
    unpack b (N % 2 ^ s) h ++ unpack b (N >>> s) (count - h)
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
      dsimp only
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

/-- Digits below `2^w` in base `2^b ≤ 2^w` give a number of at most `w · len` bits. -/
theorem ofDigits_lt_of_le {b w : ℕ} (hbw : b ≤ w) (L : List ℕ) (hL : ∀ x ∈ L, x < 2 ^ w) :
    Nat.ofDigits (2 ^ b) L < 2 ^ (w * L.length) := by
  induction L with
  | nil => simp
  | cons c L ih =>
    have hc := hL c (by simp)
    have ih := ih fun x hx ↦ hL x (by simp [hx])
    have hb : 2 ^ b ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hbw
    rw [Nat.ofDigits_cons, List.length_cons, Nat.mul_succ, pow_add]
    nlinarith [Nat.zero_le (Nat.ofDigits (2 ^ b) L)]

theorem size_pack_le_of_le {b w : ℕ} (hbw : b ≤ w) {L : List ℕ} (hL : ∀ x ∈ L, x < 2 ^ w) :
    (pack b L).size ≤ w * L.length := by
  rw [Nat.size_le, pack_eq]; exact ofDigits_lt_of_le hbw L hL

/-- **Cost of packing** `len L` coefficients of at most `w` bits: per level of the splitting,
the steps through the list and an addition and a shift of numbers of at most `w · len` bits;
per node, a small product `b · (len/2)` (at most `X`) and two steps on the lengths (of at most
`K` bits). -/
@[cost_le] theorem pack_cost_le (C : CostModel) {b w K X : ℕ} (hbw : b ≤ w) (h2K : 2 ≤ K) :
    ∀ L : List ℕ, (∀ x ∈ L, x < 2 ^ w) → L.length.size ≤ K →
      C.mul b.size (L.length / 2).size ≤ X →
      costOf C (pack b L) ≤
        halvingBound (2 * C.unit + 2 * C.add w w) (4 * C.unit + 2 * C.add K K + X) L.length := by
  intro L
  induction hn : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  intro hL hK hX
  by_cases h1 : n ≤ 1
  · rw [halvingBound_le_one _ _ h1]
    cost_unfold pack.counted
    rw [hn]
    cost_bound
  · have hmono : ∀ m, m ≤ n → C.mul b.size (m / 2).size ≤ X :=
      fun m hm ↦ (C.mul_mono le_rfl (Nat.size_le_size (by omega))).trans (hn ▸ hX)
    have kT : (n / 2).size ≤ K := (Nat.size_le_size (by omega)).trans hK
    have kD : (n - n / 2).size ≤ K := (Nat.size_le_size (by omega)).trans hK
    have hT := ih (n / 2) (by omega) (L.take (n / 2)) (by simp; omega)
      (fun x hx ↦ hL x (List.mem_of_mem_take hx)) kT (hmono _ (by omega))
    have hD := ih (n - n / 2) (by omega) (L.drop (n / 2)) (by simp; omega)
      (fun x hx ↦ hL x (List.mem_of_mem_drop hx)) kD (hmono _ (by omega))
    -- the sizes of the big operands: at most `w n` bits
    have sT : (pack b (L.take (n / 2))).size ≤ w * n :=
      (size_pack_le_of_le hbw (L := L.take (n / 2)) fun x hx ↦ hL x (List.mem_of_mem_take hx)).trans
        (Nat.mul_le_mul_left _ (by rw [List.length_take]; omega))
    have sD : (pack b (L.drop (n / 2))).size ≤ w * (n - n / 2) :=
      (size_pack_le_of_le hbw (L := L.drop (n / 2)) fun x hx ↦ hL x (List.mem_of_mem_drop hx)).trans
        (Nat.mul_le_mul_left _ (by rw [List.length_drop]; omega))
    have sS : (pack b (L.drop (n / 2)) <<< (b * (n / 2))).size ≤ w * n := by
      rw [Nat.shiftLeft_eq, Nat.size_le]
      calc pack b (L.drop (n / 2)) * 2 ^ (b * (n / 2)) < 2 ^ (w * (n - n / 2)) * 2 ^ (w * (n / 2)) :=
            Nat.mul_lt_mul_of_lt_of_le (Nat.size_le.1 sD)
              (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hbw)) (by positivity)
        _ = 2 ^ (w * n) := by rw [← pow_add, ← Nat.mul_add]; congr 2; omega
    have sD' : (pack b (L.drop (n / 2))).size ≤ w * n := sD.trans (Nat.mul_le_mul_left _ (by omega))
    have sB : (b * (n / 2)).size ≤ w * n :=
      (Nat.size_le.2 Nat.lt_two_pow_self).trans (Nat.mul_le_mul hbw (by omega))
    have hlin := C.add_mul_le (w := w) (show 1 ≤ n by omega)
    have hstep := halvingBound_step (2 * C.unit + 2 * C.add w w) (4 * C.unit + 2 * C.add K K + X)
      (show 2 ≤ n by omega)
    cost_unfold pack.counted
    simp only [List.length_take, List.length_drop, hn, min_eq_left (Nat.div_le_self n 2)] at *
    cost_bound

theorem length_unpack (b : ℕ) : ∀ N count : ℕ, (unpack b N count).length = count := by
  intro N count
  induction count using Nat.strong_induction_on generalizing N with
  | _ count ih =>
    rw [unpack]
    split_ifs with h0 h1
    · simp [h0]
    · simp [h1]
    · dsimp only
      rw [List.length_append, ih _ (by omega), ih _ (by omega)]; omega

theorem size_shiftRight_le (N s : ℕ) : (N >>> s).size ≤ N.size - s := by
  rw [Nat.shiftRight_eq_div_pow, Nat.size_le]
  rcases Nat.le_total s N.size with h | h
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel h]
    exact Nat.lt_size_self N
  · rw [Nat.div_eq_of_lt ((Nat.lt_size_self N).trans_le (Nat.pow_le_pow_right (by norm_num) h))]
    simp

/-- **Cost of unpacking** `count` digits of `b` bits from a number of at most
`b (count + 1)` bits: per level, the steps of the appends and a reduction, a shift and a
power of two on numbers of at most `2b · count` bits; per node, a small product `b · (count/2)`
(at most `X`) and four steps on the counts (of at most `K` bits). -/
@[cost_le] theorem unpack_cost_le (C : CostModel) {b K X : ℕ} (hb : 1 ≤ b) (h2K : 2 ≤ K) :
    ∀ count N : ℕ, N.size ≤ b * (count + 1) → count.size ≤ K →
      C.mul b.size (count / 2).size ≤ X →
      costOf C (unpack b N count) ≤
        halvingBound (C.unit + 3 * C.add (2 * b) (2 * b)) (2 * C.unit + 4 * C.add K K + X) count := by
  intro count
  induction count using Nat.strong_induction_on with
  | _ count ih =>
  intro N hN hK hX
  by_cases h1 : count ≤ 1
  · rw [halvingBound_le_one _ _ h1]
    rcases (by omega : count = 0 ∨ count = 1) with rfl | rfl
    · cost_unfold unpack.counted; cost_bound
    · cost_unfold unpack.counted; cost_bound
  · have hmono : ∀ m, m ≤ count → C.mul b.size (m / 2).size ≤ X :=
      fun m hm ↦ (C.mul_mono le_rfl (Nat.size_le_size (by omega))).trans hX
    set h := count / 2 with hh
    have kH : h.size ≤ K := (Nat.size_le_size (by omega)).trans hK
    have kD : (count - h).size ≤ K := (Nat.size_le_size (by omega)).trans hK
    have sM : (N % 2 ^ (b * h)).size ≤ b * (h + 1) :=
      (Nat.size_le.2 (Nat.mod_lt _ (by positivity))).trans (by nlinarith)
    have sS : (N >>> (b * h)).size ≤ b * (count - h + 1) :=
      (size_shiftRight_le _ _).trans (by
        have : b * (count + 1) - b * h = b * (count - h + 1) := by
          rw [← Nat.mul_sub]; congr 1; omega
        omega)
    have hM := ih h (by omega) (N % 2 ^ (b * h)) sM kH (hmono _ (by omega))
    have hS := ih (count - h) (by omega) (N >>> (b * h)) sS kD (hmono _ (by omega))
    -- the big operands have at most `2 b count` bits
    have hbc : b * (count + 1) ≤ 2 * b * count := by
      calc b * (count + 1) ≤ b * (2 * count) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * b * count := by ring
    have hbh : b * h + 1 ≤ b * (count + 1) := by
      have := Nat.mul_le_mul_left b (show h ≤ count by omega); nlinarith
    have sB : (b * h).size ≤ 2 * b * count :=
      (Nat.size_le.2 Nat.lt_two_pow_self).trans (by nlinarith)
    have hlin := C.add_mul_le (w := 2 * b) (show 1 ≤ count by omega)
    have hstep := halvingBound_step (C.unit + 3 * C.add (2 * b) (2 * b))
      (2 * C.unit + 4 * C.add K K + X) (show 2 ≤ count by omega)
    cost_unfold unpack.counted
    rw [length_unpack]
    cost_bound

/-- A schoolbook product with an empty factor takes a step per coefficient. -/
@[cost_le] theorem mul_nil_cost (C : CostModel) (f : List ℕ) :
    costOf C (Chapter2.Poly.mul f []) ≤ (5 * f.length + 1) * C.unit := by
  induction f with
  | nil => cost_unfold Chapter2.Poly.mul.counted
  | cons a f ih =>
    have h₁ : costOf C (Chapter2.Poly.smul a []) = 2 * C.unit := by
      cost_unfold Chapter2.Poly.smul.counted
    have h₂ : ∀ g : List ℕ, costOf C (Chapter2.Poly.add [] g) = C.unit := fun g ↦ by
      cost_unfold Chapter2.Poly.add.counted
    cost_unfold Chapter2.Poly.mul.counted
    simp only [Chapter2.Poly.smul, List.map_nil, h₁, h₂]
    nlinarith

theorem nil_mul_cost (C : CostModel) (g : List ℕ) : costOf C (Chapter2.Poly.mul [] g) = C.unit := by
  cost_unfold Chapter2.Poly.mul.counted

/-- The width of one coefficient in binary segmentation over `Z_n`, for polynomials with at
most `d` coefficients: enough for the coefficients of the product. -/
def segWidth (n d : ℕ) : ℕ := 2 * n.size + 3 * d.size + 2

/-- The cost of binary segmentation with `b`-bit digits for at most `d` coefficients, with
lengths of at most `K` bits: the big product, the two packings and the unpacking (each a
halving recursion), and the bookkeeping. -/
def mulNatBound (C : CostModel) (b d K : ℕ) : ℕ :=
  C.mul (b * d) (b * d) +
    3 * halvingBound (2 * C.unit + 6 * C.add (2 * b) (2 * b))
      (4 * C.unit + 4 * C.add K K + C.mul b.size K) (2 * d) + (5 * d + 8) * C.lin K

/-- **Cost of Algorithm 9.6.1** with `b`-bit digits, for coefficients of at most `w ≥ b`
bits whose product has coefficients below `2^b` (the condition of `mulNat_eq`). -/
@[cost_le] theorem mulNat_cost_le (C : CostModel) {b w d K : ℕ} (hb : 1 ≤ b) (hbw : b ≤ w) (h2K : 2 ≤ K)
    (hdK : (2 * d).size ≤ K) (F G : List ℕ) (hF : ∀ x ∈ F, x < 2 ^ w) (hG : ∀ x ∈ G, x < 2 ^ w)
    (hlF : F.length ≤ d) (hlG : G.length ≤ d) (hprod : ∀ c ∈ mul F G, c < 2 ^ b) :
    costOf C (mulNat b F G) ≤ mulNatBound C w d K := by
  unfold mulNatBound
  by_cases hnil : F = [] ∨ G = []
  · have hz : costOf C (Chapter2.Poly.mul F G) ≤ (5 * d + 1) * C.unit := by
      rcases hnil with rfl | rfl
      · rw [nil_mul_cost]; nlinarith
      · exact (mul_nil_cost C F).trans (Nat.mul_le_mul_right _ (by omega))
    cost_unfold mulNat.counted
    split_ifs <;> cost_bound
  · push_neg at hnil
    obtain ⟨hF0, hG0⟩ := hnil
    have hK' : ∀ m, m ≤ 2 * d → m.size ≤ K := fun m hm ↦ (Nat.size_le_size hm).trans hdK
    have hX : ∀ m, m ≤ 2 * d → C.mul b.size (m / 2).size ≤ C.mul w.size K :=
      fun m hm ↦ C.mul_mono (Nat.size_le_size hbw) (hK' _ (by omega))
    have hpack : ∀ L : List ℕ, (∀ x ∈ L, x < 2 ^ w) → L.length ≤ d →
        costOf C (pack b L) ≤ halvingBound (2 * C.unit + 6 * C.add (2 * w) (2 * w))
          (4 * C.unit + 4 * C.add K K + C.mul w.size K) (2 * d) := fun L hL hl ↦ by
      refine (pack_cost_le C hbw h2K L hL (hK' _ (by omega)) (hX _ (by omega))).trans
        (halvingBound_le ?_ ?_ (by omega))
      · have := C.add_mono (show w ≤ 2 * w by omega) (show w ≤ 2 * w by omega); omega
      · omega
    have sF : (pack b F).size ≤ w * d :=
      (size_pack_le_of_le hbw hF).trans (Nat.mul_le_mul_left _ hlF)
    have sG : (pack b G).size ≤ w * d :=
      (size_pack_le_of_le hbw hG).trans (Nat.mul_le_mul_left _ hlG)
    -- the product is the number with the digits of `F G`, which fit in `b` bits
    have sN : (pack b F * pack b G).size ≤ b * (F.length + G.length - 1 + 1) := by
      have hpr : pack b F * pack b G = Nat.ofDigits (2 ^ b) (mul F G) := by
        rw [pack_eq, pack_eq, ofDigits_eq_eval, ofDigits_eq_eval, ofDigits_eq_eval,
          toPolynomial_mul, eval_mul]
      rw [hpr, Nat.size_le]
      refine (Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow (by omega)) hprod).trans_le ?_
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by
        rw [length_mul_nat hF0 hG0]; omega))
    have hX' : ∀ m, m ≤ 2 * d → C.mul b.size (m / 2).size ≤ C.mul w.size K := hX
    have hun := (unpack_cost_le C hb h2K (F.length + G.length - 1) _ sN (hK' _ (by omega))
      (hX' _ (by omega))).trans (halvingBound_le (c' := 2 * C.unit + 6 * C.add (2 * w) (2 * w))
        (d' := 4 * C.unit + 4 * C.add K K + C.mul w.size K)
        (by have := C.add_mono (show 2 * b ≤ 2 * w by omega) (show 2 * b ≤ 2 * w by omega); omega)
        (by omega) (show F.length + G.length - 1 ≤ 2 * d by omega))
    cost_unfold mulNat.counted
    simp only [hF0, hG0, or_self, if_false, List.length_cons] at *
    cost_bound

theorem mulNatBound_mono (C : CostModel) {b b' d K : ℕ} (h : b ≤ b') :
    mulNatBound C b d K ≤ mulNatBound C b' d K := by
  unfold mulNatBound
  have h₁ := C.mul_mono (Nat.mul_le_mul_right d h) (Nat.mul_le_mul_right d h)
  have h₂ := C.add_mono (show 2 * b ≤ 2 * b' by omega) (show 2 * b ≤ 2 * b' by omega)
  have h₃ := C.mul_mono (Nat.size_le_size h) (le_refl K)
  have := halvingBound_le (n := 2 * d) (n' := 2 * d)
    (show 2 * C.unit + 6 * C.add (2 * b) (2 * b) ≤ 2 * C.unit + 6 * C.add (2 * b') (2 * b') by omega)
    (show 4 * C.unit + 4 * C.add K K + C.mul b.size K ≤ 4 * C.unit + 4 * C.add K K + C.mul b'.size K by
      omega) le_rfl
  omega

/-- **Binary segmentation with the width chosen automatically**: the width
`b = size (len · ΣF · ΣG) + 1` costs two sums, two small products and a few steps. -/
@[cost_le] theorem mulNatAuto_cost_le (C : CostModel) {n d : ℕ} (F G : List ℕ) (hF : ∀ x ∈ F, x < n)
    (hG : ∀ x ∈ G, x < n) (hlF : F.length ≤ d) (hlG : G.length ≤ d) :
    costOf C (mulNatAuto F G) ≤ mulNatBound C (segWidth n d) d (2 * segWidth n d) +
      2 * C.mul (2 * segWidth n d) (2 * segWidth n d) + (3 * d + 6) * C.lin (2 * segWidth n d) := by
  set β := segWidth n d with hβ
  have hβv : β = 2 * n.size + 3 * d.size + 2 := rfl
  have hn2 : n < 2 ^ n.size := Nat.lt_size_self n
  have hsum : ∀ L : List ℕ, (∀ x ∈ L, x < n) → L.length ≤ d → L.sum.size ≤ d.size + n.size :=
    fun L hL hl ↦ by
      have : L.sum ≤ d * n := by
        have := List.sum_le_card_nsmul L n (fun x hx ↦ (hL x hx).le)
        simp only [smul_eq_mul] at this
        exact this.trans (Nat.mul_le_mul_right n hl)
      exact (Nat.size_le_size this).trans (size_mul_le d n)
  have hsF := hsum F hF hlF
  have hsG := hsum G hG hlG
  have hprod : (F.sum * G.sum).size ≤ 2 * β := by
    have := size_mul_le F.sum G.sum; omega
  have hlFs := Nat.size_le_size hlF
  have hb : (F.length * (F.sum * G.sum)).size + 1 ≤ β := by
    have := size_mul_le F.length (F.sum * G.sum)
    have := size_mul_le F.sum G.sum
    omega
  -- the product by binary segmentation: coefficients of at most `β` bits, digits of the
  -- chosen width, which the product's coefficients fit (as in `mulNatAuto_eq`)
  have hwid : ∀ x ∈ F ++ G, x < 2 ^ β := fun x hx ↦ by
    have hx : x < n := by
      rcases List.mem_append.mp hx with h | h
      · exact hF x h
      · exact hG x h
    exact hx.trans (hn2.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hcoef : ∀ c ∈ mul F G, c < 2 ^ ((F.length * (F.sum * G.sum)).size + 1) := fun c hc ↦ by
    have h := coeff_mul_le (fun x hx ↦ List.le_sum_of_mem hx) (fun y hy ↦ List.le_sum_of_mem hy)
      c hc
    have h₁ := Nat.lt_size_self (F.length * (F.sum * G.sum))
    have h₂ : 2 ^ (F.length * (F.sum * G.sum)).size ≤
        2 ^ ((F.length * (F.sum * G.sum)).size + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmn := mulNat_cost_le C (b := (F.length * (F.sum * G.sum)).size + 1) (w := β) (d := d)
    (K := 2 * β) (by omega) hb (by omega) (by
      have := size_mul_le 2 d; rw [show Nat.size 2 = 2 by decide] at this; omega)
    F G (fun x hx ↦ hwid x (List.mem_append_left _ hx))
    (fun x hx ↦ hwid x (List.mem_append_right _ hx)) hlF hlG hcoef
  have hSF := (CostM.sum_cost_le_nat C (k := 2 * β) F (by omega)).trans
    (Nat.mul_le_mul (show F.length + 1 ≤ d + 1 by omega) (le_refl (C.lin (2 * β))))
  have hSG := (CostM.sum_cost_le_nat C (k := 2 * β) G (by omega)).trans
    (Nat.mul_le_mul (show G.length + 1 ≤ d + 1 by omega) (le_refl (C.lin (2 * β))))
  cost_unfold mulNatAuto.counted
  cost_bound

@[val_le] theorem length_mul_le_nat (F G : List ℕ) : (mul F G).length ≤ F.length + G.length := by
  by_cases hF : F = []
  · subst hF; simp [mul]
  by_cases hG : G = []
  · subst hG
    induction F with
    | nil => simp [mul]
    | cons a F ih =>
      by_cases hF' : F = []
      · subst hF'; simp [mul, add, smul]
      · have := ih hF'; simp only [mul, smul, List.map_nil, add, List.length_cons] at this ⊢; omega
  · rw [length_mul_nat hF hG]; omega

/-- The bound of `mulMod_cost_le`: binary segmentation at width `β = segWidth n d`, and a
reduction modulo `n` of each of the (at most `2d`) coefficients of the product. -/
def mulModBound (C : CostModel) (n d : ℕ) : ℕ :=
  mulNatBound C (segWidth n d) d (2 * segWidth n d) +
    2 * C.mul (2 * segWidth n d) (2 * segWidth n d) +
    (3 * d + 6) * C.lin (2 * segWidth n d) + 2 * d * C.divMod (segWidth n d) n.size +
    (4 * d + 5) * C.unit

/-- **Cost of a product in `Z_n[t]` by binary segmentation** (Algorithm 9.6.1), for
polynomials with at most `d` coefficients: one multiplication of integers of at most
`segWidth n d · d` bits, the packings and the unpacking (`O(d log d)` steps on numbers of
`O(log n + log d)` bits), and `2d` reductions modulo `n`.  With a quasi-linear integer
multiplication this is quasi-linear in `d log n`. -/
@[cost_le] theorem mulMod_cost_le (C : CostModel) {n d : ℕ} [NeZero n] (f g : Chapter2.Poly (ZMod n))
    (hf : f.length ≤ d) (hg : g.length ≤ d) :
    costOf C (mulMod n f g) ≤ mulModBound C n d := by
  set β := segWidth n d with hβ
  have hβv : β = 2 * n.size + 3 * d.size + 2 := rfl
  set F := f.map ZMod.val with hFdef
  set G := g.map ZMod.val with hGdef
  have hF : ∀ x ∈ F, x < n := by
    simp only [hFdef, List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact ZMod.val_lt a
  have hG : ∀ x ∈ G, x < n := by
    simp only [hGdef, List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact ZMod.val_lt a
  have hlF : F.length ≤ d := by simp [hFdef, hf]
  have hlG : G.length ≤ d := by simp [hGdef, hg]
  have hA := mulNatAuto_cost_le C F G hF hG hlF hlG
  -- the coefficients of the product, reduced modulo `n`
  have hP : mulNatAuto F G = mul F G := mulNatAuto_eq F G
  have hlen : (mulNatAuto F G).length ≤ 2 * d := by
    rw [hP]; have := length_mul_le_nat F G; omega
  have hcoef : ∀ c ∈ mulNatAuto F G, c.size ≤ β := fun c hc ↦ by
    rw [hP] at hc
    have h := coeff_mul_le (A := n) (A' := n) (fun x hx ↦ (hF x hx).le) (fun y hy ↦ (hG y hy).le)
      c hc
    have := Nat.size_le_size (h.trans (Nat.mul_le_mul_right (n * n) hlF))
    have := size_mul_le d (n * n)
    have := size_mul_le n n
    omega
  have hred : (List.map (fun a => C.divMod a.size n.size) (mulNatAuto F G)).sum ≤
      2 * d * C.divMod β n.size :=
    (sum_map_le_length_mul _ _ fun c hc ↦ C.divMod_mono _ (hcoef c hc)).trans
      (Nat.mul_le_mul_right _ hlen)
  have hu : ((mulNatAuto F G).length + 1) * C.unit ≤ (2 * d + 1) * C.unit :=
    Nat.mul_le_mul_right _ (by omega)
  have hu' : (f.length + 1 + (g.length + 1)) * C.unit ≤ (2 * d + 2) * C.unit :=
    Nat.mul_le_mul_right _ (by omega)
  unfold mulModBound
  cost_unfold mulMod.counted
  rw [← hFdef, ← hGdef]
  nlinarith

end PrimeNumbers.Chapter9