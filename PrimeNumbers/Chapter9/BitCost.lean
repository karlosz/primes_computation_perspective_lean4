import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Common
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# §9.1 Bit complexity: the cost model

Crandall & Pomerance, *Prime Numbers: A Computational Perspective*, Section 9.1
("Tour of grammar-school methods").

The book measures running time in *bit operations*.  This file sets up that measure once.
It depends on nothing else in the project; every algorithm file imports it and states its
running time next to its correctness theorem, in a final section "Running time".

## The layer of abstraction

* `Nat.size n` is the number of bits of `n` (`size_mul_le`, `log_two_le_size`, …).
* A `CostModel` says how many bit operations a multiplication and a division with
  remainder take, as functions of the *bit lengths* of the operands.  It is the book's
  `M(n)` made precise.  Analyses are proved for an arbitrary cost model where possible, so
  they survive a change of multiplication algorithm (Karatsuba, FFT, … of §9.5), and the
  plain operation counts they rest on are kept as theorems of their own.
* `school` is the "grammar-school" model of §9.1: multiplying an `a`-bit by a `b`-bit
  number costs `a b`; dividing an `a`-bit number by a `b`-bit number costs
  `(a - b + 1) b` (one row of work per quotient bit — the book's `O((1 + ln q) ln x)` of
  Exercise 2.6).

## How an algorithm is analysed

For an algorithm `f` we define `fCost C …`, which follows the recursion of `f` branch by
branch and adds up `C.mul`/`C.divMod` at the bit lengths of the *actual operands* of each
big-number operation `f` performs.  Additions, comparisons and shifts are linear in the
bit length and dominated by the multiplications and divisions next to them; they are not
counted.
-/

namespace PrimeNumbers.Chapter9

/-! ## Bit lengths -/

/-- The product of an `a`-bit and a `b`-bit number has at most `a + b` bits. -/
theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_le_of_lt {a b : ℕ} (h : a < b) : a.size ≤ b.size := Nat.size_le_size h.le

/-- `⌊log₂ n⌋ ≤` the bit length of `n` (indeed it is one less, for `n ≠ 0`). -/
theorem log_two_le_size (n : ℕ) : Nat.log 2 n ≤ n.size := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')).le

theorem size_le_self (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self

/-- A sum has at most one bit more than the longer summand. -/
theorem size_add_le (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le, pow_succ]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h₁ : 2 ^ a.size ≤ 2 ^ max a.size b.size :=
    Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h₂ : 2 ^ b.size ≤ 2 ^ max a.size b.size :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  omega

/-- A sum has at most as many bits as its summands together (a bound without `max`). -/
theorem size_add_le_add (a b : ℕ) : (a + b).size ≤ a.size + b.size := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have h₁ := size_add_le a b
  have : 0 < a.size := Nat.size_pos.mpr ha
  have : 0 < b.size := Nat.size_pos.mpr hb
  omega

/-- A product plus a carry stays below the product of the bounds: `p q + c < A B`.  (So the
operand `x y + c` of a modular multiplication with `x, y, c < n` has at most `2 size n`
bits.) -/
theorem mul_add_lt_mul_of_lt_left {p q c A B : ℕ} (hp : p < A) (hq : q < B) (hc : c < A) :
    p * q + c < A * B := by
  obtain ⟨A, rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  have := Nat.mul_le_mul (Nat.lt_succ_iff.mp hp) (Nat.lt_succ_iff.mp hq)
  nlinarith

theorem mul_add_lt_mul_of_lt_right {p q c A B : ℕ} (hp : p < A) (hq : q < B) (hc : c < B) :
    p * q + c < A * B := by
  rw [Nat.mul_comm p, Nat.mul_comm A]; exact mul_add_lt_mul_of_lt_left hq hp hc

/-! ## Cost models -/

/-- A cost model: what each primitive of the machine costs.  Nothing an algorithm does is
free: every call of a function costs one `unit` (its constructors, matches and branches
included), list and array steps are charged by the library's counted functions, and every
arithmetic operation is charged by the bit lengths of its operands. -/
structure CostModel where
  /-- bit operations to multiply an `a`-bit number by a `b`-bit number -/
  mul : ℕ → ℕ → ℕ
  /-- bit operations to divide an `a`-bit number by a `b`-bit number, with remainder -/
  divMod : ℕ → ℕ → ℕ
  /-- bit operations per bit of a linear-time operation (an addition, a subtraction, a
  comparison, a shift, a multiplication or division by a power of two): such an operation
  on an `a`-bit and a `b`-bit number costs `addRate · (max a b + 1)` (`CostModel.add`) -/
  addRate : ℕ
  /-- the cost of one step: a function call, a list cell visited, an array access -/
  unit : ℕ
  /-- multiplying longer numbers costs at least as much -/
  mul_mono : ∀ {a a' b b' : ℕ}, a ≤ a' → b ≤ b' → mul a b ≤ mul a' b'
  /-- dividing a longer number (by the same divisor length) costs at least as much -/
  divMod_mono : ∀ {a a' : ℕ} (b : ℕ), a ≤ a' → divMod a b ≤ divMod a' b

attribute [gcongr] CostModel.mul_mono CostModel.divMod_mono

/-- A linear-time operation on an `a`-bit and a `b`-bit number. -/
def CostModel.add (C : CostModel) (a b : ℕ) : ℕ := C.addRate * (max a b + 1)

@[gcongr] theorem CostModel.add_mono (C : CostModel) {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    C.add a b ≤ C.add a' b' :=
  Nat.mul_le_mul_left _ (by omega)

/-- A linear operation on `w n`-bit numbers costs at most `n` operations on `w`-bit ones. -/
theorem CostModel.add_mul_le (C : CostModel) {w n : ℕ} (hn : 1 ≤ n) :
    C.add (w * n) (w * n) ≤ n * C.add w w := by
  unfold CostModel.add
  simp only [max_self]
  nlinarith [Nat.zero_le C.addRate, Nat.zero_le w]

/-- **The grammar-school cost model (§9.1).**  Long multiplication of an `a`-bit by a
`b`-bit number takes `a b` bit operations; long division of an `a`-bit number by a `b`-bit
number produces at most `a - b + 1` quotient bits, each costing a `b`-bit subtraction; an
addition (ripple carry) or comparison takes `max a b + 1`; a step takes one. -/
@[simps] def school : CostModel where
  mul a b := a * b
  divMod a b := (a - b + 1) * b
  addRate := 1
  unit := 1
  mul_mono h₁ h₂ := Nat.mul_le_mul h₁ h₂
  divMod_mono b h := Nat.mul_le_mul_right b (by omega)

/-! ### Worst cases over the inputs of a given bit length -/

/-- The largest value of `g` on the numbers of at most `k` bits. -/
def maxOnBits (k : ℕ) (g : ℕ → ℕ) : ℕ := (Finset.range (2 ^ k)).sup g

theorem le_maxOnBits {k x : ℕ} (g : ℕ → ℕ) (hx : x.size ≤ k) : g x ≤ maxOnBits k g :=
  Finset.le_sup (f := g) (Finset.mem_range.mpr (Nat.size_le.mp hx))

@[gcongr] theorem maxOnBits_mono (g : ℕ → ℕ) : Monotone (maxOnBits · g) := fun _ _ h ↦
  Finset.sup_mono (Finset.range_subset_range.mpr (Nat.pow_le_pow_right (by norm_num) h))

theorem maxOnBits_le {k B : ℕ} {g : ℕ → ℕ} (h : ∀ x, x.size ≤ k → g x ≤ B) :
    maxOnBits k g ≤ B :=
  Finset.sup_le fun x hx ↦ h x (Nat.size_le.mpr (Finset.mem_range.mp hx))

/-- The largest value of `g` on pairs of numbers of at most `k` bits. -/
def maxOnBits₂ (k : ℕ) (g : ℕ → ℕ → ℕ) : ℕ := maxOnBits k fun x ↦ maxOnBits k (g x)

theorem le_maxOnBits₂ {k x y : ℕ} (g : ℕ → ℕ → ℕ) (hx : x.size ≤ k) (hy : y.size ≤ k) :
    g x y ≤ maxOnBits₂ k g :=
  (le_maxOnBits (g x) hy).trans (le_maxOnBits (fun x ↦ maxOnBits k (g x)) hx)

theorem maxOnBits₂_le {k B : ℕ} {g : ℕ → ℕ → ℕ}
    (h : ∀ x y, x.size ≤ k → y.size ≤ k → g x y ≤ B) : maxOnBits₂ k g ≤ B :=
  maxOnBits_le fun x hx ↦ maxOnBits_le fun y hy ↦ h x y hx hy

@[gcongr] theorem maxOnBits₂_mono (g : ℕ → ℕ → ℕ) : Monotone (maxOnBits₂ · g) := fun _ _ h ↦
  maxOnBits₂_le fun _ _ hx hy ↦ le_maxOnBits₂ g (hx.trans h) (hy.trans h)

/-- The worst cost of a division of numbers of at most `k` bits (a division is not more
expensive for a longer dividend, but may be for a shorter divisor). -/
def CostModel.divBound (C : CostModel) (k : ℕ) : ℕ := (Finset.range (k + 1)).sup (C.divMod k)

theorem CostModel.divMod_le_divBound (C : CostModel) {a b k : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    C.divMod a b ≤ C.divBound k :=
  (C.divMod_mono b ha).trans (Finset.le_sup (f := C.divMod k) (Finset.mem_range.mpr (by omega)))

@[gcongr] theorem CostModel.divBound_mono (C : CostModel) : Monotone C.divBound := fun a b h ↦
  Finset.sup_le fun c hc ↦ C.divMod_le_divBound (Nat.le_refl a |>.trans h)
    (by have := Finset.mem_range.mp hc; omega)

theorem CostModel.mul_le_mul_bound (C : CostModel) {a b k : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    C.mul a b ≤ C.mul k k := C.mul_mono ha hb

theorem school_divBound_le (k : ℕ) : school.divBound k ≤ (k + 1) * k :=
  Finset.sup_le fun b hb ↦ by
    have := Finset.mem_range.mp hb
    show (k - b + 1) * b ≤ _
    exact Nat.mul_le_mul (by omega) (by omega)

/-! ### Counting models

An *operation count* is the cost under a model that charges `1` for the operations counted
and `0` for the rest: so the number of multiplications, divisions or writes an algorithm
performs is derived from its code exactly like its bit complexity. -/

/-- The model charging `m` per multiplication, `d` per division and `u` per step, and
nothing for linear-time operations. -/
@[simps] def counting (m d u : ℕ) : CostModel where
  mul _ _ := m
  divMod _ _ := d
  addRate := 0
  unit := u
  mul_mono _ _ := le_rfl
  divMod_mono _ _ := le_rfl

/-- Counts multiplications (a product of residues — multiply and reduce — counts once). -/
abbrev mulCount : CostModel := counting 1 0 0
/-- Counts divisions with remainder. -/
abbrev divCount : CostModel := counting 0 1 0
/-- Counts multiplications and divisions. -/
abbrev opCount : CostModel := counting 1 1 0
/-- Counts elementary steps (memory writes). -/
abbrev writeCount : CostModel := counting 0 0 1

theorem school_divMod_self (k : ℕ) : school.divMod k k = k := by simp
@[simp] theorem school_add (a b : ℕ) : school.add a b = max a b + 1 := by
  simp [CostModel.add, school]
@[simp] theorem counting_add (m d u a b : ℕ) : (counting m d u).add a b = 0 := by
  simp [CostModel.add]

/-- One "multiply two residues and reduce" modulo a `k`-bit modulus: the unit of work of
all modular algorithms. -/
def CostModel.mulMod (C : CostModel) (k : ℕ) : ℕ := C.mul k k + C.divMod (2 * k) k

/-- One step on numbers of at most `k` bits: a call (or a list or array step) and one
linear-time operation (an addition, a comparison, a shift).  The unit of the bookkeeping
around the multiplications and divisions. -/
def CostModel.lin (C : CostModel) (k : ℕ) : ℕ := C.unit + C.add k k

@[simp] theorem school_lin (k : ℕ) : school.lin k = k + 2 := by
  simp only [CostModel.lin, school_add, max_self]; rw [show school.unit = 1 from rfl]; omega

@[simp] theorem counting_mulMod (m d u k : ℕ) : (counting m d u).mulMod k = m + d := rfl

/-- In the grammar-school model a modular multiplication costs `2k² + k ≤ 2 (k + 1)²`. -/

theorem school_mulMod (k : ℕ) : school.mulMod k = 2 * k ^ 2 + k := by
  simp only [CostModel.mulMod, school]
  rw [show 2 * k - k + 1 = k + 1 by omega]
  ring

/-- Multiplying two residues modulo `m` and reducing costs at most `C.mulMod (size m)`. -/
theorem mul_add_divMod_le (C : CostModel) {a b m : ℕ} (ha : a < m) (hb : b < m) :
    C.mul a.size b.size + C.divMod (a * b).size m.size ≤ C.mulMod m.size := by
  refine Nat.add_le_add (C.mul_mono (size_le_of_lt ha) (size_le_of_lt hb))
    (C.divMod_mono _ ?_)
  have := size_mul_le a b
  have := size_le_of_lt ha
  have := size_le_of_lt hb
  omega

/-! ## Halving recursions -/

/-- `f a + f b ≤ f (a + b)` for `a, b ≥ 1`: on each level of a halving recursion the work of
the halves adds up to at most that of the whole. -/
def Superadditive (f : ℕ → ℕ) : Prop := ∀ ⦃a b⦄, 1 ≤ a → 1 ≤ b → f a + f b ≤ f (a + b)

theorem Superadditive.add {f g : ℕ → ℕ} (hf : Superadditive f) (hg : Superadditive g) :
    Superadditive fun m ↦ f m + g m := fun a b ha hb ↦ by
  have := hf ha hb; have := hg ha hb; dsimp only; omega

/-- With a monotone weight: `w a f a + w b f b ≤ w (a + b) (f a + f b) ≤ w (a + b) f (a + b)`. -/
theorem Superadditive.mul_mono {f w : ℕ → ℕ} (hf : Superadditive f) (hw : Monotone w) :
    Superadditive fun m ↦ w m * f m := fun a b ha hb ↦ by
  have := Nat.mul_le_mul_right (f a) (hw (Nat.le_add_right a b))
  have := Nat.mul_le_mul_right (f b) (hw (Nat.le_add_left b a))
  have := Nat.mul_le_mul_left (w (a + b)) (hf ha hb)
  dsimp only; nlinarith

/-- `m ↦ m · w m` for a monotone weight `w` (a constant one: `m ↦ m c`). -/
theorem _root_.Monotone.superadditive_mul {w : ℕ → ℕ} (hw : Monotone w) :
    Superadditive fun m ↦ m * w m := fun a b _ _ ↦ by
  have := Nat.mul_le_mul_left a (hw (Nat.le_add_right a b))
  have := Nat.mul_le_mul_left b (hw (Nat.le_add_left b a))
  dsimp only; rw [Nat.add_mul]; omega

theorem Superadditive.comp_mul {f : ℕ → ℕ} (hf : Superadditive f) {k : ℕ} (hk : 1 ≤ k) :
    Superadditive fun m ↦ f (k * m) := fun a b ha hb ↦ by
  dsimp only; rw [Nat.mul_add]; exact hf (by nlinarith) (by nlinarith)

/-- A superadditive function of a monotone parameter `w m`, monotone in the parameter. -/
theorem Superadditive.of_param {g : ℕ → ℕ → ℕ} {w : ℕ → ℕ} (hg : ∀ p, Superadditive (g p))
    (hmono : ∀ m, Monotone (g · m)) (hw : Monotone w) : Superadditive fun m ↦ g (w m) m :=
  fun a b ha hb ↦ by
    have := hmono a (hw (Nat.le_add_right a b))
    have := hmono b (hw (Nat.le_add_left b a))
    have := hg (w (a + b)) ha hb
    dsimp only at *; omega

/-- **The master theorem for halving recursions.**  A problem of size `n` above a threshold
`L ≥ 1` splits into two of sizes `⌊n/2⌋` and `⌈n/2⌉` (passing them the invariant `I`) at a
cost of `F n + d` beyond theirs, and one of size at most `L` costs at most `G n + e`.  With `F`
and `G` superadditive, a problem of size `n` costs at most `⌈log₂ n⌉ F n + G n + n e + (n - 1) d`
(for `n ≥ 1`): the work `F` of each of the `⌈log₂ n⌉` levels, `G` and `e` over the leaves, `d`
per node. -/
theorem halving_master {α : Type*} (size : α → ℕ) (I : α → Prop) (T : α → ℕ)
    {F G : ℕ → ℕ} {L d e : ℕ} (hL : 1 ≤ L)
    (hF : Superadditive F) (hG : Superadditive G)
    (leaf : ∀ x, I x → size x ≤ L → T x ≤ G (size x) + e)
    (node : ∀ x, I x → L < size x → ∃ y z, I y ∧ I z ∧ size y = size x / 2 ∧
      size z = size x - size x / 2 ∧ T x ≤ T y + T z + F (size x) + d) :
    ∀ x, I x → 1 ≤ size x →
      T x ≤ Nat.clog 2 (size x) * F (size x) + G (size x) + size x * e + (size x - 1) * d := by
  intro x hx hx1
  induction h : size x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  by_cases hn : n ≤ L
  · have := leaf x hx (h ▸ hn)
    rw [h] at this
    have : e ≤ n * e := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨y, z, hy, hz, sy, sz, hT⟩ := node x hx (by omega)
  rw [h] at sy sz hT
  have ihy := ih (n / 2) (by omega) y hy (by omega) sy
  have ihz := ih (n - n / 2) (by omega) z hz (by omega) sz
  -- the halves have one level fewer: `⌈log₂ ⌈n/2⌉⌉ = ⌈log₂ n⌉ - 1`
  have hc : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := Nat.clog_of_two_le (by norm_num) (by omega)
  have c₁ := Nat.mul_le_mul_right (F (n / 2))
    (Nat.clog_mono_right 2 (show n / 2 ≤ (n + 1) / 2 by omega))
  rw [show n - n / 2 = (n + 1) / 2 by omega] at ihz
  have f := Nat.mul_le_mul_left (Nat.clog 2 ((n + 1) / 2))
    (hF (a := n / 2) (b := (n + 1) / 2) (by omega) (by omega))
  have g := hG (a := n / 2) (b := (n + 1) / 2) (by omega) (by omega)
  rw [show n / 2 + (n + 1) / 2 = n by omega] at f g
  have hd : (n / 2 - 1) * d + ((n + 1) / 2 - 1) * d + d = (n - 1) * d := by
    rw [← Nat.add_mul, ← Nat.succ_mul]; congr 1; omega
  have he : n / 2 * e + (n + 1) / 2 * e = n * e := by rw [← Nat.add_mul]; congr 1; omega
  rw [hc]
  nlinarith

/-- `c n ⌈log₂ n⌉ + d (2n - 1)` (and `d` for the empty input): the cost of a halving recursion
with work `c` per element on each level and `d` per node and per leaf. -/
def halvingBound (c d n : ℕ) : ℕ := c * max n 1 * Nat.clog 2 (max n 1) + d * (2 * max n 1 - 1)

/-- The master theorem for work `c n + d` at a node of size `n` and `d` at a leaf. -/
theorem halvingBound_of_rec {α : Type*} (size : α → ℕ) (I : α → Prop) (T : α → ℕ) {c d : ℕ}
    (leaf : ∀ x, I x → size x ≤ 1 → T x ≤ d)
    (node : ∀ x, I x → 1 < size x → ∃ y z, I y ∧ I z ∧ size y = size x / 2 ∧
      size z = size x - size x / 2 ∧ T x ≤ T y + T z + c * size x + d) :
    ∀ x, I x → T x ≤ halvingBound c d (size x) := by
  intro x hx
  unfold halvingBound
  rcases Nat.eq_zero_or_pos (size x) with h0 | h1
  · have := leaf x hx (by omega); simp [h0]; omega
  have := halving_master size I T (F := (c * ·)) (G := fun _ ↦ 0) le_rfl
    (fun a b _ _ ↦ (Nat.mul_add c a b).ge) (fun _ _ _ _ ↦ le_rfl)
    (fun x hx h ↦ by simpa using leaf x hx h) node x hx h1
  rw [show max (size x) 1 = size x by omega]
  have : size x * d + (size x - 1) * d = d * (2 * size x - 1) := by
    rw [← Nat.add_mul, Nat.mul_comm]; congr 1; omega
  nlinarith

theorem halvingBound_mono (c d : ℕ) : Monotone (halvingBound c d) := fun a b h ↦ by
  unfold halvingBound
  have h' : max a 1 ≤ max b 1 := max_le_max h le_rfl
  have := Nat.clog_mono_right 2 h'
  have := Nat.mul_le_mul (Nat.mul_le_mul_left c h') this
  have := Nat.mul_le_mul_left d (show 2 * max a 1 - 1 ≤ 2 * max b 1 - 1 by omega)
  omega

@[gcongr] theorem halvingBound_le {c c' d d' n n' : ℕ} (hc : c ≤ c') (hd : d ≤ d') (hn : n ≤ n') :
    halvingBound c d n ≤ halvingBound c' d' n' := by
  refine le_trans ?_ (halvingBound_mono c' d' hn)
  unfold halvingBound
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) le_rfl)
    (Nat.mul_le_mul_right _ hd)

theorem halvingBound_superadditive (c d : ℕ) : Superadditive (halvingBound c d) :=
  fun a b ha hb ↦ by
  unfold halvingBound
  rw [show max a 1 = a by omega, show max b 1 = b by omega, show max (a + b) 1 = a + b by omega]
  have h₁ := Nat.mul_le_mul_left (c * a) (Nat.clog_mono_right 2 (Nat.le_add_right a b))
  have h₂ := Nat.mul_le_mul_left (c * b) (Nat.clog_mono_right 2 (Nat.le_add_left b a))
  have h₃ : d * (2 * a - 1) + d * (2 * b - 1) ≤ d * (2 * (a + b) - 1) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have h₄ : c * a * Nat.clog 2 (a + b) + c * b * Nat.clog 2 (a + b) =
      c * (a + b) * Nat.clog 2 (a + b) := by ring
  omega

end PrimeNumbers.Chapter9
