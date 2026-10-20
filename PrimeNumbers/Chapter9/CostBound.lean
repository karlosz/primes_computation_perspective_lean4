import PrimeNumbers.Chapter9.Counted

/-!
# `cost_bound`: closing cost inequalities

After `cost_unfold`, a running-time goal is an inequality between a sum of charges — `C.add`,
`C.mul`, `C.divMod`, `C.unit` at the bit lengths of the actual operands, and costs of
callees — and a bound written with worst-case quantities: `C.lin k` (one step on `k`-bit
numbers), `C.mul k k`, `C.divBound k`, `C.mulMod k`.

`cost_bound` bounds every charge on the left by every quantity on the right that it can,
proving the size conditions from the hypotheses (`x.size ≤ k`, `x < n`, …), and closes the
goal by linear arithmetic with these facts and the hypotheses (e.g. the bounds of callees or
an induction hypothesis).  So a cost proof is `cost_unfold f.counted` followed by
`cost_bound`, with the size facts and callee bounds it needs stated as `have`s.
-/

namespace PrimeNumbers.Chapter9

open Lean Meta Elab Tactic

/-- The constants of cost terms: cost models, costs of counted code, and the cost classes. -/
def isCostConst (c : Name) : Bool :=
  [``CostModel, ``CostM, ``MulCost, ``DivCost, ``PowCost, ``AddCost, ``CmpCost, ``InvCost,
    ``CastCost, ``HashCost].any (·.isPrefixOf c)

/-- `size_le`: prove `a ≤ b` between bit lengths (and other naturals) from the hypotheses:
by `omega`; through `Nat.size_le_size`; or through a hypothesis `t.size ≤ k` with `x ≤ t`. -/
syntax "size_le" : tactic

/-- Try `x.size ≤ k` through a hypothesis `h : t.size ≤ k'` with `x ≤ t` and `k' ≤ k`. -/
elab "size_le_hyp" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let_expr LE.le _ _ lhs _ := ty | continue
    let_expr Nat.size _ := lhs | continue
    let s ← saveState
    try
      evalTactic (← `(tactic| exact le_trans (Nat.size_le_size (by omega))
        (le_trans $(mkIdent d.userName) (by omega))))
      return
    catch _ => s.restore
  throwError "size_le_hyp: no hypothesis applies"

theorem _root_.Nat.size_two : Nat.size 2 = 2 := by decide

/-- The bit length of a numeral, evaluated (`Nat.size 8 = 4`), as charged for operations
with literals. -/
simproc_decl reduceNatSize (Nat.size _) := fun e => do
  let_expr Nat.size n := e | return .continue
  let some k := n.nat? | return .continue
  let r := mkNatLit k.size
  let pf ← mkDecideProof (← mkEq e r)
  return .done { expr := r, proof? := some pf }

/-- The arguments `t` of the bit lengths `t.size` in an expression. -/
partial def sizeArgs (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``Nat.size 1 then
    let t := e.appArg!
    if acc.contains t then acc else acc.push t
  else match e with
    | .app f a => sizeArgs a (sizeArgs f acc)
    | .mdata _ b => sizeArgs b acc
    | _ => acc

/-- Try `x.size ≤ R` through a bit length `t.size` in `R` with `x ≤ t`. -/
elab "size_le_goal" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let_expr LE.le _ _ lhs rhs := tgt | throwError "size_le_goal: not an inequality"
  let_expr Nat.size x := lhs | throwError "size_le_goal: not a bit length"
  for t in sizeArgs rhs do
    let s ← saveState
    try
      let xs ← Term.exprToSyntax x
      let ts ← Term.exprToSyntax t
      evalTactic (← `(tactic| exact le_trans (Nat.size_le_size (show $xs ≤ $ts by omega))
        (by omega)))
      return
    catch _ => s.restore
  throwError "size_le_goal: no bit length applies"

macro_rules
  | `(tactic| size_le) => `(tactic| first
      | omega
      | (simp only [Nat.size_zero, Nat.size_one, Nat.size_two, reduceNatSize] at *; omega)
      | exact Nat.size_le_size (by omega)
      | size_le_hyp
      | size_le_goal)

/-- One step on numbers of at most `k` bits: a call and a linear-time operation. -/
theorem CostModel.unit_le_lin (C : CostModel) (k : ℕ) : C.unit ≤ C.lin k :=
  Nat.le_add_right _ _

theorem CostModel.add_le_lin (C : CostModel) {a b k : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    C.add a b ≤ C.lin k :=
  (C.add_mono ha hb).trans (Nat.le_add_left _ _)

theorem CostModel.lin_mono (C : CostModel) {a b : ℕ} (h : a ≤ b) : C.lin a ≤ C.lin b :=
  Nat.add_le_add_left (C.add_mono h h) _

theorem CostModel.mul_le_mulMod (C : CostModel) {a b k : ℕ} (ha : a ≤ k) (hb : b ≤ k) :
    C.mul a b ≤ C.mulMod k :=
  (C.mul_mono ha hb).trans (Nat.le_add_right _ _)

/-! ### Halving recursions

A recursion that splits its input of size `n ≥ 2` into halves `⌊n/2⌋` and `⌈n/2⌉`, at a cost
of `c n + d` for the split and the join, costs at most `halvingBound c d n`
(`halvingBound_step`): `c n ⌈log₂ n⌉` for the levels and `d` per node. -/

/-- `c n ⌈log₂ n⌉ + d (2n - 1)`, for `n ≥ 1` (and `d` for the empty input). -/
def halvingBound (c d n : ℕ) : ℕ := c * max n 1 * Nat.clog 2 (max n 1) + d * (2 * max n 1 - 1)

theorem halvingBound_le_one (c d : ℕ) {n : ℕ} (hn : n ≤ 1) : halvingBound c d n = d := by
  have : max n 1 = 1 := by omega
  simp [halvingBound, this]

theorem halvingBound_step (c d : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    halvingBound c d (n / 2) + halvingBound c d (n - n / 2) + (c * n + d) ≤ halvingBound c d n := by
  have hL : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    rw [Nat.clog_of_one_lt (by norm_num) (by omega), show n + 2 - 1 = n + 1 by omega]
  have h₁ : Nat.clog 2 (n / 2) ≤ Nat.clog 2 ((n + 1) / 2) := Nat.clog_mono_right _ (by omega)
  have h₂ : n - n / 2 = (n + 1) / 2 := by omega
  unfold halvingBound
  rw [h₂, show max n 1 = n by omega, show max (n / 2) 1 = n / 2 by omega,
    show max ((n + 1) / 2) 1 = (n + 1) / 2 by omega, hL]
  set L := Nat.clog 2 ((n + 1) / 2)
  have h₃ : c * (n / 2) * Nat.clog 2 (n / 2) ≤ c * (n / 2) * L := Nat.mul_le_mul_left _ h₁
  have h₄ : n / 2 + (n + 1) / 2 = n := by omega
  have h₅ : d * (2 * (n / 2) - 1) + d * (2 * ((n + 1) / 2) - 1) + d = d * (2 * n - 1) := by
    rw [← Nat.mul_add, ← Nat.mul_add_one]; congr 1; omega
  have h₆ : c * (n / 2) * L + c * ((n + 1) / 2) * L = c * n * L := by
    rw [← Nat.add_mul, ← Nat.mul_add, h₄]
  have h₇ : c * n * (L + 1) = c * n * L + c * n := by ring
  linarith [h₃, h₅]

theorem halvingBound_mono (c d : ℕ) : Monotone (halvingBound c d) := fun a b h ↦ by
  unfold halvingBound
  have h' : max a 1 ≤ max b 1 := max_le_max h le_rfl
  have := Nat.clog_mono_right 2 h'
  have := Nat.mul_le_mul (Nat.mul_le_mul_left c h') this
  have := Nat.mul_le_mul_left d (show 2 * max a 1 - 1 ≤ 2 * max b 1 - 1 by omega)
  omega

theorem halvingBound_le {c c' d d' n n' : ℕ} (hc : c ≤ c') (hd : d ≤ d') (hn : n ≤ n') :
    halvingBound c d n ≤ halvingBound c' d' n' := by
  refine le_trans ?_ (halvingBound_mono c' d' hn)
  unfold halvingBound
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) le_rfl)
    (Nat.mul_le_mul_right _ hd)

theorem halvingBound_superadditive (c d : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    halvingBound c d a + halvingBound c d b ≤ halvingBound c d (a + b) := by
  unfold halvingBound
  rw [show max a 1 = a by omega, show max b 1 = b by omega, show max (a + b) 1 = a + b by omega]
  have h₁ := Nat.mul_le_mul_left (c * a) (Nat.clog_mono_right 2 (Nat.le_add_right a b))
  have h₂ := Nat.mul_le_mul_left (c * b) (Nat.clog_mono_right 2 (Nat.le_add_left b a))
  have h₃ : d * (2 * a - 1) + d * (2 * b - 1) ≤ d * (2 * (a + b) - 1) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have h₄ : c * a * Nat.clog 2 (a + b) + c * b * Nat.clog 2 (a + b) =
      c * (a + b) * Nat.clog 2 (a + b) := by ring
  omega

/-- `cost_atom_le`: prove `A ≤ B` for one charge `A` and one worst-case quantity `B`. -/
macro "cost_atom_le" : tactic => `(tactic| first
  | exact le_rfl
  | exact CostModel.unit_le_lin _ _
  | exact CostModel.add_le_lin _ (by size_le) (by size_le)
  | exact CostModel.add_mono _ (by size_le) (by size_le)
  | exact CostModel.lin_mono _ (by size_le)
  | exact CostModel.mul_mono _ (by size_le) (by size_le)
  | exact CostModel.mul_le_mulMod _ (by size_le) (by size_le)
  | exact CostModel.divMod_le_divBound _ (by size_le) (by size_le)
  | exact CostModel.divMod_mono _ _ (by size_le)
  | exact CostModel.divBound_mono _ (by size_le))

/-- The charges and worst-case quantities in an expression: applications of the fields of a
cost model and of `lin`, `divBound`, `mulMod` (outside binders). -/
private partial def atoms (e : Expr) : StateT (Array Expr) MetaM Unit := do
  if e.hasLooseBVars then return
  if let some c := e.getAppFn.constName? then
    let arity : Option Nat := match c with
      | ``CostModel.mul | ``CostModel.divMod | ``CostModel.add => some 3
      | ``CostModel.lin | ``CostModel.divBound | ``CostModel.mulMod => some 2
      | ``CostModel.unit => some 1
      | _ => none
    if let some n := arity then
      if e.getAppNumArgs == n then
        unless (← get).contains e do modify (·.push e)
        return
    -- a sum of costs over a list (e.g. the charges of a `map`): one quantity, so that
    -- normalizing inside its function cannot tell it apart from its bound
    if c == ``List.sum && e.getAppNumArgs == 4 &&
        e.getUsedConstants.any (fun c => isCostConst c) then
      unless (← get).contains e do modify (·.push e)
      return
  match e with
  | .app f a => atoms f; atoms a
  | .mdata _ b => atoms b
  | _ => pure ()

/-- The products in an expression (outside binders). -/
private partial def products (e : Expr) : StateT (Array Expr) MetaM Unit := do
  if e.hasLooseBVars then return
  if e.isAppOfArity ``HMul.hMul 6 then
    unless (← get).contains e do modify (·.push e)
  match e with
  | .app f a => products f; products a
  | .mdata _ b => products b
  | _ => pure ()

/-- Can a charge with head `a` be bounded by a quantity with head `b`? -/
private def headsMatch (a b : Expr) : Bool :=
  match a.getAppFn.constName?, b.getAppFn.constName? with
  | some x, some y =>
    (x == y) || (x == ``CostModel.unit && y == ``CostModel.lin) ||
      (x == ``CostModel.add && y == ``CostModel.lin) ||
      (x == ``CostModel.mul && y == ``CostModel.mulMod) ||
      (x == ``CostModel.divMod && y == ``CostModel.divBound)
  | _, _ => false

/-- Prove `a ≤ b` between naturals by `size_le`, remembering the outcome. -/
private def proveLe (memo : IO.Ref (Std.HashMap (Expr × Expr) (Option Expr))) (a b : Expr) :
    TacticM (Option Expr) := do
  if a == b then return some (← mkAppM ``le_refl #[a])
  if let some r := (← memo.get).get? (a, b) then return r
  -- the arithmetic of sizes does not need the hypotheses about costs
  let mut lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (← isProp ty) && (ty.isForall || ty.getUsedConstants.any (fun c =>
        isCostConst c || c == ``halvingBound)) then
      lctx := lctx.erase d.fvarId
  let m ← mkFreshExprMVarAt lctx (← getLocalInstances) (← mkAppM ``LE.le #[a, b])
  let s ← saveState
  let r ← try
      let gs ← Term.withoutErrToSorry <|
        Tactic.run m.mvarId! (evalTactic (← `(tactic| size_le)))
      let pf ← instantiateMVars m
      if gs.isEmpty && !pf.hasSorry then pure (some pf) else s.restore; pure none
    catch _ => s.restore; pure none
  memo.modify (·.insert (a, b) r)
  return r

/-- A proof that the charge `a` is at most the quantity `b`, if the sizes allow. -/
private def boundAtom (memo : IO.Ref (Std.HashMap (Expr × Expr) (Option Expr))) (a b : Expr) :
    TacticM (Option Expr) := do
  let some fa := a.getAppFn.constName? | return none
  let some fb := b.getAppFn.constName? | return none
  let xa := a.getAppArgs
  let xb := b.getAppArgs
  let C := xa[0]!
  unless xb[0]! == C do return none
  let le := proveLe memo
  match fa, fb with
  | ``CostModel.unit, ``CostModel.lin => some <$> mkAppM ``CostModel.unit_le_lin #[C, xb[1]!]
  | ``CostModel.add, ``CostModel.add =>
    let some h₁ ← le xa[1]! xb[1]! | return none
    let some h₂ ← le xa[2]! xb[2]! | return none
    some <$> mkAppM ``CostModel.add_mono #[C, h₁, h₂]
  | ``CostModel.add, ``CostModel.lin =>
    let some h₁ ← le xa[1]! xb[1]! | return none
    let some h₂ ← le xa[2]! xb[1]! | return none
    some <$> mkAppM ``CostModel.add_le_lin #[C, h₁, h₂]
  | ``CostModel.lin, ``CostModel.lin =>
    let some h ← le xa[1]! xb[1]! | return none
    some <$> mkAppM ``CostModel.lin_mono #[C, h]
  | ``CostModel.mul, ``CostModel.mul =>
    let some h₁ ← le xa[1]! xb[1]! | return none
    let some h₂ ← le xa[2]! xb[2]! | return none
    some <$> mkAppM ``CostModel.mul_mono #[C, h₁, h₂]
  | ``CostModel.mul, ``CostModel.mulMod =>
    let some h₁ ← le xa[1]! xb[1]! | return none
    let some h₂ ← le xa[2]! xb[1]! | return none
    some <$> mkAppM ``CostModel.mul_le_mulMod #[C, h₁, h₂]
  | ``CostModel.divMod, ``CostModel.divBound =>
    let some h₁ ← le xa[1]! xb[1]! | return none
    let some h₂ ← le xa[2]! xb[1]! | return none
    some <$> mkAppM ``CostModel.divMod_le_divBound #[C, h₁, h₂]
  | ``CostModel.divMod, ``CostModel.divMod =>
    unless xa[2]! == xb[2]! do return none
    let some h ← le xa[1]! xb[1]! | return none
    some <$> mkAppM ``CostModel.divMod_mono #[C, xa[2]!, h]
  | ``CostModel.divBound, ``CostModel.divBound =>
    let some h ← le xa[1]! xb[1]! | return none
    some <$> mkAppM ``CostModel.divBound_mono #[C, h]
  | _, _ => return none

/-- Bound the charges of the goal `lhs ≤ rhs` (and of the hypotheses about costs) by its
worst-case quantities, adding the facts to the context; with `verbose`, report the charges
that nothing bounds. -/
def costBoundFacts (verbose : Bool) : TacticM Unit := withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let_expr LE.le _ _ lhs rhs := tgt | throwError "cost_bound: the goal is not an inequality"
  -- the quantities to bound by: those of the goal's right side and of the hypotheses about
  -- costs (e.g. `C.add (w n) (w n) ≤ n · C.add w w`)
  let ((), rs₀) ← (atoms rhs).run #[]
  let mut ls : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.getUsedConstants.any (fun c => isCostConst c) &&
        (← isProp ty) && !ty.isForall then
      ls := ((← (atoms ty).run ls)).2
  let rs := ls.foldl (fun r a => if r.contains a then r else r.push a) rs₀
  ls := ((← (atoms lhs).run ls)).2
  let memo ← IO.mkRef ({} : Std.HashMap (Expr × Expr) (Option Expr))
  let mut facts : Array Expr := #[]
  for a in ls do
    if rs.contains a then continue
    let mut bounded := false
    for b in rs do
      if let some p ← boundAtom memo a b then
        facts := facts.push p; bounded := true
    if verbose && !bounded then logInfo m!"cost_bound: nothing bounds {a}"
  let mut g ← getMainGoal
  for p in facts do
    let (_, g') ← (← g.assert `hcost (← inferType p) p).intro1P
    g := g'
  replaceMainGoal [g]

/-- After distributing (`ring_nf`), the products on the right are nonnegative, for steps
like `(k + 1) X ≥ X`. -/
def addProductFacts : TacticM Unit := withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let_expr LE.le _ _ _ rhs := tgt | return
  let ((), ps) ← (products rhs).run #[]
  -- and the products in the hypotheses (which may need to be dropped)
  let mut ps := ps
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (← isProp ty) && !ty.isForall then ps := ((← (products ty).run ps)).2
  let mut g ← getMainGoal
  for p in ps do
    if (← inferType p) == mkConst ``Nat then
      let pf ← mkAppM ``Nat.zero_le #[p]
      let (_, g') ← (← g.assert `hcost0 (← inferType pf) pf).intro1P
      g := g'
  replaceMainGoal [g]

/-- Distribute (`ring_nf`) in the goal and in the hypotheses about costs only (each renamed
first, so that shadowed hypotheses are reached too). -/
def ringNfCosts : TacticM Unit := do
  let mut g ← getMainGoal
  let mut hs : Array Ident := #[]
  let mut i := 0
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.getUsedConstants.any (fun c => isCostConst c) &&
        !ty.isForall &&
        (← g.withContext (isProp ty)) then
      let n := Name.mkSimple s!"cost_h{i}"
      i := i + 1
      g ← g.rename d.fvarId n
      hs := hs.push (mkIdent n)
  replaceMainGoal [g]
  for h in hs do
    evalTactic (← `(tactic| try ring_nf at $h:ident))
  evalTactic (← `(tactic| try ring_nf))

/-- Is this hypothesis about costs (a charge, a cost, a cost bound)? -/
def isCostHyp (ty : Expr) : MetaM Bool := do
  return ty.getUsedConstants.any (fun c => isCostConst c ||
      c == ``halvingBound) && (← isProp ty) && !ty.isForall

/-- `linarith` with the hypotheses about costs only (the arithmetic of sizes is done by
`cost_atom_le` before). -/
def linarithCosts : TacticM Unit := withMainContext do
  -- (shadowed names are reached through `‹_›` of their type)
  let mut hs : Array Term := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isCostHyp ty then hs := hs.push (← `(‹$(← Term.exprToSyntax ty)›))
  evalTactic (← `(tactic| linarith only [$hs,*]))

/-- The opaque quantities of a cost inequality: charges, worst-case quantities, costs of
callees and halving bounds (outside binders). -/
private partial def opaques (e : Expr) : StateT (Array Expr) MetaM Unit := do
  if e.hasLooseBVars then return
  if let some c := e.getAppFn.constName? then
    let arity : Option Nat := match c with
      | ``CostModel.mul | ``CostModel.divMod | ``CostModel.add => some 3
      | ``CostModel.lin | ``CostModel.divBound | ``CostModel.mulMod => some 2
      | ``CostModel.unit => some 1
      | ``CostM.cost => some 3
      | ``halvingBound => some 3
      | ``MulCost.mulCost | ``DivCost.divCost | ``AddCost.addCost | ``CmpCost.cmpCost => some 5
      | ``PowCost.powCost => some 5
      | ``InvCost.invCost | ``CastCost.castCost | ``HashCost.hashCost => some 4
      | _ => none
    if let some n := arity then
      if e.getAppNumArgs == n then
        unless (← get).contains e do modify (·.push e)
        return
    -- a sum of costs over a list (e.g. the charges of a `map`): one quantity, so that
    -- normalizing inside its function cannot tell it apart from its bound
    if c == ``List.sum && e.getAppNumArgs == 4 &&
        e.getUsedConstants.any (fun c => isCostConst c) then
      unless (← get).contains e do modify (·.push e)
      return
  match e with
  | .app f a => opaques f; opaques a
  | .mdata _ b => opaques b
  | _ => pure ()

/-- Clear the hypotheses that are not about costs (sizes, lengths, …): once the charges are
bounded, the final arithmetic does not need them. -/
def clearNonCost : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx).decls.toList.reverse.filterMap id do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (← isProp ty) && !(← isCostHyp ty) then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

/-- Replace the opaque quantities of the goal and of the hypotheses about costs by variables,
so that normalizing the arithmetic does not touch the sizes inside them. -/
def generalizeCosts : TacticM (Array Name) := withMainContext do
  let mut es : Array Expr := #[]
  es := ((← (opaques (← instantiateMVars (← getMainTarget))).run es)).2
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isCostHyp ty then es := ((← (opaques ty).run es)).2
  -- larger quantities first, so that a quantity is replaced before its parts
  let sorted := es.qsort fun a b => a.sizeWithoutSharing > b.sizeWithoutSharing
  let mut names : Array Name := #[]
  for e in sorted do
    let n ← mkFreshUserName `q
    let x := mkIdent n
    let s ← saveState
    try
      evalTactic (← `(tactic| generalize $(← Term.exprToSyntax e) = $x at *))
      evalTactic (← `(tactic| have := Nat.zero_le $x))
      names := names.push n
    catch _ => s.restore
  return names

private partial def summands (e : Expr) : Array Expr :=
  if e.isAppOfArity ``HAdd.hAdd 6 then summands e.appFn!.appArg! ++ summands e.appArg! else #[e]

private partial def factors (e : Expr) : Array Expr :=
  if e.isAppOfArity ``HMul.hMul 6 then factors e.appFn!.appArg! ++ factors e.appArg! else #[e]

/-- Split a monomial into its cost variable (if exactly one) and its other non-numeral
factors. -/
private def splitMonomial (vars : Array FVarId) (m : Expr) : Option (Expr × Array Expr) :=
  let fs := factors m
  let qs := fs.filter fun f => f.isFVar && vars.contains f.fvarId!
  let rest := fs.filter fun f => !(f.isFVar && vars.contains f.fvarId!) && f.nat?.isNone &&
    !f.isRawNatLit
  if qs.size == 1 && !rest.isEmpty then some (qs[0]!, rest) else none

private def prodOf (fs : Array Expr) : MetaM Expr := do
  if fs.isEmpty then return mkNatLit 1
  fs[1:].foldlM (fun acc f => mkAppM ``HMul.hMul #[acc, f]) fs[0]!

/-- For each step-like term `q · t` on the left and `q · T` on the right (`q` a cost, `t`, `T`
lengths or sizes), add `q · t ≤ q · T` when `t ≤ T` follows by `omega` (after cancelling
common factors). -/
def scaleFacts (vars : Array FVarId) : TacticM Unit := withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let_expr LE.le _ _ lhs rhs := tgt | return
  let ls := (summands lhs).filterMap (splitMonomial vars)
  let mut rs := (summands rhs).filterMap (splitMonomial vars)
  -- the step allowances of the hypotheses (e.g. `6 q d ≤ S d` for a node bound)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, l, _) := ty.le? then
      rs := rs ++ (summands l).filterMap (splitMonomial vars)
  let mut facts : Array Expr := #[]
  for (q, fl) in ls do
    for (q', fr) in rs do
      unless q == q' do continue
      -- cancel the common factors
      let common := fl.filter fr.contains
      let tl := fl.filter (!common.contains ·)
      let tr := fr.filter (!common.contains ·)
      if tr.isEmpty then continue
      let t ← prodOf tl
      let T ← prodOf tr
      let X ← prodOf common
      let m ← mkFreshExprMVar (← mkAppM ``LE.le #[t, T])
      let st ← saveState
      try
        let gs ← Term.withoutErrToSorry <| Tactic.run m.mvarId! (evalTactic (← `(tactic| omega)))
        unless gs.isEmpty do st.restore; continue
        let h ← instantiateMVars m
        let h ← mkAppM ``Nat.mul_le_mul_right #[X, h]
        facts := facts.push (← mkAppM ``Nat.mul_le_mul_left #[q, h])
      catch _ => st.restore
  let mut g ← getMainGoal
  for p in facts do
    let (_, g') ← (← g.assert `hscale (← inferType p) p).intro1P
    g := g'
  replaceMainGoal [g]

/-- For each term `t · q` on the left (`q` a cost) and each hypothesis `q ≤ q'` (or
`u + q ≤ u + q'`, as monotonicity of `C.lin` gives) between costs, add `t · q ≤ t · q'`:
a cost bounded by another stays bounded when counted `t` times. -/
def costScaleFacts (vars : Array FVarId) : TacticM Unit := withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let_expr LE.le _ _ lhs _ := tgt | return
  let mut ls := (summands lhs).filterMap (splitMonomial vars)
  let isVar (e : Expr) := e.isFVar && vars.contains e.fvarId!
  let mut les : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.le? | continue
    -- the terms that bound callees (on the right of their bounds) need the scaling too
    ls := ls ++ (summands r).filterMap (splitMonomial vars)
    if isVar l && isVar r then les := les.push (l, d.toExpr)
    else if l.isAppOfArity ``HAdd.hAdd 6 && r.isAppOfArity ``HAdd.hAdd 6 &&
        l.appFn!.appArg! == r.appFn!.appArg! && isVar l.appArg! && isVar r.appArg! then
      try les := les.push (l.appArg!, ← mkAppM ``Nat.le_of_add_le_add_left #[d.toExpr])
      catch _ => pure ()
  let mut facts : Array Expr := #[]
  let mut seen : Array (Expr × Expr) := #[]
  for (q, fl) in ls do
    for (x, h) in les do
      unless x == q do continue
      let f ← prodOf fl
      if seen.contains (f, h) then continue
      seen := seen.push (f, h)
      try facts := facts.push (← mkAppM ``Nat.mul_le_mul_left #[f, h])
      catch _ => pure ()
  let mut g ← getMainGoal
  for p in facts do
    let (_, g') ← (← g.assert `hscale (← inferType p) p).intro1P
    g := g'
  replaceMainGoal [g]

/-- The arithmetic atoms of an expression: its maximal subterms that are not sums, products,
differences or numerals. -/
private partial def arithAtoms (e : Expr) : StateT (Array Expr) MetaM Unit := do
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 ||
      e.isAppOfArity ``HSub.hSub 6 then
    arithAtoms e.appFn!.appArg!; arithAtoms e.appArg!
  else if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``Eq 3 then
    arithAtoms e.appFn!.appArg!; arithAtoms e.appArg!
  else if e.nat?.isSome || e.isRawNatLit then pure ()
  else unless (← get).contains e do modify (·.push e)

/-- Clear the hypotheses unrelated to the goal: keep those that share an arithmetic atom with
the goal, or with a hypothesis kept (closing up), e.g. the bounds of callees and the facts
relating them. -/
def clearUnrelated (vars : Array FVarId) : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut keep : Array Expr := ((← (arithAtoms tgt).run #[])).2
  let mut hyps : Array (FVarId × Array Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (← isProp ty) then
      let as ← if ty.isForall then pure #[] else do pure ((← (arithAtoms ty).run #[])).2
      hyps := hyps.push (d.fvarId, as)
  let mut kept : Array FVarId := #[]
  let mut changed := true
  while changed do
    changed := false
    for (f, as) in hyps do
      if kept.contains f then continue
      let ty ← instantiateMVars (← f.getType)
      if as.any keep.contains || ty.hasAnyFVar (vars.contains ·) then
        kept := kept.push f
        keep := as.foldl (fun k a => if k.contains a then k else k.push a) keep
        changed := true
  let mut g ← getMainGoal
  for (f, _) in hyps.reverse do
    unless kept.contains f do
      try g ← g.clear f catch _ => pure ()
  replaceMainGoal [g]

/-- Give the shadowed hypotheses (`this✝`, …) fresh accessible names, so that the steps
working `at *` reach them too. -/
def renameShadowed : TacticM Unit := do
  let mut g ← getMainGoal
  let mut i := 0
  for d in ← g.withContext getLCtx do
    if d.isImplementationDetail then continue
    let lctx ← g.withContext getLCtx
    let shadowed := match lctx.findFromUserName? d.userName with
      | some d' => d'.fvarId != d.fvarId
      | none => false
    if d.userName.hasMacroScopes || shadowed then
      g ← g.rename d.fvarId (Name.mkSimple s!"cost_s{i}")
      i := i + 1
  replaceMainGoal [g]

/-- The steps of `cost_bound`; with `verbose`, report the charges that nothing bounds. -/
def costBound (verbose : Bool) : TacticM Unit := do
  renameShadowed
  evalTactic (← `(tactic| try simp (config := { zetaDelta := true }) only [CostModel.lin,
    CostModel.mulMod, Nat.size_zero, Nat.size_one, Nat.size_two, reduceNatSize] at *))
  costBoundFacts verbose
  let names ← generalizeCosts
  evalTactic (← `(tactic| try ring_nf at *))
  ringNfCosts
  let vars ← withMainContext do
    let lctx ← getLCtx
    return names.filterMap fun n => (lctx.findFromUserName? n).map (·.fvarId)
  scaleFacts vars
  costScaleFacts vars
  evalTactic (← `(tactic| try ring_nf at *))
  ringNfCosts
  clearUnrelated vars
  addProductFacts
  evalTactic (← `(tactic| linarith))

/-- `cost_bound`: close a cost inequality `lhs ≤ rhs` — each charge on the left is bounded
by the worst-case quantities on the right (`cost_atom_le`), then linear arithmetic. -/
elab "cost_bound" : tactic => costBound false

/-- `cost_bound?`: as `cost_bound`, reporting the charges that nothing on the right bounds. -/
elab "cost_bound?" : tactic => costBound true

end PrimeNumbers.Chapter9
