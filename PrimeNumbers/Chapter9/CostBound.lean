import PrimeNumbers.Chapter9.Counted
import Lean.Elab.Tactic.Omega.Frontend
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log

/-!
# `cost_bound`: closing cost inequalities

After `cost_unfold`, a running-time goal `L ≤ R` is an inequality between a sum of charges
(`C.unit`, `C.add a b`, `C.mul a b`, `C.divMod a b` at the bit lengths of the actual
operands) and costs of callees on the left, and a bound on the right.  `cost_bound` proves it
by a fixed procedure, with this contract:

1. **Normal forms.**  Both sides are sums of *coefficients* times *basis quantities*.  The
   basis is `1`, `C.unit`, the charges `C.add a b`, `C.mul a b`, `C.divMod a b`,
   `C.divBound k`, and the opaque costs (calls `costOf C (g …)`, `gcdCost C k`, …); `C.lin`
   and `C.mulMod` unfold to it.  Coefficients are expressions without costs of the model: in
   sizes, parameters, and costs in *other* models (`costOf mulCount …` is a number).
2. **Bounds.**  A cost on the left that the right does not have is replaced by its bound: a
   hypothesis (the induction hypothesis, a bound of the user's), else an `@[cost_le]` lemma
   instantiated at the call (its hypotheses discharged by the facts below, its free
   parameters taken from the right side, or the tightest).  A bound may have other costs
   on its left (`q + E ≤ B`): they are credited to the right.  Each hypothesis serves once.
3. **Monotonicity.**  The remaining charges and costs on the left go to larger ones of the
   right (`C.mul a b ≤ C.mul k k` for `a, b ≤ k`, `gcdCost C a ≤ gcdCost C b`: the
   `@[gcongr]` lemmas), or to a larger cost that has a bound — those with the fewest choices
   first, each where it fits.
4. **Coefficients.**  For each basis quantity, the coefficient on the left must be at most
   the one on the right: by `omega` (after distributing products), by linear arithmetic, by
   factoring out the scale variables that no fact mentions (a cost per operation `s`), or
   monomial by monomial (`fuel · k ≤ fuel · k²`, by a maximal flow).  Failing all, linear
   arithmetic over all the hypotheses has the last word.

The facts for `omega` are derived from the operands, not added to the goal: value bounds
`t < B` (hypotheses, `x % m < m`, `x y + c < A B`, the `@[val_le]` lemmas), bit lengths
(`(x y).size ≤ x.size + y.size`, `t.size ≤ B.size`, `0 < t.size`), powers of two
(`k < 2 ^ k`) and logarithms (`log₂ t ≤ t.size`, `log₂ t ≤ log₂ u` for `t ≤ u`).

So a cost proof is `cost_unfold f.counted` and `cost_bound`, with the induction of the
recursion around them and the genuine mathematics (a logarithm identity, the arithmetic of a
halving recursion) as hypotheses; `cost_bound?` prints the normal forms, and a failure names
the coefficient that does not fit.  A lonely call on the left is unfolded, and the branches
(`if`) of the goal are split, first.  `cost_O` proves uniform big-O bounds `∀ᴼ …` the same
way, finding the constant.
-/

namespace PrimeNumbers.Chapter9

open Lean Meta Elab Tactic

/-- The constants of cost terms: cost models, costs of counted code, and the cost classes. -/
def isCostConst (c : Name) : Bool :=
  [``CostModel, ``CostM, ``MulCost, ``DivCost, ``PowCost, ``AddCost, ``CmpCost, ``InvCost,
    ``CastCost, ``HashCost, `PrimeNumbers.Chapter9.ArithCost].any (·.isPrefixOf c)

theorem _root_.Nat.size_two : Nat.size 2 = 2 := by decide

/-- The bit length of a numeral, evaluated (`Nat.size 8 = 4`), as charged for operations
with literals. -/
simproc_decl reduceNatSize (Nat.size _) := fun e => do
  let_expr Nat.size n := e | return .continue
  let some k := n.nat? | return .continue
  let r := mkNatLit k.size
  let pf ← mkDecideProof (← mkEq e r)
  return .done { expr := r, proof? := some pf }

/-- One step on numbers of at most `k` bits: a call and a linear-time operation. -/
theorem CostModel.unit_le_lin (C : CostModel) (k : ℕ) : C.unit ≤ C.lin k :=
  Nat.le_add_right _ _

@[gcongr] theorem CostModel.lin_mono (C : CostModel) {a b : ℕ} (h : a ≤ b) : C.lin a ≤ C.lin b :=
  Nat.add_le_add_left (C.add_mono h h) _

/-! ### Operands: value bounds and bit lengths -/

/-- The cost model of a cost expression (the first one it mentions). -/
partial def costModelOf (e : Expr) : Option Expr :=
  if e.isAppOfArity ``CostM.cost 3 then some e.appFn!.appFn!.appArg!
  else if let some c := e.getAppFn.constName? then
    if (``CostModel).isPrefixOf c && e.getAppNumArgs ≥ 1 &&
      (e.getAppArgs[0]!.isFVar || e.getAppArgs[0]!.isConst) then some e.getAppArgs[0]!
    else go e
  else go e
where
  go (e : Expr) : Option Expr := match e with
    | .app f a => (costModelOf f).orElse fun _ => costModelOf a
    | .mdata _ b => costModelOf b
    | _ => none

register_option cost_bound.profile : Bool := {
  defValue := false
  descr := "report the time of each step of `cost_bound`"
}

/-- Run a step of `cost_bound`, timing it under `cost_bound.profile`. -/
def step {m : Type → Type} [Monad m] [MonadLiftT BaseIO m] [MonadOptions m] [MonadLog m]
    [AddMessageContext m] {α} (name : String) (x : m α) : m α := do
  unless cost_bound.profile.get (← getOptions) do return ← x
  let t₀ ← IO.monoMsNow
  let r ← x
  logInfo m!"cost_bound: {name} {(← IO.monoMsNow) - t₀}ms"
  return r

namespace CostFacts

/-- A bound `t < ub` (`strict`) or `t ≤ ub`, with its proof. -/
structure Bound where
  ub : Expr
  strict : Bool
  pf : Expr

def Bound.le (b : Bound) : MetaM Expr :=
  if b.strict then mkAppM ``Nat.le_of_lt #[b.pf] else pure b.pf

/-- A fact for `omega`: its proof, its atoms, and whether `omega` case splits on it (`max`,
`min`, truncated subtraction, disjunctions, implications). -/
structure Fact where
  pf : Expr
  atoms : Array Expr
  splits : Bool

structure State where
  /-- the goal at the start, in whose context the arithmetic facts are proved (the later
  goals differ only in hypotheses about costs, and in hypotheses rewritten by `simp`) -/
  ctx : MVarId
  /-- the cost model of the goal: hypotheses about other models' costs (counts of operations)
  are arithmetic facts -/
  model : Option Expr := none
  /-- the bit lengths `t.size` bounded by hypotheses `t.size ≤ R` -/
  hypSized : Array Expr := #[]
  /-- the value bounds of the terms seen -/
  bounds : Std.HashMap Expr (Array Bound) := {}
  /-- the terms whose bit lengths are bounded, with the depth (in bounds of bounds) -/
  sized : Std.HashMap Expr Nat := {}
  /-- the facts derived, given to `omega` -/
  facts : Array Fact := #[]
  /-- the hypotheses of `ctx` that are not about costs -/
  ctxHyps : Option (Array Fact) := none
  /-- the arithmetic facts proved -/
  proved : Std.HashMap Expr Expr := {}
  /-- the arithmetic facts that `omega` cannot prove from the facts so far -/
  failed : Std.HashSet Expr := {}
  /-- the logarithms `log₂ t` bounded -/
  logged : Array Expr := #[]
  /-- the number of calls of `omega` -/
  omegaCalls : Nat := 0
  /-- the inequalities `a ≤ b` that `proveLe` cannot prove from the facts so far -/
  failedLe : Std.HashSet (Expr × Expr) := {}
  /-- the upper bounds of atoms found (`atomBounds`) -/
  atomBounds : Std.HashMap Expr (Array (Expr × Expr)) := {}

abbrev FactM := StateRefT State TacticM

/-- Run in the context of the main goal. -/
def withMain {α} (x : FactM α) : FactM α := do (← getMainGoal).withContext x

def isNat (e : Expr) : MetaM Bool := do
  if e.hasLooseBVars then return false
  try return (← whnfR (← inferType e)).isConstOf ``Nat catch _ => return false

/-- Is this hypothesis about costs (it mentions a cost model or a cost)? -/
def mentionsCost (ty : Expr) : Bool :=
  ty.getUsedConstants.any isCostConst

/-- The atoms of an arithmetic fact for `omega`: its maximal subterms not built by the
arithmetic and the logic that `omega` knows. -/
partial def omegaAtoms (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let bin := e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 ||
    e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HDiv.hDiv 6 ||
    e.isAppOfArity ``HMod.hMod 6 || e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 ||
    e.isAppOfArity ``GE.ge 4 || e.isAppOfArity ``GT.gt 4 || e.isAppOfArity ``Eq 3 ||
    e.isAppOfArity ``Ne 3 || e.isAppOfArity ``Max.max 4 || e.isAppOfArity ``Min.min 4 ||
    e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2
  if bin then omegaAtoms e.appArg! (omegaAtoms e.appFn!.appArg! acc)
  else if e.isAppOfArity ``Not 1 then omegaAtoms e.appArg! acc
  else if e.isArrow then omegaAtoms e.bindingBody! (omegaAtoms e.bindingDomain! acc)
  else if e.nat?.isSome || e.isRawNatLit then acc
  else if acc.contains e then acc else acc.push e

/-- The variables of an expression (the atoms of the relevance of facts: robust to the
different instance paths of the same term). -/
def varsOf (e : Expr) : Array Expr :=
  (Lean.collectFVars {} e).fvarIds.map Expr.fvar

/-- The facts relevant to `p`: those sharing variables with it, or with a fact relevant to it. -/
def relevantFacts (p : Expr) (cands : Array Fact) : Array Fact := Id.run do
  let mut keep := varsOf p
  let mut chosen : Array Bool := cands.map fun _ => false
  let mut changed := true
  while changed do
    changed := false
    for h : i in [:cands.size] do
      if chosen[i]! then continue
      let as := cands[i].atoms
      if as.any keep.contains then
        chosen := chosen.set! i true
        keep := as.foldl (fun k a => if k.contains a then k else k.push a) keep
        changed := true
  let mut out := #[]
  for h : i in [:cands.size] do
    if chosen[i]! then out := out.push cands[i]
  return out

/-- Does `omega` case split on a fact of this type? -/
def splits (ty : Expr) : Bool :=
  ty.isArrow || (ty.find? fun e => e.isAppOf ``Max.max || e.isAppOf ``Min.min ||
    e.isAppOf ``HSub.hSub || e.isAppOf ``Or || e.isAppOf ``Iff).isSome

/-- A fact with its atoms. -/
def mkFact (pf : Expr) : MetaM Fact := do
  let ty ← instantiateMVars (← inferType pf)
  return { pf, atoms := varsOf ty, splits := splits ty }

/-- The hypotheses of the context that are not about costs. -/
def ctxHyps : FactM (Array Fact) := do
  if let some hs := (← get).ctxHyps then return hs
  let model := (← get).model
  let hs ← (← get).ctx.withContext do
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).cleanupAnnotations
      let cost := match model with
        | some C => mentionsCost ty && (ty.find? (· == C)).isSome
        | none => mentionsCost ty
      -- (arithmetic propositions only)
      let arith := ty.isAppOf ``LE.le || ty.isAppOf ``LT.lt || ty.isAppOf ``GE.ge ||
        ty.isAppOf ``GT.gt || ty.isAppOf ``Eq || ty.isAppOf ``Ne || ty.isAppOf ``Not ||
        ty.isAppOf ``And || ty.isAppOf ``Or || ty.isAppOf ``Iff
      if (← isProp ty) && !cost && !ty.isForall && arith then
        hs := hs.push { pf := d.toExpr, atoms := varsOf ty, splits := splits ty }
    return hs
  modify fun s => { s with ctxHyps := some hs }
  return hs

/-- Prove `p` by `omega` from `hyps`, in the context of the goal at the start. -/
def runOmega (p : Expr) (hyps : Array Expr) : FactM (Option Expr) := do
  modify fun s => { s with omegaCalls := s.omegaCalls + 1 }
  let t₀ ← IO.monoMsNow
  let r ← (← get).ctx.withContext do
    let m ← mkFreshExprSyntheticOpaqueMVar p
    let s ← Meta.saveState
    try
      if let some g ← m.mvarId!.falseOrByContra then
        g.withContext do
          let ty ← g.getType
          -- the negated goal, introduced by `falseOrByContra`
          let neg := (← getLCtx).lastDecl.filter (!·.isImplementationDetail) |>.map (·.toExpr)
          let g' ← mkFreshExprSyntheticOpaqueMVar ty
          Lean.Elab.Tactic.Omega.omega (hyps ++ neg.toArray).toList g'.mvarId!
          g.assign (← mkAuxTheorem ty (← instantiateMVars g') (zetaDelta := true))
      let pf ← instantiateMVars m
      if pf.hasExprMVar then s.restore; pure none else pure (some pf)
    catch _ => s.restore; pure none
  if cost_bound.profile.get (← getOptions) then
    let dt := (← IO.monoMsNow) - t₀
    if dt > 100 then logInfo m!"cost_bound: omega {dt}ms {r.isSome} {p} ({hyps.size} facts)"
  return r

/-- Prove an arithmetic fact by `omega`, from the hypotheses that are not about costs, the
facts derived and `extra` (those relevant to it): first from the facts that `omega` need
not case split on, then from all. -/
def proveArith (p : Expr) (extra : Array Expr := #[]) (quick := false) :
    FactM (Option Expr) := do
  let p ← instantiateMVars p
  if let some pf := (← get).proved.get? p then return some pf
  if extra.isEmpty && (← get).failed.contains p then return none
  let extra ← (← get).ctx.withContext (extra.mapM fun e => (mkFact e : FactM _))
  let rel := relevantFacts p ((← ctxHyps) ++ (← get).facts ++ extra)
  let simple := rel.filter (!·.splits)
  let r ← match ← runOmega p (simple.map (·.pf)) with
    | some pf => pure (some pf)
    | none =>
      if quick then return none
      if simple.size < rel.size then runOmega p (rel.map (·.pf)) else pure none
  match r with
  | some pf => modify fun s => { s with proved := s.proved.insert p pf }
  | none => if extra.isEmpty then modify fun s => { s with failed := s.failed.insert p }
  return r

def addFact (pf : Expr) : FactM Unit := do
  let f ← (← get).ctx.withContext (mkFact pf : FactM _)
  modify fun s => { s with facts := s.facts.push f, failed := {}, failedLe := {} }

/-- The arguments `t` of the bit lengths `t.size` in `e`. -/
partial def sizeArgsOf (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOfArity ``Nat.size 1 then
    let t := e.appArg!
    if acc.contains t then acc else acc.push t
  else match e with
    | .app f a => sizeArgsOf a (sizeArgsOf f acc)
    | .mdata _ b => sizeArgsOf b acc
    | _ => acc

/-- Prove `a ≤ b` between expressions in bit lengths: by `omega` from the facts, or else
with the comparisons `s.size ≤ t.size` for the bit lengths `s.size` of `a` and `t.size` of
`b` with `s ≤ t`, and `k ≤ t.size` when `a` is a numeral `k` and `2^(k-1) ≤ t`. -/
def proveLe (a b : Expr) : FactM (Option Expr) := do
  if a == b then return some (← mkAppM ``le_refl #[a])
  let p ← mkAppM ``LE.le #[a, b]
  if let some pf ← proveArith p then return some pf
  if (← get).failedLe.contains (a, b) then return none
  -- the bit lengths of `b`, and those bounded by hypotheses (`t.size ≤ k`)
  let hypSized := (← get).hypSized
  let ys := (sizeArgsOf b).filter (!hypSized.contains ·) ++ hypSized
  let mut extra := #[]
  for y in ys do
    for x in sizeArgsOf a do
      if let some h ← proveArith (← mkAppM ``LE.le #[x, y]) then
        extra := extra.push (← mkAppM ``Nat.size_le_size #[h])
    if let some k := a.nat? then
      if k ≥ 1 then
        let pow ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit (k - 1)]
        if let some h ← proveArith (← mkAppM ``LE.le #[pow, y]) then
          let iff ← mkAppOptM ``Nat.lt_size #[mkNatLit (k - 1), y]
          extra := extra.push (← mkAppM ``Iff.mpr #[iff, h])
  let r ← if extra.isEmpty then pure none else proveArith p extra
  if r.isNone then modify fun s => { s with failedLe := s.failedLe.insert (a, b) }
  return r

/-- The bound on `t` that the relation `ty` (proved by `pf`) states, if any: `t < B`,
`t ≤ B`, `B > t`, `B ≥ t` over the naturals. -/
def boundOf? (t ty pf : Expr) : Option Bound :=
  let nat (α : Expr) := α.isConstOf ``Nat
  match_expr ty with
  | LT.lt α _ l r => if l == t && nat α then some ⟨r, true, pf⟩ else none
  | LE.le α _ l r => if l == t && nat α then some ⟨r, false, pf⟩ else none
  | GT.gt α _ r l => if l == t && nat α then some ⟨r, true, pf⟩ else none
  | GE.ge α _ r l => if l == t && nat α then some ⟨r, false, pf⟩ else none
  | _ => none

/-- The bounds on `t` among the hypotheses. -/
def hypBounds (t : Expr) : FactM (Array Bound) := withMain do
  let mut bs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some b := boundOf? t (← instantiateMVars d.type).cleanupAnnotations d.toExpr then
      bs := bs.push b
  return bs

/-- Unify `ty` with a hypothesis or a derived fact. -/
def findHyp (ty : Expr) : FactM (Option Expr) := do
  let facts := (← get).facts.map (·.pf)
  withMain do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let s ← Meta.saveState
      if ← withReducible (isDefEq ty d.type) then return some d.toExpr
      s.restore
    for f in facts do
      let s ← Meta.saveState
      if ← withReducible (isDefEq ty (← inferType f)) then return some f
      s.restore
    return none

/-- A trivial side condition (`∀ a b, MulCost.mulCost mulCount a b = 1`): by `rfl` after
introducing, or `decide`. -/
def proveTrivial (ty : Expr) : TacticM (Option Expr) := do
  let m ← mkFreshExprMVar ty
  let s ← saveState
  try
    let gs ← Term.withoutErrToSorry <| Tactic.run m.mvarId!
      (evalTactic (← `(tactic| first | (intros; rfl) | decide)))
    if gs.isEmpty then return some (← instantiateMVars m)
    s.restore; return none
  catch _ => s.restore; return none

/-- Discharge the hypotheses `xs` of a lemma instance: instances by synthesis, hypotheses
with metavariables by unification with a hypothesis or fact, the others by a hypothesis or
`omega`. -/
def discharge (xs : Array Expr) (bis : Array BinderInfo) : FactM Bool := do
  for x in xs, bi in bis do
    let x ← instantiateMVars x
    unless x.isMVar do continue
    let ty ← instantiateMVars (← inferType x)
    if bi.isInstImplicit then
      let some inst ← synthInstance? ty | return false
      unless ← isDefEq x inst do return false
      continue
    unless ← isProp ty do continue
    -- a free bound `a ≤ ?k`: the tightest, `?k := a`
    if let some (_, a, k) := ty.le? then
      if k.isMVar && !a.hasExprMVar then
        if !(← k.mvarId!.isAssigned) then
          if ← isDefEq k a then
            unless ← isDefEq x (← mkAppM ``le_refl #[a]) do return false
            continue
    if ty.hasExprMVar then
      let some h ← findHyp ty | return false
      unless ← isDefEq x h do return false
    else
      let h ← match ← findHyp ty with
        | some h => pure (some h)
        | none => match_expr ty with
          | LE.le α _ a b => if α.isConstOf ``Nat then proveLe a b else proveArith ty
          | _ => match ← proveArith ty with
            | some h => pure (some h)
            | none => withMain (proveTrivial ty)
      let some h := h | return false
      unless ← isDefEq x h do return false
  return true

def isArith (e : Expr) : Bool :=
  e.isAppOf ``HAdd.hAdd || e.isAppOf ``HMul.hMul || e.isAppOf ``HSub.hSub ||
    e.isAppOf ``HDiv.hDiv || e.isAppOf ``HMod.hMod || e.isAppOf ``HPow.hPow

/-- The applications of constants in `e` (outside binders), but for the arithmetic. -/
partial def headApps (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.hasLooseBVars then acc else
  let acc := if e.getAppFn.isConst && !isArith e && e.getAppNumArgs > 0 && !acc.contains e
    then acc.push e else acc
  match e with
  | .app f a => headApps a (headApps f acc)
  | .mdata _ b => headApps b acc
  | _ => acc

/-- Assign the metavariables of the patterns by unification with the targets of the same
head (or leave them), so that `k` succeeds. -/
partial def assignTargets (pats : List Expr) (targets : Array Expr) (k : FactM Bool) :
    FactM Bool := do
  match pats with
  | [] => k
  | p :: ps =>
    let p ← instantiateMVars p
    if !p.hasExprMVar then return ← assignTargets ps targets k
    for c in targets do
      unless c.getAppFn == p.getAppFn && c.getAppNumArgs == p.getAppNumArgs do continue
      let s ← Meta.saveState
      if (← withReducible (isDefEq p c)) then
        if ← assignTargets ps targets k then return true
      s.restore
    assignTargets ps targets k

/-- The bound `t < r` (or `≤`) that `f : ∀ …, l < r` gives at `t`: `l` unified with `t`, the
hypotheses discharged — with the free parameters of `r` taken from `targets` where they
unify, else the tightest. -/
def instBound (f t : Expr) (targets : Array Expr := #[]) : FactM (Option Bound) := withMain do
  let s ← Meta.saveState
  let (xs, bis, concl) ← forallMetaTelescopeReducing (← inferType f)
  let (l, r, strict) ← match_expr concl with
    | LT.lt _ _ l r => pure (l, r, true)
    | LE.le _ _ l r => pure (l, r, false)
    | _ => s.restore; return none
  unless ← withReducible (isDefEq l t) do s.restore; return none
  let ok ← assignTargets (headApps (← instantiateMVars r) #[]).toList targets (discharge xs bis)
  let pf ← instantiateMVars (mkAppN f xs)
  let r ← instantiateMVars r
  if !ok || pf.hasExprMVar || r.hasExprMVar then s.restore; return none
  return some ⟨r, strict, pf⟩

/-- Bounds `t < B` from the `@[val_le]` lemmas about the head of `t`. -/
def lemmaBounds (t : Expr) : FactM (Array Bound) := do
  let some c := t.getAppFn.constName? | return #[]
  let mut bs := #[]
  for decl in (((valLeExt.getState (← getEnv)).get? c).getD #[]) do
    if let some b ← instBound (← mkConstWithFreshMVarLevels decl) t then bs := bs.push b
  return bs

mutual
/-- The bounds of `x ∘ y` from the first bounds of `x` and `y` (`op` monotone: `lt`, `le` its
lemmas for strict and plain bounds). -/
partial def pairs (op lt le : Name) (x y : Expr) : FactM (Array Bound) := do
  let mut bs := #[]
  for b₁ in (← valBounds x)[:2] do
    for b₂ in (← valBounds y)[:2] do
      let ub ← mkAppM op #[b₁.ub, b₂.ub]
      bs := bs.push <| ← if b₁.strict && b₂.strict then
          pure (Bound.mk ub true (← mkAppM lt #[b₁.pf, b₂.pf]))
        else pure (Bound.mk ub false (← mkAppM le #[← b₁.le, ← b₂.le]))
  return bs

/-- The value bounds of `t`, derived (and recorded as facts) on first use. -/
partial def valBounds (t : Expr) : FactM (Array Bound) := do
  if let some bs := (← get).bounds.get? t then return bs
  modify fun s => { s with bounds := s.bounds.insert t #[] }
  if t.nat?.isSome then
    let bs := #[{ ub := t, strict := false, pf := (← mkAppM ``le_refl #[t]) : Bound }]
    modify fun s => { s with bounds := s.bounds.insert t bs }
    return bs
  let hyps ← hypBounds t
  let mut bs : Array Bound := #[]
  match_expr t with
  | HMod.hMod _ _ _ _ x m =>
    discard <| valBounds x
    if let some h ← proveArith (← mkAppM ``LT.lt #[mkNatLit 0, m]) then
      bs := bs.push (Bound.mk m true (← mkAppM ``Nat.mod_lt #[x, h]))
    bs := bs.push (Bound.mk x false (← mkAppM ``Nat.mod_le #[x, m]))
  | HDiv.hDiv _ _ _ _ x m =>
    discard <| valBounds x
    bs := bs.push (Bound.mk x false (← mkAppM ``Nat.div_le_self #[x, m]))
  | HSub.hSub _ _ _ _ x y =>
    discard <| valBounds x
    bs := bs.push (Bound.mk x false (← mkAppM ``Nat.sub_le #[x, y]))
  | HMul.hMul _ _ _ _ x y =>
    bs := bs ++ (← pairs ``HMul.hMul ``Nat.mul_lt_mul'' ``Nat.mul_le_mul x y)
  | HAdd.hAdd _ _ _ _ x y =>
    let by_ ← valBounds y
    -- a product plus a carry: `p q + c < A B`
    if let some (p, q) := (match_expr x with
        | HMul.hMul _ _ _ _ p q => some (p, q) | _ => none) then
      for bp in (← valBounds p).filter (·.strict) do
        for bq in (← valBounds q).filter (·.strict) do
          for bc in by_.filter (·.strict) do
            let ub ← mkAppM ``HMul.hMul #[bp.ub, bq.ub]
            if bc.ub == bp.ub then
              let pf ← mkAppM ``mul_add_lt_mul_of_lt_left #[bp.pf, bq.pf, bc.pf]
              bs := bs.push (Bound.mk ub true pf)
            else if bc.ub == bq.ub then
              let pf ← mkAppM ``mul_add_lt_mul_of_lt_right #[bp.pf, bq.pf, bc.pf]
              bs := bs.push (Bound.mk ub true pf)
    bs := bs ++ (← pairs ``HAdd.hAdd ``Nat.add_lt_add ``Nat.add_le_add x y)
  | _ =>
    for a in t.getAppArgs do
      if ← isNat a then discard <| valBounds a
    bs := bs ++ (← lemmaBounds t)
  for b in bs do addFact b.pf
  let all := hyps ++ bs
  modify fun s => { s with bounds := s.bounds.insert t all }
  return all
end

/-- The facts about the bit length of `t`. -/
partial def sizeFacts (t : Expr) (depth : Nat := 0) : FactM Unit := do
  if let some d := (← get).sized.get? t then
    if d ≤ depth then return
  modify fun s => { s with sized := s.sized.insert t depth }
  let st := mkApp (mkConst ``Nat.size) t
  if let some k := t.nat? then
    addFact (← mkDecideProof (← mkEq st (mkNatLit k.size)))
    return
  match_expr t with
  | HMul.hMul _ _ _ _ x y =>
    sizeFacts x depth; sizeFacts y depth; addFact (← mkAppM ``size_mul_le #[x, y])
  | HAdd.hAdd _ _ _ _ x y =>
    sizeFacts x depth; sizeFacts y depth
    addFact (← mkAppM ``size_add_le_add #[x, y])
    addFact (← mkAppM ``size_add_le #[x, y])
  | HPow.hPow _ _ _ _ b k =>
    if b.nat? == some 2 then
      addFact (← mkAppOptM ``Nat.size_pow #[k])
      -- `k < 2 ^ k`, `0 < 2 ^ k` (and so on for the exponent)
      addFact (← mkAppOptM ``Nat.lt_two_pow_self #[k])
      addFact (← mkAppM ``Nat.two_pow_pos #[k])
      sizeFacts k depth
  | _ => pure ()
  -- through the value bounds (and the bounds of these, once: a bound `x ≤ x + c` would
  -- lead on forever)
  for b in ← valBounds t do
    if b.ub == t then continue
    if depth < 2 then sizeFacts b.ub (depth + 1)
    addFact (← mkAppM ``Nat.size_le_size #[← b.le])
  if let some h ← proveArith (← mkAppM ``LT.lt #[mkNatLit 0, t]) then
    addFact (← mkAppM ``Iff.mpr #[← mkAppOptM ``Nat.size_pos #[t], h])
    -- and `1 < t.size` for `2 ≤ t`
    if let some h ← proveArith (← mkAppM ``LE.le #[mkNatLit 2, t]) then
      let iff ← mkAppOptM ``Nat.lt_size #[mkNatLit 1, t]
      addFact (← mkAppM ``Iff.mpr #[iff, ← mkExpectedTypeHint h
        (← mkAppM ``LE.le #[← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 1], t])])
  unless isArith t do addFact (← mkAppM ``size_le_self #[t])

/-- The operands whose bit lengths appear in `e`, and the arguments (naturals) of the calls
whose costs appear in `e`. -/
partial def sizeTerms (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  if e.hasLooseBVars then return acc
  if e.isAppOfArity ``Nat.size 1 then
    let t := e.appArg!
    return ← sizeTerms t (if acc.contains t then acc else acc.push t)
  if e.isAppOfArity ``CostM.cost 3 then
    let mut acc := acc
    for a in e.appArg!.getAppArgs do
      if (← isNat a) && !acc.contains a then acc := acc.push a
      acc ← sizeTerms a acc
    return acc
  match e with
  | .app f a => sizeTerms a (← sizeTerms f acc)
  | .mdata _ b => sizeTerms b acc
  | _ => return acc

/-- The logarithms `Nat.log 2 t` in `e` (outside binders). -/
partial def logTerms (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.hasLooseBVars then acc
  else if e.isAppOfArity ``Nat.log 2 && e.appFn!.appArg!.nat? == some 2 then
    if acc.contains e then acc else acc.push e
  else match e with
    | .app f a => logTerms a (logTerms f acc)
    | .mdata _ b => logTerms b acc
    | .forallE _ d b _ => logTerms b (logTerms d acc)
    | _ => acc

/-- Derive the facts about the operands of the goal and of the hypotheses. -/
def operandFacts : FactM Unit := do
  let (ts, hs) ← withMain do
    let mut ts ← sizeTerms (← instantiateMVars (← getMainTarget)) #[]
    let mut hs := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).cleanupAnnotations
      unless (← isProp ty) && !ty.isForall do continue
      ts ← sizeTerms ty ts
      -- the bit lengths bounded by hypotheses
      if let some (_, l, _) := ty.le? then
        if l.isAppOfArity ``Nat.size 1 && !mentionsCost ty then hs := hs.push l.appArg!
      if let some (_, l, _) := ty.lt? then
        if l.isAppOfArity ``Nat.size 1 && !mentionsCost ty then hs := hs.push l.appArg!
    return (ts, hs)
  let hs := hs.foldl (fun a t => if a.contains t then a else a.push t) (← get).hypSized
  modify fun s => { s with hypSized := hs }
  -- `log₂ t ≤ t.size`
  let logs ← withMain do
    let mut ls : Array Expr := #[]
    let tgt ← instantiateMVars (← getMainTarget)
    let mut es := #[tgt]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      es := es.push (← instantiateMVars d.type)
    for e in es do ls := logTerms e ls
    return ls
  for l in logs do
    unless (← get).logged.contains l do
      -- `log₂ t ≤ log₂ u` for `t ≤ u`
      for l' in (← get).logged do
        withMain do
          if let some h ← proveArith (← mkAppM ``LE.le #[l.appArg!, l'.appArg!]) then
            addFact (← mkAppOptM ``Nat.log_mono_right #[mkNatLit 2, none, none, h])
          if let some h ← proveArith (← mkAppM ``LE.le #[l'.appArg!, l.appArg!]) then
            addFact (← mkAppOptM ``Nat.log_mono_right #[mkNatLit 2, none, none, h])
      modify fun s => { s with logged := s.logged.push l }
      withMain do
        addFact (← mkAppM ``log_two_le_size #[l.appArg!])
        sizeFacts l.appArg!
  for t in ts do
    let t₀ ← IO.monoMsNow
    withMain (sizeFacts t)
    if cost_bound.profile.get (← getOptions) then
      logInfo m!"cost_bound: operand {t} {(← IO.monoMsNow) - t₀}ms"

/-! ### Callees -/

/-- The costs in `e` that a lemma or hypothesis may bound: calls `CostM.cost C α (g.counted …)`
and applications of heads with `@[cost_le]` lemmas (e.g. `gcdCost C k`), outside binders. -/
partial def costsIn (env : Environment) (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.hasLooseBVars then acc
  else if e.isAppOfArity ``CostM.cost 3 && e.appArg!.getAppFn.isConst then
    if acc.contains e then acc else acc.push e
  else
    let acc := match e.getAppFn.constName? with
      | some c => if ((costLeExt.getState env).get? c).isSome && !acc.contains e then acc.push e
          else acc
      | none => acc
    match e with
    | .app f a => costsIn env a (costsIn env f acc)
    | .mdata _ b => costsIn env b acc
    | _ => acc

/-- Instantiate the bound `f : ∀ …, costOf C (g …) ≤ B` at the cost `a`. -/
def instCostBound (f : Expr) (a : Expr) (targets : Array Expr) : FactM (Option Expr) := do
  return (← instBound f a targets).map (·.pf)

/-- Bound the costs of the calls on the left of the goal by the `@[cost_le]` lemmas and the
local hypotheses (an induction hypothesis), adding the instances to the context; then the
costs on the right of these bounds that have lemmas (`gcdCost C k`), and so on. -/
def calleeFacts (verbose : Bool) : FactM Unit := do
  let env ← getEnv
  let (calls, targets, hyps, known) ← withMain do
    let tgt ← instantiateMVars (← getMainTarget)
    let_expr LE.le _ _ lhs rhs := tgt | throwError "cost_bound: the goal is not an inequality"
    let mut hyps : Array (Name × Expr) := #[]
    let mut known : Array Expr := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).cleanupAnnotations
      unless ← isProp ty do continue
      if ty.isForall then
        if let some k ← costLemmaKey? ty then hyps := hyps.push (k, d.toExpr)
      else if let some (_, l, _) := ty.le? then
        -- the costs that a hypothesis bounds (alone or with others, `q + E ≤ B`)
        known := costsIn env l known
    return (costsIn env lhs #[], headApps rhs #[], hyps, known)
  let mut work := calls
  let mut done := known
  let mut pfs : Array Expr := #[]
  let mut round := 0
  while !work.isEmpty && round < 4 do
    round := round + 1
    let mut next := #[]
    for a in work do
      if done.contains a then continue
      done := done.push a
      let some g := costKey? a | continue
      -- an induction hypothesis first; else every lemma that applies (up to three: the
      -- bounds of a callee may differ in form, e.g. exact or through `gcdCost`)
      let mut found : Array Expr := #[]
      for (k, h) in hyps do
        if k == g then
          if let some pf ← instCostBound h a targets then found := found.push pf; break
      if found.isEmpty then
        for decl in (((costLeExt.getState env).get? g).getD #[]) do
          if found.size ≥ 3 then break
          let f ← mkConstWithFreshMVarLevels decl
          if let some pf ← instCostBound f a targets then
            let ty ← instantiateMVars (← withMain (inferType pf))
            unless ← found.anyM (fun q => do
                return (← instantiateMVars (← withMain (inferType q))) == ty) do
              found := found.push pf
      for pf in found do
        pfs := pfs.push pf
        -- the costs that the bound is in terms of
        let ty ← instantiateMVars (← withMain (inferType pf))
        if let some (_, _, r) := ty.le? then
          -- (the calls of the model are parameters of the bound; the counts in other models,
          -- `costOf mulCount …`, and the quantities like `gcdCost C k` are bounded further)
          let model := (← get).model
          next := (costsIn env r #[]).foldl (fun n c =>
            if (c.isAppOfArity ``CostM.cost 3 && (model.isNone || costModelOf c == model)) ||
              n.contains c then n else n.push c) next
      match found with
      | #[] => if verbose then logInfo m!"cost_bound: no bound for {a}"
      | _ => pure ()
    work := next
  -- the bounds on other models' costs (counts of operations) are arithmetic facts
  let model := (← get).model
  for pf in pfs do
    let ty ← instantiateMVars (← withMain (inferType pf))
    if let some (_, l, _) := ty.le? then
      if model.isSome && costModelOf l != model then withMain (addFact pf)
  let mut g ← getMainGoal
  let mut i := 0
  for pf in pfs do
    let (_, g') ← (← g.assert (Name.mkSimple s!"hcall{i}") (← g.withContext (inferType pf))
      pf).intro1P
    g := g'
    i := i + 1
  replaceMainGoal [g]

end CostFacts

open CostFacts

/-! ### Charges -/

/-- A proof that the charge of a division is at most the worst case `C.divBound k` of the
sizes, if they allow (the only comparison of charges of different operations: `C.lin` and
`C.mulMod` are unfolded). -/
private def boundAtom (a b : Expr) : FactM (Option Expr) := do
  let_expr CostModel.divMod C x y := a | return none
  let_expr CostModel.divBound C' k := b | return none
  unless C == C' do return none
  let some hx ← proveLe x k | return none
  let some hy ← proveLe y k | return none
  some <$> mkAppM ``CostModel.divMod_le_divBound #[C, hx, hy]

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

/-- A monomial: its numeral coefficient and its atoms with their exponents
(`3 * x * y ^ 2` ↦ `(3, [(x, 1), (y, 2)])`). -/
partial def monomial (e : Expr) (acc : Nat × Array (Expr × Nat) := (1, #[])) :
    Nat × Array (Expr × Nat) :=
  let add (x : Expr) (k : Nat) (acc : Nat × Array (Expr × Nat)) :=
    match acc.2.findIdx? (·.1 == x) with
    | some i => (acc.1, acc.2.modify i fun (y, j) => (y, j + k))
    | none => (acc.1, acc.2.push (x, k))
  if e.isAppOfArity ``HMul.hMul 6 then monomial e.appArg! (monomial e.appFn!.appArg! acc)
  else if let some k := e.nat? then (acc.1 * k, acc.2)
  else if e.isAppOfArity ``HPow.hPow 6 then
    match e.appArg!.nat? with
    | some k => add e.appFn!.appArg! k acc
    | none => add e 1 acc
  else add e 1 acc

/-- The product `x₁ ^ e₁ * ⋯` of atoms with exponents (`1` for none). -/
def atomsProd (as : Array (Expr × Nat)) : MetaM Expr := do
  let mut r : Option Expr := none
  for (x, k) in as do
    let f ← if k == 1 then pure x else mkAppM ``HPow.hPow #[x, mkNatLit k]
    r ← match r with
      | none => pure (some f)
      | some p => some <$> mkAppM ``HMul.hMul #[p, f]
  return r.getD (mkNatLit 1)

/-- A proof of `0 < x₁ ^ e₁ * ⋯` from `0 < xᵢ` (by `omega` from the facts). -/
def prodPos (as : Array (Expr × Nat)) : FactM (Option Expr) := do
  let mut r : Option Expr := none
  for (x, k) in as do
    let some hx ← proveArith (← mkAppM ``LT.lt #[mkNatLit 0, x]) | return none
    let h ← if k == 1 then pure hx else mkAppOptM ``Nat.pow_pos #[none, mkNatLit k, hx]
    r ← match r with
      | none => pure (some h)
      | some p => some <$> mkAppM ``Nat.mul_pos #[p, h]
  return r

/-- Match the atoms of the monomial `m` to those of `M`: each atom `x ^ a` of `m` to the same
atom of `M`, or else to an atom `y` of `M` with `x ≤ y`.  Returns the atoms matched, with
the proofs `x ^ a ≤ y ^ a`, and the rest of `M`. -/
def matchMonomial (m M : Array (Expr × Nat)) :
    FactM (Option (Array (Expr × Nat × Expr) × Array (Expr × Nat))) := do
  let mut rest := M
  let mut out := #[]
  for (x, a) in m do
    let take (rest : Array (Expr × Nat)) (y : Expr) : Array (Expr × Nat) :=
      rest.filterMap fun (z, j) => if z == y then (if j > a then some (z, j - a) else none)
        else some (z, j)
    match rest.find? fun (y, j) => y == x && a ≤ j with
    | some _ =>
      let xa ← if a == 1 then pure x else mkAppM ``HPow.hPow #[x, mkNatLit a]
      out := out.push (x, a, ← mkAppM ``le_refl #[xa])
      rest := take rest x
    | none =>
      let mut found := false
      for (y, j) in rest do
        if a ≤ j then
          if let some h ← proveLe x y then
            let h ← if a == 1 then pure h
              else mkAppOptM ``Nat.pow_le_pow_left #[none, none, h, mkNatLit a]
            out := out.push (y, a, h)
            rest := take rest y
            found := true
            break
      unless found do return none
  return some (out, rest)

/-- A proof of `m ≤ M` for monomials (atoms with exponents): `M` dominates `m` (its atoms
matched to atoms of `m` at least as large, the rest positive). -/
def domFact (m M : Array (Expr × Nat)) : FactM (Option Expr) := do
  if m == M then return some (← withMain do mkAppM ``le_refl #[← atomsProd m])
  let some (matched, r) ← withMain (matchMonomial m M) | return none
  withMain do
    let hr ← match r with
      | #[] => pure (some (← mkAppM ``Nat.one_pos #[]))
      | r => prodPos r
    let some hr := hr | return none
    let mut acc : Option Expr := none
    for (_, _, hx) in matched do
      acc ← match acc with
        | none => pure (some hx)
        | some p => some <$> mkAppM ``Nat.mul_le_mul #[p, hx]
    let h₀ ← match acc with
      | some p => pure p
      | none => mkAppM ``le_refl #[mkNatLit 1]
    let em' ← atomsProd (matched.map fun (y, a, _) => (y, a))
    let er ← atomsProd r
    let eM ← atomsProd M
    let h₁ ← mkAppOptM ``Nat.le_mul_of_pos_right #[none, em', hr]
    let heq ← mkFreshExprMVar (← mkEq (← mkAppM ``HMul.hMul #[em', er]) eM)
    let gs ← Term.withoutErrToSorry <| Tactic.run heq.mvarId! (evalTactic (← `(tactic| ring)))
    unless gs.isEmpty do return none
    some <$> mkAppM ``le_trans #[h₀, ← mkAppM ``le_of_le_of_eq #[h₁, ← instantiateMVars heq]]

/-! ### Normal forms

`cost_bound` puts both sides in a normal form: a sum of coefficients — expressions without
costs, in the sizes and parameters — times basis quantities.  The basis is `1`, `C.unit`,
`C.addRate` (charges of additions and steps unfold to these, `C.add a b = C.addRate *
(max a b + 1)`), and the opaque costs (`C.mul a b`, `C.divMod a b`, `C.divBound k`, costs of
calls, `gcdCost C k`, …).  The costs of calls on the left that the right does not have are
replaced by their bounds (the induction hypothesis, the `@[cost_le]` lemmas), the remaining
opaque costs on the left by larger ones of the right (monotonicity in the sizes), and then
the two sides are compared coefficient by coefficient: `cost_bound` succeeds exactly when
each coefficient on the left is at most the one on the right. -/

/-- Is `e` a cost in the model `C` (it mentions `C` in a cost; the costs in other models —
counts of operations — are coefficients)? -/
def hasCost (env : Environment) (C : Option Expr) (e : Expr) : Bool :=
  (e.getUsedConstants.any fun c => isCostConst c || ((costLeExt.getState env).get? c).isSome) &&
  match C with
  | some C => (e.find? (· == C)).isSome
  | none => true

/-- Equality of atoms up to reducible unfolding (instances). -/
def atomEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if a.getAppFn != b.getAppFn then return false
  withReducible (withNewMCtxDepth (isDefEq a b))

def findAtom (xs : Array Expr) (x : Expr) : MetaM (Option Nat) := do
  for h : i in [:xs.size] do
    if ← atomEq xs[i] x then return some i
  return none

/-- A normal form: basis quantities with their coefficients. -/
abbrev NF := Array (Expr × Expr)

def nfOne : Expr := mkNatLit 1

def NF.add (a b : NF) : MetaM NF := do
  let mut r := a
  for (x, c) in b do
    match ← findAtom (r.map (·.1)) x with
    | some i => r := r.set! i (r[i]!.1, ← mkAppM ``HAdd.hAdd #[r[i]!.2, c])
    | none => r := r.push (x, c)
  return r

def NF.scale (k : Expr) (a : NF) : MetaM NF :=
  a.mapM fun (x, c) => do
    if c.nat? == some 1 then return (x, k) else return (x, ← mkAppM ``HMul.hMul #[k, c])

def NF.coeff (a : NF) (b : Expr) : MetaM Expr := do
  match ← findAtom (a.map (·.1)) b with
  | some i => return a[i]!.2
  | none => return mkNatLit 0

/-- The normal form of a cost expression in the model `C`. -/
partial def nf (env : Environment) (C : Option Expr) (e : Expr) : MetaM NF := do
  if !hasCost env C e then return #[(nfOne, e)]
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => (← nf env C a).add (← nf env C b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    if !hasCost env C a then NF.scale a (← nf env C b)
    else if !hasCost env C b then NF.scale b (← nf env C a)
    else return #[(e, nfOne)]
  | _ => return #[(e, nfOne)]

/-- A polynomial: monomials (atoms with exponents, sorted) with numeral coefficients. -/
abbrev PolyNF := Array (Nat × Array (Expr × Nat))

def monoMul (a b : Array (Expr × Nat)) : Array (Expr × Nat) :=
  let r := b.foldl (fun acc (x, k) =>
    match acc.findIdx? (·.1 == x) with
    | some i => acc.modify i fun (y, j) => (y, j + k)
    | none => acc.push (x, k)) a
  r.qsort fun p q => p.1.lt q.1

def polyAdd (a b : PolyNF) : PolyNF :=
  b.foldl (fun acc (k, m) =>
    match acc.findIdx? (·.2 == m) with
    | some i => acc.modify i fun (j, m) => (j + k, m)
    | none => acc.push (k, m)) a

def polyMul (a b : PolyNF) : PolyNF :=
  a.foldl (fun acc (k, m) => b.foldl (fun acc (j, n) => polyAdd acc #[(k * j, monoMul m n)]) acc) #[]

/-- The polynomial of an expression (other subterms are atoms). -/
partial def poly (e : Expr) : PolyNF :=
  if let some k := e.nat? then (if k == 0 then #[] else #[(k, #[])]) else
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => polyAdd (poly a) (poly b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => polyMul (poly a) (poly b)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
    match k.nat? with
    | some n => (List.range n).foldl (fun acc _ => polyMul acc (poly a)) #[(1, #[])]
    | none => #[(1, #[(e, 1)])]
  | _ => #[(1, #[(e, 1)])]

/-- The expression of a polynomial: `Σ k * x₁ ^ e₁ * ⋯`. -/
def polyExpr (p : PolyNF) : MetaM Expr := do
  let mut r : Option Expr := none
  for (k, m) in p do
    let t ← if m.isEmpty then pure (mkNatLit k) else do
      let x ← atomsProd m
      if k == 1 then pure x else mkAppM ``HMul.hMul #[mkNatLit k, x]
    r ← match r with
      | none => pure (some t)
      | some acc => some <$> mkAppM ``HAdd.hAdd #[acc, t]
  return r.getD (mkNatLit 0)

/-- A proof of `a = b` by `ring`. -/
def ringEq (a b : Expr) : TacticM (Option Expr) := do
  if a == b then return some (← mkEqRefl a)
  let m ← mkFreshExprMVar (← mkEq a b)
  let gs ← Term.withoutErrToSorry <| Tactic.run m.mvarId! (evalTactic (← `(tactic| ring)))
  unless gs.isEmpty do return none
  return some (← instantiateMVars m)

/-- A flow from supplies `a` to capacities `b` along the allowed edges carrying all of `a`,
if there is one (by augmenting paths). -/
def maxFlow (a b : Array Nat) (ok : Array (Array Bool)) : Option (Array (Array Nat)) :=
  Id.run do
  let n := a.size
  let m := b.size
  let get (x : Array (Array Nat)) (i j : Nat) : Nat := (x[i]!)[j]!
  let allowed (i j : Nat) : Bool := (ok[i]!)[j]!
  let mut f : Array (Array Nat) := Array.replicate n (Array.replicate m 0)
  let mut left := a
  let mut room := b
  for _ in [0:n * m + n + 1] do
    let some i := (List.range n).find? (left[·]! > 0) | return some f
    -- breadth-first search over the demand nodes; `pre j = (i', j₀)`: reached from the
    -- supply node `i'`, itself reached through the flow `i' → j₀` (`j₀ = m` for the start)
    let mut pre : Array (Option (Nat × Nat)) := Array.replicate m none
    let mut queue : Array Nat := #[]
    for j in [0:m] do
      if allowed i j then
        pre := pre.set! j (some (i, m))
        queue := queue.push j
    let mut target : Option Nat := none
    let mut k := 0
    while k < queue.size do
      let j := queue[k]!
      k := k + 1
      if room[j]! > 0 then
        target := some j
        break
      for i' in [0:n] do
        if get f i' j > 0 then
          for j' in [0:m] do
            if allowed i' j' && pre[j']!.isNone then
              pre := pre.set! j' (some (i', j))
              queue := queue.push j'
    let some t := target | return none
    -- the path, and its bottleneck
    let mut path : Array (Nat × Nat × Nat) := #[]
    let mut j := t
    let mut amount := room[t]!
    for _ in [0:m + 1] do
      let some (i', j₀) := pre[j]! | break
      path := path.push (i', j₀, j)
      if j₀ == m then
        amount := min amount left[i']!
        break
      amount := min amount (get f i' j₀)
      j := j₀
    room := room.set! t (room[t]! - amount)
    for (i', j₀, j₁) in path do
      f := f.modify i' fun r => r.modify j₁ (· + amount)
      if j₀ == m then left := left.set! i' (left[i']! - amount)
      else f := f.modify i' fun r => r.modify j₀ (· - amount)
  return none

/-- A proof of `P ≤ Q` by linear arithmetic from `facts` (and, unless `only`, the hypotheses). -/
def linarithLe (P Q : Expr) (facts : Array Expr) (only := true) : FactM (Option Expr) :=
  withMain do
    let m ← mkFreshExprMVar (← mkAppM ``LE.le #[P, Q])
    try
      Mathlib.Tactic.Linarith.linarith only facts.toList {} m.mvarId!
      return some (← instantiateMVars m)
    catch _ => return none

/-- Compare `P ≤ Q` (polynomials `p`, `q`) group by group of their monomials' scale variables
(the atoms no fact mentions): `P = Σ m Pₘ`, `Q = Σ m Qₘ` and `Pₘ ≤ Qₘ`. -/
def scaleGroups (p q : PolyNF) (P Q : Expr) : FactM (Option Expr) := do
  let factAtoms := ((← ctxHyps) ++ (← get).facts).foldl (fun acc f => acc ++ f.atoms) #[]
  -- (an atom is free when no fact mentions any of its parts)
  let free (x : Expr) : Bool := (varsOf x).all (!factAtoms.contains ·)
  let split (m : Array (Expr × Nat)) : Array (Expr × Nat) × Array (Expr × Nat) :=
    (m.filter (free ·.1), m.filter (!free ·.1))
  let mut groups : Array (Array (Expr × Nat) × PolyNF × PolyNF) := #[]
  for (k, m) in p do
    let (v, r) := split m
    match groups.findIdx? (·.1 == v) with
    | some i => groups := groups.modify i fun (v, a, b) => (v, polyAdd a #[(k, r)], b)
    | none => groups := groups.push (v, #[(k, r)], #[])
  for (k, m) in q do
    let (v, r) := split m
    match groups.findIdx? (·.1 == v) with
    | some i => groups := groups.modify i fun (v, a, b) => (v, a, polyAdd b #[(k, r)])
    | none => groups := groups.push (v, #[], #[(k, r)])
  -- nothing to factor out
  if groups.all (·.1.isEmpty) then return none
  let mut facts := #[]
  for (v, a, b) in groups do
    let some h ← withMain do
        let A ← polyExpr a
        let B ← polyExpr b
        let some h ← proveLe A B |
          if cost_bound.profile.get (← getOptions) then
            logInfo m!"cost_bound: the group {v}: {A} ≰ {B}"
          return none
        let mv ← atomsProd v
        some <$> mkAppM ``Nat.mul_le_mul_left #[mv, h]
      | return none
    facts := facts.push h
  linarithLe P Q facts

/-- The atoms of a polynomial. -/
def PolyNF.atoms (p : PolyNF) : Array Expr :=
  p.foldl (fun acc (_, m) => m.foldl (fun acc (x, _) => if acc.contains x then acc else acc.push x)
    acc) #[]

/-- A proof of `a ≤ b` for applications of one function by its `@[gcongr]` lemma
(`C.mul a b ≤ C.mul a' b'`, `gcdCost C k ≤ gcdCost C k'`, `Nat.clog 2 t ≤ Nat.clog 2 u`, …),
the arguments compared by `proveLe`, else again by monotonicity. -/
partial def congrLe (a b : Expr) (depth : Nat := 6) : FactM (Option Expr) := do
  let some f := a.getAppFn.constName? | return none
  unless b.getAppFn.constName? == some f do return none
  -- (no backtracking: the comparisons may be remembered, and a failed attempt only leaves
  -- an unassigned goal behind)
  try
    let g ← withMain do mkFreshExprMVar (← mkAppM ``LE.le #[a, b])
    let (ok, st) ← withMain do
      (g.mvarId!.gcongr none (depth := 1)).run (mainGoalDischarger := fun _ ↦ pure false)
    unless ok do failure
    for m in st.newGoals do
      let some (_, x, y) := (← instantiateMVars (← m.getType)).le? | failure
      let mut h? ← proveLe x y
      if h?.isNone && depth > 0 then h? ← congrLe x y (depth - 1)
      let some h := h? | failure
      m.assign h
    return some (← instantiateMVars g)
  catch _ => return none

/-- The upper bounds `a ≤ U` (`U` free of `a`) of an atom that the proof states, with their
proofs: the hypotheses `a ≤ U`, `a < U`, the local `∀`-hypotheses instantiated at `a` (their
hypotheses discharged as those of the lemmas) and the `@[val_le]` lemmas — not the facts
derived for `omega` (`t.size ≤ t`), true but too weak to replace an atom by. -/
partial def atomBounds (a : Expr) : FactM (Array (Expr × Expr)) := do
  if let some bs := (← get).atomBounds.get? a then return bs
  modify fun s => { s with atomBounds := s.atomBounds.insert a #[] }
  let mut out := #[]
  for b in (← hypBounds a) ++ (← lemmaBounds a) do
    unless (b.ub.find? (· == a)).isSome do out := out.push (b.ub, ← withMain b.le)
  -- `max x y ≤ U ⊔ V` (the larger of the bounds if one is, else their sum), `min x y ≤ U`,
  -- `x - y ≤ U` from the bounds `x ≤ U`, `y ≤ V` (or the operands themselves), by `omega`
  let args : Option (Expr × Expr) := match_expr a with
    | Max.max _ _ x y => some (x, y) | Min.min _ _ x y => some (x, y)
    | HSub.hSub _ _ _ _ x y => some (x, y) | _ => none
  if let some (x, y) := args then
    let first (t : Expr) : FactM (Expr × Option Expr) := do
      return match (← atomBounds t)[0]? with | some (U, h) => (U, some h) | none => (t, none)
    let (U, hU) ← first x
    let (V, hV) ← first y
    let le (u v : Expr) : FactM Bool := do
      return (← withMain do proveArith (← mkAppM ``LE.le #[u, v])).isSome
    let ubs ← match_expr a with
      | Max.max _ _ _ _ => do
        if U == V || (← le V U) then pure #[U] else if ← le U V then pure #[V]
        else pure #[← withMain (mkAppM ``HAdd.hAdd #[U, V])]
      | Min.min _ _ _ _ => pure #[U, V]
      | _ => pure #[U]
    for ub in ubs do
      if ub == a then continue
      if let some pf ← withMain do
          proveArith (← mkAppM ``LE.le #[a, ub]) (#[hU, hV].filterMap id)
      then out := out.push (ub, pf)
  let hyps ← withMain do
    let mut hs := #[]
    for d in ← getLCtx do
      if !d.isImplementationDetail && (← instantiateMVars d.type).cleanupAnnotations.isForall then
        hs := hs.push d.toExpr
    return hs
  for h in hyps do
    if let some b ← instBound h a then
      unless (b.ub.find? (· == a)).isSome do out := out.push (b.ub, ← withMain b.le)
  modify fun s => { s with atomBounds := s.atomBounds.insert a out }
  return out

/-- Replace in `p` the atoms that `q` lacks by upper bounds (stated, or atoms of `q` larger by
monotonicity) — a polynomial over the naturals grows with its atoms — preferring bounds in the
atoms of `q`.  Returns the new polynomial and
the facts `c m aᵉ ≤ c m Uᵉ` of the replacements. -/
def substBounded (p q : PolyNF) : FactM (PolyNF × Array Expr) := do
  let qs := q.atoms
  let mut p := p
  let mut facts := #[]
  for _ in [0:4] do
    let mut changed := false
    for a in p.atoms do
      if qs.contains a then continue
      let mut bs ← atomBounds a
      -- an atom of `q` that is larger by monotonicity
      for b in qs do
        if let some h ← congrLe a b then bs := bs.push (b, h)
      if bs.isEmpty then continue
      let score (U : Expr) : Nat := ((poly U).atoms.filter (!qs.contains ·)).size
      let (U, h) := bs.foldl (fun b c => if score c.1 < score b.1 then c else b) bs[0]!
      if cost_bound.profile.get (← getOptions) then logInfo m!"cost_bound: {a} ≤ {U}"
      let pu := poly U
      let mut p' : PolyNF := #[]
      for (c, m) in p do
        match m.find? (·.1 == a) with
        | some (_, e) =>
          let rest := m.filter (·.1 != a)
          let hpow ← withMain do
            if e == 1 then pure h else mkAppOptM ``Nat.pow_le_pow_left #[none, none, h, mkNatLit e]
          facts := facts.push (← withMain do
            mkAppM ``Nat.mul_le_mul_left #[← polyExpr #[(c, rest)], hpow])
          p' := polyAdd p' (polyMul #[(c, rest)] ((List.range e).foldl (fun acc _ => polyMul acc pu)
            #[(1, #[])]))
        | none => p' := polyAdd p' #[(c, m)]
      p := p'
      changed := true
    unless changed do break
  return (p, facts)

/-- Prove `P ≤ Q` between coefficients: by `omega` from the facts, or else monomial by
monomial — each monomial of `P` dominated by monomials of `Q` with room in their
coefficients — and linear arithmetic. -/
partial def provePolyLe (P Q : Expr) (subst : Bool := true) : FactM (Option Expr) := do
  if P.nat? == some 0 then return some (← withMain do mkAppM ``Nat.zero_le #[Q])
  let p := poly P
  let q := poly Q
  if let some h ← withMain do proveArith (← mkAppM ``LE.le #[P, Q]) (quick := true) then
    return some h
  -- the atoms that `Q` lacks by their bounds (a polynomial grows with its atoms): what
  -- remains is often plain
  if subst then
    let (p', fs) ← substBounded p q
    if !fs.isEmpty then
      if let some h ← provePolyLe (← withMain (polyExpr p')) Q false then
        if let some pf ← linarithLe P Q (fs.push h) then return some pf
  if let some h ← withMain (proveLe P Q) then return some h
  -- the products distributed (`fuel * (k + 1)` into `fuel * k + fuel`), the atoms left as
  -- they are, so that `omega` sees the same monomials on both sides
  if let some h ← withMain do
      let P' ← polyExpr p
      let Q' ← polyExpr q
      let some hP ← ringEq P P' | return none
      let some hQ ← ringEq Q Q' | return none
      let some h ← proveLe P' Q' | return none
      some <$> mkAppM ``le_trans #[← mkAppM ``le_of_eq #[hP],
        ← mkAppM ``le_trans #[h, ← mkAppM ``le_of_eq #[← mkAppM ``Eq.symm #[hQ]]]]
  then return some h
  -- the scale variables (atoms that no fact mentions: costs per operation, …) factored out:
  -- compared group by group, `P_m * m ≤ Q_m * m` with `P_m ≤ Q_m` by `omega`
  if let some h ← scaleGroups p q P Q then return some h
  -- linear arithmetic, from the hypotheses that are not about costs (e.g. superadditivity of
  -- an abstract cost function)
  if let some h ← linarithLe P Q ((← ctxHyps).map (·.pf) ++ (← get).facts.map (·.pf))
      (only := false) then return some h
  -- which monomials of `Q` dominate which of `P`, with the proofs
  let mut edges : Array (Array (Option Expr)) := #[]
  for (_, m) in p do
    let mut row := #[]
    for (_, M) in q do row := row.push (← domFact m M)
    edges := edges.push row
  -- distribute the coefficients of `P` over those of `Q` (a maximal flow)
  let some flow := maxFlow (p.map (·.1)) (q.map (·.1))
      (edges.map (·.map Option.isSome)) |
    if cost_bound.profile.get (← getOptions) then
      logInfo m!"cost_bound: no flow from {p} to {q}, edges {edges.map (·.map Option.isSome)}"
    return none
  let mut facts := #[]
  for i in [:p.size] do
    for j in [:q.size] do
      if (flow[i]!)[j]! > 0 then
        if let some f := (edges[i]!)[j]! then facts := facts.push f
  -- (the monomials of `Q` are nonnegative)
  for (_, M) in q do
    facts := facts.push (← withMain do mkAppM ``Nat.zero_le #[← atomsProd M])
  linarithLe P Q facts

/-- A proof that the opaque cost `a` is at most `b` by monotonicity in the sizes: of a charge
by a larger quantity of the model, or of an application by its `@[gcongr]` lemma. -/
def atomLe (a b : Expr) : FactM (Option Expr) := do
  if a == b then return some (← withMain do mkAppM ``le_refl #[a])
  if let some p ← withMain (boundAtom a b) then return some p
  congrLe a b

/-- Compare the two sides of the goal in normal form (see above). -/
def normCompare (verbose : Bool) : FactM Unit := withMain do
  let env ← getEnv
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  let some (_, L, R) := tgt.le? |
    throwError "cost_bound: the goal is not an inequality:{indentExpr tgt}"
  let C := costModelOf L
  -- the bounds `q + E ≤ B` of costs `q` among the hypotheses (an induction hypothesis, the
  -- instances of the `@[cost_le]` lemmas): `q ≤ B - E`
  let mut bounds : Array (Expr × NF × Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).cleanupAnnotations
    unless (← isProp ty) && !ty.isForall do continue
    let some (_, l, r) := ty.le? | continue
    unless hasCost env C l do continue
    let nl ← nf env C l
    for (x, c) in nl do
      -- any opaque cost but the basis `C.unit`, `C.addRate`
      let basis := x.isAppOf ``CostModel.unit || x.isAppOf ``CostModel.addRate || x == nfOne
      unless c.nat? == some 1 && !basis do continue
      let rest := nl.filter (·.1 != x)
      bounds := bounds.push (x, rest, r, d.toExpr)
  let rhs ← nf env C R
  let rAtoms := rhs.map (·.1)
  let mut lhs ← nf env C L
  if verbose then
    logInfo m!"cost_bound: model {C}\nleft {lhs}\nright {rhs}\nbounds {bounds.map (·.1)}"
  let mut credit : NF := #[]
  let mut facts : Array Expr := #[]
  -- (each hypothesis eliminates one cost)
  let mut used : Array Expr := #[]
  -- the costs that the right side does not have, by their bounds — or by larger costs with
  -- bounds (monotonicity in the sizes)
  -- (first the exact bounds, to a fixed point, then the moves to larger costs)
  let mut moving := false
  for _ in [0:12] do
    let mut changed := false
    let mut next : NF := #[]
    let targets := (credit.map (·.1)).foldl (fun ts a => if ts.contains a then ts else ts.push a)
      rAtoms
    for (b, c) in lhs do
      if b == nfOne || (← findAtom targets b).isSome then
        next ← next.add #[(b, c)]
        continue
      let cands ← bounds.filterM fun x => return !used.contains x.2.2.2 && (← atomEq x.1 b)
      if cands.isEmpty then
        unless moving do
          next ← next.add #[(b, c)]
          continue
        -- a larger cost of the right side: mapped there below
        if ← targets.anyM fun t => return t != nfOne && (← atomLe b t).isSome then
          next ← next.add #[(b, c)]
          continue
        -- a larger cost with a bound: the coefficient moves there (and that cost is replaced
        -- by its bound in the next round, with all the coefficients moved to it)
        let mut moved := false
        for x in bounds do
          if used.contains x.2.2.2 then continue
          if let some h ← atomLe b x.1 then
            facts := facts.push (← mkAppM ``Nat.mul_le_mul_left #[c, h])
            next ← next.add #[(x.1, c)]
            moved := true
            break
        unless moved do next ← next.add #[(b, c)]
        if moved then changed := true
        continue
      -- a hypothesis of the user's, else the bound in terms of the right side's quantities
      let isLemma (pf : Expr) : MetaM Bool := do
        if pf.isFVar then
          return (← pf.fvarId!.getDecl).userName.toString.startsWith "hcall"
        return false
      let mut best := cands[0]!
      let mut score := 0
      for cand in cands do
        let atoms := (← nf env C cand.2.2.1).map (·.1)
        let sc ← atoms.foldlM (fun n a => do
          return if (← findAtom rAtoms a).isSome then n + 1 else n) 0
        let sc := if ← isLemma cand.2.2.2 then sc else sc + 1000
        if sc > score then best := cand; score := sc
      let (_, rest, B, pf) := best
      used := used.push pf
      next ← next.add (← NF.scale c (← nf env C B))
      credit ← credit.add (← NF.scale c rest)
      facts := facts.push (← mkAppM ``Nat.mul_le_mul_left #[c, pf])
      changed := true
    lhs := next
    if changed then moving := false
    else if moving then break
    else moving := true
  -- the other opaque costs, by larger ones of the right side: those with the fewest choices
  -- first, each where its coefficient still fits
  let targets := (credit.map (·.1)).foldl (fun ts a => if ts.contains a then ts else ts.push a)
    rAtoms
  let mut mapped : NF := #[]
  let mut pending : Array (Expr × Expr × Array (Expr × Expr)) := #[]
  for (b, c) in lhs do
    if b == nfOne || (← findAtom targets b).isSome then
      mapped ← mapped.add #[(b, c)]
      continue
    let mut opts := #[]
    for b' in targets do
      if b' == nfOne then continue
      if let some h ← atomLe b b' then opts := opts.push (b', h)
    if opts.isEmpty then
      -- a basis quantity the right side lacks: compared with `0` below
      mapped ← mapped.add #[(b, c)]
    else pending := pending.push (b, c, opts)
  let capacity (t : Expr) : MetaM Expr := do
    let Q ← rhs.coeff t
    let E ← credit.coeff t
    if E.nat? == some 0 then pure Q else mkAppM ``HAdd.hAdd #[Q, E]
  for (_, c, opts) in pending.qsort (·.2.2.size < ·.2.2.size) do
    let mut choice := opts[0]!
    if opts.size > 1 then
      for (t, h) in opts do
        let P ← mkAppM ``HAdd.hAdd #[← mapped.coeff t, c]
        if (← provePolyLe P (← capacity t)).isSome then
          choice := (t, h)
          break
    facts := facts.push (← mkAppM ``Nat.mul_le_mul_left #[c, choice.2])
    mapped ← mapped.add #[(choice.1, c)]
  -- coefficient by coefficient
  let keys := mapped.foldl (fun ks (b, _) => if ks.contains b then ks else ks.push b) targets
  for b in keys do
    let P ← mapped.coeff b
    let Q₀ ← rhs.coeff b
    let E ← credit.coeff b
    let Q ← if E.nat? == some 0 then pure Q₀ else mkAppM ``HAdd.hAdd #[Q₀, E]
    let some h ← provePolyLe P Q | do
      -- the last word to linear arithmetic over all the hypotheses (a proof may state the
      -- combination it needs), else the coefficient that does not fit
      let g ← getMainGoal
      let s ← Meta.saveState
      try
        Mathlib.Tactic.Linarith.linarith false facts.toList {} g
        replaceMainGoal []
        return
      catch _ => s.restore
      throwError "cost_bound: the coefficient of{indentExpr b}\non the left,{indentExpr P}\n\
        is not at most the one on the right,{indentExpr Q}"
    facts := facts.push (← if b == nfOne then pure h else mkAppM ``Nat.mul_le_mul_right #[b, h])
    -- the right side's terms are nonnegative
    facts := facts.push (← mkAppM ``Nat.zero_le #[← mkAppM ``HMul.hMul #[Q₀, b]])
  if verbose then logInfo m!"cost_bound: {facts.size} facts"
  let g ← getMainGoal
  try Mathlib.Tactic.Linarith.linarith true facts.toList {} g
  catch e => throwError "cost_bound: the final linear arithmetic failed: {e.toMessageData}"
  replaceMainGoal []

/-- Does `e` branch: an `if` among its summands and factors? -/
partial def branches (e : Expr) : Bool :=
  if e.isAppOf ``ite || e.isAppOf ``dite then true
  else if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 then
    branches e.appFn!.appArg! || branches e.appArg!
  else false

/-- If the left side of the goal is a single call `costOf C (f …)` that no lemma and no
hypothesis bounds, unfold it (`cost_unfold f.counted`). -/
def unfoldLonelyCall : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (_, l, _) := tgt.le? | return
  unless l.isAppOfArity ``CostM.cost 3 do return
  let some f := l.appArg!.getAppFn.constName? | return
  unless (((costLeExt.getState (← getEnv)).get? f).getD #[]).isEmpty do return
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some k ← costLemmaKey? (← instantiateMVars d.type) then
      if k == f && (← isProp d.type) then return
  evalTactic (← `(tactic| cost_unfold $(mkIdent f):ident))

/-- The steps of `cost_bound` before the comparison: the operands' facts, the bounds of the
callees, and the goal and these bounds unfolded to the basis (`C.lin`, `C.mulMod`, the
grammar-school model). -/
def costPrepare (verbose : Bool) : FactM Unit := do
  step "operands" operandFacts
  step "callees" <| calleeFacts verbose
  step "operands" operandFacts
  step "unfold" do
    let names ← withMainContext do
      let env ← getEnv
      let mut ns : Array Name := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty := (← instantiateMVars d.type).cleanupAnnotations
        if let some (_, l, _) := ty.le? then
          if (costKey? l).isSome && hasCost env none l && !ty.isForall then
            ns := ns.push d.userName
      return ns
    let ids := names.map mkIdent
    evalTactic (← `(tactic| try simp only [school_mulMod, school_lin, school_divMod_self]
      at $ids:ident* ⊢))
    evalTactic (← `(tactic| try simp only [CostModel.lin, CostModel.mulMod, max_self,
      school_add, school_mul, school_divMod, school_unit, one_mul, mul_one,
      Nat.size_zero, Nat.size_one, Nat.size_two, reduceNatSize] at $ids:ident* ⊢))

/-- The cost model of the goal `L ≤ R` (that of `L`). -/
def goalModel : TacticM (Option Expr) := withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  return tgt.le?.bind fun (_, l, _) => costModelOf l

/-- The steps of `cost_bound` on a goal without branches. -/
def costBoundCore (verbose : Bool) : TacticM Unit := do
  renameShadowed
  -- local definitions unfolded, bit lengths of numerals evaluated
  step "simp" <| evalTactic (← `(tactic| try simp (config := { zetaDelta := true }) only
    [Nat.size_zero, Nat.size_one, Nat.size_two, reduceNatSize] at *))
  let go : FactM Unit := do
    costPrepare verbose
    step "compare" <| normCompare verbose
  discard <| go.run { ctx := ← getMainGoal, model := ← goalModel }

/-- The steps of `cost_bound`: unfold a lonely call, split the branches of the goal, then
close each. -/
def costBound (verbose : Bool) : TacticM Unit := do
  let g :: rest ← getGoals | throwError "cost_bound: no goals"
  setGoals [g]
  unfoldLonelyCall
  let g :: _ ← getGoals | setGoals rest
  let tgt ← instantiateMVars (← g.getType)
  if let some (_, l, _) := tgt.le? then
    if branches l then evalTactic (← `(tactic| split_ifs))
  for g in ← getGoals do
    setGoals [g]
    costBoundCore verbose
  setGoals rest

/-- `cost_bound`: close a cost inequality `L ≤ R` (see the module documentation). -/
elab "cost_bound" : tactic => costBound false

/-- `cost_bound?`: as `cost_bound`, reporting the normal forms and the bounds used. -/
elab "cost_bound?" : tactic => costBound true

/-! ## Uniform big-O bounds

A running time `O(g)` here is *uniform*: one constant for all inputs (and all cost models,
when the model is among them) — `∀ᴼ (x : α) …, P x → f x ≤ O(g x)` is
`∃ c, ∀ (x : α) …, P x → f x ≤ c * g x`.  The constant is derived, not stated: `cost_O`
finds it.  (`isBigO_of_uniform` in `Chapter3/ProbablePrime.lean` turns such a bound into
Mathlib's `f =O[atTop] g`.) -/

/-- `O(t)` in a uniform bound `∀ᴼ …, …`: the constant of the bound times `t`. -/
syntax (name := bigOTerm) "O(" term ")" : term

/-- `∀ᴼ (x : α) …, P x → f x ≤ O(g x)`: `f x ≤ c * g x` for one constant `c` and all `x …`
with `P x`. -/
syntax (name := uniformO) "∀ᴼ " (ppSpace bracketedBinder)+ ", " term : term

macro_rules (kind := uniformO)
  | `(∀ᴼ $bs*, $body) => do
    let body ← body.raw.replaceM fun stx => do
      if stx.getKind == ``bigOTerm then return some (← `((c * $(⟨stx[1]⟩))))
      return none
    `(∃ c : ℕ, ∀ $bs*, $(⟨body⟩))

@[term_elab bigOTerm] def elabBigOTerm : Term.TermElab := fun _ _ =>
  throwError "`O(…)` outside a uniform bound `∀ᴼ …, …`"

namespace CostFacts

/-- The weight of a cost expression: the sum of its coefficients, a cost counting with the
weight of its bound.  If every charge and cost is at most `g`, the expression is at most
`weight · g`. -/
partial def weight (bounds : Array (Expr × Expr)) (depth : Nat) (e : Expr) : Nat :=
  if let some k := e.nat? then k
  else if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``Max.max 4 then
    weight bounds depth e.appFn!.appArg! + weight bounds depth e.appArg!
  else if e.isAppOfArity ``HMul.hMul 6 then
    weight bounds depth e.appFn!.appArg! * weight bounds depth e.appArg!
  else if e.isAppOfArity ``HPow.hPow 6 then
    match e.appArg!.nat? with
    | some k => weight bounds depth e.appFn!.appArg! ^ k
    | none => 1
  else if e.isAppOfArity ``HSub.hSub 6 || e.isAppOfArity ``HDiv.hDiv 6 then
    weight bounds depth e.appFn!.appArg!
  else match bounds.find? (·.1 == e) with
    | some (_, b) => if depth < 8 then weight bounds (depth + 1) b else 1
    | none => 1

end CostFacts

/-- `cost_O`: prove a uniform bound `∀ᴼ …, f ≤ O(g)`, i.e. `∃ c, ∀ …, f ≤ c * g`: bound the
costs of `f` (as `cost_bound`), take for `c` the weight of the result, and close
`f ≤ c * g` by `cost_bound`.  `cost_O [h₁, …]` adds the facts `hᵢ` first (about the bound
variables, by their names in the statement). -/
syntax "cost_O" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cost_O $[[$hs,*]]?) => do
  let g ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let_expr Exists α p := ty | throwError "cost_O: the goal is not `∃ c, …`"
  let c ← mkFreshExprMVar α
  let body ← mkFreshExprSyntheticOpaqueMVar (p.beta #[c])
  g.assign (← mkAppOptM ``Exists.intro #[α, p, c, body])
  -- the bound variables, by their names in the statement
  let n := getIntrosSize (← instantiateMVars (← body.mvarId!.getType))
  let (_, g') ← body.mvarId!.introNP n
  replaceMainGoal [g']
  -- the facts given
  for h in (hs.map (·.getElems) |>.getD #[]) do
    evalTactic (← `(tactic| have := $h))
  unfoldLonelyCall
  if (← getGoals).isEmpty then c.mvarId!.assign (mkNatLit 1); return
  -- the weight of the left side, after its costs are bounded
  let s ← saveState
  renameShadowed
  evalTactic (← `(tactic| try simp (config := { zetaDelta := true }) only
    [Nat.size_zero, Nat.size_one, Nat.size_two, reduceNatSize] at *))
  let go : CostFacts.FactM Nat := do
    costPrepare false
    evalTactic (← `(tactic| try simp only [school_mul, school_divMod, school_unit,
      school_add, max_self] at *))
    withMainContext do
      let tgt ← instantiateMVars (← getMainTarget)
      let_expr LE.le _ _ lhs _ := tgt | throwError "cost_O: not an inequality `f ≤ c * g`"
      let mut bounds := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if let some (_, l, r) := (← instantiateMVars d.type).le? then bounds := bounds.push (l, r)
      return CostFacts.weight bounds 0 lhs
  let (k, _) ← go.run { ctx := ← getMainGoal }
  s.restore
  c.mvarId!.assign (mkNatLit (max k 1))
  costBound false

end PrimeNumbers.Chapter9
