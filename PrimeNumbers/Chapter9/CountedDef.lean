import PrimeNumbers.Chapter9.Counted

/-!
# `counted_def`: write an algorithm once, in plain Lean

```
counted_def powMod (x n m : ℕ) : ℕ :=
  if n = 0 then 1 % m
  else if n % 2 = 0 then
    let y := powMod x (n / 2) m
    y * y % m
  else …
termination_by n
```

From this one body the command produces

* `powMod` — the plain definition, exactly as written (all correctness proofs are about it);
* `powMod.counted` — the same computation in a counting monad: before each value is used,
  the cost of computing it is recorded.  Values, conditions and termination measures are
  the original plain expressions; only charges are added;
* `powMod.counted_val : CostM.val C (powMod.counted …) = powMod …`, proved automatically.

`costOf C (powMod x n m)` is the number of bit operations of the call under the cost model
`C`.

**What is charged** (in evaluation order, on the operands *as elaborated*):
* `a * b`, `a / b`, `a % b`, `a ∣ b`, `a ^ e` — unless by a numeric literal (a shift or
  mask) — at the cost the type assigns (`MulCost`, `DivCost`, `PowCost`: bit lengths for
  `ℕ` and `ℤ`, a modular multiplication for `ZMod n`, …);
* a call of a function with a counted version (another `counted_def`, or a library function
  given one: `Nat.gcd`, `Nat.sqrt`, `Nat.log`, `List.prod`, the list combinators, array
  writes);
* a call of a function parameter `P` through its charge function `P_charge` (a counted
  version takes one per function parameter); a `fun`, a section `(· < B)`, a function or a
  partial application passed as an argument is charged wherever it is applied.

Conditions, `match` discriminants and `let` values are charged before the branch; an `if`,
`match` or `let` inside an expression is charged with the same branching as its value;
`&&`, `||`, `∧`, `∨` short-circuit.

**What is rejected** — so that nothing can silently be left out of the count: a call of
an expensive library function (`notFree`) without a counted version in scope; a call of a
function of this project that is neither counted nor `@[cost_free]`; an inverse; and
chargeable work under a binder that cannot be followed (e.g. inside a `fun` passed to a
function without a counted version).

Running-time theorems are proved about `costOf C (f …)`: `cost_unfold f.counted` unfolds
one step and takes the branches the hypotheses decide, `cost_simp` unfolds the bookkeeping.
-/

namespace PrimeNumbers.Chapter9

open Lean Elab Command Term Meta

/-- Library functions that are not free: a call of one of them in a `counted_def` must be
charged through its counted version (e.g. `Nat.gcd.counted`, by Algorithm 2.1.2). -/
private def notFree : List Name :=
  [``Nat.gcd, ``Nat.lcm, ``Nat.sqrt, ``Int.gcd, ``Int.lcm, ``Nat.xgcd, ``Nat.gcdA, ``Nat.gcdB,
   ``Int.sqrt, ``Nat.minFac, ``Nat.primeFactorsList, ``Nat.primeFactors, ``Nat.factorization,
   ``Nat.divisors, ``Nat.factorial, ``Nat.choose, ``Nat.totient, ``Nat.Prime, ``Prime,
   ``Squarefree, ``IsSquare, ``Nat.Coprime, ``Inv.inv, ``ZMod.inv, ``HDiv.hDiv, ``Nat.find,
   ``List.prod, ``Multiset.prod, ``Finset.prod, ``Nat.pow, ``Nat.log, ``Nat.clog,
   ``Array.setIfInBounds, ``Array.set!, ``Array.replicate, ``Array.set,
   ``legendreSym, ``jacobiSym, ``orderOf]

/-- Elaborate a call `g a₁ … aₖ`; if its head is a constant `g` with a counted version,
return `g.counted` and the elaborated arguments.  A call that cannot be charged — of a
library function that is not free (`notFree`) or of a function of this project that is
neither counted nor `@[cost_free]` — is an error. -/
private def classifyCall (e : Expr) (ref : Syntax) : TermElabM (Option (Name × Array Expr)) := do
  let some c := e.getAppFn.constName? | return none
  if (← whnfR (← inferType e)).isSort then return none   -- a type, not a computation
  let env ← getEnv
  let cc := c ++ `counted
  if env.contains cc then return some (cc, e.getAppArgs)
  if notFree.contains c then
    throwErrorAt ref "counted_def: `{c}` is not free, and no `{cc}` is in scope to charge it \
      (import the file that defines it)"
  if (`PrimeNumbers).isPrefixOf c && !costFreeAttr.hasTag env c &&
      !(env.find? c).any (fun i => i.isCtor) && (env.getProjectionFnInfo? c).isNone then
    throwErrorAt ref "counted_def: `{c}` has no counted version; define it with \
      `counted_def`, or mark it `@[cost_free]` if it does no big-number arithmetic"
  return none

/-- Elaborate a call on its own. -/
private def elabCallAlone (call : Syntax) : TermElabM Expr := do
  let e ← elabTerm call none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private def countedCallee? (call : Syntax) : TermElabM (Expr × Option (Name × Array Expr)) := do
  let e ← elabCallAlone call
  return (e, ← classifyCall e call[0])

/-- The calls of a `counted_def` body as elaborated in place (`call_site%`), so that each is
charged exactly as it is computed — e.g. `power 2 k` at the type the context gives `2`. -/
initialize callSites : IO.Ref (Std.HashMap Name Expr) ← IO.mkRef {}

/-- `call_site% s e`: the expression `e`, recorded as the call site `s`. -/
syntax (name := callSite) "call_site% " ident ppSpace term:max : term

@[term_elab callSite] private def elabCallSite : TermElab := fun stx ety? => do
  let r ← elabTerm stx[2] ety?
  callSites.modify (·.insert stx[1].getId r)
  return r

/-- `no_counted% (g a₁ … aₖ)`: the call itself, but an error if `g` has a counted version —
used for calls under a binder, whose cost cannot be charged in place. -/
syntax (name := noCounted) "no_counted% " term:max : term

@[term_elab noCounted] private def elabNoCounted : TermElab := fun stx ety? => do
  let call := stx[1]
  let (e, cc?) ← countedCallee? call
  if let some (cc, _) := cc? then
    throwErrorAt call[0] "counted_def: the call of `{cc.getPrefix}` inside a nested binding \
      form (`fun`, `do`, …) cannot be counted in place; lift it out of the binder"
  if let some ety := ety? then discard <| isDefEq (← inferType e) ety
  return e

/-- `charge% (a ∘ b)`: the charge for one primitive operation, on its operands *as
elaborated* (so with any coercions inserted): `chargeMul a b` for `a * b`, `chargeMod a b`
for `a % b` and `a / b`, `chargeMod b a` for `a ∣ b`, `chargePow a e` for `a ^ e`. -/
syntax (name := chargeOp) "charge% " term:max : term

@[term_elab chargeOp] private def elabChargeOp : TermElab := fun stx ety? => do
  let e ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let args := e.getAppArgs
  let (prim, x, y) ← match e.getAppFn.constName?, args.size with
    | some ``HMul.hMul, 6 => pure (``NatArith.chargeMul, args[4]!, args[5]!)
    | some ``HMod.hMod, 6 => pure (``NatArith.chargeMod, args[4]!, args[5]!)
    | some ``HDiv.hDiv, 6 => pure (``NatArith.chargeMod, args[4]!, args[5]!)
    | some ``HPow.hPow, 6 => pure (``NatArith.chargePow, args[4]!, args[5]!)
    | some ``Dvd.dvd, 4 => pure (``NatArith.chargeMod, args[3]!, args[2]!)
    | _, _ => throwErrorAt stx[1] "counted_def: cannot charge {e}"
  elabTerm (← `($(mkCIdent prim) $(← exprToSyntax x) $(← exprToSyntax y))) ety?

/-- For each explicit parameter of the constant `c`: is it a function? -/
private def explicitFunParams (c : Name) : MetaM (Array Bool) := do
  forallTelescopeReducing (← getConstInfo c).type fun xs _ => do
    let mut r := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then r := r.push (← whnfR d.type).isForall
    return r

/-- Does an elaborated charge function do any chargeable work? -/
private def chargesSomething (e : Expr) : MetaM Bool := do
  let consts := e.getUsedConstants
  if consts.any (fun c => c == ``NatArith.chargeMul || c == ``NatArith.chargeMod ||
      c == ``NatArith.chargePow || (c.isStr && c.getString! == "counted")) then return true
  let lctx ← getLCtx
  return e.hasAnyFVar fun x =>
    (lctx.find? x).any fun d => d.userName.toString.endsWith "_charge"

private def isHole (t : Syntax) : Bool := t.isOfKind ``Lean.Parser.Term.hole

/-- `charge_tag% k a`: the argument `a`, marked as the `k`-th argument of a call, so that its
charge function can be found after elaboration (when implicit arguments and dot notation
have moved the arguments around). -/
syntax (name := chargeTag) "charge_tag% " num ppSpace term:max : term

@[term_elab chargeTag] private def elabChargeTag : TermElab := fun stx ety? => do
  let r ← elabTerm stx[2] ety?
  return mkMData (KVMap.empty.insert `chargeTag (.ofNat stx[1].isNatLit?.get!)) r

/-- The tag of an argument marked by `charge_tag%`. -/
private def chargeTag? : Expr → Option Nat
  | .mdata d _ => match d.find `chargeTag with
    | some (.ofNat k) => some k
    | _ => none
  | _ => none

/-- `counted_call% (g a₁ … aₖ) [c₁, …, cₖ]`: the cost of a call — `g.counted a₁ … aₖ` when
`g` has a counted version (passing, for each function argument `aᵢ`, its charge function
`cᵢ`), otherwise nothing (`pure ()`), after checking that the functions passed to `g` do
no chargeable work. -/
syntax (name := countedCall) "counted_call% " ident ppSpace term:max " [" term,* "]" : term

/-- Is `b` a binder of one of the cost classes (`MulCost`, `DivCost`, `PowCost`)?  Counted
versions may take these in addition to the binders of the plain function. -/
private def isCostInst (ty : Expr) : Bool :=
  match ty.getAppFn.constName? with
  | some c => c == ``MulCost || c == ``DivCost || c == ``PowCost || c == ``Monad ||
      c == ``NatArith
  | none => false

/-- Build the counted call `cc a₁ … aₖ charges…` in the monad `m`: the binders of `cc` are
the monad and its instances, the binders of the plain function (to which `args` are
assigned in order), possibly cost-class instances (synthesized), and the charge functions
of the function parameters (elaborated from `charges`). -/
private def mkCountedCall (cc : Name) (m : Expr) (args : Array Expr) (charges : Array Syntax)
    (ref : Syntax) : TermElabM Expr := do
  let fn ← mkConstWithFreshMVarLevels cc
  let (xs, bis, _) ← forallMetaTelescopeReducing (← inferType fn)
  let monadTy := mkForall `_ .default (mkSort levelOne) (mkSort levelOne)
  let mut monadDone := false
  let mut i := 0          -- next plain argument
  let mut j := 0          -- next charge function
  for h : k in [0:xs.size] do
    let x := xs[k]
    let ty ← instantiateMVars (← inferType x)
    if !monadDone && bis[k]! == .implicit && ty == monadTy then
      -- the counting monad (it follows any section variables of the plain function)
      unless ← isDefEq x m do throwErrorAt ref "counted_def: monad mismatch"
      monadDone := true
    else if bis[k]! == .instImplicit && isCostInst ty then
      x.mvarId!.assign (← synthInstance ty)
    else if i < args.size then
      unless ← isDefEq x args[i]! do
        throwErrorAt ref "counted_def: argument mismatch in the counted call of `{cc}`"
      i := i + 1
    else if bis[k]! == .instImplicit then
      x.mvarId!.assign (← synthInstance ty)
    else
      let some ch := charges[j]? | throwErrorAt ref "counted_def: missing charge function"
      unless ← isDefEq x (← elabTermEnsuringType ch ty) do
        throwErrorAt ref "counted_def: charge function mismatch"
      j := j + 1
  instantiateMVars (mkAppN fn xs)

@[term_elab countedCall] private def elabCountedCall : TermElab := fun stx ety? => do
  let site := stx[1].getId
  let call := stx[2]
  let charges := stx[4].getSepArgs
  -- the call as elaborated in place, if its site has been elaborated (else wait for it)
  if !(← callSites.get).contains site then tryPostpone
  let inPlace? ← match (← callSites.get).get? site with
    | some e => do
        let mut e ← instantiateMVars e
        if e.hasExprMVar then
          tryPostpone
          synthesizeSyntheticMVarsNoPostponing
          e ← instantiateMVars e
        let lctx ← getLCtx
        pure (if e.hasExprMVar || e.hasAnyFVar (fun x => !lctx.contains x) then none
          else some e)
    | none => pure none
  let tagged : Bool := charges.any (!isHole ·)
  -- the tags of the function arguments are found on the call elaborated alone
  let alone? ← if tagged || inPlace?.isNone then some <$> elabCallAlone call else pure none
  let e := inPlace?.getD (alone?.getD default)
  -- a function value (a partial application) costs nothing until it is applied
  if (← whnfR (← inferType e)).isForall then return ← elabTerm (← `(pure ())) ety?
  let cc? ← classifyCall e call[0]
  let some c := e.getAppFn.constName? | return ← elabTerm (← `(pure ())) ety?
  let some m := (← getLCtx).findFromUserName? `countedMonad
    | throwErrorAt call "counted_def: no counting monad in scope"
  -- the explicit arguments, whether each is a function, and its tag
  let explicitArgs ← forallTelescopeReducing (← inferType e.getAppFn) fun xs _ => do
    let mut r : Array (Expr × Bool × Option Nat) := #[]
    for h : j in [0:xs.size] do
      if j < e.getAppNumArgs then
        let d ← xs[j].fvarId!.getDecl
        if d.binderInfo.isExplicit then
          let tag := alone?.bind fun a => if j < a.getAppNumArgs then chargeTag? a.getAppArgs[j]!
            else none
          r := r.push (e.getAppArgs[j]!.consumeMData, (← whnfR d.type).isForall, tag)
    return r
  let chargeFor (tag : Option Nat) : Option Syntax := do
    let ch ← charges[← tag]?
    if isHole ch then none else some ch
  match cc? with
  | some (cc, args) =>
      let mut extra : Array Syntax := #[]
      for h : i in [0:explicitArgs.size] do
        let (_, isFun, tag) := explicitArgs[i]
        if isFun then
          let some ch := chargeFor tag
            | throwErrorAt call[0] "counted_def: cannot charge the function passed as argument \
                {i + 1} of `{c}`; pass a `fun`, a function or a function parameter"
          extra := extra.push ch
      let r ← mkCountedCall cc m.toExpr (args.map (·.consumeMData)) extra call
      if let some ety := ety? then discard <| isDefEq (← inferType r) ety
      return r
  | none =>
      -- `g` is free: the functions passed to it must not do chargeable work
      for (a, isFun, tag) in explicitArgs do
        unless isFun do continue
        let some ch := chargeFor tag | continue
        let aTy ← whnfR (← inferType a)
        let expected ← forallTelescopeReducing aTy fun xs _ =>
          mkForallFVars xs (mkApp m.toExpr (mkConst ``Unit))
        let ce ← instantiateMVars (← elabTermEnsuringType ch expected)
        if ← chargesSomething ce then
          throwErrorAt call[0] "counted_def: the function passed to `{c}` does work that \
            cannot be charged (`{c}` has no counted version)"
      elabTerm (← `(pure ())) ety?

/-- `charge_of% (g a₁ … aₖ) [c₁, …, cₖ]`, for a function `g a₁ … aₖ` (possibly a partial
application, whose arguments have the charge functions `cᵢ`): the charge function
`fun x₁ … xⱼ ↦ cost of g a₁ … aₖ x₁ … xⱼ`, at the expected function type. -/
syntax (name := chargeOf) "charge_of% " term:max " [" term,* "]" : term

@[term_elab chargeOf] private def elabChargeOf : TermElab := fun stx ety? => do
  let some ety := ety? | throwErrorAt stx "charge_of%: expected type unknown"
  let fn := stx[1]
  let charges : Array Term := stx[3].getSepArgs.map (⟨·⟩)
  -- the head and the arguments given (tagged with the positions of their charges)
  let (head, given) : Syntax × Array Syntax := match fn with
    | `($g $as*) => (g, as.map (·.raw))
    | _ => (fn, #[])
  let given ← given.mapIdxM fun i a =>
    return (← `(charge_tag% $(Syntax.mkNumLit (toString i)) $(⟨a⟩))).raw
  forallTelescopeReducing ety fun xs res => do
    let xsStx ← xs.mapM fun x => exprToSyntax x
    let holes ← xs.mapM fun _ => `(_)
    let site := mkIdent (← mkFreshUserName `site)
    let call := Syntax.mkApp ⟨head⟩ ((given.map (⟨·⟩)) ++ xsStx)
    let body ← elabTermEnsuringType
      (← `(bind (counted_call% $site $call [$(charges ++ holes),*]) fun _ => pure ())) res
    mkLambdaFVars xs body

/-- `costOf C (f a₁ … aₖ)`: the number of bit operations that the call `f a₁ … aₖ` of an
algorithm defined by `counted_def` performs under the cost model `C`, i.e.
`CostM.cost C (f.counted a₁ … aₖ)`. -/
syntax (name := costOfStx) "costOf " term:max ppSpace term:max : term

@[term_elab costOfStx] private def elabCostOf : TermElab := fun stx ety? => do
  let call := stx[2]
  match (← countedCallee? call).2 with
  | some (cc, args) =>
      let C ← elabTermEnsuringType stx[1] (mkConst ``CostModel)
      let m := mkApp (mkConst ``CostM) C
      let r ← mkCountedCall cc m args #[] call
      let α ← mkFreshTypeMVar
      unless ← isDefEq (← inferType r) (mkApp m α) do throwErrorAt call "costOf: type mismatch"
      let res := mkApp3 (mkConst ``CostM.cost) C (← instantiateMVars α) r
      if let some ety := ety? then discard <| isDefEq (← inferType res) ety
      return res
  | none => throwErrorAt call "costOf: `{call}` is not a call of a counted algorithm"

open PrettyPrinter Delaborator SubExpr in
/-- Print `CostM.cost C (f.counted a₁ … aₖ)` as `costOf C (f a₁ … aₖ)`. -/
@[delab app.PrimeNumbers.Chapter9.CostM.cost]
private def delabCostOf : Delab := do
  let e ← getExpr
  guard (e.getAppNumArgs == 3)
  let x := e.appArg!
  let .const c ls := x.getAppFn | failure
  guard (c.isStr && c.getString! == "counted" && x.getAppNumArgs ≥ 3)
  let _ := ls
  let some call ← liftM (m := MetaM) (observing? <| mkAppOptM c.getPrefix
      ((x.getAppArgs.extract 3 x.getAppNumArgs).map some)) | failure
  let C ← withNaryArg 0 delab
  let some callStx ← liftM (m := MetaM) (observing? (PrettyPrinter.delab call)) | failure
  `(costOf $C $callStx)

/-- Is `t` a numeric literal or a power of two `2 ^ e`?  Multiplying, dividing or reducing by
one is a shift or a mask, which is not charged. -/
private def isNumLit (t : Term) : Bool :=
  let t := match t with | `(($e)) => e | e => e
  t.raw.isNatLit?.isSome || match t with
    | `(2 ^ $_) => true
    | _ => false

/-- Does the syntax contain a charged operator (`*`, `%`, `/`, `∣` or `^` not by a literal)? -/
private partial def hasCharged (stx : Syntax) : Bool :=
  match stx with
  | `($a * $b) | `($a % $b) =>
      !(isNumLit a || isNumLit b) || hasCharged a || hasCharged b
  | `($a / $b) => !isNumLit b || hasCharged a || hasCharged b
  | `($a ∣ $b) => !isNumLit a || hasCharged a || hasCharged b
  | `($a ^ $k) => !(isNumLit a && isNumLit k) || hasCharged a || hasCharged k
  | _ => stx.getArgs.any hasCharged

/-- Does the syntax mention one of the identifiers `xs`? -/
private partial def mentions (xs : List Name) (stx : Syntax) : Bool :=
  (stx.isIdent && xs.contains stx.getId) || stx.getArgs.any (mentions xs)

/-- What `counted_def` knows about the function being defined. -/
private structure Ctx where
  /-- its name (recursive calls) -/
  self : Name
  /-- its function parameters, with their charge functions -/
  funs : Array (Name × Ident)
  /-- the positions of the function parameters among the explicit arguments -/
  funPos : Array Nat

/-- Charges, in evaluation order. -/
private abbrev HoistM := StateT (Array Term) MacroM

/-- Put the recorded charges in front of `body`, in order. -/
private def wrap (charges : Array Term) (body : Term) : MacroM Term := do
  let mut r := body
  for comp in charges.reverse do
    r ← `(bind $comp fun _ => $r)
  return r

/-- The body of a `fun` (`fun x y ↦ b`), if it is one. -/
private def funBody? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Lean.Parser.Term.fun && stx[1].isOfKind ``Lean.Parser.Term.basicFun then
    some stx[1][3]
  else none

/-- Replace the `·` of a section `(… · …)` by the identifiers `xs`, in order. -/
private partial def fillCDots (xs : Array Ident) (stx : Syntax) : StateM Nat Syntax := do
  if stx.isOfKind ``Lean.Parser.Term.cdot then
    let i ← get; set (i + 1); return xs[i]!.raw
  match stx with
  | .node info kind args => return .node info kind (← args.mapM (fillCDots xs))
  | _ => pure stx

private partial def countCDots (stx : Syntax) : Nat :=
  if stx.isOfKind ``Lean.Parser.Term.cdot then 1 else (stx.getArgs.map countCDots).sum

/-- A section `(B < ·)` as the equivalent `fun`. -/
private def sectionToFun? (stx : Syntax) : MacroM (Option Syntax) := do
  unless stx.isOfKind ``Lean.Parser.Term.paren do return none
  let k := countCDots stx[1]
  if k == 0 then return none
  let xs ← (Array.range k).mapM fun i => do
    return mkIdent (← Macro.addMacroScope (Name.mkSimple s!"sec{i}"))
  let body := ((fillCDots xs stx[1]).run' 0)
  return some (← `(fun $xs* => $(⟨body⟩)))

private partial def stripParens : Syntax → Syntax
  | `(($e)) => stripParens e
  | e => e

mutual

/-- **Charging.**  Walk an expression in evaluation order (innermost first, left to right),
recording a charge for every charged operation (on its plain operands), every call of a
counted function (its counted version) and every call of a function parameter (its charge
function).  The residual expression is the original one, so values, `if` conditions and
termination measures stay the original plain expressions.  A conditional sub-expression
(`if`, `match`, `let`) is charged with the same branching as its value. -/
private partial def hoist (ctx : Ctx) (e : Syntax) : HoistM Syntax := do
  match e with
  | `($a * $b) =>
      let ra ← hoist ctx a; let rb ← hoist ctx b
      unless isNumLit ⟨a⟩ || isNumLit ⟨b⟩ do
        modify (·.push (← `(charge% ($(⟨ra⟩) * $(⟨rb⟩)))))
      `($(⟨ra⟩) * $(⟨rb⟩))
  | `($a % $b) =>
      let ra ← hoist ctx a; let rb ← hoist ctx b
      unless isNumLit ⟨b⟩ do
        modify (·.push (← `(charge% ($(⟨ra⟩) % $(⟨rb⟩)))))
      `($(⟨ra⟩) % $(⟨rb⟩))
  | `($a / $b) =>
      let ra ← hoist ctx a; let rb ← hoist ctx b
      unless isNumLit ⟨b⟩ do
        modify (·.push (← `(charge% ($(⟨ra⟩) / $(⟨rb⟩)))))
      `($(⟨ra⟩) / $(⟨rb⟩))
  | `($a ^ $k) =>
      let ra ← hoist ctx a; let rk ← hoist ctx k
      unless isNumLit a do
        match k.raw.isNatLit? with
        | some n =>
            -- `a ^ n` is computed as `((a * a) * a) ⋯`: charge each product
            for i in [1:n] do
              let lit := Syntax.mkNumLit (toString i)
              modify (·.push (← `(charge% ($(⟨ra⟩) ^ $lit * $(⟨ra⟩)))))
        | none => modify (·.push (← `(charge% ($(⟨ra⟩) ^ $(⟨rk⟩)))))
      `($(⟨ra⟩) ^ $(⟨rk⟩))
  | `($_⁻¹) =>
      Macro.throwErrorAt e "counted_def: an inverse is not a primitive operation; compute it \
        with a counted function such as `modInv`"
  | `($a ∣ $b) =>
      -- a divisibility test computes `b mod a`
      let ra ← hoist ctx a; let rb ← hoist ctx b
      unless isNumLit ⟨a⟩ do
        modify (·.push (← `(charge% ($(⟨ra⟩) ∣ $(⟨rb⟩)))))
      `($(⟨ra⟩) ∣ $(⟨rb⟩))
  | `($a && $b) =>
      let ra ← hoist ctx a
      let (rb, cb) ← (hoist ctx b).run #[]
      unless cb.isEmpty do
        let wb ← wrap cb (← `(pure ()))
        modify (·.push (← `(if $(⟨ra⟩) then $wb else pure ())))
      `($(⟨ra⟩) && $(⟨rb⟩))
  | `($a || $b) =>
      let ra ← hoist ctx a
      let (rb, cb) ← (hoist ctx b).run #[]
      unless cb.isEmpty do
        let wb ← wrap cb (← `(pure ()))
        modify (·.push (← `(if $(⟨ra⟩) then pure () else $wb)))
      `($(⟨ra⟩) || $(⟨rb⟩))
  | `($a ∧ $b) =>
      let ra ← hoist ctx a
      let (rb, cb) ← (hoist ctx b).run #[]
      unless cb.isEmpty do
        let wb ← wrap cb (← `(pure ()))
        modify (·.push (← `(if $(⟨ra⟩) then $wb else pure ())))
      `($(⟨ra⟩) ∧ $(⟨rb⟩))
  | `($a ∨ $b) =>
      let ra ← hoist ctx a
      let (rb, cb) ← (hoist ctx b).run #[]
      unless cb.isEmpty do
        let wb ← wrap cb (← `(pure ()))
        modify (·.push (← `(if $(⟨ra⟩) then pure () else $wb)))
      `($(⟨ra⟩) ∨ $(⟨rb⟩))
  | `(if $c then $a else $b) =>
      let rc ← hoist ctx c
      let (ra, ca) ← (hoist ctx a).run #[]
      let (rb, cb) ← (hoist ctx b).run #[]
      unless ca.isEmpty && cb.isEmpty do
        let wa ← wrap ca (← `(pure ()))
        let wb ← wrap cb (← `(pure ()))
        modify (·.push (← `(if $(⟨rc⟩) then $wa else $wb)))
      `(if $(⟨rc⟩) then $(⟨ra⟩) else $(⟨rb⟩))
  | `(if $h:ident : $c then $a else $b) =>
      let rc ← hoist ctx c
      let (ra, ca) ← (hoist ctx a).run #[]
      let (rb, cb) ← (hoist ctx b).run #[]
      unless ca.isEmpty && cb.isEmpty do
        let wa ← wrap ca (← `(pure ()))
        let wb ← wrap cb (← `(pure ()))
        modify (·.push (← `(if $h:ident : $(⟨rc⟩) then $wa else $wb)))
      `(if $h:ident : $(⟨rc⟩) then $(⟨ra⟩) else $(⟨rb⟩))
  | `(let $x:ident := $v; $b) =>
      let rv ← hoist ctx v
      let (rb, cb) ← (hoist ctx b).run #[]
      unless cb.isEmpty do
        let wb ← wrap cb (← `(pure ()))
        modify (·.push (← `(let $x:ident := $(⟨rv⟩); $wb)))
      `(let $x:ident := $(⟨rv⟩); $(⟨rb⟩))
  | `($f:ident $args*) => hoistApp ctx f args
  | `($x:ident) =>
      -- `l.prod`, `n.size`: a call written as a field of a variable
      if x.getId.isStr && !x.getId.getPrefix.isAnonymous && x.getId != ctx.self then
        let site := mkIdent (← withFreshMacroScope (MonadQuotation.addMacroScope `site))
        modify (·.push (← `(counted_call% $site $x:ident [])))
        return ← `(call_site% $site $x:ident)
      return x
  | `($f $args*) =>
      -- a call with a computed head (e.g. dot notation `(l.map g).prod`)
      let f' ← hoist ctx f
      hoistApp ctx ⟨f'⟩ args
  | _ =>
      if e.isOfKind ``Lean.Parser.Term.match then
        -- charge the discriminants, then the selected alternative
        let discrs' ← hoist ctx e[3]
        let alts := e[5][0].getArgs
        let mut alts' := #[]
        let mut chargeAlts := #[]
        let mut any := false
        for alt in alts do
          let (r, c) ← (hoist ctx alt[3]).run #[]
          any := any || !c.isEmpty
          alts' := alts'.push (alt.setArg 3 r)
          chargeAlts := chargeAlts.push (alt.setArg 3 (← wrap c (← `(pure ()))))
        let m := (e.setArg 3 discrs')
        if any then
          modify (·.push ⟨m.setArg 5 (m[5].setArg 0 (mkNullNode chargeAlts))⟩)
        return m.setArg 5 (m[5].setArg 0 (mkNullNode alts'))
      if e.isOfKind ``Lean.Parser.Term.fun || e.isOfKind ``Lean.Parser.Term.do ||
          e.isOfKind ``Lean.Parser.Term.have || e.isOfKind ``Lean.Parser.Term.let then
        if hasCharged e || mentions (ctx.self :: (ctx.funs.map (·.1)).toList) e then
          Macro.throwErrorAt e "counted_def: arithmetic, a recursive call or a call of a \
            function parameter inside a nested binding form (`fun`, `do`, …) cannot be \
            counted in place; lift it out of the binder"
        return ← guardCalls e
      match e with
      | .node info kind args => return .node info kind (← args.mapM (hoist ctx))
      | _ => pure e
where
  /-- Under a binder nothing is hoisted; calls are checked not to need counting. -/
  guardCalls (e : Syntax) : HoistM Syntax := do
    if let `($f:ident $args*) := e then
      let args' ← args.mapM fun a => do return (⟨← guardCalls a.raw⟩ : Term)
      return ← `(no_counted% ($f $args'*))
    match e with
    | .node info kind args => return .node info kind (← args.mapM guardCalls)
    | _ => pure e

/-- An argument: a `fun` is kept as it is (its work is charged through its charge
function), anything else is charged in place. -/
private partial def hoistArg (ctx : Ctx) (a : Syntax) : HoistM Syntax := do
  if (funBody? (stripParens a)).isSome then return a
  if (← sectionToFun? a).isSome then return a
  hoist ctx a

/-- The charge function of an argument passed for a function parameter: for a `fun`, the
same `fun` with its body's charges; for a function parameter of our own, its charge
function. -/
private partial def chargeOfArg (ctx : Ctx) (a : Syntax) : MacroM (Option Term) := do
  if let some f ← sectionToFun? a then return ← chargeOfArg ctx f
  let a := stripParens a
  if a.isIdent then
    if let some (_, c) := ctx.funs.find? (·.1 == a.getId) then return some c
    return some (← `(charge_of% $(⟨a⟩) []))
  if let some body := funBody? a then
    let (_, c) ← (hoist ctx body).run #[]
    return some ⟨a.setArg 1 (a[1].setArg 3 (← wrap c (← `(pure ()))))⟩
  if let `($g:ident $as*) := a then
    unless g.getId == ctx.self || ctx.funs.any (·.1 == g.getId) do
      let cs ← as.mapM fun b => do return (← chargeOfArg ctx b).getD (← `(_))
      return some (← `(charge_of% ($(⟨a⟩)) [$cs,*]))
  return none

private partial def hoistApp (ctx : Ctx) (f : Term) (args : Array Term) : HoistM Syntax := do
  let args' ← args.mapM fun a => do return (⟨← hoistArg ctx a.raw⟩ : Term)
  let call ← `($f $args'*)
  let fid := if f.raw.isIdent then f.raw.getId else .anonymous
  if fid == ctx.self then
    -- charge a recursive call by running its counted version; its *value* is the plain
    -- call, so the counted and plain versions agree by unfolding once
    let mut extra : Array Term := #[]
    for i in ctx.funPos do
      let some a := args[i]? | Macro.throwErrorAt f "counted_def: partial recursive call"
      let some c ← chargeOfArg ctx a
        | Macro.throwErrorAt a "counted_def: cannot charge this function argument; pass a \
            `fun` or a function parameter"
      extra := extra.push c
    modify (·.push (← `($(mkIdent (ctx.self ++ `counted)) $args'* $extra*)))
  else if let some (_, c) := ctx.funs.find? (·.1 == fid) then
    -- a call of a function parameter: charge it with its charge function
    modify (·.push (← `($c $args'*)))
  else
    -- a call of another function: charge its counted version, if it has one; the
    -- arguments that may be functions are tagged with the position of their charge function
    let mut tagged : Array Term := #[]
    let mut charges : Array Term := #[]
    for h : k in [0:args.size] do
      match ← chargeOfArg ctx args[k] with
      | some c =>
          tagged := tagged.push (← `(charge_tag% $(Syntax.mkNumLit (toString k)) $(args'[k]!)))
          charges := charges.push c
      | none =>
          tagged := tagged.push args'[k]!
          charges := charges.push (← `(_))
    let site := mkIdent (← withFreshMacroScope (MonadQuotation.addMacroScope `site))
    modify (·.push (← `(counted_call% $site ($f $tagged*) [$charges,*])))
    return ← `(call_site% $site ($call))
  return call

end

/-- Translate a plain function body into a computation in the counting monad.  At the top
level of each branch, `if`, `match` and `let` structure the computation; every charge of an
expression (including `if` conditions, `match` discriminants and `let` values) is recorded,
left to right, before it is used. -/
private partial def translate (ctx : Ctx) (e : Term) : MacroM Term := do
  if e.raw.isOfKind ``Lean.Parser.Term.match then
    -- (node layout: "match" generalizing? motive? discriminants "with" matchAlts)
    let (discrs', c) ← (hoist ctx e.raw[3]).run #[]
    let alts := e.raw[5][0].getArgs
    let alts' ← alts.mapM fun alt => do
      return alt.setArg 3 (← translate ctx ⟨alt[3]⟩)
    let m := (e.raw.setArg 3 discrs').setArg 5 (e.raw[5].setArg 0 (mkNullNode alts'))
    return ← wrap c ⟨m⟩
  match e with
  | `(($e)) => translate ctx e
  | `(if $c then $a else $b) => do
      let (c', cs) ← (hoist ctx c).run #[]
      let ta ← translate ctx a
      let tb ← translate ctx b
      wrap cs (← `(if $(⟨c'⟩) then $ta else $tb))
  | `(if $h:ident : $c then $a else $b) => do
      let (c', cs) ← (hoist ctx c).run #[]
      let ta ← translate ctx a
      let tb ← translate ctx b
      wrap cs (← `(if $h:ident : $(⟨c'⟩) then $ta else $tb))
  | `(let $x:ident := $v; $b) => do
      let (v', cs) ← (hoist ctx v).run #[]
      let tb ← translate ctx b
      wrap cs (← `(let $x:ident := $(⟨v'⟩); $tb))
  | `(let $x:ident : $t := $v; $b) => do
      let (v', cs) ← (hoist ctx v).run #[]
      let tb ← translate ctx b
      wrap cs (← `(let $x:ident : $t := $(⟨v'⟩); $tb))
  | `(let $p:term := $v; $b) => do
      let (v', cs) ← (hoist ctx v).run #[]
      let tb ← translate ctx b
      wrap cs (← `(let $p:term := $(⟨v'⟩); $tb))
  | _ => do
      let (r, cs) ← (hoist ctx e).run #[]
      wrap cs (← `(pure $(⟨r⟩)))

/-- Is `t` an application of a cost class (`MulCost M`, …)? -/
private def isCostClass (t : Term) : Bool :=
  match t with
  | `($c:ident $_*) =>
      ["MulCost", "DivCost", "PowCost"].contains c.getId.eraseMacroScopes.getString!
  | _ => false

/-- The domains of a (non-dependent) function type `A₁ → ⋯ → Aₖ → B`. -/
private partial def arrowDomains : Term → Array Term
  | `($a → $b) => #[a] ++ arrowDomains b
  | _ => #[]

/-- Generate the plain definition, the counted one and the value lemma. -/
private def expandCounted (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (f : Ident) (bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty body : Term)
    (suff : TSyntax ``Lean.Parser.Termination.suffix) : MacroM Syntax := do
  let counted := mkIdent (f.getId ++ `counted)
  let mo := mkIdent `countedMonad
  -- explicit arguments; function parameters get a charge function each
  let mut args : Array Ident := #[]
  let mut funs : Array (Name × Ident) := #[]
  let mut funPos : Array Nat := #[]
  let mut chargeBs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut chargeBsC : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for b in bs do
    match b with
    | `(bracketedBinder| ($xs:ident* : $t)) | `(bracketedBinder| ($xs:ident* : $t := $_)) =>
        for x in xs do
          let doms := arrowDomains t
          unless doms.isEmpty do
            let c := mkIdent (Name.mkSimple (x.getId.toString ++ "_charge"))
            funs := funs.push (x.getId, c)
            funPos := funPos.push args.size
            let tyM ← doms.foldrM (fun d r => `($d → $r)) (← `($mo Unit))
            let tyC ← doms.foldrM (fun d r => `($d → $r)) (← `(CostM C Unit))
            chargeBs := chargeBs.push (← `(bracketedBinder| ($c : $tyM)))
            chargeBsC := chargeBsC.push (← `(bracketedBinder| ($c : $tyC)))
          args := args.push x
    | _ => pure ()
  let ctx : Ctx := { self := f.getId, funs, funPos }
  let tbody ← translate ctx body
  -- cost-class instances (`[MulCost M]`, …) are needed by the counted version only
  let plainBs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := bs.filter fun b =>
    match b with
      | `(bracketedBinder| [$t]) => !isCostClass t
      | `(bracketedBinder| [$_ : $t]) => !isCostClass t
      | _ => true
  let c₁ ← `(command| $[$doc?:docComment]?
    def $f $plainBs* : $ty := $body
    $suff:suffix)
  let c₂ ← `(command| $[$doc?:docComment]?
    def $counted {$mo : Type → Type} [Monad $mo] [NatArith $mo] $bs* $chargeBs* : $mo $ty :=
      $tbody
    $suff:suffix)
  let valName := mkIdent (f.getId ++ `counted_val)
  let fCall := Syntax.mkApp f (args.map fun a => ⟨a.raw⟩)
  let cCall := Syntax.mkApp counted (args.map (fun a => ⟨a.raw⟩) ++ funs.map (fun c => ⟨c.2.raw⟩))
  let eqDef := mkIdent (f.getId ++ `eq_def)
  let ceqDef := mkIdent (f.getId ++ `counted ++ `eq_def)
  let c₃ ← `(command|
    /-- Counting does not change the value. -/
    theorem $valName (C : CostModel) $bs* $chargeBsC* : CostM.val C $cCall = $fCall := by
      rw [$ceqDef:ident]; conv_rhs => rw [$eqDef:ident]
      repeat' (first | split_ifs | split | cost_simp))
  return mkNullNode #[c₁, c₂, c₃]

/-- `counted_def f binders : τ := body [termination_by …] [decreasing_by …]` -/
syntax (name := countedDef) (docComment)? "counted_def " ident bracketedBinder* " : " term
  " := " term Lean.Parser.Termination.suffix : command

/-- `counted_def f binders : A₁ → ⋯ → τ | pats => rhs | …` (equation style) -/
syntax (name := countedDefEqns) (docComment)? "counted_def " ident bracketedBinder* " : " term
  Lean.Parser.Command.declValEqns : command

macro_rules
  | `($[$doc?:docComment]? counted_def $f:ident $bs:bracketedBinder* : $ty := $body
      $suff:suffix) => expandCounted doc? f bs ty body suff

macro_rules
  | `($[$doc?:docComment]? counted_def $f:ident $bs:bracketedBinder* : $ty
      $eqns:declValEqns) => do
    -- `declValEqns` is `matchAlts terminationSuffix whereDecls?`
    let alts := eqns.raw[0][0]
    let suff : TSyntax ``Lean.Parser.Termination.suffix := ⟨eqns.raw[0][1]⟩
    -- the number of pattern columns, and the types they range over
    let altArr := alts[0].getArgs
    let some alt₀ := altArr[0]? | Macro.throwError "counted_def: no equations"
    let ncols := alt₀[1][0].getSepArgs.size
    -- peel `A → B` and named `(x y : A) → B` arrows; named arguments keep their names
    let mut args : Array (Option Ident × Term) := #[]
    let mut res : Term := ty
    while args.size < ncols do
      match res with
      | `(($xs:ident* : $a) → $b) => args := args ++ xs.map (fun x => (some x, a)); res := b
      | `($a → $b) => args := args.push (none, a); res := b
      | _ => Macro.throwErrorAt ty "counted_def: the type must have one arrow per pattern column"
    if args.size != ncols then
      Macro.throwErrorAt ty "counted_def: the type must have one arrow per pattern column"
    let mut newBs := bs
    let mut discrs : Array Term := #[]
    for h : i in [0:args.size] do
      let (x?, a) := args[i]
      let x ← match x? with
        | some x => pure x
        | none => pure (mkIdent (← Macro.addMacroScope (Name.mkSimple s!"eqnArg{i}")))
      newBs := newBs.push (← `(bracketedBinder| ($x : $a)))
      discrs := discrs.push x
    let altsArr : Array (TSyntax ``Lean.Parser.Term.matchAlt) := altArr.map (⟨·⟩)
    let ds ← discrs.mapM fun x => `(Lean.Parser.Term.matchDiscr| $x:term)
    let body ← `(match $[$ds],* with $altsArr:matchAlt*)
    expandCounted doc? f newBs res body suff

end PrimeNumbers.Chapter9
