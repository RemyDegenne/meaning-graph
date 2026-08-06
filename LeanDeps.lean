module

public import Lean
public import Lean.Meta.Instances

@[expose] public section

/-!
# Dependency analysis for the declarations of a Lean project

Computes, for every declaration of a project, which constants its *type* uses (`DeclDeps.typeDeps`)
and which its type *and* body use (`DeclDeps.deps`), plus the graph-level passes that run on the
result: reverse edges and transitive closure in topological order.

This module depends on Lean core only — no Lake, no document format, no notion of a "project
directory" or of output — so it can be reused by any tool that needs to know what a declaration
rests on.

## Why not just `Expr.getUsedConstants`?

The elaborated type and value of a declaration under-report what its *source* needs, in four ways
this module compensates for:

* **compiler-generated helpers** (`_proof_N`, `match_N`, structure field defaults, well-founded
  recursion helpers) are constants of the project itself, but nobody wrote them; stopping at such a
  name hides what it in turn depends on. `expandThroughInternals` recurses through them, and only
  through them.
* **`Expr.proj` nodes**: `Expr.foldConsts` walks *through* a projection without ever offering the
  structure name it carries. `projStructureNames` recovers those names.
* **notation**: a notation's macro stores the constants it expands to as pre-resolved `Name` *data*
  inside embedded `Syntax`, invisible to a constant walk. `notationExpansionDeps` reconstructs them.
* **coercions**: an elaborated term keeps only the underlying `@[coe]` function and drops the
  instance, yet the instance is what makes the source's `↑`/`⇑` elaborate.
  `coercionInstancesByType` recovers it.

## Entry points

`Context.of env rootPrefix` computes the project-wide tables once; `Context.declDeps` then answers
per declaration, threading a memo cache. `declDepsOf` wraps both for the common
"give me everything" case.

The graph passes (`reverseDeps`, `transitiveDeps`) are deliberately stated over plain `Name`-keyed
maps rather than over any declaration record, so a caller can decide which edges count (e.g.
type-only edges for theorems) before running them.
-/

open Lean
open Lean.Meta

namespace LeanDeps

/-! ## Name classification

Which constants are the project's own user-written declarations, and which are compiler output.
This is what bounds the analysis: helper constants are expanded *through* (their dependencies are
pulled in instead of the helper), and everything outside the project is left alone.
-/

/-- True if `s` is `pfx` followed by a non-empty sequence of digits, the naming convention used
by the compiler for auto-generated declarations like `match_1`, `eq_2`, `hcongr_11`. -/
def isPrefixWithDigitSuffix (pfx s : String) : Bool :=
  s.startsWith pfx &&
    let rest := s.drop pfx.length
    !rest.isEmpty && rest.toString.toList.all Char.isDigit

/-- True if `s` is a single name component the compiler generates: anything underscore-led
(`_hyg`, `_proof_3`, `_private`, ...), a `match_<n>`/`eq_<n>`/`hcongr_<n>` helper, or the
equation-lemma names `eq_def`/`eq_unfold`. -/
def isAuxComponent (s : String) : Bool :=
  s.startsWith "_"
    || isPrefixWithDigitSuffix "match_" s
    || isPrefixWithDigitSuffix "eq_" s || s == "eq_def" || s == "eq_unfold"
    || isPrefixWithDigitSuffix "hcongr_" s

/-- Auto-generated companion names that Lean exposes *no* dedicated environment predicate for, so
they can only be recognized by their (stable) spelling. A name *any* of whose components matches is
treated as internal, matched at every component (not just the last) so helpers nested under an
already-internal name (e.g. `Foo.match_1.eq_1`) are caught too.

This list is deliberately the residual left after `shouldExpose` first consults everything Lean
*does* know directly:
* the recursor family (`rec`, `recOn`, `casesOn`, `brecOn`, `below`, `binductionOn`, ...) →
  `ConstantInfo.recInfo` and `isAuxRecursor`;
* `noConfusion` → `isNoConfusion` (note: its `noConfusionType` sibling is *not* covered by that
  predicate, hence it remains here);
* constructor companions (`mk.inj`, `mk.injEq`, `mk.sizeOf_spec`, ...) → `hasConstructorPrefix`,
  which keys on `ctorInfo` rather than on the string `mk`, so a user declaration named `Foo.mk`
  (a structure whose real constructor was renamed to free up `mk`) or a legitimate theorem such as
  `Kernel.prodMkLeft_inj` is never mistaken for compiler output.

What is left here are companions Lean attaches to *ordinary* declarations (not just constructors)
or to types without flagging them: `congr_simp` (added to defs and inductives alike), the `@[ext]`
lemma `ext_iff`, the induction principle `ind`, the constructor-index helper `ctorIdx`, and
`noConfusionType`.

`noConfusionType`, `ctorIdx`, and `congr_simp` were each observed leaking on a Mathlib-backed test
project when removed. `ind` and `ext_iff` were *not* exercised by that project (no Prop inductive's
`.ind` nor any `@[ext]` structure surfaced one), but they are standard generated companions and are
kept here so the analysis stays correct on projects that do use them. -/
def internalComponentNames : List String :=
  ["noConfusionType", "ind", "ctorIdx", "ext_iff", "congr_simp"]

/-- True if any component of `name` is an auxiliary component (`isAuxComponent`) or one of the
compiler's auto-generated companion names (`internalComponentNames`). -/
def isInternalName : Name → Bool
  | .anonymous => false
  | .num p _ => isInternalName p
  | .str p s =>
      isAuxComponent s
      || s ∈ internalComponentNames
      || isInternalName p

/-- True when some strict prefix of `name` is the name of a constructor in `env`, i.e. `name` lives
inside a constructor's namespace. Everything Lean places there (`S.mk.inj`, `S.mk.injEq`,
`S.mk.sizeOf_spec`, ...) is auto-generated and should be hidden.

This keys on the environment's `ctorInfo` rather than on the spelling of the prefix, so it hides
these companions for *any* constructor name (`mk`, a custom `intro`, ...) while leaving a user
declaration that merely happens to be named like a constructor (its prefix is not a `ctorInfo`)
untouched. -/
def hasConstructorPrefix (env : Environment) (name : Name) : Bool :=
  go name.getPrefix
where
  -- Matching the two non-empty constructors rather than calling `getPrefix` makes the recursion
  -- structural, so this needs no `partial`. Same function: `(.str p _).getPrefix = p`.
  go : Name → Bool
    | .anonymous => false
    | .str p s =>
      (match env.find? (.str p s) with | some (.ctorInfo _) => true | _ => false) || go p
    | .num p i =>
      (match env.find? (.num p i) with | some (.ctorInfo _) => true | _ => false) || go p

/-- True if `prefixName` is `n` itself or one of its dotted ancestors. This is a *component-wise*
test, not a string prefix: the name `LMLExtra.Foo` does *not* have prefix `LML`. -/
def hasPrefixName (n prefixName : Name) : Bool :=
  n == prefixName || match n with
    | .str p _ => hasPrefixName p prefixName
    | .num p _ => hasPrefixName p prefixName
    | .anonymous => false

/-- The module `name` was declared in, if `env` records one (declarations added to the current
module, rather than imported, have no module index). -/
def moduleNameOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- True if `name` is defined in a project module (one whose name has `rootPrefix` as a prefix).
This is keyed on the declaration's *module*, not its name: a project's declaration names need not
share the root module prefix (e.g. module `LeanMachineLearning.…` declaring `Bandits.foo`). -/
def isProjectLocalConst (env : Environment) (rootPrefix : Name) (name : Name) : Bool :=
  (moduleNameOf env name).any (hasPrefixName · rootPrefix)

/-- Decides whether a declaration is one the project's author actually wrote, as opposed to
compiler output (recursors, projections, constructor companions, hygienic helpers, ...) or a
declaration from outside the project. This is both the set a consumer would display and the
boundary at which dependency expansion stops (see `expandThroughInternals`). -/
def shouldExpose (env : Environment) (rootPrefix : Name) (name : Name) (info : ConstantInfo) : Bool :=
  if let some moduleName := moduleNameOf env name then
    if !hasPrefixName moduleName rootPrefix then
      false
    else if env.isProjectionFn name then
      false
    else if isInternalName name || name.isInternal || name.isImplementationDetail then
      false
    else if isAuxRecursor env name || isNoConfusion env name then
      false
    else if hasConstructorPrefix env name then
      false
    else match info with
      | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
      | _ => true
  else if env.isProjectionFn name then
    false
  else
    false

/-- All constants belonging to modules whose name has `rootPrefix`, paired with their module
name, gathered directly from `env.header.moduleData` so that the (typically much larger) set of
constants from imported libraries is never iterated. -/
def projectConstants (env : Environment) (rootPrefix : Name) : Array (Name × Name × ConstantInfo) :=
  (Array.range env.header.modules.size).foldl (fun acc idx =>
    let modName := env.header.modules[idx]!.module
    if hasPrefixName modName rootPrefix then
      let data := env.header.moduleData[idx]!
      (Array.zip data.constNames data.constants).foldl
        (fun acc2 (cname, cinfo) => acc2.push (cname, modName, cinfo)) acc
    else acc) #[]

/-! ## Constants used by an expression -/

/-- Every structure name carried by an `Expr.proj` node inside `e`, in traversal order and
possibly with repeats (all consumers dedup).

`Expr.getUsedConstants` does *not* report these: its underlying `Expr.foldConsts` recurses through
a `.proj S i b` node into `b` without ever offering `S`. So a structure that an elaborated term
reaches only by projecting one of its fields — never by naming it — is absent from the constant
list, and would be absent from a declaration's `deps`/`typeDeps`.

This is a correctness guard, not a fix for an observed failure. Surface-level field access
(`x.field`) elaborates to an application of the projection *function* (`S.field x`), which
`getUsedConstants` reports normally; bare `.proj` nodes come from the compiler's own recursion
machinery (`brecOn`, `._f`, `.wf._unary._proof_n`) and from upstream `Equiv`/`Subtype`-style
bundled structures. Scanning the 438950-constant environment of a Mathlib-backed target found 14
distinct names lost this way — `PProd`, `WellFoundedRelation`, `Equiv`, `Subtype`, `Zero`, ... —
and **none** of them was a declaration of the target project itself. Such names are dropped
anyway by consumers that keep only the project's own declarations, so recovering them changes no
output today; they are simply the correct input to those filters if a project ever does elaborate
a `.proj` of one of its own structures.

The walk memoizes on the `Expr` nodes themselves so heavily-shared proof terms are not re-walked:
`Hashable Expr` is the hash cached in the expression header and `BEq Expr` is the native
`Expr.eqv`, so both are cheap. It is still ~3x the cost of core's `foldConsts` (which memoizes on
a pointer set from unsafe code); that is immaterial here because only the target project's own
constants are ever walked. -/
def projStructureNames (e : Expr) : Array Name :=
  (go e (#[], {})).1
where
  -- `e` is memoized *after* its subterms are walked, not before. Either order computes the same
  -- thing — a term is never a strict subterm of itself, so a node being walked can never be
  -- re-encountered inside its own walk — but marking it afterwards means the memo satisfies a
  -- simple invariant throughout: everything in `seen` has already contributed its names to `acc`.
  -- That is what `Proofs/Deps.lean` inducts on to show the memo loses nothing.
  go (e : Expr) (st : Array Name × Std.HashSet Expr) : Array Name × Std.HashSet Expr :=
    let (acc, seen) := st
    if seen.contains e then
      st
    else
      let (acc, seen) :=
        match e with
        | .app f a => go a (go f (acc, seen))
        | .lam _ t b _ => go b (go t (acc, seen))
        | .forallE _ t b _ => go b (go t (acc, seen))
        | .letE _ t v b _ => go b (go v (go t (acc, seen)))
        | .mdata _ b => go b (acc, seen)
        | .proj s _ b => go b (acc.push s, seen)
        | _ => (acc, seen)
      (acc, seen.insert e)

/-- Like `Expr.getUsedConstants`, but also reports the structure name of every `Expr.proj` node
(see `projStructureNames` for why that name would otherwise be lost). -/
def exprUsedConstants (e : Expr) : Array Name :=
  e.getUsedConstants ++ projStructureNames e

/-- One-level "used constants" for a declaration's type (and, if `includeValue`, also its
value/body), handling inductive constructor types and structure field-default functions: for
inductives/structures, `info.type` alone does not mention constructor field types, so those are
pulled in from the constructors' types and (for structures) field-default functions. -/
def usedConstantsOf (env : Environment) (name : Name) (info : ConstantInfo)
    (includeValue : Bool) : Array Name :=
  let typeUsed :=
    match info with
    | .inductInfo val =>
      val.ctors.foldl (fun acc ctorName =>
        match env.find? ctorName with
        | some ctorInfo => acc ++ exprUsedConstants ctorInfo.type
        | none => acc) (exprUsedConstants info.type)
    | _ => exprUsedConstants info.type
  if !includeValue then
    typeUsed
  else
    let valueUsed :=
      match info with
      | .defnInfo val => exprUsedConstants val.value
      | .thmInfo val => exprUsedConstants val.value
      | .inductInfo _ =>
        if (getStructureInfo? env name).isNone then
          #[]
        else
          (getStructureFields env name).foldl (fun acc fieldName =>
            match getDefaultFnForField? env name fieldName with
            | some defaultFn =>
              match env.find? defaultFn >>= ConstantInfo.value? with
              | some value => acc ++ exprUsedConstants value
              | none => acc
            | none => acc) #[]
      | _ => #[]
    typeUsed ++ valueUsed

/-! ## Data dependencies: a value's meaning, minus the proofs inside it

A bundled structure instance carries data fields *and* proof obligations:

```lean
noncomputable def SquareIntegrable.toL2Isom : SquareIntegrable ι E P 𝓕 ≃ₗᵢ[ℝ] lpMeas … where
  toFun X := ⟨toL2 ι E P 𝓕 X, by …⟩
  invFun X := …
  left_inv X := by …
  right_inv X := by …
```

`left_inv` and `right_inv` are proofs, kernel-checked exactly as a theorem's proof is. By the
argument recorded in `Referee.Collect` — an upstream proof needs no trust, because the kernel
rechecked it and anything left unproved arrives as a `sorry` or an extra axiom — they say nothing
about what the definition *means*. Yet `usedConstantsOf … (includeValue := true)` reports every
lemma their tactics happened to call: on the declaration above that is the difference between 132
dependencies and 280, and it is what puts definitions at the top of every degree distribution while
`structure`, `inductive` and `typeclass` (whose value contributions are field types and defaults,
never proofs) show no excess at all.

The walk below is `exprUsedConstants` with one change: at an application that *returns a structure or
class*, it skips the arguments filling that constant's `Prop`-valued parameters (`constPropMask`).
It recurses, so a proof nested inside a data field is skipped too — the `by` block above is the
second field of a `Subtype.mk` sitting inside `toFun`, and is reached by exactly the same rule.

The restriction to structure-returning applications is what keeps the rule true. "The `Prop`
arguments of an application that returns a structure are that instance's obligations" is a fact
about bundled structures; "every `Prop` argument is an obligation" is not, and the case it gets
wrong is choice. `noncomputable def IsPreBrownianReal.mk X h := h.exists_continuous_modification.choose`
elaborates to `Exists.choose _ p (IsPreBrownianReal.exists_continuous_modification h)`, whose third
parameter is a proof — so an unrestricted mask dropped the *only* project declaration in the body,
and the site reported that definition as resting on nothing. `Exists.choose` returns a bare type
variable, not a structure, so the restriction keeps it. See `constPropMask` for what this costs.

The mask is read off *declared types*, not inferred from the arguments, which is what keeps it cheap
and context-free: nothing here has to type-check a subterm sitting under binders.

This is deliberately *not* applied to a theorem's own proof. `Referee.meaningDeps` already drops that wholesale
by taking `typeDeps`, and the two mechanisms are kept separate so that neither has to be correct
about the other's case.
-/

/-- For each parameter position of the constant `fn`, whether that parameter is `Prop`-valued, i.e.
filled by a proof rather than by data — but only when `fn` *returns* a structure or class, since
that is the case in which its `Prop` parameters really are a bundled instance's obligations. Every
other constant masks nothing.

Read off `fn`'s *declared type*, which makes this both cheap and independent of any local context:
telescoping `∀ (x₁ : T₁) … (xₙ : Tₙ), R` binds each parameter as a local hypothesis, so `isProof`
can ask a well-posed question about it even when the argument at that position, in the term being
walked, sits under binders of its own, and leaves `R`'s head constant in hand for the structure test.

Keyed on the *return type*, not on `fn` being a constructor. A structure instance is very often
built by *calling* something that returns the structure rather than by a constructor literal —
`instance : NormedAddCommGroup … := Function.Injective.normedAddCommGroup hf hproof …` — and the
proof obligations are then ordinary arguments to an ordinary function. Masking constructors alone
left 188 of `BrownianMotion`'s 263 non-theorem declarations completely unreduced, all of this shape;
keying on the return type covers them, because `NormedAddCommGroup β` is a class.

What the restriction costs, measured over `BrownianMotion`'s 232 exposed definitions: the value walk
reports 9654 edges unmasked and 6476 with a mask over *every* `Prop` parameter, so the mask removes
3178; restricted to structure-returning applications it removes 2985 of those 3178, and the count of
declarations it reduces not at all goes from 97 to 130. Nearly all of the difference is Prop-valued
*typeclass instances* (`[IsProbabilityMeasure P]` and friends) on type formers such as
`SimpleProcess` and `ClassD`, whose result is a `Sort` rather than a structure application.

The head constant is taken as written, without `whnf`: a `def F : Type _ := ↥someSubmodule` masks
nothing even though it unfolds to a `Subtype`. That is the conservative direction, and it avoids
reducing an arbitrary return type. Note one case the rule does not catch:
`Classical.indefiniteDescription` returns `{x // p x}`, a `Subtype`, so its proof argument is still
masked — `Classical.choose`, `Exists.choose` and `Nonempty.some` all return a bare type variable and
are not.

Returns `#[]` — every position data — when `fn` is unknown, does not return a structure, or its type
will not telescope. That is the conservative direction: it can only keep edges a correct mask would
have dropped, never drop one it would have kept. -/
def constPropMask (fn : Name) : MetaM (Array Bool) := do
  let env ← getEnv
  let some info := env.find? fn | return #[]
  try
    Meta.forallTelescopeReducing info.type fun xs body => do
      let some head := body.getAppFn.constName? | return #[]
      unless isStructure env head do return #[]
      xs.mapM Meta.isProof
  catch _ =>
    return #[]

/-- Walk state for `dataValueConstants`: the memo over already-visited nodes (same rationale as
`projStructureNames` — heavily shared proof terms must not be re-walked), the constructor masks
computed so far (shared across declarations, since `Meta.forallTelescopeReducing` on a Mathlib
structure is far from free), and the constants collected. -/
private structure DataWalk where
  seen : Std.HashSet Expr := {}
  masks : Std.HashMap Name (Array Bool) := {}
  acc : Array Name := #[]

private partial def dataWalkGo (e : Expr) : StateT DataWalk MetaM Unit := do
  if (← get).seen.contains e then
    return
  modify fun s => { s with seen := s.seen.insert e }
  -- An application of a named constant is where the mask applies. Handled before the structural
  -- match and returning early, so the spine's partial applications are never walked generically —
  -- which is what makes skipping a proof argument actually skip it.
  if e.isApp then
    if let .const c _ := e.getAppFn then
      let mask ← match (← get).masks.get? c with
        | some m => pure m
        | none =>
          let m ← constPropMask c
          modify fun s => { s with masks := s.masks.insert c m }
          pure m
      modify fun s => { s with acc := s.acc.push c }
      let args := e.getAppArgs
      for h : i in [0:args.size] do
        -- `none` (over-application past the declared telescope) counts as data.
        if mask[i]? != some true then
          dataWalkGo args[i]
      return
  match e with
  | .app f a => dataWalkGo f; dataWalkGo a
  | .lam _ t b _ => dataWalkGo t; dataWalkGo b
  | .forallE _ t b _ => dataWalkGo t; dataWalkGo b
  | .letE _ t v b _ => dataWalkGo t; dataWalkGo v; dataWalkGo b
  | .mdata _ b => dataWalkGo b
  -- Same recovery as `projStructureNames`: the structure name of a `.proj` is otherwise lost.
  | .proj s _ b => modify fun st => { st with acc := st.acc.push s }; dataWalkGo b
  | .const c _ => modify fun st => { st with acc := st.acc.push c }
  | _ => pure ()

/-- The constants a declaration's *value* mentions outside the proofs inside it, or `#[]` when it
has no value this applies to.

Only `.defnInfo` — `def`, `abbrev` and `instance`, the kinds that can carry a bundled structure
instance. A theorem's value is handled by `Referee.meaningDeps` taking `typeDeps`, and `structure`/`inductive`
contribute field types and defaults rather than a value, with no proof excess to remove.

Not `@[expose]`, for the same reason as `evalNameExpr?`: the body refers to the `private`
`dataWalkGo`. Nothing is lost, since no importer needs to unfold this. -/
@[no_expose] def dataValueConstants (info : ConstantInfo) : MetaM (Array Name) := do
  match info with
  | .defnInfo val =>
    let (_, st) ← (dataWalkGo val.value).run {}
    return st.acc
  | _ => return #[]

/-! ## Dependencies the elaborated term does not mention: notation -/

/-- The `String` a string-literal `Expr` holds, if `e` is one. -/
private def exprStrLit? (e : Expr) : Option String :=
  match e with
  | .lit (.strVal s) => some s
  | _ => none

/-- Reconstructs the `Name` value that `e` builds, if `e` is a `Name.anonymous`/`Name.str`/
`Name.mkStr1..4` application. Notation and macro definitions store the constants they expand to as
pre-resolved `Name` *data* built this way (inside the embedded `Syntax`), so these references are
invisible to `Expr.getUsedConstants`; reconstructing them is how we recover the dependency.

Not `@[expose]`, so that the body may keep referring to the `private` `exprStrLit?`. Nothing is
lost: this is a `partial` definition, so importers cannot unfold it either way. -/
@[no_expose] partial def evalNameExpr? (e : Expr) : Option Name := do
  match e.getAppFnArgs with
  | (``Lean.Name.anonymous, _) => some .anonymous
  | (``Lean.Name.mkStr1, #[a]) => some (.str .anonymous (← exprStrLit? a))
  | (``Lean.Name.mkStr2, #[a, b]) =>
    some (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b))
  | (``Lean.Name.mkStr3, #[a, b, c]) =>
    some (.str (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b)) (← exprStrLit? c))
  | (``Lean.Name.mkStr4, #[a, b, c, d]) =>
    some (.str (.str (.str (.str .anonymous (← exprStrLit? a)) (← exprStrLit? b)) (← exprStrLit? c))
      (← exprStrLit? d))
  | (``Lean.Name.str, #[p, s]) => some (.str (← evalNameExpr? p) (← exprStrLit? s))
  | _ => none

/-- Every `Name` value embedded anywhere in `e` (reconstructed via `evalNameExpr?`). -/
def collectEmbeddedNames (e : Expr) : Array Name := Id.run do
  let mut acc : Array Name := #[]
  if let some n := evalNameExpr? e then acc := acc.push n
  match e with
  | .app f a => return acc ++ collectEmbeddedNames f ++ collectEmbeddedNames a
  | .lam _ t b _ => return acc ++ collectEmbeddedNames t ++ collectEmbeddedNames b
  | .forallE _ t b _ => return acc ++ collectEmbeddedNames t ++ collectEmbeddedNames b
  | .letE _ t v b _ =>
    return acc ++ collectEmbeddedNames t ++ collectEmbeddedNames v ++ collectEmbeddedNames b
  | .mdata _ b => return acc ++ collectEmbeddedNames b
  | .proj _ _ b => return acc ++ collectEmbeddedNames b
  | _ => return acc

/-- True if `n` names a notation/syntax parser (its type is `Lean.ParserDescr`/`TrailingParserDescr`). -/
def isNotationKind (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some info => info.type.isConstOf ``Lean.ParserDescr || info.type.isConstOf ``Lean.TrailingParserDescr
  | none => false

/-- Maps each notation parser to the constants its expansion references. A notation's macro definition
embeds both its own parser kind and the constant(s) it abbreviates as pre-resolved `Name` data (see
`evalNameExpr?`). Scanning the project's definitions, any whose body embeds a notation kind `K`
contributes its other embedded (real) constants as dependencies of `K` — so a standalone rendering
of `K` inlines what it stands for instead of failing with `unknown constant`. -/
def notationExpansionDeps (env : Environment) (projectConsts : Array (Name × Name × ConstantInfo)) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut m : Std.HashMap Name (Array Name) := {}
  for (_, _, cinfo) in projectConsts do
    if let .defnInfo v := cinfo then
      let names := (collectEmbeddedNames v.value).filter (env.contains ·)
      let kinds := names.filter (isNotationKind env ·)
      unless kinds.isEmpty do
        let realDeps := names.filter (!isNotationKind env ·)
        for k in kinds do
          m := m.insert k ((m.getD k #[]) ++ realDeps)
  return m

/-! ## Dependencies the elaborated term does not mention: coercions -/

/-- Coercion type classes whose instances Lean unfolds at use sites: an elaborated term keeps only
the underlying `@[coe]` function, never the instance, so a coercion's dependency on its instance is
invisible to `getUsedConstants`. The instance must still be replayed for the source's `↑`/`⇑` to
elaborate. -/
def coercionClasses : List Name :=
  [``CoeFun, ``CoeSort, ``Coe, ``CoeTC, ``CoeHead, ``CoeTail, ``CoeHTCT, ``CoeOut, ``CoeDep]

/-- If `type` is, under its binders, a coercion-class application `Cls Src …`, the type coerced
*from* (`Src`). -/
def coercionSource? (type : Expr) : Option Expr :=
  match type with
  | .forallE _ _ b _ => coercionSource? b
  | _ =>
    let (fn, args) := type.getAppFnArgs
    if coercionClasses.contains fn && args.size ≥ 1 then some args[0]!
    else none

/-- If `type` is, under its binders, a coercion-class application `Cls Src …`, the head constant of
`Src`. -/
def coercionSourceType? (type : Expr) : Option Name :=
  coercionSource? type >>= (·.getAppFn.constName?)

/-- A coercion instance, together with the project constants that must be present for it to be
relevant (see `coercionInstancesByType`). -/
structure CoercionInstance where
  /-- The instance declaration. -/
  name : Name
  /-- Project-local constants occurring in the coerced-from type, other than its head. -/
  witnesses : Array Name
deriving Inhabited

/-- Maps a type's head constant to the exposed coercion instances coercing *from* it. A declaration
mentioning such a type needs these instances replayed so its source coercions still elaborate (the
instances themselves never appear in the elaborated term; see `coercionClasses`).

The head constant alone is too coarse a key. `instance : CoeFun (SquareIntegrable ι E P 𝓕) …` has
coerced-from type `{ x // x ∈ SquareIntegrable … }`, whose head is **`Subtype`** — so keying on the
head filed it under `Subtype` and handed it to every declaration mentioning a subtype at all. In
brownian-motion that was 208 declarations, none of which mention `SquareIntegrable`, and each one
inherited `SquareIntegrable`'s whole closure. Many of those declarations live in modules that do
not even import the one defining the instance, so the edge was not merely useless but impossible.

`witnesses` records the other project constants in the coerced-from type (`SquareIntegrable` here),
and `Context.declDeps` only replays the instance for declarations that mention all of them. -/
def coercionInstancesByType (env : Environment) (rootPrefix : Name) (exposed : Std.HashSet Name)
    (projectConsts : Array (Name × Name × ConstantInfo)) :
    Std.HashMap Name (Array CoercionInstance) := Id.run do
  let mut m : Std.HashMap Name (Array CoercionInstance) := {}
  for (cname, _, cinfo) in projectConsts do
    if exposed.contains cname && Lean.Meta.isInstanceCore env cname then
      if let some src := coercionSource? cinfo.type then
        if let some head := src.getAppFn.constName? then
          let witnesses := src.getUsedConstants.filter fun c =>
            c != head && isProjectLocalConst env rootPrefix c
          m := m.insert head ((m.getD head #[]).push { name := cname, witnesses })
  return m

/-! ## Expansion through compiler-generated helpers -/

/-- Memo table for the one-level expansion of internal helpers, shared across the declarations of
one run (see `expandThroughInternals`). -/
abbrev Cache := Std.HashMap Name (Array Name)

/-- Expands `start` by following constants that are project-local (share `rootPrefix`) but are
not themselves exposed declarations — i.e. compiler-generated helpers such as `_proof_N`,
`match_..`, or structure field-default functions — recursively pulling in whatever *they* depend
on instead of stopping at their (uninformative) name. Exposed declarations and external
(non-project) constants are kept as-is without further expansion.

This mirrors the recursive dependency-collection idea from
https://github.com/mattrobball/lean-informal/blob/main/Informal/Deps.lean, bounded to the
project's own constants so it doesn't walk into upstream library internals. `cache` memoizes the
one-level expansion of internal helpers across declarations. -/
partial def expandThroughInternals (env : Environment) (rootPrefix : Name)
    (exposed : Std.HashSet Name) (cache : Cache) (start : Array Name) : Array Name × Cache :=
  go cache {} #[] start.toList
where
  go (cache : Cache) (visited : Std.HashSet Name) (acc : Array Name) :
      List Name → Array Name × Cache
    | [] => (acc, cache)
    | n :: rest =>
      if visited.contains n then
        go cache visited acc rest
      else
        let visited := visited.insert n
        let isInternalHelper := !exposed.contains n && isProjectLocalConst env rootPrefix n
        if !isInternalHelper then
          go cache visited (acc.push n) rest
        else
          match cache.get? n with
          | some deps => go cache visited acc (rest ++ deps.toList)
          | none =>
            match env.find? n with
            | none => go cache visited acc rest
            | some info =>
              let deps := usedConstantsOf env n info true
              go (cache.insert n deps) visited acc (rest ++ deps.toList)

/-! ## Per-declaration dependencies -/

/-- The dependencies of one declaration. -/
structure DeclDeps where
  /-- Constants used by the declaration's *type*, expanded through compiler-generated helpers and
  deduplicated. Never contains the declaration itself. -/
  typeDeps : Array Name
  /-- Constants used by the declaration's type *and* its value/body (plus, for a notation, what its
  expansion references), expanded and deduplicated the same way. Never contains the declaration
  itself. -/
  deps : Array Name
  /-- Like `deps`, but with the proofs inside the value skipped (`dataValueConstants`): what the
  declaration's statement and *data* rest on, dropping the lemmas its embedded proof obligations
  happen to call.

  Equal to `deps` unless the `Context` was built with `withDataValueConsts` *and* this declaration
  is a `.defnInfo`, so a caller that does not ask for the extra analysis sees no change. -/
  dataDeps : Array Name
deriving Repr, Inhabited

/-- The project-wide tables the per-declaration analysis needs, computed once by `Context.of` and
reused for every declaration. -/
structure Context where
  env : Environment
  /-- Root module prefix delimiting the project: a constant counts as project-local when the module
  declaring it has this prefix (see `isProjectLocalConst`). -/
  rootPrefix : Name
  /-- Every constant declared by a project module, as `(name, module, info)`. -/
  constants : Array (Name × Name × ConstantInfo)
  /-- The project's user-written declarations (`shouldExpose`); expansion stops at these. -/
  exposed : Std.HashSet Name
  /-- Notation kind ↦ constants its expansion references (`notationExpansionDeps`). -/
  notationDeps : Std.HashMap Name (Array Name)
  /-- Type head constant ↦ coercion instances coercing from it (`coercionInstancesByType`). -/
  coercionInstances : Std.HashMap Name (Array CoercionInstance)
  /-- Project constant ↦ the module declaring it. -/
  declModule : Std.HashMap Name Name
  /-- Project module ↦ the project modules it can see (`visibleProjectModules`). -/
  visibleModules : Std.HashMap Name (Std.HashSet Name)
  /-- Declaration ↦ the constants its value mentions outside its proofs (`dataValueConstants`).

  Empty unless `withDataValueConsts` has been run, and populated only for `.defnInfo`; `declDeps`
  falls back to the full value walk for anything absent, so `DeclDeps.dataDeps` degrades to `deps`
  rather than to nothing. Filling it needs `MetaM` (deciding whether a constructor field is
  `Prop`-valued is a typing question), which is why it is a separate pass rather than part of the
  pure `Context.of`. -/
  dataValueConsts : Std.HashMap Name (Array Name) := {}

/-- For each project module, the project modules it can see: itself plus everything it imports,
transitively.

Only project modules are tracked. A project module can only be reached from another project module
(nothing upstream imports the project), so reachability among them never leaves the set.

Relies on `moduleNames` being in dependency order — Lean writes a module's imports before the
module itself — so one forward pass suffices. -/
def visibleProjectModules (env : Environment) (rootPrefix : Name) :
    Std.HashMap Name (Std.HashSet Name) := Id.run do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut visible : Std.HashMap Name (Std.HashSet Name) := {}
  for i in [0:names.size] do
    let modName := names[i]!
    if !hasPrefixName modName rootPrefix then
      continue
    let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert modName
    if h : i < data.size then
      for imp in data[i].imports do
        if hasPrefixName imp.module rootPrefix then
          seen := seen.insert imp.module
          for m in visible.getD imp.module {} do
            seen := seen.insert m
    visible := visible.insert modName seen
  return visible

/-- Scans `env` for the project rooted at `rootPrefix` and builds the tables `Context.declDeps`
needs. Does the whole-environment work once, so a caller analysing many declarations should build
this a single time. -/
def Context.of (env : Environment) (rootPrefix : Name) : Context :=
  let constants := projectConstants env rootPrefix
  let exposed : Std.HashSet Name :=
    constants.foldl (fun acc (name, _, info) =>
      if shouldExpose env rootPrefix name info then acc.insert name else acc) {}
  { env := env
    rootPrefix := rootPrefix
    constants := constants
    exposed := exposed
    notationDeps := notationExpansionDeps env constants
    coercionInstances := coercionInstancesByType env rootPrefix exposed constants
    declModule := constants.foldl (fun acc (name, mod, _) => acc.insert name mod) {}
    visibleModules := visibleProjectModules env rootPrefix }

/-- The dependencies of the single declaration `name` (whose `ConstantInfo` is `info`), threading
the memo `cache` used by `expandThroughInternals`; the updated cache is returned alongside and
should be passed to the next call. -/
def Context.declDeps (ctx : Context) (cache : Cache) (name : Name) (info : ConstantInfo) :
    DeclDeps × Cache :=
  -- Adds, for every referenced type with coercion instances, those instances (see `coercionClasses`),
  -- but only the ones whose coerced-from type this declaration actually mentions in full: the head
  -- constant on its own is far too coarse a match (see `coercionInstancesByType`).
  let addCoercionInsts (cs : Array Name) : Array Name :=
    let present : Std.HashSet Name := cs.foldl (fun acc c => acc.insert c) {}
    cs ++ cs.foldl (init := #[]) fun acc c =>
      acc ++ (ctx.coercionInstances.getD c #[]).filterMap fun inst =>
        if inst.witnesses.all present.contains then some inst.name else none
  let typeUsedConstants := addCoercionInsts (usedConstantsOf ctx.env name info false)
  -- When this declaration *is* a notation, also depend on the constants it expands to (which are
  -- stored as `Name` data inside its macro and so invisible to `getUsedConstants`); see
  -- `notationExpansionDeps`. The reverse direction (a declaration whose *source* uses a notation)
  -- is syntactic, and so is left to callers that have the source syntax at hand.
  let allUsedConstants :=
    addCoercionInsts (usedConstantsOf ctx.env name info true ++ ctx.notationDeps.getD name #[])
  -- The same inputs as `allUsedConstants`, with the value's contribution replaced by its
  -- proof-skipped form where one was computed. Everything downstream — coercion instances,
  -- expansion through internal helpers, the visibility filter — is applied identically, so the
  -- result is comparable to `deps` edge for edge.
  let dataUsedConstants :=
    match ctx.dataValueConsts.get? name with
    | some valueConsts =>
      addCoercionInsts (usedConstantsOf ctx.env name info false ++ valueConsts
        ++ ctx.notationDeps.getD name #[])
    | none => allUsedConstants
  let (typeExpanded, cache) :=
    expandThroughInternals ctx.env ctx.rootPrefix ctx.exposed cache typeUsedConstants
  let (allExpanded, cache) :=
    expandThroughInternals ctx.env ctx.rootPrefix ctx.exposed cache allUsedConstants
  let (dataExpanded, cache) :=
    expandThroughInternals ctx.env ctx.rootPrefix ctx.exposed cache dataUsedConstants
  -- A declaration can only reference what its own module can see. Any project-local dependency in
  -- a module this one does not import is impossible, so it is an artifact of the analysis (a
  -- too-eagerly replayed coercion instance, say) rather than a real edge. Constants outside the
  -- project are left alone: they are never emitted, and pruning them here would only hide them
  -- from the assumption counts.
  let visible := ctx.visibleModules.getD (ctx.declModule.getD name .anonymous) {}
  let importable (dep : Name) : Bool :=
    match ctx.declModule.get? dep with
    | none => true
    | some mod => visible.contains mod
  let dedup (cs : Array Name) : Array Name :=
    cs.foldl (fun acc dep =>
      if dep != name && importable dep && !acc.contains dep then acc.push dep else acc) #[]
  ({ typeDeps := dedup typeExpanded, deps := dedup allExpanded, dataDeps := dedup dataExpanded },
    cache)

/-- Fills `Context.dataValueConsts` for every exposed `.defnInfo`, so that `declDeps` can report
`DeclDeps.dataDeps`.

Restricted to `.defnInfo` because that is where the excess is: `def` and `instance` account for
essentially all of the gap between `typeDeps` and `deps` (on `BrownianMotion`, 6709 of 6711 edges),
while `structure`, `inductive` and `typeclass` show none. That also keeps the cost proportional to a
small minority of declarations — 263 of 1692 there — rather than to the whole project. -/
def Context.withDataValueConsts (ctx : Context) : MetaM Context := do
  let mut consts : Std.HashMap Name (Array Name) := {}
  for (name, _, info) in ctx.constants do
    if ctx.exposed.contains name then
      if info matches .defnInfo _ then
        consts := consts.insert name (← dataValueConstants info)
  return { ctx with dataValueConsts := consts }

/-- The dependencies of every exposed declaration of the project, in environment order, sharing one
expansion cache. -/
def Context.allDeclDeps (ctx : Context) : Array (Name × DeclDeps) := Id.run do
  let mut cache : Cache := {}
  let mut out : Array (Name × DeclDeps) := #[]
  for (name, _, info) in ctx.constants do
    if ctx.exposed.contains name then
      let (deps, cache') := ctx.declDeps cache name info
      cache := cache'
      out := out.push (name, deps)
  return out

/-- One-shot entry point: the dependencies of every declaration the project rooted at `rootPrefix`
declares itself. -/
def declDepsOf (env : Environment) (rootPrefix : Name) : Array (Name × DeclDeps) :=
  (Context.of env rootPrefix).allDeclDeps

/-! ## Graph passes

These operate on the dependency graph alone — an `Array (Name × Array Name)` of edges, or the same
data as a `Std.HashMap` — so the caller chooses which edges count. A consumer that treats a
theorem's proof as opaque, for instance, feeds `typeDeps` for theorems and `deps` for everything
else, and every pass then agrees on that choice.
-/

/-- Reverses the edges of `nodes`, keeping only edges whose target is itself one of the `nodes`
(a dependency on something outside the graph — an upstream library constant — has no reverse edge
to record). Each entry lists its users in the order they appear in `nodes`. -/
def reverseDeps (nodes : Array (Name × Array Name)) : Std.HashMap Name (Array Name) :=
  let known : Std.HashSet Name := nodes.foldl (fun s (n, _) => s.insert n) {}
  nodes.foldl
    (fun acc (name, deps) =>
      deps.foldl
        (fun inner dep =>
          if known.contains dep then
            inner.insert dep ((inner.getD dep #[]).push name)
          else
            inner)
        acc)
    {}

/-- The walk state: which nodes have been entered, and the post-order emitted so far. -/
abbrev VisitState := Std.HashSet Name × Array Name

/-- The depth-first walk `topologicalClosure` runs, with an explicit `fuel` bounding the recursion
*depth* so that this is a total definition rather than a `partial` one.

Fuel is what makes the recursion structural. It is not a safety valve: `topologicalClosure` passes
`depsMap.size + 1`, and `Proofs/Deps.lean` proves that is always enough — recursion descends only
from a node that has dependencies, hence is a key of `depsMap`, and never twice from the same key,
so the depth cannot exceed the number of keys. Running out is therefore unreachable, and the
`0` case below is what a proof discharges rather than what a run relies on. -/
def visitFuel (depsMap : Std.HashMap Name (Array Name)) :
    Nat → VisitState → Name → VisitState
  | 0, st, _ => st
  | fuel + 1, (visited, order), n =>
    if visited.contains n then
      (visited, order)
    else
      -- Mark `n` before recursing so a dependency cycle cannot loop forever.
      let visited := visited.insert n
      let (visited, order) :=
        (depsMap.getD n #[]).foldl (fun acc d => visitFuel depsMap fuel acc d) (visited, order)
      -- Emit `n` only after all of its dependencies have been emitted.
      (visited, order.push n)

/-- Computes the declarations reachable from `start` via `depsMap`, in *topological* order: every
declaration appears after all of the declarations it depends on (a depth-first post-order). This is
the order in which the declarations could be emitted into a single self-contained Lean file, with
each definition preceding its first use.

Cycles (e.g. mutual recursion) are tolerated: a node is marked visited on entry, so the walk
terminates, and the members of a cycle come out in some arbitrary but otherwise dependency-respecting
order. -/
def topologicalClosure (depsMap : Std.HashMap Name (Array Name)) (start : Array Name) :
    Array Name :=
  (start.foldl (fun acc n => visitFuel depsMap (depsMap.size + 1) acc n) (({}, #[]) : VisitState)).2

/-- The transitive closure of `name`'s dependencies, topologically ordered (every dependency before
the declarations that use it) and excluding `name` itself, so it is directly usable as the body of
a minimal standalone file for `name`. -/
def transitiveDeps (depsMap : Std.HashMap Name (Array Name)) (name : Name) : Array Name :=
  (topologicalClosure depsMap (depsMap.getD name #[])).filter (· != name)

end LeanDeps
