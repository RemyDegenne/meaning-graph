module

public import MeaningGraph
-- The checks below are `#guard`s, which Lean elaborates into compile-time (`meta`)
-- definitions, so the declarations under test have to be imported at that level too.
meta import MeaningGraph

@[expose] public section

/-!
# Tests for `MeaningGraph`

Unit checks for the standalone dependency analysis: the name classification that decides where the
analysis stops, the `Expr`-level constant collection the dependency lists are built from, the
recovery of dependencies the elaborated term drops (notation, coercions), and the graph passes that
run on the resulting `(name, deps)` graph.

Each check is a `#guard`, so any regression turns into a build error. Run with `lake build MeaningGraphTest`.

The functions that need a full `Environment` (`usedConstantsOf`, `expandThroughInternals`,
`Context.declDeps`) are exercised against a real project instead; they are not unit-tested here
because constructing a synthetic `Environment` is impractical.
-/

open Lean Std
open MeaningGraph

namespace MeaningGraph.Test

/-! ## Name classification -/

-- `isPrefixWithDigitSuffix pfx s`: `pfx` then a non-empty run of digits.
#guard isPrefixWithDigitSuffix "match_" "match_1"
#guard isPrefixWithDigitSuffix "match_" "match_12"
#guard !isPrefixWithDigitSuffix "match_" "match_"          -- empty suffix
#guard !isPrefixWithDigitSuffix "match_" "match_x"         -- non-digit suffix
#guard !isPrefixWithDigitSuffix "match_" "match_1a"        -- mixed suffix
#guard !isPrefixWithDigitSuffix "match_" "prefix_1"        -- wrong prefix
#guard isPrefixWithDigitSuffix "eq_" "eq_2"
#guard isPrefixWithDigitSuffix "hcongr_" "hcongr_11"

-- `isAuxComponent`: a single name component that the compiler auto-generates.
#guard isAuxComponent "_hyg"           -- underscore-led
#guard isAuxComponent "_proof_3"
#guard isAuxComponent "match_1"
#guard isAuxComponent "eq_4"
#guard isAuxComponent "eq_def"
#guard isAuxComponent "eq_unfold"
#guard isAuxComponent "hcongr_2"
#guard !isAuxComponent "eq"            -- bare `eq` is a legitimate component
#guard !isAuxComponent "matchup"       -- not the `match_<n>` pattern
#guard !isAuxComponent "foo"

-- `isInternalName`: true if *any* component is auxiliary or a known compiler suffix.
#guard isInternalName `Foo.match_1
#guard isInternalName `Foo._proof_2
#guard isInternalName `Foo.bar._hyg        -- internal in a non-leaf position
-- The recursor family, `casesOn`, and constructor companions like `injEq` are deliberately
-- *not* caught here: `shouldExpose` excludes them via environment metadata instead
-- (`isAuxRecursor`, `hasConstructorPrefix`, `ConstantInfo.recInfo`), since string-matching alone
-- can't distinguish them from a user declaration that happens to share the name.
#guard !isInternalName `List.rec
#guard !isInternalName `Foo.casesOn
#guard !isInternalName `Foo.injEq
-- `mk` is *not* flagged syntactically: the real constructor is excluded via the environment
-- (`ctorInfo`) in `shouldExpose`, while a user `def Foo.mk` must remain exposed.
#guard !isInternalName `Foo.mk
#guard !isInternalName `Nat.add
#guard !isInternalName `Foo.bar
#guard !isInternalName `Foo.barRec        -- `rec` only matches as a whole component

-- `hasPrefixName n p`: `p` is `n` itself or one of its dotted ancestors (component-wise,
-- NOT a string prefix).
#guard hasPrefixName `LML `LML
#guard hasPrefixName `LML.Foo.Bar `LML
#guard hasPrefixName `LML.Foo.Bar `LML.Foo
#guard !hasPrefixName `LMLExtra.Foo `LML   -- must not match on a string prefix
#guard !hasPrefixName `LML `LML.Foo        -- a descendant is not a prefix
#guard !hasPrefixName `Other.LML `LML      -- prefix must be anchored at the root

/-! ## `Expr`-level constant collection

Up to Lean 4.33, `Expr.getUsedConstants` recursed *through* an `Expr.proj` node without ever
reporting the structure name it carries, so a structure an elaborated term reaches only by
projecting a field would have been missing from the declaration's `deps`/`typeDeps`;
`projStructureNames` recovered exactly those names and `exprUsedConstants` appended them to what
core reports. Core closed the gap in 4.34, so `exprUsedConstants` is now `getUsedConstants`
unchanged, and `projStructureNames` remains the proven statement of the recovery that would be
needed again were core to regress — the first guard below is what would fail.

Both are pure functions of an `Expr`, so — unlike `usedConstantsOf`, which needs an
`Environment` — they can be checked here directly. -/

private def natE : Expr := .const `Nat []
private def zeroE : Expr := .const `Nat.zero []
private def projA : Expr := .proj `A 0 (.bvar 0)

-- The 4.34 fix `exprUsedConstants` now relies on: core itself reports the structure name of a
-- projection of a bound variable. If this fails, core dropped the name again and
-- `exprUsedConstants` must go back to appending `projStructureNames`.
#guard Expr.getUsedConstants projA == #[`A]
#guard projStructureNames projA == #[`A]
#guard exprUsedConstants projA == #[`A]

-- Projections are found under every structural node the walk descends into.
#guard projStructureNames (.app projA (.proj `B 1 (.bvar 1))) == #[`A, `B]
#guard projStructureNames (.lam `x natE projA .default) == #[`A]
#guard projStructureNames (.forallE `x natE projA .default) == #[`A]
#guard projStructureNames (.letE `x natE projA (.proj `B 0 (.bvar 0)) false) == #[`A, `B]
#guard projStructureNames (.mdata {} projA) == #[`A]

-- Structurally identical subterms are walked once, so a shared projection is reported once...
#guard projStructureNames (.app projA projA) == #[`A]
-- ...while two *different* projections of the same structure both report it (consumers dedup).
#guard projStructureNames (.app projA (.proj `A 1 (.bvar 0))) == #[`A, `A]

-- With no projection anywhere, `projStructureNames` finds nothing to recover.
#guard projStructureNames (.app natE zeroE) == (#[] : Array Name)

-- Ordinary constants and projected structures are both reported.
#guard exprUsedConstants (.app zeroE projA) == #[`Nat.zero, `A]

/-! ## Dependencies the elaborated term does not mention -/

-- `coercionSourceType?`: the type coerced *from* in a coercion-class application, seen through binders.
#guard coercionSourceType? (mkApp2 (mkConst ``CoeFun) (mkConst ``Nat) (mkConst ``Nat)) == some `Nat
#guard coercionSourceType?
  (.forallE `x (mkConst ``Nat) (mkApp2 (mkConst ``CoeOut) (mkConst ``Int) (mkConst ``Int)) .default)
  == some `Int
#guard coercionSourceType? (mkConst ``Nat) == none   -- not a coercion-class application

-- `evalNameExpr?`: reconstruct the `Name` an `Expr` builds via `Name.anonymous`/`mkStr*`/`str`.
#guard evalNameExpr? (mkConst ``Lean.Name.anonymous) == some Name.anonymous
#guard evalNameExpr? (mkApp2 (mkConst ``Lean.Name.mkStr2) (mkStrLit "Foo") (mkStrLit "bar"))
  == some `Foo.bar
#guard evalNameExpr? (mkConst ``Nat.add) == none   -- not a name-building application
-- `collectEmbeddedNames` finds such names anywhere in the expression tree.
#guard (collectEmbeddedNames
  (mkApp (mkConst ``id) (mkApp2 (mkConst ``Lean.Name.mkStr2) (mkStrLit "A") (mkStrLit "b")))).contains
  `A.b

/-! ## Data dependencies: the proofs inside a value

Unlike `usedConstantsOf` and `Context.declDeps`, these need only *an* `Environment`, not a project
one, so they are checked here against this file's own — the declarations below are the fixtures.

Each check is an `#eval` returning `Bool` rather than a `#guard`, because the functions run in
`MetaM`; `#guard_msgs` turns a wrong answer into a build error just the same. -/

structure Boxed where
  val : Nat
  isPos : 0 < val

/-- Built by a constructor literal: `Nat.one_pos` fills the `Prop`-valued field `isPos`. -/
def boxedLiteral : Boxed := ⟨1, Nat.one_pos⟩

/-- Built by *calling* something that returns a `Boxed`, which is the shape the mask has to handle
beyond constructors — `instance : NormedAddCommGroup … := Function.Injective.normedAddCommGroup …`
is the same pattern. `Nat.lt_irrefl` here is an argument to an ordinary function, not a field. -/
def boxedOfProof (n : Nat) (h : 0 < n) : Boxed := ⟨n, h⟩
def boxedCalled : Boxed := boxedOfProof 2 (Nat.succ_pos 1)

def mentions (declName constName : Name) (dataOnly : Bool) : MetaM Bool := do
  let env ← getEnv
  let some info := env.find? declName | return false
  let consts ← if dataOnly then dataValueConstants info
    else pure (usedConstantsOf env declName info (includeValue := true))
  return consts.contains constName

-- The proof filling a constructor's `Prop` field is dropped, while the data field is kept.
/-- info: false -/
#guard_msgs in
#eval mentions ``boxedLiteral ``Nat.one_pos (dataOnly := true)
/-- info: true -/
#guard_msgs in
#eval mentions ``boxedLiteral ``Boxed.mk (dataOnly := true)
-- Positive control: the ordinary walk *does* report it, so the check above is not vacuous.
/-- info: true -/
#guard_msgs in
#eval mentions ``boxedLiteral ``Nat.one_pos (dataOnly := false)

-- The same for a proof passed to a non-constructor, which is what generalizing the mask beyond
-- constructors buys. The data argument is kept.
/-- info: true -/
#guard_msgs in
#eval mentions ``boxedCalled ``boxedOfProof (dataOnly := true)

-- Here Lean abstracts the proof argument into an auxiliary `boxedCalled._proof_1` rather than
-- leaving `Nat.succ_pos` in the term, so *neither* walk names the lemma directly and asking about
-- it would prove nothing either way. What distinguishes them is the aux constant: the ordinary walk
-- reports it (and `expandThroughInternals` would then pull its dependencies in), the data walk skips
-- it along with the rest of the `Prop`-valued argument.
/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  let env ← getEnv
  let some info := env.find? ``boxedCalled | return false
  let data ← dataValueConstants info
  let all := usedConstantsOf env ``boxedCalled info (includeValue := true)
  return all.any isInternalName && !data.any isInternalName

/-! ### Choice: the case the mask must *not* cover

`Exists.choose`'s proof argument is not an obligation discharged beside the data — it is what
supplies the data, and the lemma proving it is the only project declaration a definition of this
shape names at all. Masking every `Prop` parameter dropped it, which is why the mask is restricted
to constants that return a structure. -/

theorem existsPos : ∃ n : Nat, 0 < n := ⟨1, Nat.one_pos⟩

/-- The shape of `IsPreBrownianReal.mk`: the whole body is `.choose` of a project lemma. -/
noncomputable def chosenPos : Nat := existsPos.choose

-- The lemma survives the data walk, where an unrestricted mask would have dropped it.
/-- info: true -/
#guard_msgs in
#eval mentions ``chosenPos ``existsPos (dataOnly := true)

-- `constPropMask` reads declared types: `boxedOfProof`'s second parameter is the `Prop` one, and
-- `boxedOfProof` returns a structure, so the mask applies to it.
/-- info: #[false, true] -/
#guard_msgs in
#eval constPropMask ``boxedOfProof
-- `Exists.choose` returns a bare type variable rather than a structure, so it masks nothing even
-- though its third parameter *is* a proof. This is the check that pins the restriction down.
/-- info: #[] -/
#guard_msgs in
#eval constPropMask ``Exists.choose
-- An unknown constant masks nothing, so every argument stays data (the conservative direction).
/-- info: #[] -/
#guard_msgs in
#eval constPropMask `No.Such.Constant

/-! ## Graph passes

These run on the plain `(name, deps)` graph, with the caller having already chosen which edges
count. In this repo, `Referee.Collect` wraps each of them for its own declaration record and
`Test/Collect.lean` checks that wrapping; what is checked here is the passes themselves.
-/

/-! ### `topologicalClosure` (depth-first post-order: every dependency before its users) -/

private def diamond : HashMap Name (Array Name) :=
  .ofList [(`A, #[`B, `C]), (`B, #[`D]), (`C, #[`D]), (`D, #[`E]), (`E, #[])]

-- Dependencies come out before the declarations that use them: `E` (deepest) first, the start
-- node `A` last. Each node appears exactly once.
#guard topologicalClosure diamond #[`A] == #[`E, `D, `B, `C, `A]
#guard topologicalClosure diamond #[`B, `C] == #[`E, `D, `B, `C]
#guard topologicalClosure diamond #[`E] == #[`E]
#guard topologicalClosure diamond #[] == (#[] : Array Name)

-- A cycle must terminate and visit each node exactly once.
private def cyclic : HashMap Name (Array Name) :=
  .ofList [(`A, #[`B]), (`B, #[`A])]
#guard topologicalClosure cyclic #[`A] == #[`B, `A]

-- Unknown nodes are treated as leaves (no entry ⇒ no further deps).
#guard topologicalClosure diamond #[`Z] == #[`Z]

-- The defining property: for the full ordering, every node precedes all nodes that depend on it.
-- Here `lib → util → core`, with an extra `app → lib`, so the order must be core, util, lib, app.
private def layered : HashMap Name (Array Name) :=
  .ofList [(`app, #[`lib]), (`lib, #[`util]), (`util, #[`core]), (`core, #[])]
#guard topologicalClosure layered #[`app] == #[`core, `util, `lib, `app]

/-! ### `transitiveDeps` (the closure of one node, topologically ordered, minus the node itself) -/

#guard transitiveDeps diamond `A == #[`E, `D, `B, `C]
#guard transitiveDeps diamond `E == (#[] : Array Name)
#guard transitiveDeps diamond `Z == (#[] : Array Name)   -- unknown node ⇒ no dependencies
-- Self-reference (mutual recursion) is filtered out, but the cycle partner is kept.
#guard transitiveDeps cyclic `A == #[`B]
#guard transitiveDeps cyclic `B == #[`A]

/-! ### `reverseDeps` (who uses whom, restricted to nodes of the graph) -/

private def revGraph : Array (Name × Array Name) := #[
  (`A, #[`B, `C]),
  (`B, #[`C]),
  (`C, #[]),
  -- `D` depends on `C` and on `External`, which is not a node of this graph.
  (`D, #[`C, `External])
]

#guard (reverseDeps revGraph).getD `C #[] == #[`A, `B, `D]   -- users in `nodes` order
#guard (reverseDeps revGraph).getD `B #[] == #[`A]
#guard (reverseDeps revGraph).getD `A #[] == (#[] : Array Name)
-- An edge pointing outside the graph records nothing, so no spurious node appears.
#guard !(reverseDeps revGraph).contains `External

end MeaningGraph.Test
