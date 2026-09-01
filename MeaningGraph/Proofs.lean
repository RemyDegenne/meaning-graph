module

public import MeaningGraph

@[expose] public section

/-!
# Proofs about `MeaningGraph`

`MeaningGraph` decides two things before any dependency is computed at all: **which constants
belong to the project**, and **which of those a human actually wrote**. Everything downstream
inherits those answers. A constant wrongly excluded is invisible to every consumer: it never
appears in a report, never enters a closure, never shows up in a count — silently, because nothing
downstream can tell "not a project declaration" from "not there".

So the boundary is where a proof is worth most, and it is also the part of `MeaningGraph` that is
pure: `hasPrefixName` and `isInternalName` are total functions on `Name` with no environment in
sight.
`Name` is an ordinary inductive, so unlike `Json` it supports `induction` directly.

## What is proved

* `hasPrefixName` is a genuine prefix order — reflexive, transitive, closed under extending a name
  — and it is **component-wise**, not textual: `LMLExtra.Foo` does not have prefix `LML`, the case
  the docstring singles out. Also that the anonymous name is a prefix of everything, which is what
  makes an empty `--root` match the whole environment rather than nothing.
* `isInternalName` is **inherited downwards**: anything nested under a compiler-generated name is
  itself internal. That is the docstring's reason for matching at every component rather than only
  the last, and it is what stops a helper like `Foo.match_1.eq_1` from leaking through by being one
  level deeper than the check.

## A note on `partial`

Six definitions in `MeaningGraph` used to be `partial` without needing to be — `isInternalName`,
`projStructureNames`, `collectEmbeddedNames`, `coercionSource?`, `coercionSourceType?` and
`hasConstructorPrefix`. All six recurse structurally, and a `partial def` has no equations, so all
six were unprovable for no reason. They are ordinary definitions now; `hasConstructorPrefix` needed
its `go` rewritten to match on `Name`'s constructors instead of calling `getPrefix`, which is the
same function written so Lean can see the recursion.

`topologicalClosure` was `partial` for a real reason — its termination argument is about a visited
set that grows — and is now total via an explicit fuel bound; see the section on it below. What is
still `partial` in `MeaningGraph` is `expandThroughInternals`, a worklist with the same shape of
argument, and `evalNameExpr?`, whose recursion goes through `Expr.getAppFnArgs` rather than a
constructor.

## What is *not* proved about the closure

Two things, and both are the same missing lemma. `topologicalClosure` passes `depsMap.size + 1` as
fuel, and the argument that this is always enough — recursion descends only from a node with
dependencies, hence a key of `depsMap`, and never twice from the same key, so depth cannot exceed
the number of keys — is written down but not formalized. Everything below holds for *any* fuel and
so does not depend on it.

Given that lemma, two more theorems follow from the invariants already here: **completeness** (every
node reachable from `start` is emitted, not just every root), and the **ordering** property itself.
The ordering argument is: when `n` is pushed, each dependency `d` has been visited, so by
`finished_preserved` it has been emitted, so it precedes `n` — *unless* `d` is an ancestor still on
the walk's stack, which is exactly a cycle. Making that precise needs a reachability relation and an
acyclicity hypothesis, which is the honest form of the docstring's "cycles are tolerated, and their
members come out in some arbitrary order".
-/

open Lean

namespace MeaningGraph.Proofs

open MeaningGraph

/-! ## The project boundary -/

/-- Every name has itself as a prefix. -/
theorem hasPrefixName_self (n : Name) : hasPrefixName n n := by
  induction n <;> simp [hasPrefixName]

/-- The anonymous name is a prefix of everything.

Which is why an empty root prefix selects the whole environment rather than nothing — the degenerate
case a caller passing `.anonymous` for `--root` lands in. -/
theorem hasPrefixName_anonymous (n : Name) : hasPrefixName n .anonymous := by
  induction n with
  | anonymous => simp [hasPrefixName]
  | str p s ih => simp [hasPrefixName, ih]
  | num p i ih => simp [hasPrefixName, ih]

/-- Extending a name keeps its prefixes: a declaration nested inside a project module is still in
the project. -/
theorem hasPrefixName_str {n p : Name} {s : String} (h : hasPrefixName n p) :
    hasPrefixName (.str n s) p := by
  simp [hasPrefixName, h]

theorem hasPrefixName_num {n p : Name} {i : Nat} (h : hasPrefixName n p) :
    hasPrefixName (.num n i) p := by
  simp [hasPrefixName, h]

/-- The prefix relation is transitive, so the boundary is closed under nesting. -/
theorem hasPrefixName_trans {n m p : Name} (h₁ : hasPrefixName n m) (h₂ : hasPrefixName m p) :
    hasPrefixName n p := by
  induction n with
  | anonymous =>
    simp [hasPrefixName] at h₁
    subst h₁; exact h₂
  | str q s ih =>
    rw [hasPrefixName] at h₁
    rcases Bool.or_eq_true _ _ |>.mp h₁ with he | hr
    · simp at he; subst he; exact h₂
    · exact hasPrefixName_str (ih hr)
  | num q i ih =>
    rw [hasPrefixName] at h₁
    rcases Bool.or_eq_true _ _ |>.mp h₁ with he | hr
    · simp at he; subst he; exact h₂
    · exact hasPrefixName_num (ih hr)

/-- **The test is component-wise, not textual.** `LMLExtra.Foo` shares the *characters* `LML` with
the root `LML` and is nonetheless not in it — the case `hasPrefixName`'s docstring calls out, and
the one a `String.startsWith` implementation would get wrong. -/
theorem hasPrefixName_not_textual :
    ¬ hasPrefixName (.str (.str .anonymous "LMLExtra") "Foo") (.str .anonymous "LML") := by
  simp [hasPrefixName]

/-- And the corresponding positive case, so the theorem above is not vacuous. -/
theorem hasPrefixName_nested :
    hasPrefixName (.str (.str .anonymous "LML") "Foo") (.str .anonymous "LML") := by
  simp [hasPrefixName]

/-! ## Compiler-generated names -/

/-- **Internality is inherited downwards.** Anything nested under a compiler-generated name is
itself compiler-generated.

This is why `isInternalName` matches at *every* component rather than only the last: a helper Lean
attaches to a helper, such as `Foo.match_1.eq_1`, is one level deeper than the name that gives it
away. Without this the analysis would expand into a helper's own internals and report them as
project declarations. -/
theorem isInternalName_of_hasPrefixName {n p : Name}
    (hp : hasPrefixName n p) (h : isInternalName p) : isInternalName n := by
  induction n with
  | anonymous =>
    simp [hasPrefixName] at hp
    subst hp; exact h
  | str q s ih =>
    rw [hasPrefixName] at hp
    rcases Bool.or_eq_true _ _ |>.mp hp with he | hr
    · simp at he; subst he; exact h
    · simp [isInternalName, ih hr]
  | num q i ih =>
    rw [hasPrefixName] at hp
    rcases Bool.or_eq_true _ _ |>.mp hp with he | hr
    · simp at he; subst he; exact h
    · simp [isInternalName, ih hr]

/-- A compiler-generated name is caught. -/
theorem isInternalName_hyg : isInternalName (.str (.str .anonymous "Foo") "_hyg") := by
  simp [isInternalName, isAuxComponent]

/-- And an ordinary lemma name is not. This is the direction that matters: a false positive here
deletes a real declaration from the site, silently, because nothing downstream can tell "filtered
out" from "not there". -/
theorem not_isInternalName_ordinary :
    ¬ isInternalName (.str (.str .anonymous "Nat") "add_comm") := by
  simp [isInternalName, isAuxComponent, isPrefixWithDigitSuffix, internalComponentNames]

/-! ### What could not be checked here

The `match_1` and `eq_1` shapes — the ones `isPrefixWithDigitSuffix` exists for — cannot be settled
by `decide`, `rfl` or `simp`. They reduce to concrete `String.drop`/`String.isEmpty` computations,
and in this toolchain `String` is backed by opaque primitives that neither the kernel nor `simp`
evaluates: even `("match_1".drop 6).isEmpty = false` is not provable without `native_decide` (which
would add `Lean.ofReduceBool` to the axiom list, and is not worth it for an example).

`Test/Deps.lean` covers those cases as `#guard`s, which *do* run them, at compile time, through the
compiler rather than the kernel. That is the right division: the general theorems are here, the
concrete evaluations are there, and each is checked by the tool that can actually check it. -/

/-! ## The topological closure

`topologicalClosure` is the pass whose output is *executed*: `Referee/Extract.lean` emits the
declarations of a standalone `.lean` file in exactly this order, so a wrong answer here is a file
that does not compile. The docstring claims three things — that the walk terminates despite cycles,
that nothing is emitted twice, and that every declaration appears after the ones it depends on.

The first is now a fact about the definition rather than a promise: `visitFuel` is total, fuel
bounds the recursion *depth*, and `topologicalClosure` passes `depsMap.size + 1`.

What follows proves the second, plus the invariants the third rests on. All of it holds for **any**
fuel, so none of it depends on the bound being right.
-/

variable (dm : Std.HashMap Name (Array Name))


/-- The visited set only ever grows. -/
theorem visited_mono : ∀ (f : Nat) (st : VisitState) (n m : Name),
    st.1.contains m → (visitFuel dm f st n).1.contains m := by
  intro f
  induction f with
  | zero => intro st n m h; simpa [visitFuel] using h
  | succ f ih =>
    have hfold : ∀ (ds : List Name) (st : VisitState) (m : Name),
        st.1.contains m → (ds.foldl (fun acc d => visitFuel dm f acc d) st).1.contains m := by
      intro ds
      induction ds with
      | nil => intro st m h; simpa using h
      | cons d ds ihd => intro st m h; exact ihd _ _ (ih _ _ _ h)
    intro st n m h
    obtain ⟨visited, order⟩ := st
    rw [visitFuel]
    split
    · exact h
    · simp only
      rw [← Array.foldl_toList]
      exact hfold _ _ _ (by simp [Std.HashSet.contains_insert, h])

theorem visited_mono_fold (f : Nat) : ∀ (ds : List Name) (st : VisitState) (m : Name),
    st.1.contains m → (ds.foldl (fun acc d => visitFuel dm f acc d) st).1.contains m := by
  intro ds
  induction ds with
  | nil => intro st m h; simpa using h
  | cons d ds ihd => intro st m h; exact ihd _ _ (visited_mono dm f _ _ _ h)

/-- Anything emitted during a call was unvisited when the call began. -/
theorem emitted_new : ∀ (f : Nat) (st : VisitState) (n x : Name),
    x ∈ (visitFuel dm f st n).2 → x ∉ st.2 → ¬ st.1.contains x := by
  intro f
  induction f with
  | zero => intro st n x hx hnot; simp [visitFuel] at hx; exact absurd hx hnot
  | succ f ih =>
    have hfold : ∀ (ds : List Name) (st : VisitState) (x : Name),
        x ∈ (ds.foldl (fun acc d => visitFuel dm f acc d) st).2 → x ∉ st.2 →
        ¬ st.1.contains x := by
      intro ds
      induction ds with
      | nil => intro st x hx hnot; simp at hx; exact absurd hx hnot
      | cons d ds ihd =>
        intro st x hx hnot
        by_cases hst1 : x ∈ (visitFuel dm f st d).2
        · exact ih _ _ _ hst1 hnot
        · intro hc
          exact ihd _ _ (by simpa using hx) hst1 (visited_mono dm f _ _ _ hc)
    intro st n x hx hnot
    obtain ⟨visited, order⟩ := st
    rw [visitFuel] at hx
    split at hx
    · exact absurd hx hnot
    · rename_i hn
      simp only at hx
      rw [← Array.foldl_toList] at hx
      rcases Array.mem_push.mp hx with h' | h'
      · intro hc
        exact hfold _ _ _ h' hnot (by simp [Std.HashSet.contains_insert, hc])
      · subst h'; simpa using hn

theorem emitted_new_fold (f : Nat) : ∀ (ds : List Name) (st : VisitState) (x : Name),
    x ∈ (ds.foldl (fun acc d => visitFuel dm f acc d) st).2 → x ∉ st.2 → ¬ st.1.contains x := by
  intro ds
  induction ds with
  | nil => intro st x hx hnot; simp at hx; exact absurd hx hnot
  | cons d ds ihd =>
    intro st x hx hnot
    by_cases hst1 : x ∈ (visitFuel dm f st d).2
    · exact emitted_new dm f _ _ _ hst1 hnot
    · intro hc
      exact ihd _ _ (by simpa using hx) hst1 (visited_mono dm f _ _ _ hc)

/-- Everything emitted has been visited, and nothing is emitted twice. -/
def WalkInv (st : VisitState) : Prop :=
  (∀ x ∈ st.2, st.1.contains x) ∧ st.2.toList.Nodup

theorem inv_preserved : ∀ (f : Nat) (st : VisitState) (n : Name),
    WalkInv st → WalkInv (visitFuel dm f st n) := by
  intro f
  induction f with
  | zero => intro st n h; simpa [visitFuel] using h
  | succ f ih =>
    have hfold : ∀ (ds : List Name) (st : VisitState), WalkInv st →
        WalkInv (ds.foldl (fun acc d => visitFuel dm f acc d) st) := by
      intro ds
      induction ds with
      | nil => intro st h; simpa using h
      | cons d ds ihd => intro st h; exact ihd _ (ih _ _ h)
    intro st n h
    obtain ⟨visited, order⟩ := st
    rw [visitFuel]
    split
    · exact h
    · rename_i hn
      simp only
      rw [← Array.foldl_toList]
      have hstart : WalkInv ((visited.insert n, order) : VisitState) :=
        ⟨fun x hx => by simp [Std.HashSet.contains_insert, h.1 x hx], h.2⟩
      have hinv := hfold ((dm.getD n #[]).toList) _ hstart
      have hn' := visited_mono_fold dm f ((dm.getD n #[]).toList)
        ((visited.insert n, order) : VisitState) n (by simp [Std.HashSet.contains_insert])
      have hnotmem : n ∉ (List.foldl (fun acc d => visitFuel dm f acc d)
          ((visited.insert n, order) : VisitState) ((dm.getD n #[]).toList)).2 := by
        intro hmem
        by_cases hord : n ∈ order
        · exact absurd (h.1 n hord) (by simpa using hn)
        · exact (emitted_new_fold dm f _ _ _ hmem hord) (by simp [Std.HashSet.contains_insert])
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Array.mem_push.mp hx with h' | h'
        · exact hinv.1 x h'
        · subst h'; exact hn'
      · rw [Array.toList_push]
        refine List.nodup_append.mpr ⟨hinv.2, by simp, ?_⟩
        intro a ha b hb heq
        have hbn : b = n := by simpa using hb
        subst hbn
        subst heq
        exact hnotmem (by simpa using ha)

/-- The emitted order only ever grows. -/
theorem order_mem_mono : ∀ (f : Nat) (st : VisitState) (n y : Name),
    y ∈ st.2 → y ∈ (visitFuel dm f st n).2 := by
  intro f
  induction f with
  | zero => intro st n y h; simpa [visitFuel] using h
  | succ f ih =>
    have hfold : ∀ (ds : List Name) (st : VisitState) (y : Name),
        y ∈ st.2 → y ∈ (ds.foldl (fun acc d => visitFuel dm f acc d) st).2 := by
      intro ds
      induction ds with
      | nil => intro st y h; simpa using h
      | cons d ds ihd => intro st y h; exact ihd _ _ (ih _ _ _ h)
    intro st n y h
    obtain ⟨visited, order⟩ := st
    rw [visitFuel]
    split
    · exact h
    · simp only
      rw [← Array.foldl_toList]
      exact Array.mem_push.mpr (Or.inl (hfold _ _ _ h))

theorem order_mem_mono_fold (f : Nat) : ∀ (ds : List Name) (st : VisitState) (y : Name),
    y ∈ st.2 → y ∈ (ds.foldl (fun acc d => visitFuel dm f acc d) st).2 := by
  intro ds
  induction ds with
  | nil => intro st y h; simpa using h
  | cons d ds ihd => intro st y h; exact ihd _ _ (order_mem_mono dm f _ _ _ h)

/-- Anything a call newly visits, that call also emits. -/
theorem visited_emitted : ∀ (f : Nat) (st : VisitState) (n x : Name),
    (visitFuel dm f st n).1.contains x → ¬ st.1.contains x →
    x ∈ (visitFuel dm f st n).2 := by
  intro f
  induction f with
  | zero => intro st n x hx hnot; simp [visitFuel] at hx; exact absurd hx hnot
  | succ f ih =>
    have hfold : ∀ (ds : List Name) (st : VisitState) (x : Name),
        (ds.foldl (fun acc d => visitFuel dm f acc d) st).1.contains x → ¬ st.1.contains x →
        x ∈ (ds.foldl (fun acc d => visitFuel dm f acc d) st).2 := by
      intro ds
      induction ds with
      | nil => intro st x hx hnot; simp at hx; exact absurd hx hnot
      | cons d ds ihd =>
        intro st x hx hnot
        by_cases hd : (visitFuel dm f st d).1.contains x
        · exact order_mem_mono_fold dm f ds _ _ (ih _ _ _ hd hnot)
        · exact ihd _ _ (by simpa using hx) hd
    intro st n x hx hnot
    obtain ⟨visited, order⟩ := st
    by_cases hn : visited.contains n
    · rw [visitFuel, ite_eq_left hn] at hx
      exact absurd hx hnot
    · rw [visitFuel, ite_eq_right hn] at hx ⊢
      simp only at hx ⊢
      rw [← Array.foldl_toList] at hx ⊢
      by_cases hxn : x = n
      · subst hxn; exact Array.mem_push.mpr (Or.inr rfl)
      · refine Array.mem_push.mpr (Or.inl ?_)
        exact hfold _ _ _ hx (by simp [Std.HashSet.contains_insert, hnot, Ne.symm hxn])

theorem inv_fold (f : Nat) : ∀ (ns : List Name) (st : VisitState),
    WalkInv st → WalkInv (ns.foldl (fun acc n => visitFuel dm f acc n) st) := by
  intro ns
  induction ns with
  | nil => intro st h; simpa using h
  | cons n ns ihn => intro st h; exact ihn _ (inv_preserved dm f _ _ h)

/-- **No declaration is emitted twice.**

The claim the extraction depends on most directly: a standalone file that declares the same
constant twice does not compile, and nothing else in the pipeline would catch it. -/
theorem topologicalClosure_nodup (start : Array Name) :
    (topologicalClosure dm start).toList.Nodup := by
  rw [topologicalClosure, ← Array.foldl_toList]
  exact (inv_fold dm _ _ _ ⟨by simp, by simp⟩).2

/-- Visiting a node at positive fuel always leaves it visited. -/
theorem mem_visited_of_visit (f : Nat) (st : VisitState) (n : Name) :
    (visitFuel dm (f + 1) st n).1.contains n := by
  obtain ⟨visited, order⟩ := st
  by_cases hn : visited.contains n
  · rw [visitFuel, ite_eq_left hn]; exact hn
  · rw [visitFuel, ite_eq_right hn]
    simp only
    rw [← Array.foldl_toList]
    exact visited_mono_fold dm f _ _ _ (by simp [Std.HashSet.contains_insert])

/-- Everything visited has been emitted. True of the initial state and preserved, because a call
never returns leaving a node it entered unfinished. -/
def Finished (st : VisitState) : Prop := ∀ x, st.1.contains x → x ∈ st.2

theorem finished_preserved (f : Nat) (st : VisitState) (n : Name) (h : Finished st) :
    Finished (visitFuel dm f st n) := by
  intro x hx
  by_cases hst : st.1.contains x
  · exact order_mem_mono dm f _ _ _ (h x hst)
  · exact visited_emitted dm f _ _ _ hx hst

theorem finished_fold (f : Nat) : ∀ (ns : List Name) (st : VisitState),
    Finished st → Finished (ns.foldl (fun acc m => visitFuel dm f acc m) st) := by
  intro ns
  induction ns with
  | nil => intro st h; simpa using h
  | cons m ms ihm => intro st h; exact ihm _ (finished_preserved dm f _ _ h)

theorem mem_order_fold (f : Nat) : ∀ (ns : List Name) (st : VisitState) (n : Name),
    Finished st → n ∈ ns →
    n ∈ (ns.foldl (fun acc m => visitFuel dm (f + 1) acc m) st).2 := by
  intro ns
  induction ns with
  | nil => intro st n _ hmem; simp at hmem
  | cons m ms ihm =>
    intro st n hfin hmem
    rcases List.mem_cons.mp hmem with rfl | hrest
    · refine order_mem_mono_fold dm (f + 1) ms _ _ ?_
      exact finished_preserved dm (f + 1) st n hfin n (mem_visited_of_visit dm f st n)
    · exact ihm _ _ (finished_preserved dm (f + 1) _ _ hfin) hrest

/-- **Every root is emitted.** Each element of `start` appears in the output. -/
theorem mem_topologicalClosure_of_mem_start (start : Array Name) (n : Name) (hn : n ∈ start) :
    n ∈ topologicalClosure dm start := by
  rw [topologicalClosure, ← Array.foldl_toList]
  exact mem_order_fold dm dm.size _ _ _ (by intro x hx; simp at hx) (by simpa using hn)

/-! ## The base of the dependency analysis: `projStructureNames` loses nothing

Everything on the site is downstream of the dependency analysis being right, and the analysis
bottoms out in walks over `Expr`. If a constant can hide from one of those walks, every closure
above it under-reports — and under-reporting is the direction that matters: the site then claims a
result rests on less than it does, which is indistinguishable from a result that really does rest on
less.

`projStructureNames` recovers the structure names carried by `Expr.proj` nodes, which
`Expr.getUsedConstants` dropped up to Lean 4.33 (core reports them itself since 4.34, so the walk
is now the kept-in-reserve statement of the recovery rather than a live part of
`exprUsedConstants`). Its own docstring records that it was added as "a correctness guard,
not a fix for an observed failure" — which is exactly the situation where a proof beats a test,
because the failure would be on term shapes no target project happened to elaborate.

The risk in it is the **memo**. The walk skips any subterm it has already seen, and a memo that
skips too much loses names silently. What follows is that it does not: everything the naive
structural walk (`projNames`) would report, the memoized walk reports.

### The assumption, stated rather than hidden

`Expr` has **no** `LawfulBEq`, `EquivBEq` or `LawfulHashable` instance in this toolchain — none of
the three synthesizes — so nothing about a `Std.HashSet Expr` can be proved unconditionally. Rather
than assume `LawfulBEq Expr` (which is likely *false*: `Expr`'s `BEq` need not distinguish terms
differing only in binder names), the theorem takes the weakest hypothesis that actually makes the
memo safe:

    hcompat : ∀ x y, x == y → projNames x = projNames y

*equal-as-the-memo-sees-it implies the same proj-names*. That is precisely the property a memo keyed
on `==` needs, and stating it is the point: it converts "we hope skipping seen subterms is fine"
into one inspectable sentence about `Expr`'s equality.
-/


def projNames : Expr → List Name
  | .app f a => projNames f ++ projNames a
  | .lam _ t b _ => projNames t ++ projNames b
  | .forallE _ t b _ => projNames t ++ projNames b
  | .letE _ t v b _ => projNames t ++ projNames v ++ projNames b
  | .mdata _ b => projNames b
  | .proj s _ b => s :: projNames b
  | _ => []

def ProjInv (st : Array Name × Std.HashSet Expr) : Prop :=
  ∀ x, st.2.contains x → ∀ s ∈ projNames x, s ∈ st.1

section
variable [EquivBEq Expr] [LawfulHashable Expr]
  (hcompat : ∀ x y : Expr, (x == y) = true → projNames x = projNames y)

include hcompat in
theorem go_spec : ∀ (e : Expr) (st : Array Name × Std.HashSet Expr), ProjInv st →
    ProjInv (projStructureNames.go e st) ∧
    (∀ x ∈ st.1, x ∈ (projStructureNames.go e st).1) ∧
    (∀ s ∈ projNames e, s ∈ (projStructureNames.go e st).1) := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.app f a)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      obtain ⟨i1, i2, i3⟩ := ihf (acc, seen) hinv
      obtain ⟨j1, j2, j3⟩ := iha _ i1
      refine ⟨?_, fun x hx => j2 _ (i2 _ hx), ?_⟩
      · intro x hx s hsm
        rw [Std.HashSet.contains_insert] at hx
        rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
        · rw [← hcompat _ _ heq] at hsm
          rcases List.mem_append.mp (by simpa [projNames] using hsm) with h | h
          · exact j2 _ (i3 s h)
          · exact j3 s h
        · exact j1 x hin s hsm
      · intro s hsm
        rcases List.mem_append.mp (by simpa [projNames] using hsm) with h | h
        · exact j2 _ (i3 s h)
        · exact j3 s h
  | lam nm t b bi iht ihb =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.lam nm t b bi)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      obtain ⟨i1, i2, i3⟩ := iht (acc, seen) hinv
      obtain ⟨j1, j2, j3⟩ := ihb _ i1
      refine ⟨?_, fun x hx => j2 _ (i2 _ hx), ?_⟩
      · intro x hx s hsm
        rw [Std.HashSet.contains_insert] at hx
        rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
        · rw [← hcompat _ _ heq] at hsm
          rcases List.mem_append.mp (by simpa [projNames] using hsm) with h | h
          · exact j2 _ (i3 s h)
          · exact j3 s h
        · exact j1 x hin s hsm
      · intro s hsm
        rcases List.mem_append.mp (by simpa [projNames] using hsm) with h | h
        · exact j2 _ (i3 s h)
        · exact j3 s h
  | forallE nm t b bi iht ihb =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.forallE nm t b bi)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      obtain ⟨i1, i2, i3⟩ := iht (acc, seen) hinv
      obtain ⟨j1, j2, j3⟩ := ihb _ i1
      refine ⟨?_, fun x hx => j2 _ (i2 _ hx), ?_⟩
      · intro x hx s hsm
        rw [Std.HashSet.contains_insert] at hx
        rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
        · rw [← hcompat _ _ heq] at hsm
          rcases List.mem_append.mp (by simpa [projNames] using hsm) with h | h
          · exact j2 _ (i3 s h)
          · exact j3 s h
        · exact j1 x hin s hsm
      · intro s hsm
        rcases List.mem_append.mp (by simpa [projNames] using hsm) with h | h
        · exact j2 _ (i3 s h)
        · exact j3 s h
  | letE nm t v b nd iht ihv ihb =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.letE nm t v b nd)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      obtain ⟨i1, i2, i3⟩ := iht (acc, seen) hinv
      obtain ⟨j1, j2, j3⟩ := ihv _ i1
      obtain ⟨k1, k2, k3⟩ := ihb _ j1
      have hall : ∀ s ∈ projNames (Expr.letE nm t v b nd),
          s ∈ (projStructureNames.go b (projStructureNames.go v
            (projStructureNames.go t (acc, seen)))).1 := by
        intro s hsm
        have hsplit : s ∈ projNames t ∨ s ∈ projNames v ∨ s ∈ projNames b := by
          simpa [projNames] using hsm
        rcases hsplit with h | h | h
        · exact k2 _ (j2 _ (i3 s h))
        · exact k2 _ (j3 s h)
        · exact k3 s h
      refine ⟨?_, fun x hx => k2 _ (j2 _ (i2 _ hx)), hall⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · exact hall s (by rw [hcompat _ _ heq]; exact hsm)
      · exact k1 x hin s hsm
  | mdata d b ihb =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.mdata d b)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      obtain ⟨i1, i2, i3⟩ := ihb (acc, seen) hinv
      refine ⟨?_, i2, fun s hsm => i3 s (by simpa [projNames] using hsm)⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · rw [← hcompat _ _ heq] at hsm
        exact i3 s (by simpa [projNames] using hsm)
      · exact i1 x hin s hsm
  | proj sn idx b ihb =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.proj sn idx b)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      have hinv' : ProjInv (acc.push sn, seen) := fun x hx t htm =>
        Array.mem_push.mpr (Or.inl (hinv x hx t htm))
      obtain ⟨i1, i2, i3⟩ := ihb (acc.push sn, seen) hinv'
      have hsn : sn ∈ (projStructureNames.go b (acc.push sn, seen)).1 :=
        i2 _ (Array.mem_push.mpr (Or.inr rfl))
      have hall : ∀ t ∈ projNames (Expr.proj sn idx b),
          t ∈ (projStructureNames.go b (acc.push sn, seen)).1 := by
        intro t htm
        rcases List.mem_cons.mp (by simpa [projNames] using htm) with rfl | h
        · exact hsn
        · exact i3 t h
      refine ⟨?_, fun x hx => i2 _ (Array.mem_push.mpr (Or.inl hx)), hall⟩
      intro x hx t htm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · exact hall t (by rw [hcompat _ _ heq]; exact htm)
      · exact i1 x hin t htm
  | bvar i =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.bvar i)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      refine ⟨?_, fun x hx => hx, by simp [projNames]⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · rw [← hcompat _ _ heq] at hsm; simp [projNames] at hsm
      · exact hinv x hin s hsm
    all_goals simp
  | fvar fv =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.fvar fv)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      refine ⟨?_, fun x hx => hx, by simp [projNames]⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · rw [← hcompat _ _ heq] at hsm; simp [projNames] at hsm
      · exact hinv x hin s hsm
    all_goals simp
  | mvar mv =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.mvar mv)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      refine ⟨?_, fun x hx => hx, by simp [projNames]⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · rw [← hcompat _ _ heq] at hsm; simp [projNames] at hsm
      · exact hinv x hin s hsm
    all_goals simp
  | sort u =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.sort u)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      refine ⟨?_, fun x hx => hx, by simp [projNames]⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · rw [← hcompat _ _ heq] at hsm; simp [projNames] at hsm
      · exact hinv x hin s hsm
    all_goals simp
  | const nm us =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.const nm us)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      refine ⟨?_, fun x hx => hx, by simp [projNames]⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · rw [← hcompat _ _ heq] at hsm; simp [projNames] at hsm
      · exact hinv x hin s hsm
    all_goals simp
  | lit l =>
    intro st hinv
    obtain ⟨acc, seen⟩ := st
    rw [projStructureNames.go]
    by_cases hs : seen.contains (Expr.lit l)
    · rw [ite_eq_left hs]; exact ⟨hinv, fun x hx => hx, hinv _ hs⟩
    · rw [ite_eq_right hs]
      simp only
      refine ⟨?_, fun x hx => hx, by simp [projNames]⟩
      intro x hx s hsm
      rw [Std.HashSet.contains_insert] at hx
      rcases Bool.or_eq_true _ _ |>.mp hx with heq | hin
      · rw [← hcompat _ _ heq] at hsm; simp [projNames] at hsm
      · exact hinv x hin s hsm
    all_goals simp

include hcompat in
/-- **The memo loses nothing.** -/
theorem projStructureNames_complete (e : Expr) (s : Name) (h : s ∈ projNames e) :
    s ∈ projStructureNames e := by
  have hinit : ProjInv ((#[], {}) : Array Name × Std.HashSet Expr) := by
    intro x hx; simp at hx
  have := (go_spec hcompat e (#[], {}) hinit).2.2 s h
  simpa [projStructureNames] using this

end

/-! ## Completeness: the closure is closed

The invariants above hold for any fuel. This section supplies the missing piece — that
`depsMap.size + 1` is always enough — and with it the theorem the rest of the tool leans on without
saying so.

**Why the bound works.** The walk descends only from a node with dependencies, hence a key of
`depsMap`, and never twice from the same key, because a node is marked visited before its
dependencies are walked. So `unvisitedKeys` — how many keys the walk has not yet entered — strictly
decreases at every recursive call, and the recursion depth cannot exceed the number of keys.

**What it buys.** `transitiveDeps_closed`: if `y` is in a declaration's transitive closure and `z` is
a dependency of `y`, then `z` is in that closure too. Three separate features assume this and none
of them states it:

* `Referee/Diff.lean` finds indirect invalidation by *one pass* over `dataTransDeps`, not a fixpoint
  — correct only because the closure is already closed. Its docstring says "closing the changed set
  over `dataTransDeps` finds it exactly", which is true precisely under this theorem;
* `Referee/Audit.lean` defines coverage as "accepted, and every project declaration in its statement
  closure accepted too", and walks that closure bottom-up as a reading queue;
* the declaration graph lays the closure out in rows by depth.

A closure that was not closed would make all three quietly wrong in the same direction — reporting
less to re-read, less to accept, and less to look at — which is the direction that reads exactly
like a library with fewer dependencies.
-/

variable (dm : Std.HashMap Name (Array Name))

/-! ### A measure that strictly decreases at every recursive call -/

theorem length_filter_mono {α} (l : List α) (p q : α → Bool) (h : ∀ a, p a → q a) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    by_cases hp : p a
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h a hp)]
      simpa using ih
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      by_cases hq : q a
      · rw [List.filter_cons_of_pos hq]; simp; omega
      · rw [List.filter_cons_of_neg (by simpa using hq)]; exact ih

theorem length_filter_lt {α} (l : List α) (p q : α → Bool) (n : α)
    (h : ∀ a, p a → q a) (hn : n ∈ l) (hq : q n) (hp : ¬ p n) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hn
  | cons a as ih =>
    rcases List.mem_cons.mp hn with rfl | hrest
    · rw [List.filter_cons_of_neg (by simpa using hp), List.filter_cons_of_pos hq]
      have := length_filter_mono as p q h
      simp; omega
    · by_cases hpa : p a
      · rw [List.filter_cons_of_pos hpa, List.filter_cons_of_pos (h a hpa)]
        simpa using ih hrest
      · rw [List.filter_cons_of_neg (by simpa using hpa)]
        have := ih hrest
        by_cases hqa : q a
        · rw [List.filter_cons_of_pos hqa]; simp; omega
        · rw [List.filter_cons_of_neg (by simpa using hqa)]; exact this

/-- How many of `dm`'s keys the walk has not entered yet. Strictly decreases at every recursive
call, which is why `depsMap.size + 1` fuel is always enough. -/
def unvisitedKeys (visited : Std.HashSet Name) : Nat :=
  (dm.keys.filter (fun k => !visited.contains k)).length

theorem unvisitedKeys_le (visited : Std.HashSet Name) : unvisitedKeys dm visited ≤ dm.size := by
  rw [unvisitedKeys, ← Std.HashMap.length_keys]
  exact List.length_filter_le _ _

theorem unvisitedKeys_mono {v v' : Std.HashSet Name} (h : ∀ x, v.contains x → v'.contains x) :
    unvisitedKeys dm v' ≤ unvisitedKeys dm v := by
  refine length_filter_mono _ _ _ ?_
  intro a ha
  simp only [Bool.not_eq_true'] at ha ⊢
  by_cases hc : v.contains a
  · rw [h a hc] at ha; exact absurd ha (by simp)
  · simpa using hc

theorem unvisitedKeys_lt {v : Std.HashSet Name} {n : Name} (hn : n ∈ dm)
    (hv : ¬ v.contains n) : unvisitedKeys dm (v.insert n) < unvisitedKeys dm v := by
  refine length_filter_lt _ _ _ n ?_ (Std.HashMap.mem_keys.mpr hn) (by simpa using hv) ?_
  · intro a ha
    simp only [Bool.not_eq_true'] at ha ⊢
    by_cases hc : v.contains a
    · rw [show (v.insert n).contains a = true from by simp [Std.HashSet.contains_insert, hc]] at ha
      exact absurd ha (by simp)
    · simpa using hc
  · simp [Std.HashSet.contains_insert]

/-! ### Every dependency is visited before its dependent is emitted -/

theorem mem_visited_fold (f : Nat) : ∀ (ds : List Name) (st : VisitState) (z : Name),
    z ∈ ds → (ds.foldl (fun acc d => visitFuel dm (f + 1) acc d) st).1.contains z := by
  intro ds
  induction ds with
  | nil => intro st z hz; simp at hz
  | cons d ds ihd =>
    intro st z hz
    rcases List.mem_cons.mp hz with rfl | hrest
    · exact visited_mono_fold dm (f + 1) ds _ _ (mem_visited_of_visit dm f st z)
    · exact ihd _ _ hrest

theorem deps_visited : ∀ (f : Nat) (st : VisitState) (n : Name),
    unvisitedKeys dm st.1 < f →
    ∀ y ∈ (visitFuel dm f st n).2, y ∉ st.2 →
    ∀ z ∈ dm.getD y #[], (visitFuel dm f st n).1.contains z := by
  intro f
  induction f with
  | zero => intro st n hf; exact absurd hf (Nat.not_lt_zero _)
  | succ f ih =>
    have hfold : ∀ (ds : List Name) (st : VisitState),
        unvisitedKeys dm st.1 < f →
        ∀ y ∈ (ds.foldl (fun acc d => visitFuel dm f acc d) st).2, y ∉ st.2 →
        ∀ z ∈ dm.getD y #[],
          (ds.foldl (fun acc d => visitFuel dm f acc d) st).1.contains z := by
      intro ds
      induction ds with
      | nil => intro st _ y hy hny; simp at hy; exact absurd hy hny
      | cons d ds ihd =>
        intro st hlt y hy hny z hz
        have hmono : unvisitedKeys dm (visitFuel dm f st d).1 < f :=
          Nat.lt_of_le_of_lt (unvisitedKeys_mono dm (visited_mono dm f st d)) hlt
        by_cases hy1 : y ∈ (visitFuel dm f st d).2
        · exact visited_mono_fold dm f ds _ _ (ih st d hlt y hy1 hny z hz)
        · exact ihd _ hmono y (by simpa using hy) hy1 z hz
    intro st n hf y hy hny z hz
    obtain ⟨visited, order⟩ := st
    have hf' : unvisitedKeys dm visited < f + 1 := hf
    by_cases hn : visited.contains n
    · rw [visitFuel, ite_eq_left hn] at hy; exact absurd hy hny
    · rw [visitFuel, ite_eq_right hn] at hy ⊢
      simp only at hy ⊢
      rw [← Array.foldl_toList] at hy ⊢
      by_cases hempty : dm.getD n #[] = #[]
      · rw [hempty] at hy ⊢
        simp only [List.foldl_nil] at hy ⊢
        rcases Array.mem_push.mp hy with hyo | rfl
        · exact absurd hyo hny
        · rw [hempty] at hz; simp at hz
      · have hmem : n ∈ dm := by
          by_cases hc : n ∈ dm
          · exact hc
          · exact absurd (Std.HashMap.getD_eq_fallback hc) hempty
        have hlt : unvisitedKeys dm (visited.insert n) < f :=
          Nat.lt_of_lt_of_le (unvisitedKeys_lt dm hmem (by simpa using hn)) (by omega)
        rcases Array.mem_push.mp hy with hyo | rfl
        · exact hfold _ _ hlt y hyo hny z hz
        · obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
          exact mem_visited_fold dm g _ _ z (by simpa using hz)

theorem deps_visited_fold (f : Nat) : ∀ (ns : List Name) (st : VisitState),
    unvisitedKeys dm st.1 < f →
    ∀ y ∈ (ns.foldl (fun acc m => visitFuel dm f acc m) st).2, y ∉ st.2 →
    ∀ z ∈ dm.getD y #[],
      (ns.foldl (fun acc m => visitFuel dm f acc m) st).1.contains z := by
  intro ns
  induction ns with
  | nil => intro st _ y hy hny; simp at hy; exact absurd hy hny
  | cons d ds ihd =>
    intro st hlt y hy hny z hz
    have hmono : unvisitedKeys dm (visitFuel dm f st d).1 < f :=
      Nat.lt_of_le_of_lt (unvisitedKeys_mono dm (visited_mono dm f st d)) hlt
    by_cases hy1 : y ∈ (visitFuel dm f st d).2
    · exact visited_mono_fold dm f ds _ _ (deps_visited dm f st d hlt y hy1 hny z hz)
    · exact ihd _ hmono y (by simpa using hy) hy1 z hz

/-- **The output is closed under taking dependencies.** -/
theorem topologicalClosure_closed (start : Array Name) (y z : Name)
    (hy : y ∈ topologicalClosure dm start) (hz : z ∈ dm.getD y #[]) :
    z ∈ topologicalClosure dm start := by
  rw [topologicalClosure, ← Array.foldl_toList] at hy ⊢
  have hinit : unvisitedKeys dm (∅ : Std.HashSet Name) < dm.size + 1 :=
    Nat.lt_succ_of_le (unvisitedKeys_le dm _)
  have hfin : Finished (start.toList.foldl
      (fun acc m => visitFuel dm (dm.size + 1) acc m) (({}, #[]) : VisitState)) :=
    finished_fold dm _ _ _ (by intro x hx; simp at hx)
  exact hfin z (deps_visited_fold dm (dm.size + 1) start.toList _ hinit y hy (by simp) z hz)

/-- **`transitiveDeps` really is transitively closed.** -/
theorem transitiveDeps_closed (x y z : Name) (hy : y ∈ transitiveDeps dm x)
    (hz : z ∈ dm.getD y #[]) (hzx : z ≠ x) : z ∈ transitiveDeps dm x := by
  rw [transitiveDeps, Array.mem_filter] at hy ⊢
  exact ⟨topologicalClosure_closed dm _ y z hy.1 hz, by simpa using hzx⟩

end MeaningGraph.Proofs
