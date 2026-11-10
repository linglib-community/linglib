module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Basic
public import Linglib.Core.Data.Part

/-!
# Variable assignments

A variable assignment gives values to variables. In first-order logic and in Dynamic Predicate
Logic an assignment is total, a Tarskian valuation of every variable; in Heim and Kratzer's
composition rules, in DRT and in partial dynamic logics it is partial, defined on the variables the
discourse has introduced. A plural information state is a set of assignments, total in
Brasoveanu's compositional system and partial in van den Berg's.

## Main definitions

* `Assignment E`: total assignments `ℕ → E`, indexed by numerals.
* `PluralAssign Var D`: sets of partial assignments `Var → Part D`, with `PluralAssign.value` the
  values a variable takes across them and `PluralAssign.restrict` the substate where it takes a
  given value.

## Notation

* `g[n ↦ x]`: `Function.update g n x`, overwriting the value of a total assignment, scoped to
  `Assignment` (`open scoped Assignment`).

## Implementation notes

* A partial assignment is a partial function `Var →. D`, written as the family `Var → Part D` so
  that it carries the pointwise order of partial values. That order is the extension order of
  [van den Berg][van-den-berg-1996] (Definition 4.1, (39)), whose undefined value is `⊥`; the
  domain is `PFun.Dom`, and one assignment extends another iff they agree on its domain
  (`PFun.le_iff_eqOn_dom`).
* The assignments of [Heim and Kratzer][heim-kratzer-1998] are `ℕ → Part D`, and their modified
  assignment ((13)) is `Function.update g n (Part.some d)`, whose domain gains `n`
  (`PFun.dom_update_some`). `Assignment E` and `g[n ↦ x]` are the total, overwriting
  counterparts.
* Equality and the order of partial assignments are decidable where their domains are
  (`Linglib/Core/Data/Part.lean`). A system whose states are `Finset`s of assignments needs
  `DecidableEq` on the assignments themselves and takes `Var → Option D`.
* Random assignment `[x]`, relating assignments that agree off `x`, is
  `DynamicSemantics.Update.randomAssign` at the function-type register structure; it is not
  redefined here.
* Use these names only for the variable-binding role — the state that quantifiers `update` and
  free variables look up. A `ℕ → E` that is not variable-binding state (interpretation tables,
  lookup arrays) should stay a plain function type.

## References

* [groenendijk-stokhof-1991]
* [heim-kratzer-1998]
* [henkin-monk-tarski-1971]
* [van-den-berg-1996]
* [brasoveanu-2008]
* [haug-dalrymple-2020]
* [spector-2026]
-/

@[expose] public section

/-! ### Total assignments -/

/-- `Assignment E` is the type of total variable assignments, sending each index in `ℕ` to a value
in `E`: an entity for entity pronouns, a situation index for situation pronouns, a time for
temporal variables. Heim and Kratzer index by numerals too, but their assignments are partial,
`ℕ → Part E`. -/
abbrev Assignment (E : Type*) := ℕ → E

namespace Assignment

/-- `g[n ↦ x]` is the assignment sending `n` to `x` and agreeing with `g` elsewhere, overwriting
any value `g` gave `n`. It is notation for `Function.update g n x`. -/
scoped notation:max g "[" n " ↦ " x "]" => Function.update g n x

end Assignment

/-! ### Plural assignments -/

/-- `PluralAssign Var D` is the type of plural assignments, sets of partial assignments: the plural
information states of [van den Berg][van-den-berg-1996] and the plural assignments of
[Spector][spector-2026]. [Brasoveanu][brasoveanu-2008]'s plural information states are sets of total
assignments ([Haug and Dalrymple][haug-dalrymple-2020] note the difference). -/
abbrev PluralAssign (Var D : Type*) := Set (Var → Part D)

namespace PluralAssign

variable {Var D : Type*} {G H : PluralAssign Var D} {g : Var → Part D} {x : Var} {a d : D}

/-! #### Values -/

/-- `G.value x` is the set of values `x` takes in `G`; assignments leaving `x` unvalued
contribute none. -/
def value (G : PluralAssign Var D) (x : Var) : Set D :=
  {d | ∃ g ∈ G, d ∈ g x}

@[simp] theorem mem_value : d ∈ G.value x ↔ ∃ g ∈ G, d ∈ g x :=
  Iff.rfl

theorem value_mono (h : G ⊆ H) : G.value x ⊆ H.value x :=
  fun _ ⟨g, hg, hd⟩ ↦ ⟨g, h hg, hd⟩

@[simp] theorem value_empty : (∅ : PluralAssign Var D).value x = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hg, _⟩ ↦ hg

@[simp] theorem value_singleton : ({g} : PluralAssign Var D).value x = {d : D | d ∈ g x} := by
  ext
  simp

@[simp] theorem value_union : (G ∪ H).value x = G.value x ∪ H.value x := by
  ext
  simp [or_and_right, exists_or]

/-! #### Restriction -/

/-- `G.restrict x a` is the substate of `G` whose assignments send `x` to `a`, written $G_{x=a}$ by
[Spector][spector-2026] (§6.2). -/
def restrict (G : PluralAssign Var D) (x : Var) (a : D) : PluralAssign Var D :=
  {g ∈ G | a ∈ g x}

@[simp] theorem mem_restrict : g ∈ G.restrict x a ↔ g ∈ G ∧ a ∈ g x :=
  Iff.rfl

theorem value_restrict_subset : (G.restrict x a).value x ⊆ {a} :=
  fun _ ⟨_, hg, hd⟩ ↦ Part.mem_unique hd hg.2

theorem value_restrict (h : (G.restrict x a).Nonempty) : (G.restrict x a).value x = {a} :=
  let ⟨g, hg⟩ := h
  (Set.Nonempty.subset_singleton_iff (s := (G.restrict x a).value x) ⟨a, g, hg, hg.2⟩).1
    value_restrict_subset

/-! #### Single values -/

/-- `x` has the single value `d` in `G` exactly when some assignment in `G` sends `x` to `d` and
every value `x` takes in `G` is `d`. [Spector][spector-2026]'s `atomic(x)` (§6.3) holds when the
values of `x` are a single atom. -/
theorem value_eq_singleton_iff :
    G.value x = {d} ↔ (∃ g ∈ G, d ∈ g x) ∧ ∀ g ∈ G, ∀ a ∈ g x, a = d :=
  Set.eq_singleton_iff_unique_mem.trans <| and_congr_right fun _ ↦
    ⟨fun h g hg a ha ↦ h a ⟨g, hg, ha⟩, fun h _ ⟨g, hg, ha⟩ ↦ h g hg _ ha⟩

theorem eq_of_mem_restrict (h : G.value x = {d}) (hg : g ∈ G.restrict x a) : a = d :=
  h.subset ⟨g, hg.1, hg.2⟩

@[simp] theorem value_singleton_eq_singleton_iff :
    ({g} : PluralAssign Var D).value x = {d} ↔ d ∈ g x := by
  rw [value_singleton, Set.eq_singleton_iff_unique_mem]
  exact ⟨And.left, fun h ↦ ⟨h, fun _ hd' ↦ Part.mem_unique hd' h⟩⟩

/-- The restriction of `G` to `x = a` gives `x` the single value `d` exactly when it is nonempty
and `d = a`. -/
theorem value_restrict_eq_singleton_iff :
    (G.restrict x a).value x = {d} ↔ (G.restrict x a).Nonempty ∧ d = a := by
  refine ⟨fun h ↦ ?_, fun ⟨hne, hd⟩ ↦ hd.symm ▸ value_restrict hne⟩
  have hd : d ∈ (G.restrict x a).value x := h ▸ rfl
  exact ⟨let ⟨g, hg, _⟩ := hd; ⟨g, hg⟩, value_restrict_subset hd⟩

end PluralAssign
