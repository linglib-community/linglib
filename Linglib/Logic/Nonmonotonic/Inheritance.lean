module

public import Linglib.Core.Data.Fintype.Order
public import Linglib.Logic.Nonmonotonic.Preferential
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Default inheritance

This file defines default inheritance in a taxonomy: a node takes the value of an attribute
from the most specific nodes above it that specify one, so a value specified lower down
overrides one specified higher up. The taxonomy is a partial order in which `a ≤ m` reads "`a`
isA `m`", and an attribute is a partial map `att : α → Option β`, the values nodes specify
themselves. Default inheritance organizes the lexicon of Word Grammar [hudson-2010] and of the
defaults-based morphology of DATR [evans-gazdar-1996] and Network Morphology
[brown-hippisley-2012], and the hierarchical lexicon of Construction Morphology.

The specifiers of a node are the nodes above it with a value of their own, and the node inherits
the values of its minimal specifiers. This is the Specificity Principle: a value specified at a
more specific node overrides one specified at a less specific node. The definition depends on the
order alone. Two incomparable specifiers with different values, as in the Nixon diamond, leave a
node with both values. Each is a credulous conclusion, and a skeptical reasoner draws neither. A
value is a skeptical conclusion when it is the only value inherited, which on a well-founded
taxonomy is preferential consequence (`mem_necessityFilter_iff_inherited_subset`). A node
inherits at most one value when the specifiers above it form a chain, as in a single-parent
hierarchy, or when no node lies below two specifiers, as with the members of a choice set. The
procedural account climbs the taxonomy from the node and takes the first value found. It agrees
with the definition for every order of the climb that never visits a node before a node below it,
such as the order of ascending degree by which inheritance networks build their extensions.

## Main definitions

* `DefaultInheritance.specifiers`: the nodes above a node that specify the attribute.
* `DefaultInheritance.inherited`: the values of a node's minimal specifiers.

## Main results

* `DefaultInheritance.inherited_eq_singleton_of_eq_some`: a node's own value is the only one it
  inherits.
* `DefaultInheritance.inherited_eq_singleton_of_isLeast`: the value of a least specifier is the
  only one inherited.
* `DefaultInheritance.subsingleton_inherited_of_isChain`,
  `DefaultInheritance.subsingleton_inherited_of_pairwiseDisjoint`: specifiers in a chain, or
  with pairwise disjoint lower sets, leave no conflict.
* `DefaultInheritance.mem_inherited_of_find?_eq_some`,
  `DefaultInheritance.find?_bind_eq_of_inherited_eq_singleton`: a bottom-up search returns an
  inherited value, the only one when there is no conflict.
* `DefaultInheritance.mem_necessityFilter_iff_inherited_subset`: skeptical inheritance as
  preferential consequence.

## Implementation notes

The isA links are strict and only the link from a node to its value is defeasible, so the
specificity is the strong kind, and every path has a single defeasible link. The problems of
longer defeasible paths, floating conclusions and zombie arguments, do not arise. Two values
compete when they are values of one attribute. [hudson-2010] also lets links compete when one
link isA the other, and relations compete when they belong to one choice set. Neither kind of
competition is modelled here. The taxonomy is a partial order rather than a preorder because isA
is acyclic. The node types of the consumers are finite, and `partialOrderOfCovers` builds their
orders from immediate isA edges.

## References

* [strasser-antonelli-2024]
* [hudson-2010]
* [evans-gazdar-1996]
* [brown-hippisley-2012]
-/

@[expose] public section

namespace DefaultInheritance

variable {α β : Type*} [PartialOrder α] {att : α → Option β} {a m : α} {v w : β}

variable (att) in
/-- The specifiers of `a`: the nodes above `a` with a value of their own. -/
def specifiers (a : α) : Set α := {m | a ≤ m ∧ (att m).isSome}

variable (att) in
/-- The values `a` inherits: those of its most specific specifiers, the credulous conclusions. -/
def inherited (a : α) : Set β := {v | ∃ m, Minimal (· ∈ specifiers att a) m ∧ att m = some v}

theorem mem_specifiers : m ∈ specifiers att a ↔ a ≤ m ∧ (att m).isSome := Iff.rfl

theorem mem_inherited :
    v ∈ inherited att a ↔ ∃ m, Minimal (· ∈ specifiers att a) m ∧ att m = some v := Iff.rfl

instance [DecidableLE α] : DecidablePred (· ∈ specifiers att a) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance [Fintype α] [DecidableLE α] [DecidableEq β] : DecidablePred (· ∈ inherited att a) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

theorem exists_le_of_mem_inherited (h : v ∈ inherited att a) : ∃ m, a ≤ m ∧ att m = some v :=
  let ⟨m, hm, hv⟩ := h
  ⟨m, hm.prop.1, hv⟩

/-- The value of a least specifier is the only value inherited. -/
theorem inherited_eq_singleton_of_isLeast (h : IsLeast (specifiers att a) m)
    (hm : att m = some v) : inherited att a = {v} := by
  ext w
  refine ⟨fun ⟨m', hm', hw⟩ ↦ ?_, fun hw ↦ ⟨m, h.minimal, hm.trans (congrArg _ hw.symm)⟩⟩
  rw [h.minimal_iff.1 hm', hm, Option.some_inj] at hw
  exact hw.symm

/-- A node's own value overrides every value above it. -/
theorem inherited_eq_singleton_of_eq_some (h : att a = some v) : inherited att a = {v} :=
  inherited_eq_singleton_of_isLeast ⟨⟨le_rfl, by simp [h]⟩, fun _ hm ↦ hm.1⟩ h

/-- A node inherits at most one value when its specifiers form a chain, as in a single-parent
hierarchy. -/
theorem subsingleton_inherited_of_isChain (h : IsChain (· ≤ ·) (specifiers att a)) :
    (inherited att a).Subsingleton := by
  rintro v ⟨m, hm, hv⟩ w ⟨m', hm', hw⟩
  obtain rfl : m = m' := by
    rcases eq_or_ne m m' with e | e
    · exact e
    rcases h hm.prop hm'.prop e with hle | hle
    · exact hm'.eq_of_le hm.prop hle
    · exact (hm.eq_of_le hm'.prop hle).symm
  exact Option.some_injective _ (hv.symm.trans hw)

/-- No node inherits two values when no node lies below two specifiers, as when the specifiers
are members of one choice set. -/
theorem subsingleton_inherited_of_pairwiseDisjoint
    (h : {m | (att m).isSome}.PairwiseDisjoint Set.Iic) : (inherited att a).Subsingleton := by
  refine subsingleton_inherited_of_isChain fun m hm m' hm' hne ↦ ?_
  exact absurd (h hm.2 hm'.2 hne) (Set.not_disjoint_iff.2 ⟨a, hm.1, hm'.1⟩)

section Search

variable [DecidableLE α] {l : List α}

/-- A search that climbs from `a` through `l` and takes the value of the first specifier it
meets returns an inherited value. The climb may be in any order that never visits a node
before a node below it, and `l` must hold every specifier. -/
theorem mem_inherited_of_find?_eq_some (hl : l.Pairwise fun x y ↦ ¬ y < x)
    (hs : ∀ m ∈ specifiers att a, m ∈ l) (hm : l.find? (· ∈ specifiers att a) = some m)
    (hv : att m = some v) : v ∈ inherited att a := by
  obtain ⟨hma, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.1 hm
  refine ⟨m, ⟨of_decide_eq_true hma, fun y hy hym ↦ ?_⟩, hv⟩
  by_contra hmy
  have hlt : y < m := lt_of_le_not_ge hym hmy
  rcases List.mem_append.1 (hs y hy) with hya | hyb
  · exact absurd (decide_eq_true hy) (by simpa using has y hya)
  · rcases List.mem_cons.1 hyb with rfl | hyb
    · exact lt_irrefl _ hlt
    · exact (List.pairwise_cons.1 (List.pairwise_append.1 hl).2.1).1 y hyb hlt

/-- When a node inherits exactly one value, every bottom-up search returns it. -/
theorem find?_bind_eq_of_inherited_eq_singleton (hl : l.Pairwise fun x y ↦ ¬ y < x)
    (hs : ∀ m ∈ specifiers att a, m ∈ l) (h : inherited att a = {v}) :
    (l.find? (· ∈ specifiers att a)).bind att = some v := by
  obtain ⟨m₀, hm₀, -⟩ : v ∈ inherited att a := h ▸ Set.mem_singleton v
  match hm : l.find? (· ∈ specifiers att a) with
  | none => exact absurd (decide_eq_true hm₀.prop) (List.find?_eq_none.1 hm m₀ (hs m₀ hm₀.prop))
  | some m =>
    obtain ⟨w, hw⟩ :=
      Option.isSome_iff_exists.1 (of_decide_eq_true (List.find?_eq_some_iff_append.1 hm).1).2
    have := mem_inherited_of_find?_eq_some hl hs hm hw
    rw [h, Set.mem_singleton_iff] at this
    simp [hw, this]

end Search

/-- A node inherits no value but `v`, the skeptical conclusion, exactly when its specifiers
preferentially entail specifying `v`: on a well-founded hierarchy, its most specific specifiers all
specify `v`. -/
theorem mem_necessityFilter_iff_inherited_subset [WellFoundedLT α] :
    {m | att m = some v} ∈ OrderingSemantics.necessityFilter inferInstance (specifiers att a) ↔
      inherited att a ⊆ {v} := by
  rw [OrderingSemantics.necessityFilter_eq_principal_of_wellFounded wellFounded_lt,
    Filter.mem_principal]
  refine ⟨fun h w ⟨m, hm, hw⟩ ↦ ?_, fun h m hm ↦ ?_⟩
  · have : att m = some v := h hm
    rw [hw, Option.some_inj] at this
    exact this
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hm.prop.2
    have : w = v := h ⟨m, hm, hw⟩
    exact this ▸ hw

end DefaultInheritance
