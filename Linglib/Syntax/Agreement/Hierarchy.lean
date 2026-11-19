module

public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# The Agreement Hierarchy

A controller such as Russian *vrač* 'doctor' denoting a woman, or British English *committee*,
admits two agreements: syntactic agreement follows the feature value the controller is
assigned, semantic agreement its meaning. [corbett-1979] ranges the targets of agreement in
four positions, the attributive modifier, the predicate, the relative pronoun and the personal
pronoun, and claims that the likelihood of semantic agreement never decreases from one to the
next. A record of that likelihood at some of the positions [respects the
hierarchy](##Agreement.RespectsHierarchy) when it is monotone where it is recorded, and then
semantic agreement possible at a position [is possible at every later
one](##Agreement.RespectsHierarchy.allows_semantic), as syntactic agreement [is at every
earlier one](##Agreement.RespectsHierarchy.allows_syntactic).

## Implementation notes

* The attributive is the least position, the order in which [corbett-1991] prints the
  hierarchy; [corbett-2006] prints the same ranking with `>`, for decreasing canonicity. With
  the attributive least, the claim of the hierarchy is monotonicity.
* `RespectsHierarchy` takes any preorder of positions and any preorder of values, so that it
  serves the four positions, a hierarchy within the predicate, a finer division of the
  attributive and a product of a hierarchy with the stages of a change alike, and corpus
  proportions of semantic agreement as well as availabilities. A position carrying no value,
  because agreement does not apply there or there are no data, is skipped: values are compared
  only across comparable positions that both carry one. A record with a value everywhere
  respects the hierarchy exactly when it is `Monotone`.
* `Availability` has the five degrees that [corbett-1991]'s summary of the evidence shades.

## References

* [corbett-1979]
* [corbett-1983]
* [corbett-1991]
* [corbett-2006]
-/

@[expose] public section

namespace Agreement

/-- A position of the Agreement Hierarchy ([corbett-1979]). -/
inductive Position where
  /-- The attributive modifier (French *un bon livre*). -/
  | attributive
  /-- The predicate, a finite verb or a predicate adjective (Russian *kniga interesna*). -/
  | predicate
  /-- The relative pronoun (German *der ~ die ~ das*). -/
  | relativePronoun
  /-- The personal pronoun (English *he ~ she ~ it*). -/
  | personalPronoun
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- The Agreement Hierarchy as a chain:
`attributive < predicate < relativePronoun < personalPronoun`. -/
instance : LinearOrder Position := LinearOrder.lift' Position.ctorIdx (by decide)

/-- Whether an agreement form follows the feature value the controller is assigned or the
controller's meaning. -/
inductive Kind where
  | syntactic
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- Syntactic agreement lies below semantic agreement, so that a map to agreements is
monotone when it never trades semantic agreement for syntactic. -/
instance : LinearOrder Kind := LinearOrder.lift' Kind.ctorIdx (by decide)

/-- The availability of semantic agreement at a position of a hierarchy, in the five degrees
of [corbett-1991]'s summary of hybrid nouns, ordered by the likelihood of semantic
agreement. -/
inductive Availability where
  | syntacticOnly
  | mostlySyntactic
  | both
  | mostlySemantic
  | semanticOnly
  deriving DecidableEq, Repr, Fintype

namespace Availability

/-- Availabilities are ordered by the likelihood of semantic agreement. -/
instance : LinearOrder Availability := LinearOrder.lift' Availability.ctorIdx (by decide)

/-- Which agreement an availability admits: each, unless only the other is found. -/
def Allows (a : Availability) : Kind → Prop
  | .syntactic => a ≠ .semanticOnly
  | .semantic => a ≠ .syntacticOnly

instance (a : Availability) : DecidablePred a.Allows
  | .syntactic => inferInstanceAs (Decidable (a ≠ .semanticOnly))
  | .semantic => inferInstanceAs (Decidable (a ≠ .syntacticOnly))

theorem monotone_allows_semantic : Monotone (Allows · .semantic) :=
  (by decide : ∀ a b : Availability, a ≤ b → a.Allows .semantic → b.Allows .semantic)

theorem antitone_allows_syntactic : Antitone (Allows · .syntactic) :=
  (by decide : ∀ a b : Availability, a ≤ b → b.Allows .syntactic → a.Allows .syntactic)

end Availability

section RespectsHierarchy

variable {ι κ α : Type*} [Preorder ι] [Preorder κ] [Preorder α] {f : ι → Option α}

/-- A map recording a value at some positions of a hierarchy respects it when the value
never decreases along the hierarchy: of two comparable positions that both carry a value, the
later carries the larger. -/
def RespectsHierarchy (f : ι → Option α) : Prop :=
  ∀ ⦃i j⦄, i ≤ j → ∀ a ∈ f i, ∀ b ∈ f j, a ≤ b

instance [h : Decidable (∀ i j, i ≤ j → ∀ a ∈ f i, ∀ b ∈ f j, a ≤ b)] :
    Decidable (RespectsHierarchy f) := h

@[simp]
theorem respectsHierarchy_some_comp {g : ι → α} :
    RespectsHierarchy (some ∘ g) ↔ Monotone g := by
  simp [RespectsHierarchy, Monotone]

/-- A map respecting a hierarchy respects it along any monotone map into it. -/
theorem RespectsHierarchy.comp_monotone (hf : RespectsHierarchy f) {g : κ → ι}
    (hg : Monotone g) : RespectsHierarchy (f ∘ g) :=
  fun _ _ h ↦ hf (hg h)

variable {f : ι → Option Availability} {i j : ι} {a b : Availability}

/-- Under the hierarchy, semantic agreement possible at a position is possible at every later
position ([corbett-1979]). -/
theorem RespectsHierarchy.allows_semantic (hf : RespectsHierarchy f) (h : i ≤ j) (ha : a ∈ f i)
    (hb : b ∈ f j) : a.Allows .semantic → b.Allows .semantic :=
  Availability.monotone_allows_semantic (hf h a ha b hb)

/-- Under the hierarchy, syntactic agreement possible at a position is possible at every
earlier position ([corbett-1979]). -/
theorem RespectsHierarchy.allows_syntactic (hf : RespectsHierarchy f) (h : i ≤ j) (ha : a ∈ f i)
    (hb : b ∈ f j) : b.Allows .syntactic → a.Allows .syntactic :=
  Availability.antitone_allows_syntactic (hf h a ha b hb)

end RespectsHierarchy

end Agreement
