module

public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Heyting.Basic
public import Linglib.Logic.Consequence

/-!
# Domain semantics

Domain semantics evaluates a sentence at an index, an information state paired with a world; the
state is the set of worlds over which epistemic modals quantify. *Might $\varphi$* is true when
$\varphi$ holds at some world of the state and *must $\varphi$* when it holds at every one,
whatever the world of evaluation. A state accepts a sentence when the sentence is true, relative
to the state, at each of its worlds: [*must $\varphi$* is accepted exactly where $\varphi$
is](##Sentence.acceptedIn_must_iff), and *might $\varphi$* [by the states with a world verifying
$\varphi$ and by the absurd state](##Sentence.acceptedIn_might_iff).

The language has three consequence relations, one for each notion of satisfaction:
[standard](##StandardConsequence) consequence preserves truth at every index,
[diagonal](##DiagonalConsequence) consequence truth at the indices whose world lies in their
state, and [informational](##InformationalConsequence) consequence acceptance. Standard
consequence [is diagonal](##StandardConsequence.diagonalConsequence).

## Implementation notes

The context of an index is fixed, so a sentence is a function of the information state and the
world. Each consequence relation is `Consequence.Entails` for its own models.

## References

* [yalcin-2007]
-/

@[expose] public section

namespace DomainSemantics

open Consequence

variable {W : Type*}

/-- A sentence, its context fixed, is true or false at an information state and a world. -/
abbrev Sentence (W : Type*) := Set W → W → Prop

namespace Sentence

variable (φ : Sentence W) {p s : Set W}

/-- A nonepistemic sentence places a condition on the world alone. -/
def ofProp (p : Set W) : Sentence W := fun _ w ↦ w ∈ p

/-- *might φ* is true when `φ` holds at some world of the state. -/
def might : Sentence W := fun s _ ↦ ∃ w' ∈ s, φ s w'

/-- *must φ* is true when `φ` holds at every world of the state. -/
def must : Sentence W := fun s _ ↦ ∀ w' ∈ s, φ s w'

/-- A state accepts a sentence when the sentence is true, relative to the state, at each of its
worlds. -/
def AcceptedIn (s : Set W) : Prop := ∀ w ∈ s, φ s w

@[simp] theorem ofProp_empty : ofProp (∅ : Set W) = ⊥ := rfl

theorem might_might : φ.might.might = φ.might := by
  ext s w
  exact ⟨fun ⟨_, _, h⟩ ↦ h, fun ⟨w', hw', h⟩ ↦ ⟨w', hw', w', hw', h⟩⟩

theorem must_eq_compl_might_compl : φ.must = φᶜ.mightᶜ := by
  ext s w; simp [must, might]

@[simp] theorem acceptedIn_empty : φ.AcceptedIn ∅ := fun _ h ↦ h.elim

theorem acceptedIn_ofProp_iff : (ofProp p).AcceptedIn s ↔ s ⊆ p := .rfl

theorem acceptedIn_must_iff : φ.must.AcceptedIn s ↔ φ.AcceptedIn s :=
  ⟨fun h w hw ↦ h w hw w hw, fun h _ _ ↦ h⟩

theorem acceptedIn_might_iff : φ.might.AcceptedIn s ↔ s = ∅ ∨ ∃ w ∈ s, φ s w := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
  · simp
  · exact ⟨fun h ↦ .inr (h w hw), fun h _ _ ↦ h.resolve_left (Set.nonempty_iff_ne_empty.1 ⟨w, hw⟩)⟩

end Sentence

/-- An index pairs an information state with a world of evaluation. -/
structure Index (W : Type*) where
  /-- The information state, over which epistemic modals quantify. -/
  state : Set W
  /-- The world of evaluation. -/
  world : W

namespace Index

/-- An index satisfies a sentence when the sentence is true at its world relative to its
state. -/
def Satisfies (i : Index W) (φ : Sentence W) : Prop := φ i.state i.world

/-- An index is diagonal when its world lies in its information state. -/
def IsDiagonal (i : Index W) : Prop := i.world ∈ i.state

end Index

/-- Standard consequence preserves truth at every index. -/
def StandardConsequence (Γ : Set (Sentence W)) (φ : Sentence W) : Prop :=
  Γ ⊨[Index.Satisfies] φ

/-- Diagonal consequence preserves truth at the diagonal indices. -/
def DiagonalConsequence (Γ : Set (Sentence W)) (φ : Sentence W) : Prop :=
  Γ ⊨[fun i : {i : Index W // i.IsDiagonal} ↦ i.val.Satisfies] φ

/-- Informational consequence preserves acceptance in an information state. -/
def InformationalConsequence (Γ : Set (Sentence W)) (φ : Sentence W) : Prop :=
  Γ ⊨[fun s (ψ : Sentence W) ↦ ψ.AcceptedIn s] φ

variable {Γ : Set (Sentence W)} {φ ψ : Sentence W}

theorem standardConsequence_iff :
    StandardConsequence Γ φ ↔ ∀ s w, (∀ γ ∈ Γ, γ s w) → φ s w :=
  ⟨fun h s w ↦ h ⟨s, w⟩, fun h i ↦ h i.state i.world⟩

theorem diagonalConsequence_iff :
    DiagonalConsequence Γ φ ↔ ∀ s, ∀ w ∈ s, (∀ γ ∈ Γ, γ s w) → φ s w :=
  ⟨fun h s w hw ↦ h ⟨⟨s, w⟩, hw⟩, fun h i ↦ h i.val.state i.val.world i.property⟩

theorem informationalConsequence_iff :
    InformationalConsequence Γ φ ↔ ∀ s, (∀ γ ∈ Γ, γ.AcceptedIn s) → φ.AcceptedIn s :=
  .rfl

/-- The diagonal indices are among the indices, so standard consequence is diagonal. -/
theorem StandardConsequence.diagonalConsequence (h : StandardConsequence Γ φ) :
    DiagonalConsequence Γ φ :=
  h.comap Subtype.val fun _ _ ↦ .rfl

theorem informationalConsequence_singleton_iff :
    InformationalConsequence {φ} ψ ↔ ∀ s, φ.AcceptedIn s → ψ.AcceptedIn s := by
  simp [InformationalConsequence, Entails]

end DomainSemantics
