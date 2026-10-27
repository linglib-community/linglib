module

public import Mathlib.Data.Set.Insert
public import Mathlib.Order.Heyting.Basic

/-!
# Domain semantics

Domain semantics evaluates a sentence at an index pairing a world with an information state, a
set of worlds over which epistemic modals quantify: *might φ* is true when `φ` holds at some world
of the state and *must φ* when it holds at every one, whatever the world of evaluation. A state
accepts a sentence when the sentence is true, relative to the state, at each of its worlds. A
nonepistemic sentence is accepted by the states that entail it, *must φ* by the states that
accept `φ`, and *might φ* by the states with a world verifying `φ` and by the absurd state.

Consequence preserves truth at every index (standard), truth at the diagonal indices, those whose
world lies in the state (diagonal), or acceptance (informational).

## Main definitions

* `DomainSemantics.Sentence W`: sentences, a Boolean algebra pointwise.
* `Sentence.ofProp`, `Sentence.might`, `Sentence.must`: nonepistemic sentences and the modals.
* `Sentence.AcceptedIn`: acceptance in an information state.
* `StandardConsequence`, `DiagonalConsequence`, `InformationalConsequence`.

## Main statements

* `Sentence.acceptedIn_must_iff`: *must φ* is accepted exactly where `φ` is.
* `Sentence.acceptedIn_might_iff`: *might φ* is accepted by the absurd state and by the states
  with a world verifying `φ`.
* `informationalConsequence_singleton_iff`: informational consequence from one premise is
  inclusion of the accepting states.

## Implementation notes

The context of an index is fixed, so a sentence is a function of the information state and the
world.

## References

* [yalcin-2007]
-/

@[expose] public section

namespace DomainSemantics

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

/-- Standard consequence preserves truth at every index. -/
def StandardConsequence (Γ : List (Sentence W)) (φ : Sentence W) : Prop :=
  ∀ s w, (∀ γ ∈ Γ, γ s w) → φ s w

/-- Diagonal consequence preserves truth at the diagonal indices, those whose world lies in the
information state. -/
def DiagonalConsequence (Γ : List (Sentence W)) (φ : Sentence W) : Prop :=
  ∀ s w, w ∈ s → (∀ γ ∈ Γ, γ s w) → φ s w

/-- Informational consequence preserves acceptance. -/
def InformationalConsequence (Γ : List (Sentence W)) (φ : Sentence W) : Prop :=
  ∀ s, (∀ γ ∈ Γ, γ.AcceptedIn s) → φ.AcceptedIn s

variable {Γ : List (Sentence W)} {φ ψ : Sentence W}

theorem StandardConsequence.diagonalConsequence (h : StandardConsequence Γ φ) :
    DiagonalConsequence Γ φ :=
  fun s w _ hΓ ↦ h s w hΓ

theorem informationalConsequence_singleton_iff :
    InformationalConsequence [φ] ψ ↔ ∀ s, φ.AcceptedIn s → ψ.AcceptedIn s := by
  simp [InformationalConsequence]

end DomainSemantics
