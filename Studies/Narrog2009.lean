module

public import Linglib.Data.Statistics.Narrog2009
public import Linglib.Core.Order.IntervalOrder

/-!
# Narrog (2009): Modality in Japanese

[narrog-2009a] tests eighteen modal markers of Modern Japanese against aspect, negation, tense,
nominalization and illocutionary modulation in a corpus, recording for each marker and category
whether the marker can embed the category, be embedded by it, or both (`Narrog2009.scopes`).

A model of clause structure assigns each marker and each category a stretch of a scale of scope.
We take the stretches to be intervals of a linear order and say that an assignment represents the
data on a set of markers and a set of categories when a marker that only embeds a category lies
wholly above it, one that is only embedded lies wholly below it, and one that does both overlaps
it (`Represents`). A model with layers assigns points.

No assignment of points represents the data, whenever the markers include *hazu* and
*ka mo sirenai*: the first overlaps both internal negation and tense, and the second lies above
the one and overlaps the other (`not_represents_pure`). No assignment of intervals represents
the data with respect to external negation and tense once the markers include the predictive
evidential *-soo* and the desiderative *-tai*, which form with those two categories the
configuration that precedence of intervals excludes (`not_represents`). With nominalization left
aside, the volitive markers have a representation and so do the non-volitive ones
(`exists_represents_isVolitive`, `exists_represents_not_isVolitive`), in which every marker is a
point and only the categories are stretches.

## Implementation notes

A cell that the table marks as holding only in a resultative reading or only in the
counterfactual past is taken at face value, and a cell of no interaction constrains nothing. The
scope of one modal marker over another, which the study tabulates separately and summarizes in
the table's column of layers, and the layers of the markers in non-matrix clauses are not used.

## References

* [narrog-2009a]
-/

@[expose] public section

namespace Narrog2009

open NonemptyInterval

variable {β : Type*} [LinearOrder β]

/-- A marker is volitive when it is boulomaic, deontic or a mood. -/
def Marker.IsVolitive (m : Marker) : Prop :=
  (markers m).category = .boulomaic ∨ (markers m).category = .deontic ∨
    (markers m).category = .mood

instance : DecidablePred Marker.IsVolitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- What the scope relation `s` of a marker to a category requires of their intervals `i` and
`j`: the marker's lies above when it only embeds, below when it is only embedded, and overlaps
when both hold. -/
def Scope.Holds : Scope → NonemptyInterval β → NonemptyInterval β → Prop
  | .embeds, i, j => j.Precedes i
  | .embedded, i, j => i.Precedes j
  | .both, i, j => i.Overlaps j
  | .none, _, _ => True

instance (s : Scope) (i j : NonemptyInterval β) : Decidable (s.Holds i j) := by
  cases s <;> unfold Scope.Holds <;> infer_instance

/-- The intervals `f` of the markers and `g` of the categories represent the scope data on the
markers `S` and the categories `C`. -/
def Represents (S : Set Marker) (C : Set Category) (f : Marker → NonemptyInterval β)
    (g : Category → NonemptyInterval β) : Prop :=
  ∀ m ∈ S, ∀ c ∈ C, (scopes m c).scope.Holds (f m) (g c)

theorem Represents.mono {S S' : Set Marker} {C C' : Set Category}
    {f : Marker → NonemptyInterval β} {g : Category → NonemptyInterval β}
    (h : Represents S C f g) (hS : S' ⊆ S) (hC : C' ⊆ C) : Represents S' C' f g :=
  fun m hm c hc ↦ h m (hS hm) c (hC hc)

private theorem not_overlaps_of_precedes {i j : NonemptyInterval β} (h : i.Precedes j) :
    ¬ i.Overlaps j := fun ho ↦ not_lt_of_ge ho.2 h

/-- No assignment of points to the markers and the categories represents the data on markers
that include *hazu* and *ka mo sirenai*. -/
theorem not_represents_pure {S : Set Marker} {C : Set Category} (hh : .hazu ∈ S)
    (hk : .kaMoSirenai ∈ S) (hn : .internalNegation ∈ C) (ht : .tense ∈ C) (ℓ : Marker → β)
    (ℓ' : Category → β) : ¬ Represents S C (fun m ↦ pure (ℓ m)) fun c ↦ pure (ℓ' c) := by
  intro h
  have h₁ : (pure (ℓ .hazu)).Overlaps (pure (ℓ' .internalNegation)) := h _ hh _ hn
  have h₂ : (pure (ℓ .hazu)).Overlaps (pure (ℓ' .tense)) := h _ hh _ ht
  have h₃ : (pure (ℓ' .internalNegation)).Precedes (pure (ℓ .kaMoSirenai)) := h _ hk _ hn
  have h₄ : (pure (ℓ .kaMoSirenai)).Overlaps (pure (ℓ' .tense)) := h _ hk _ ht
  exact not_lt_of_ge (h₄.1.trans (h₂.2.trans h₁.1)) h₃

/-- No assignment of intervals represents the data with respect to external negation and tense
on markers that include the predictive evidential *-soo* and the desiderative *-tai*. -/
theorem not_represents {S : Set Marker} {C : Set Category} (hs : .soo1 ∈ S) (ht : .tai ∈ S)
    (hn : .externalNegation ∈ C) (hT : .tense ∈ C) (f : Marker → NonemptyInterval β)
    (g : Category → NonemptyInterval β) : ¬ Represents S C f g := by
  intro h
  have h₁ : (f .tai).Precedes (g .externalNegation) := h _ ht _ hn
  have h₂ : (f .soo1).Precedes (g .tense) := h _ hs _ hT
  have h₃ : (f .tai).Overlaps (g .tense) := h _ ht _ hT
  have h₄ : (f .soo1).Overlaps (g .externalNegation) := h _ hs _ hn
  rcases IsIntervalOrder.two_plus_two h₁ h₂ with h' | h'
  exacts [not_overlaps_of_precedes h' h₃, not_overlaps_of_precedes h' h₄]

/-- The interval from `a` to `a + n`. -/
private def range (a n : ℕ) : NonemptyInterval ℕ := ⟨(a, a + n), Nat.le_add_right a n⟩

/-- Nominalization aside, the volitive markers have a representation by points. -/
theorem exists_represents_isVolitive :
    ∃ (p : Marker → ℕ) (g : Category → NonemptyInterval ℕ),
      Represents {m | m.IsVolitive} {c | c ≠ .nominalization} (fun m ↦ pure (p m)) g := by
  refine ⟨fun m ↦ match m with
      | .tai | .teHosii => 1 | .nakerebaNaranai => 2 | .rebaIi | .beki => 3 | _ => 4,
    fun c ↦ match c with
      | .stativeAspect | .completiveAspect => range 1 1
      | .internalNegation | .tense => range 1 2
      | .externalNegation => range 4 0
      | _ => range 5 0, ?_⟩
  intro m hm c hc
  revert hm hc; cases m <;> cases c <;> decide

/-- Nominalization aside, the non-volitive markers have a representation by points. -/
theorem exists_represents_not_isVolitive :
    ∃ (p : Marker → ℕ) (g : Category → NonemptyInterval ℕ),
      Represents {m | ¬ m.IsVolitive} {c | c ≠ .nominalization} (fun m ↦ pure (p m)) g := by
  refine ⟨fun m ↦ match m with
      | .eru | .rareru | .kotoGaDekiru => 1 | .soo1 => 2 | .hazu | .yoo | .rasii => 3
      | .kaMoSirenai => 4 | .soo2 => 5 | _ => 6,
    fun c ↦ match c with
      | .stativeAspect | .completiveAspect => range 1 1
      | .internalNegation => range 1 2
      | .externalNegation => range 2 2
      | .tense => range 3 2
      | _ => range 7 0, ?_⟩
  intro m hm c hc
  revert hm hc; cases m <;> cases c <;> decide

end Narrog2009
