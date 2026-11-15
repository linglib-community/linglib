module

public import Linglib.Semantics.Modification.Classification

/-!
# Noun coercion licensed by non-vacuity

[kamp-partee-1995]'s non-vacuity principle asks that a predicate have both a positive and a
negative extension in its local domain, and their head primacy principle makes the extension of
the head noun the local domain of its modifier. In order terms a predicate is non-vacuous within
a domain when the domain neither excludes it nor lies within it, so the two ways of being vacuous
are those of the modifier classes: a privative adjective is
[excluded by its head](##Modifier.IsPrivative.not_isNonVacuous), and a tautologous one such as
*real* [contains it](##not_isNonVacuous_self). [partee-2010]'s proposal is that the head is then
shifted, as a last resort, to include the adjective's value, *fur* to real or fake fur, and a
privative adjective [shifts its head](##Modifier.IsPrivative.shiftsHead_iff) exactly when there
are things in its value and things in the noun.

## Implementation notes

Head primacy is taken in its simplest form, which makes the local domain the positive extension of
the head. `IsNonVacuous` is bivalent, where [kamp-partee-1995] work with partial predicates.
Complement coercion (`Studies/Pustejovsky1995.lean`) and the type shifts of noun phrases
(`Semantics/Quantification/Individual.lean`) are different notions.

## References

* [kamp-partee-1995]
* [partee-2010]
-/

@[expose] public section

section Order

variable {α : Type*} [PartialOrder α] [OrderBot α] {p d d' : α}

/-- `p` is non-vacuous within `d` when `d` neither excludes `p` nor lies within it; on predicates,
both the positive and the negative extension of `p` meet `d`. -/
def IsNonVacuous (p d : α) : Prop :=
  ¬ Disjoint p d ∧ ¬ d ≤ p

theorem IsNonVacuous.mono (h : IsNonVacuous p d) (hdd' : d ≤ d') : IsNonVacuous p d' :=
  ⟨fun h' ↦ h.1 (h'.mono_right hdd'), fun h' ↦ h.2 (hdd'.trans h')⟩

/-- Nothing is non-vacuous within itself, so a tautologous modifier such as *real*, whose value is
the noun, is vacuous within its head. -/
theorem not_isNonVacuous_self (p : α) : ¬ IsNonVacuous p p :=
  fun h ↦ h.2 le_rfl

end Order

variable {W E : Type*}

/-- A predicate is non-vacuous within a domain when something in the domain satisfies it and
something in the domain does not. -/
theorem isNonVacuous_iff_exists {p d : E → Prop} :
    IsNonVacuous p d ↔ (∃ x, d x ∧ p x) ∧ ∃ x, d x ∧ ¬ p x := by
  simp [IsNonVacuous, Pi.disjoint_iff, Pi.le_def, and_comm]

theorem isNonVacuous_sup_self_iff {p d : E → Prop} :
    IsNonVacuous p (d ⊔ p) ↔ (∃ x, p x) ∧ ∃ x, d x ∧ ¬ p x := by
  rw [isNonVacuous_iff_exists]
  exact ⟨fun ⟨⟨x, _, hx⟩, ⟨y, hy, hny⟩⟩ ↦ ⟨⟨x, hx⟩, y, hy.resolve_right hny, hny⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy, hny⟩⟩ ↦ ⟨⟨x, Or.inr hx, hx⟩, ⟨y, Or.inl hy, hny⟩⟩⟩

namespace Modifier

/-- A privative modifier is never non-vacuous within the extension of its noun, the local domain
that head primacy assigns. -/
theorem IsPrivative.not_isNonVacuous {adj : Modifier (W → E → Prop)} (hp : IsPrivative adj)
    (N : W → E → Prop) (w : W) : ¬ IsNonVacuous (adj N w) (N w) :=
  fun h ↦ h.1 (Pi.disjoint_iff.1 (hp N) w)

/-- `adj` shifts the head `N` at `w` when `adj N` is vacuous within `N`, the local domain that head
primacy assigns, and non-vacuous within `N` widened to include the adjective's value. -/
def ShiftsHead (adj : Modifier (W → E → Prop)) (N : W → E → Prop) (w : W) : Prop :=
  ¬ IsNonVacuous (adj N w) (N w) ∧ IsNonVacuous (adj N w) (N w ⊔ adj N w)

variable {adj : Modifier (W → E → Prop)} {N : W → E → Prop} {w : W}

/-- A compound already non-vacuous within its head does not shift the head. -/
theorem not_shiftsHead_of_isNonVacuous (h : IsNonVacuous (adj N w) (N w)) :
    ¬ ShiftsHead adj N w :=
  fun h' ↦ h'.1 h

/-- A privative adjective shifts its head exactly when there are things in its value and things
in the noun, so *fake fur* widens *fur* just when there are fake furs and real furs. -/
theorem IsPrivative.shiftsHead_iff (hp : IsPrivative adj) :
    ShiftsHead adj N w ↔ (∃ x, adj N w x) ∧ ∃ x, N w x := by
  rw [ShiftsHead, isNonVacuous_sup_self_iff, and_iff_right (hp.not_isNonVacuous N w)]
  exact and_congr_right fun _ ↦ exists_congr fun x ↦
    ⟨And.left, fun h ↦ ⟨h, fun h' ↦ isPrivative_iff_forall.1 hp N w x h' h⟩⟩

end Modifier
