module

public import Linglib.Semantics.Modification.Intensional

/-!
# Non-vacuity and the shift of a head noun

This file defines non-vacuity and the shift of a head noun by its modifier.

A predicate is non-vacuous within a domain if the domain neither excludes it nor lies within it.
A modifier shifts its head noun if its value is vacuous within the noun and non-vacuous within
the noun widened by that value.

A privative modifier is [vacuous within its noun](##Modifier.IsPrivative.not_isNonVacuous), and
[so is the identity](##not_isNonVacuous_self). A privative modifier
[shifts its noun](##Modifier.IsPrivative.shiftsHead_iff) exactly when something is in its value
and something is in the noun.

## Implementation notes

Non-vacuity and the choice of the noun as domain are Kamp and Partee's principles, and the shift
is Partee's. `IsNonVacuous` is bivalent, where their predicates are partial.

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
