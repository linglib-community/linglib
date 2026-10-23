module

public import Linglib.Semantics.Modification.Classification

/-!
# Noun coercion licensed by non-vacuity

Kamp and Partee's non-vacuity principle asks that a predicate have both a positive and a
negative extension in its local domain, and their head primacy principle makes the extension of
the head noun the local domain of its modifier. A privative adjective is never non-vacuous within
its head, and neither is a tautologous one such as *real*. Partee's proposal is that the head is
then shifted, as a last resort, to include the adjective's value, *fur* to real or fake fur, so
that the compound becomes non-vacuous.

## Main definitions

* `Semantics.Property.IsNonVacuous P w d`: `P` has a positive and a negative extension within `d` at
  `w`.
* `Semantics.Property.ShiftsHead adj N w`: `adj N` is vacuous within `N` and non-vacuous within `N`
  widened by the adjective's value, so Partee's rule shifts the head.

## Main statements

* `Semantics.Property.not_isNonVacuous_of_isPrivative`, `not_isNonVacuous_self`: privative and
  tautologous modifiers are vacuous within their head.
* `Semantics.Property.shiftsHead_iff_of_isPrivative`: a privative adjective shifts its head exactly
  when there are both things in its value and things in the noun.
* `Semantics.Property.not_shiftsHead_of_isNonVacuous`: a compound already non-vacuous within its
  head is not shifted.

## Implementation notes

The principles are Kamp and Partee's (NVP) and (HPP), Partee's (18) and (20), with head primacy
in its simplest form, which makes the local domain the positive extension of the head.
`IsNonVacuous` is bivalent, simplifying the partial setting of Kamp and Partee. Complement
coercion (`Studies/Pustejovsky1995.lean`) and the type shifts of noun phrases
(`Semantics/Quantification/Individual.lean`) are different notions.

## References

* [kamp-partee-1995]
* [partee-2010]
-/

@[expose] public section

namespace Semantics.Property

open Modifier

variable {W E : Type*}

/-- `P` is non-vacuous within `d` at `w` when both its positive and its negative extension at
`w` meet `d`. -/
def IsNonVacuous (P : Property W E) (w : W) (d : E → Prop) : Prop :=
  (∃ x, d x ∧ P w x) ∧ (∃ x, d x ∧ ¬ P w x)

theorem IsNonVacuous.mono {P : Property W E} {w : W} {d d' : E → Prop}
    (h : IsNonVacuous P w d) (hdd' : d ≤ d') : IsNonVacuous P w d' :=
  ⟨h.1.imp fun x hx ↦ ⟨hdd' x hx.1, hx.2⟩, h.2.imp fun x hx ↦ ⟨hdd' x hx.1, hx.2⟩⟩

theorem isNonVacuous_of_disjoint {P Q : Property W E} {w : W} {d : E → Prop} (h : Disjoint P Q)
    (hP : ∃ x, d x ∧ P w x) (hQ : ∃ x, d x ∧ Q w x) : IsNonVacuous P w d :=
  ⟨hP, hQ.imp fun _ hx ↦ ⟨hx.1, fun hPx ↦ h.le_bot w _ ⟨hPx, hx.2⟩⟩⟩

theorem not_isNonVacuous_of_isPrivative {adj : Modifier (Property W E)}
    (hp : Modifier.IsPrivative adj) (N : Property W E) (w : W) :
    ¬ IsNonVacuous (adj N) w (N w) :=
  fun h ↦ h.1.elim fun x hx ↦ isPrivative_iff.1 hp N w x hx.2 hx.1

theorem not_isNonVacuous_self (P : Property W E) (w : W) : ¬ IsNonVacuous P w (P w) :=
  fun h ↦ h.2.elim fun _ hx ↦ hx.2 hx.1

theorem isNonVacuous_sup_self_iff {P : Property W E} {w : W} {d : E → Prop} :
    IsNonVacuous P w (d ⊔ P w) ↔ (∃ x, P w x) ∧ ∃ x, d x ∧ ¬ P w x :=
  ⟨fun ⟨⟨x, _, hx⟩, ⟨y, hy, hny⟩⟩ ↦ ⟨⟨x, hx⟩, y, hy.resolve_right hny, hny⟩,
    fun ⟨⟨x, hx⟩, ⟨y, hy, hny⟩⟩ ↦ ⟨⟨x, Or.inr hx, hx⟩, ⟨y, Or.inl hy, hny⟩⟩⟩

/-- `adj` shifts the head `N` at `w` when `adj N` is vacuous within `N`, the local domain that head
primacy assigns, and non-vacuous within `N` widened to include the adjective's value. -/
def ShiftsHead (adj : Modifier (Property W E)) (N : Property W E) (w : W) : Prop :=
  ¬ IsNonVacuous (adj N) w (N w) ∧ IsNonVacuous (adj N) w (N w ⊔ adj N w)

variable {adj : Modifier (Property W E)} {N : Property W E} {w : W}

theorem not_shiftsHead_of_isNonVacuous (h : IsNonVacuous (adj N) w (N w)) :
    ¬ ShiftsHead adj N w :=
  fun h' ↦ h'.1 h

theorem shiftsHead_iff_of_isPrivative (hp : Modifier.IsPrivative adj) :
    ShiftsHead adj N w ↔ (∃ x, adj N w x) ∧ ∃ x, N w x := by
  rw [ShiftsHead, isNonVacuous_sup_self_iff,
    and_iff_right (not_isNonVacuous_of_isPrivative hp N w)]
  exact and_congr_right fun _ ↦ exists_congr fun x ↦
    ⟨And.left, fun h ↦ ⟨h, fun h' ↦ isPrivative_iff.1 hp N w x h' h⟩⟩

end Semantics.Property
