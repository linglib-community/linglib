module

public import Linglib.Core.Combinatorics.SetFamily.Selection
public import Linglib.Semantics.Exhaustification.InnocentInclusion

/-!
# Innocence as naturality

Fox motivates innocent exclusion by arbitrariness: each maximal consistent exclusion could be
carried out on its own, so excluding an alternative outside one of them would choose arbitrarily
among them, and only the alternatives in all of them are excluded non-arbitrarily. Bar-Lev and Fox
define innocent inclusion the same way from the maximal consistent inclusions. Reading
non-arbitrary as natural, both are theorems: over finitely many alternatives, the innocently
excludable alternatives are the greatest set a natural consistent rule selects from the maximal
consistent exclusions, and the innocently includable ones the greatest it selects from the
maximal consistent inclusions.

## Main statements

* `Exhaustification.isGreatest_setOf_isInnocentlyExcludable`
* `Exhaustification.isGreatest_II`

## References

* [fox-2007]
* [bar-lev-fox-2020]
-/

@[expose] public section

namespace Exhaustification

open Set

universe u

variable {World : Type u} {ALT : Set (Set World)} {φ : Set World}

/-- **Innocent exclusion is the greatest natural consistent exclusion.** Over finitely many
alternatives and a satisfiable prejacent, the innocently excludable alternatives are the greatest
set a natural consistent rule selects from the maximal consistent exclusions. -/
theorem isGreatest_setOf_isInnocentlyExcludable (hfin : ALT.Finite) (hsat : φ.Nonempty) :
    IsGreatest ((fun F ↦ F _ {X | Maximal (IsConsistentExclusion ALT φ) X}) ''
        {F | IsNaturalSelection F ∧ IsConsistentSelection F})
      {a | IsInnocentlyExcludable ALT φ a} :=
  isGreatest_setOf_forall_maximal hfin (fun _ h ↦ h.1)
    ⟨∅, empty_subset _, by rwa [sUnion_empty, sdiff_empty]⟩

/-- **Innocent inclusion is the greatest natural consistent inclusion.** Over finitely many
alternatives, when innocent exclusion is consistent the innocently includable alternatives are
the greatest set a natural consistent rule selects from the maximal consistent inclusions. -/
theorem isGreatest_II (hfin : ALT.Finite) (hne : (exhIE ALT φ).Nonempty) :
    IsGreatest ((fun F ↦ F _ {R | Maximal (IsConsistentInclusion ALT φ) R}) ''
        {F | IsNaturalSelection F ∧ IsConsistentSelection F})
      (II ALT φ) :=
  isGreatest_setOf_forall_maximal hfin (fun _ h ↦ h.1)
    ⟨∅, empty_subset _, by rwa [sInter_empty, inter_univ]⟩

end Exhaustification
