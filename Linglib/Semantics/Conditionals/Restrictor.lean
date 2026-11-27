module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Conditionals.Basic

/-!
# The restrictor theory of conditionals

On the restrictor analysis of Lewis and Kratzer an *if*-clause is not a connective but restricts
the modal base of a possibly covert modal: *if α, must β* says that `β` is a necessity over
the modal base restricted by `α`, `β ∈ (f.restrict α).necessity g w`, and *if α, might β*
that it is a possibility there. So read, [the restrictor conditional is Lewis's variably
strict conditional](##Conditional.Restrictor.variablyStrictImp_eq_setOf_mem_necessity) over
the accessible worlds ranked by the ordering source, its *might* that conditional's *might*. Over
the best worlds it is the conditional of the closest antecedent-worlds, and with an empty ordering
source the strict conditional.

## References

* [lewis-1975]
* [kratzer-1981]
* [lewis-1981]
* [kratzer-1986]
* [kratzer-2012]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Conditional.Restrictor

open Modality

variable {W : Type*} (f g : Background W) (α β : Set W)

/-- *If α, must β* is the variably strict conditional over the accessible worlds, under the
preorders the ordering source induces. -/
theorem variablyStrictImp_eq_setOf_mem_necessity :
    variablyStrictImp f.accessibleWorlds (fun w ↦ ≤[g w]) α β =
      {w | β ∈ (f.restrict α).necessity g w} :=
  Set.ext fun w ↦ by
    rw [mem_variablyStrictImp, Set.mem_ofPred_eq, Background.necessity,
      Background.accessibleWorlds_restrict]

/-- *If α, might β* is the *might* of the variably strict conditional. -/
theorem might_variablyStrictImp_eq_setOf_possibility :
    might (variablyStrictImp f.accessibleWorlds (fun w ↦ ≤[g w])) α β =
      {w | (f.restrict α).possibility g w β} :=
  Set.ext fun w ↦ by
    rw [mem_might, variablyStrictImp_eq_setOf_mem_necessity, Set.mem_ofPred_eq,
      Set.mem_ofPred_eq, Background.possibility_iff_compl_notMem]

/-- Over the best worlds, *if α, must β* is truth at the best accessible α-worlds. -/
theorem orderingImp_eq_setOf_bestWorlds_subset :
    orderingImp f.accessibleWorlds (fun w ↦ ≤[g w]) α β =
      {w | (f.restrict α).bestWorlds g w ⊆ β} :=
  Set.ext fun w ↦ by
    rw [mem_orderingImp, Set.mem_ofPred_eq, Background.bestWorlds,
      Background.accessibleWorlds_restrict]

/-- With an empty ordering source, *if α, must β* is the strict conditional over the accessible
worlds. -/
theorem strictImp_eq_setOf_mem_simpleNecessity :
    strictImp f.accessibleWorlds α β = {w | β ∈ (f.restrict α).simpleNecessity w} :=
  Set.ext fun w ↦ by
    rw [mem_strictImp, Set.mem_ofPred_eq, Background.mem_simpleNecessity,
      Background.accessibleWorlds_restrict]

end Conditional.Restrictor
