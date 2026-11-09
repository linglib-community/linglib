module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Conditionals.Basic

/-!
# The restrictor theory of conditionals

On the restrictor analysis of Lewis and Kratzer an *if*-clause is not a connective but restricts
the modal base of a possibly covert modal: *if α, must β* says that `β` is a human necessity over
the modal base restricted by `α`, `β ∈ humanNecessity (f.restrict α) g w`, and *if α, might β*
that it is a human possibility there. So read, [the restrictor conditional is Lewis's variably
strict conditional](##Conditional.Restrictor.variablyStrictImp_eq_setOf_mem_humanNecessity) over
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

namespace Conditional.Restrictor

open Modality

variable {W : Type*} (f g : Background W) (α β : Set W)

/-- *If α, must β* is the variably strict conditional over the accessible worlds, under the
preorders the ordering source induces. -/
theorem variablyStrictImp_eq_setOf_mem_humanNecessity :
    variablyStrictImp f.accessibleWorlds (fun w ↦ premisePreorder (g w)) α β =
      {w | β ∈ humanNecessity (f.restrict α) g w} :=
  Set.ext fun w ↦ by
    rw [mem_variablyStrictImp, Set.mem_ofPred_eq, humanNecessity,
      Background.accessibleWorlds_restrict]

/-- *If α, might β* is the *might* of the variably strict conditional. -/
theorem might_variablyStrictImp_eq_setOf_humanPossibility :
    might (variablyStrictImp f.accessibleWorlds (fun w ↦ premisePreorder (g w))) α β =
      {w | humanPossibility (f.restrict α) g w β} :=
  Set.ext fun w ↦ by
    rw [mem_might, variablyStrictImp_eq_setOf_mem_humanNecessity, Set.mem_ofPred_eq,
      Set.mem_ofPred_eq, humanPossibility_iff_compl_notMem]

/-- Over the best worlds, *if α, must β* is truth at the best accessible α-worlds. -/
theorem orderingImp_eq_setOf_bestWorlds_subset :
    orderingImp f.accessibleWorlds (fun w ↦ premisePreorder (g w)) α β =
      {w | bestWorlds (f.restrict α) g w ⊆ β} :=
  Set.ext fun w ↦ by
    rw [mem_orderingImp, Set.mem_ofPred_eq, bestWorlds, Background.accessibleWorlds_restrict]

/-- With an empty ordering source, *if α, must β* is the strict conditional over the accessible
worlds. -/
theorem strictImp_eq_setOf_mem_simpleNecessity :
    strictImp f.accessibleWorlds α β = {w | β ∈ simpleNecessity (f.restrict α) w} :=
  Set.ext fun w ↦ by
    rw [mem_strictImp, Set.mem_ofPred_eq, mem_simpleNecessity,
      Background.accessibleWorlds_restrict]

end Conditional.Restrictor
