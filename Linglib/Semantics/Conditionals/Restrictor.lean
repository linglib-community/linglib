module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Conditionals.Basic

/-!
# The restrictor theory of conditionals

This file defines the restrictor conditional. On the restrictor analysis of Lewis and Kratzer an
*if*-clause is not a connective but restricts the modal base of a possibly covert modal, so
*if α, must β* is necessity over the modal base restricted by α and *if α, might β* possibility
over it. The restrictor conditional is the conditional over the best accessible antecedent-worlds
under the preorders the ordering source induces (`orderingImp`), its *might* is the *might* of
that conditional, and with an empty ordering source it is the strict conditional.

## Main definitions

* `Restrictor.conditionalNecessity`, `Restrictor.conditionalPossibility`: *if α, must β* and
  *if α, might β*.

## Main results

* `Restrictor.conditionalNecessity_iff_mem_orderingImp`,
  `Restrictor.conditionalPossibility_iff_mem_might`: the restrictor conditionals are the
  conditional over the best accessible antecedent-worlds and its *might*.
* `Restrictor.restrictor_eq_strict`: with an empty ordering source it is the strict conditional.

## References

* [D. Lewis, *Adverbs of Quantification* (1975)][lewis-1975]
* [A. Kratzer, *Conditionals* (1986)][kratzer-1986]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

@[expose] public section


namespace Conditional.Restrictor

open Modality

variable {W : Type*} (f g : Background W) (α β : W → Prop) (w : W)

/-- *If α, must β* on the restrictor analysis is necessity over the modal base restricted by
α. -/
def conditionalNecessity : Prop := necessity (f.restrict α) g β w

/-- *If α, might β* on the restrictor analysis is possibility over the modal base restricted by
α. -/
def conditionalPossibility : Prop := possibility (f.restrict α) g β w

theorem conditionalNecessity_iff_mem_orderingImp :
    conditionalNecessity f g α β w ↔
      w ∈ orderingImp (f.accessibleWorlds) (fun w ↦ premisePreorder (g w)) {v | α v} {v | β v} := by
  rw [conditionalNecessity, necessity_iff, mem_orderingImp, bestWorlds,
    Background.accessibleWorlds_restrict]
  rfl

theorem conditionalPossibility_iff_mem_might :
    conditionalPossibility f g α β w ↔
      w ∈ might (orderingImp (f.accessibleWorlds) (fun w ↦ premisePreorder (g w))) {v | α v}
        {v | β v} := by
  rw [mem_might]
  change _ ↔ w ∉ orderingImp _ _ {v | α v} {v | ¬ β v}
  rw [← conditionalNecessity_iff_mem_orderingImp, conditionalPossibility, conditionalNecessity,
    possibility_iff, necessity_iff]
  push Not
  rfl

theorem restrictor_eq_strict :
    conditionalNecessity f ⊥ α β w ↔
      w ∈ strictImp (f.accessibleWorlds) {v | α v} {v | β v} := by
  rw [conditionalNecessity_iff_mem_orderingImp, strictImp_eq_orderingImp]
  simp

theorem vacuous_conditional (h : ∀ w', w' ∈ f.accessibleWorlds w → ¬ α w') :
    conditionalNecessity f g α β w :=
  (conditionalNecessity_iff_mem_orderingImp f g α β w).2 fun v hv ↦ absurd hv.1.2 (h v hv.1.1)

theorem material_from_restrictor (hTotal : f.accessibleWorlds w = {w}) :
    conditionalNecessity f ⊥ α β w ↔ (α w → β w) := by
  rw [restrictor_eq_strict, mem_strictImp_forall, hTotal]
  simp

end Conditional.Restrictor
