module

public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Conditionals.Basic

/-!
# The restrictor theory of conditionals

On the restrictor analysis of Lewis and Kratzer an *if*-clause is not a connective but restricts
the modal base of a possibly covert modal, so *if α, must β* is necessity over the modal base
restricted by α and *if α, might β* possibility over it. With Kratzer's official necessity, which
needs no Limit Assumption, the restrictor conditional is Lewis's variably strict conditional over
the accessible worlds ranked by the ordering source, and its *might* is that conditional's
*might*. Under the Limit Assumption it is truth at the best accessible antecedent-worlds, the form
most applications state, and with an empty ordering source it is the strict conditional.

## Main definitions

* `Restrictor.conditionalNecessity`, `Restrictor.conditionalPossibility`: *if α, must β* and
  *if α, might β*.

## Main results

* `Restrictor.conditionalNecessity_iff_mem_variablyStrictImp`,
  `Restrictor.conditionalPossibility_iff_mem_might`: the restrictor conditionals are the variably
  strict conditional and its *might*.
* `Restrictor.conditionalNecessity_iff_necessity`,
  `Restrictor.conditionalNecessity_iff_mem_orderingImp`: under the Limit Assumption, truth at the
  best accessible antecedent-worlds.
* `Restrictor.restrictor_eq_strict`: with an empty ordering source it is the strict conditional.

## References

* [D. Lewis, *Adverbs of Quantification* (1975)][lewis-1975]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [D. Lewis, *Ordering Semantics and Premise Semantics for Counterfactuals* (1981)][lewis-1981]
* [A. Kratzer, *Conditionals* (1986)][kratzer-1986]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

@[expose] public section


namespace Conditional.Restrictor

open Modality

variable {W : Type*} (f g : Background W) (α β : W → Prop) (w : W)

/-- *If α, must β* on the restrictor analysis is human necessity over the modal base restricted
by α. -/
def conditionalNecessity : Prop := humanNecessity (f.restrict α) g β w

/-- *If α, might β* on the restrictor analysis is human possibility over the modal base
restricted by α. -/
def conditionalPossibility : Prop := humanPossibility (f.restrict α) g β w

/-- *If α, must β* is the variably strict conditional over the accessible worlds, under the
preorders the ordering source induces. -/
theorem conditionalNecessity_iff_mem_variablyStrictImp :
    conditionalNecessity f g α β w ↔ w ∈ variablyStrictImp (f.accessibleWorlds)
      (fun w ↦ premisePreorder (g w)) {v | α v} {v | β v} := by
  rw [conditionalNecessity, humanNecessity, Background.accessibleWorlds_restrict]
  rfl

/-- *If α, might β* is the *might* of the variably strict conditional. -/
theorem conditionalPossibility_iff_mem_might :
    conditionalPossibility f g α β w ↔ w ∈ might (variablyStrictImp (f.accessibleWorlds)
      (fun w ↦ premisePreorder (g w))) {v | α v} {v | β v} := by
  rw [conditionalPossibility, humanPossibility, humanNecessity,
    Background.accessibleWorlds_restrict]
  rfl

variable {f g α β w}

theorem necessity_of_conditionalNecessity (h : conditionalNecessity f g α β w) :
    necessity (f.restrict α) g β w :=
  necessity_of_humanNecessity h

/-- Under the Limit Assumption, *if α, must β* is necessity at the best accessible α-worlds. -/
theorem conditionalNecessity_iff_necessity (hlim : LimitAssumption (f.restrict α) g w) :
    conditionalNecessity f g α β w ↔ necessity (f.restrict α) g β w :=
  humanNecessity_iff_necessity hlim

theorem conditionalNecessity_iff_necessity_of_finite [Finite W] :
    conditionalNecessity f g α β w ↔ necessity (f.restrict α) g β w :=
  conditionalNecessity_iff_necessity (.of_finite _ _ _)

theorem conditionalNecessity_bot_iff :
    conditionalNecessity f ⊥ α β w ↔ necessity (f.restrict α) ⊥ β w :=
  conditionalNecessity_iff_necessity (.bot _ _)

theorem conditionalPossibility_iff_possibility (hlim : LimitAssumption (f.restrict α) g w) :
    conditionalPossibility f g α β w ↔ possibility (f.restrict α) g β w :=
  humanPossibility_iff_possibility hlim

theorem conditionalNecessity_iff_mem_orderingImp (hlim : LimitAssumption (f.restrict α) g w) :
    conditionalNecessity f g α β w ↔
      w ∈ orderingImp (f.accessibleWorlds) (fun w ↦ premisePreorder (g w)) {v | α v} {v | β v} := by
  rw [conditionalNecessity_iff_necessity hlim, necessity_iff, mem_orderingImp, bestWorlds,
    Background.accessibleWorlds_restrict]
  rfl

variable (f α β w)

/-- With an empty ordering source, *if α, must β* is the strict conditional over the accessible
worlds. -/
theorem restrictor_eq_strict :
    conditionalNecessity f ⊥ α β w ↔
      w ∈ strictImp (f.accessibleWorlds) {v | α v} {v | β v} := by
  rw [conditionalNecessity, humanNecessity_bot_iff, simpleNecessity_iff, mem_strictImp]
  simp [-Background.mem_accessibleWorlds, Set.subset_def, and_imp]

theorem vacuous_conditional (h : ∀ w', w' ∈ f.accessibleWorlds w → ¬ α w') :
    conditionalNecessity f g α β w := fun u hu ↦
  absurd (Background.mem_accessibleWorlds_restrict.1 hu).2
    (h u (Background.mem_accessibleWorlds_restrict.1 hu).1)

theorem material_from_restrictor (hTotal : f.accessibleWorlds w = {w}) :
    conditionalNecessity f ⊥ α β w ↔ (α w → β w) := by
  rw [restrictor_eq_strict, mem_strictImp_forall, hTotal]
  simp

end Conditional.Restrictor
