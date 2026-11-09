module

public import Linglib.Semantics.Modality.Necessity

/-!
# Strong and weak necessity

Von Fintel and Iatridou distinguish two necessity forces over Kratzer's conversational
backgrounds. Strong necessity (*must*, *have to*) is necessity over the best accessible worlds;
weak necessity (*ought*, *should*) is necessity over those worlds re-ranked by a secondary ordering
source, the lexicographic refinement in which a later ordering source undoes the ties left by an
earlier one. Selecting within the best worlds can only shrink the domain, so strong necessity
[entails weak necessity](##Modality.Directive.weakNecessity_le_principal) and [not
conversely](##Modality.Directive.exists_mem_weakNecessity_not_bestWorlds_subset); with an empty
secondary ordering source [the two coincide](##Modality.Directive.weakNecessity_bot).

## Implementation notes

Both forces are stated over best worlds, as von Fintel and Iatridou state them, and so presuppose
the Limit Assumption; under it strong necessity is Kratzer's human necessity
(`humanNecessity_eq_principal`).

## TODO

A weak necessity that needs no Limit Assumption, over the refinement of the primary ordering
source by the secondary one.

## References

* [von-fintel-iatridou-2008]
* [kratzer-1981]
* [kratzer-2012]
-/

@[expose] public section

namespace Modality.Directive

open Modality

variable {W : Type*} {f g g' : Background W} {w : W} {s : Set W}

open Filter

/-- The weak necessities at `w`, *ought φ*, are the propositions true at the best of the best
accessible worlds under a secondary ordering source `g'`. -/
def weakNecessity (f g g' : Background W) (w : W) : Filter W :=
  𝓟 (bestWorlds (.ofRel (bestAccessible f g)) g' w)

theorem mem_weakNecessity :
    s ∈ weakNecessity f g g' w ↔ (premisePreorder (g' w)).minimals (bestWorlds f g w) ⊆ s := by
  simp [weakNecessity, bestWorlds]

/-- Every strong necessity, true at the best worlds, is a weak necessity. -/
theorem weakNecessity_le_principal : weakNecessity f g g' w ≤ 𝓟 (bestWorlds f g w) := fun _ h ↦
  mem_weakNecessity.2 ((Preorder.minimals_subset _ _).trans h)

/-- With no secondary ordering source, weak necessity is strong necessity. -/
@[simp] theorem weakNecessity_bot (f g : Background W) (w : W) :
    weakNecessity f g ⊥ w = 𝓟 (bestWorlds f g w) := by
  simp [weakNecessity]

theorem exists_mem_weakNecessity_not_bestWorlds_subset :
    ∃ (f g g' : Background Bool) (s : Set Bool) (w : Bool),
      s ∈ weakNecessity f g g' w ∧ ¬ bestWorlds f g w ⊆ s := by
  refine ⟨⊥, ⊥, fun _ ↦ {{true}}, {true}, true, ?_,
    fun h ↦ absurd (h (a := false) (by simp)) (by simp)⟩
  simp [mem_weakNecessity, Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff]

end Modality.Directive
