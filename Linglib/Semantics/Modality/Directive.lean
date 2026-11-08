module

public import Linglib.Semantics.Modality.Necessity

/-!
# Strong and weak necessity

Von Fintel and Iatridou distinguish two necessity forces over Kratzer's conversational
backgrounds. Strong necessity (*must*, *have to*) is necessity over the best accessible worlds;
weak necessity (*ought*, *should*) is necessity over those worlds re-ranked by a secondary ordering
source, the lexicographic refinement in which a later ordering source undoes the ties left by an
earlier one. Selecting within the best worlds can only shrink the domain, so strong necessity
[entails weak necessity](##Modality.Directive.weakNecessity_of_necessity) and [not
conversely](##Modality.Directive.exists_weakNecessity_not_necessity); with an empty secondary
ordering source [the two coincide](##Modality.Directive.weakNecessity_bot).

## Implementation notes

Both forces are stated over best worlds, as von Fintel and Iatridou state them, and so presuppose
the Limit Assumption; under it strong necessity is Kratzer's human necessity
(`humanNecessity_iff_necessity`).

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

variable {W : Type*}

/-- Weak necessity, *ought φ*, is necessity over the best accessible worlds ranked by a secondary
ordering source `g'`. -/
def weakNecessity (f g g' : Background W) : (W → Prop) → W → Prop :=
  necessity (.ofRel (bestAccessible f g)) g'

theorem weakNecessity_iff {f g g' : Background W} {p : W → Prop} {w : W} :
    weakNecessity f g g' p w ↔
      ∀ w' ∈ (premisePreorder (g' w)).minimals (bestWorlds f g w), p w' := by
  simp [weakNecessity, bestWorlds]

theorem weakNecessity_of_necessity {f g g' : Background W} {p : W → Prop} {w : W}
    (h : necessity f g p w) : weakNecessity f g g' p w :=
  fun w' hw' ↦ h w' (by simpa using Preorder.minimals_subset _ _ hw')

/-- With no secondary ordering source, weak necessity is strong necessity. -/
@[simp] theorem weakNecessity_bot (f g : Background W) : weakNecessity f g ⊥ = necessity f g :=
  funext₂ fun p w ↦ propext <| (necessity_bot_iff _ p w).trans <| by
    simp [simpleNecessity_iff, necessity_iff]

theorem exists_weakNecessity_not_necessity :
    ∃ (f g g' : Background Bool) (p : Bool → Prop) (w : Bool),
      weakNecessity f g g' p w ∧ ¬ necessity f g p w := by
  refine ⟨⊥, ⊥, fun _ ↦ {{true}}, (· = true), true, ?_, fun h ↦ nomatch h false (by simp)⟩
  simp [weakNecessity_iff, Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff]

end Modality.Directive
