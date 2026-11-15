module

public import Linglib.Core.Relation.SetRel
public import Linglib.Semantics.Modification.Basic

/-!
# Relation images as modifiers of sets

The image of a relation is a modifier of sets that acts on each member separately, as the
modifiers of numerals and of scalar alternatives do, and relations are ordered as their images
are. So the image is [extensive](##Modifier.isExtensive_image_iff) when the relation is reflexive,
[subsective](##Modifier.isSubsective_image_iff) when the relation relates nothing to anything
else, and [privative](##Modifier.isPrivative_image_iff) only when the relation is empty.

## References

* [kamp-1975]
-/

@[expose] public section

namespace Modifier

variable {α : Type*} {R : SetRel α α}

/-- The image of a relation is extensive exactly when the relation is reflexive. -/
theorem isExtensive_image_iff : IsExtensive R.image ↔ R.IsRefl := by
  rw [← SetRel.id_subset_iff, ← SetRel.image_le_image_iff, SetRel.image_id_eq]
  rfl

/-- The image of a relation is subsective exactly when the relation relates nothing to anything
else. -/
theorem isSubsective_image_iff : IsSubsective R.image ↔ R ⊆ .id := by
  rw [← SetRel.image_le_image_iff, SetRel.image_id_eq]
  rfl

/-- The image of a relation is privative only when the relation is empty, since a set `{a, b}`
with `a` related to `b` meets its own image. -/
theorem isPrivative_image_iff : IsPrivative R.image ↔ R = ∅ := by
  refine ⟨fun h ↦ Set.eq_empty_iff_forall_notMem.2 fun ⟨a, b⟩ hab ↦ ?_, fun h s ↦ by simp [h]⟩
  exact Set.disjoint_left.1 (h {a, b}) ⟨a, by simp, hab⟩ (by simp)

end Modifier
