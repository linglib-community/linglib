module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Fusion

Fusion merges two adjacent terminal nodes into one terminal bearing both feature bundles, which a
single Vocabulary Item then spells out, as Tns and Agr fuse in the English finite verb. It is the
inverse of Fission: Fission yields more positions of exponence than the syntax has terminals,
Fusion fewer. The fused bundle is the union of the two, so a rule contributes only the condition
under which two terminals fuse. Fusion is one analysis of a portmanteau among several: an exponent
that seems to span two terminals may instead be an item of one of them whose site mentions the
other, or the exponent of a span.

## References

* [halle-marantz-1993]
* [kalin-bjorkman-etal-2026]
-/

@[expose] public section

namespace DistributedMorphology

variable {F : Type*}

/-- A Fusion rule fuses two adjacent terminals, the structurally higher first, into one bearing
both bundles when its decidable condition holds of them. -/
structure FusionRule (F : Type*) where
  /-- The condition on the two fusing bundles. -/
  condition : Finset F → Finset F → Prop
  [decCond : DecidableRel condition]

namespace FusionRule

variable [DecidableEq F] {rule : FusionRule F} {p q out : Finset F}

instance (rule : FusionRule F) : DecidableRel rule.condition := rule.decCond

/-- Applying Fusion gives the two bundles together when the condition holds, and `none`
otherwise. -/
def apply (rule : FusionRule F) (p q : Finset F) : Option (Finset F) :=
  if rule.condition p q then some (p ∪ q) else none

theorem apply_pos (h : rule.condition p q) : rule.apply p q = some (p ∪ q) := ite_eq_left h

theorem apply_neg (h : ¬ rule.condition p q) : rule.apply p q = none := ite_eq_right h

@[simp] theorem apply_eq_some_iff :
    rule.apply p q = some out ↔ rule.condition p q ∧ p ∪ q = out := by
  unfold apply; split <;> simp_all

@[simp] theorem apply_eq_none_iff : rule.apply p q = none ↔ ¬ rule.condition p q := by
  unfold apply; split <;> simp_all

theorem isSome_apply : (rule.apply p q).isSome ↔ rule.condition p q := by
  unfold apply; split <;> simp_all

end FusionRule

end DistributedMorphology
