module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Fusion

Fusion merges two adjacent terminal nodes into a single terminal bearing
both feature bundles, which a single Vocabulary Item then spells out — the
Tns+Agr fusion of English finite verbs; French *du* = P[de] fused with
D[le] is the portmanteau case. It is the inverse misalignment from Fission:
fission yields more positions of exponence than syntactic terminals, fusion
fewer. The fused bundle is the union of the two bundles; a rule contributes only
the condition under which the two terminals fuse.

## Main definitions

* `FusionRule`: the licensing condition on two adjacent bundles.
* `FusionRule.apply`: the fused bundle when the condition holds.

## Main results

* `portmanteau_needs_fusion`: an exponent whose items all draw on both
  bundles is insertable at neither unfused node.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [L. Kalin, B. Bjorkman et al.][kalin-bjorkman-etal-2026] §4.4
-/

@[expose] public section

namespace DistributedMorphology

variable {F E : Type*}

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

section Portmanteau

variable [DecidableEq F]

theorem portmanteau_needs_fusion {items : List (VocabularyItem F E)}
    {p q : Neighborhood (Finset F)} {e : E}
    (he : ∀ i ∈ items, i.exponent = e → ¬ Morphology.Exponence.Applies i p ∧
      ¬ Morphology.Exponence.Applies i q) :
    subsetPrinciple items p ≠ some e ∧ subsetPrinciple items q ≠ some e := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨i, hi, rfl, happ⟩ := subsetPrinciple_winner_mem h
  · exact (he i hi rfl).1 happ
  · exact (he i hi rfl).2 happ

end Portmanteau

end DistributedMorphology
