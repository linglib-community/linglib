/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Chain
public import Linglib.Syntax.Minimalist.Phase.Basic

/-!
# The Phase Impenetrability Condition on chains

Chomsky's Phase Impenetrability Condition bars a link of a chain from the interior of a phase, the
positions its head c-commands, to a position outside the head's maximal projection, so that the
edge is the escape hatch: such a link `Crosses` the phase. A token with one copy has no link, so
binding in situ [is not subject to it](##Minimalist.not_crosses_of_length_le_one), and movement,
covert movement included, is, as Sato and Ngui find. The interior of a phase on positions is the
c-command domain of its head, and it [carries the terms within the complement of the unordered
phase](##Minimalist.withinComplement_iff_exists_mem_cCommandDomain).

## Implementation notes

* Positions, not terms, individuate copies, so the phase interior of the unordered object
  (`SyntacticObject.phaseInterior`) cannot tell the links of a successive-cyclic chain apart, and
  the locality of links is stated on positions.

## References

* [chomsky-2000]
* [sato-ngui-2017]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

variable (hd : HeadFunction) (t : PlanarSyntacticObject) (tok : LexicalItem.Token)

/-- The positions a phase head occurring only at `a` c-commands carry the terms within its
complement. -/
theorem withinComplement_iff_exists_mem_cCommandDomain {t : PlanarSyntacticObject}
    {ℓ : LexicalItem.Token} {a : t.val.Positions} {x : SyntacticObject}
    (hu : ∀ q, t.termAt q = SyntacticObject.leaf ℓ ↔ q = a)
    (hph : (t : SyntacticObject).IsPhaseHead ℓ) :
    (t : SyntacticObject).WithinComplement ℓ x ↔
      ∃ q : t.val.Positions, ↑q ∈ t.val.cCommandDomain a ∧ t.termAt q = x := by
  have ha : t.termAt a = SyntacticObject.leaf ℓ := (hu a).2 rfl
  have hu' : ∀ q, t.termAt q = t.termAt a → q = a := fun q hq ↦ (hu q).1 (hq.trans ha)
  obtain ⟨m₀, hm₀, hℓ, hm₀ℓ⟩ := hph
  rw [← mem_phaseInterior, phaseInterior_eq_cCommandDomain fun m hm hmℓ ↦ ?_,
    SyntacticObject.mem_cCommandDomain, ← ha]
  · simpa only [RoseTree.mem_cCommandDomain] using
      PlanarSyntacticObject.cCommands_termAt_iff hu'
  · rw [PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm (by rwa [ha]),
      ← PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm₀ (by rwa [ha])]
    exact hℓ

/-- A link of the chain of `tok` leaves the phase headed at `h` when it runs from a position the
head c-commands, the phase's interior, to a position outside the head's maximal projection; the
Phase Impenetrability Condition forbids it, and a link to the edge does not leave. -/
def Crosses (h : TreePath) : Prop :=
  ∃ x ∈ links hd t tok, x.2 ∈ t.val.cCommandDomain h ∧ ¬ projectionAt hd t h ≤ x.1

instance (h : TreePath) : Decidable (Crosses hd t tok h) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem not_crosses_of_length_le_one (h : (chain t tok).length ≤ 1) (p : TreePath) :
    ¬ Crosses hd t tok p := by
  simp [Crosses, links_eq_nil_of_length_le_one hd t tok h]

end Minimalist
