/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Chain
public import Linglib.Syntax.Minimalist.SyntacticObject.Phase

/-!
# Locality on chains

Locality constrains the links of a chain. Chomsky's Phase Impenetrability Condition bars a link
from the interior of a phase, the positions its head c-commands, to a position outside the head's
maximal projection, so that the edge is the escape hatch (`Crosses`); an island is a domain no
link may leave (`Escapes`). A token with one copy has no link, so binding in situ is subject to
neither (`not_crosses_of_length_le_one`, `not_escapes_of_length_le_one`), and movement, covert
movement included, is subject to both, as Sato and Ngui find. The interior of a phase on positions
is the c-command domain of its head (`RoseTree.cCommandDomain`), and it carries the terms within
the complement of the unordered phase (`withinComplement_iff_exists_mem_cCommandDomain`).

## Main definitions

* `Minimalist.Crosses`, `Minimalist.Escapes`: a link leaving a phase from its interior, and a
  link leaving a domain.

## Main statements

* `Minimalist.withinComplement_iff_exists_mem_cCommandDomain`: the positions a phase head
  occurring once c-commands carry the terms within its complement.

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

variable (t : PlanarSyntacticObject) (tok : LexicalItem.Token)

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
  · simpa only [RoseTree.mem_cCommandDomain] using PlanarSyntacticObject.cCommands_termAt_iff hu'
  · rw [PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm (by rwa [ha]),
      ← PlanarSyntacticObject.eq_termAt_pred_of_immediatelyContains hu' hm₀ (by rwa [ha])]
    exact hℓ

/-- A link of the chain of `tok` leaves the phase headed at `h` when it runs from a position the
head c-commands, the phase's interior, to a position outside the head's maximal projection; the
Phase Impenetrability Condition forbids it, and a link to the edge does not leave. -/
def Crosses (h : TreePath) : Prop :=
  ∃ x ∈ links t tok, x.2 ∈ t.val.cCommandDomain h ∧ ¬ projectionAt t h ≤ x.1

instance (h : TreePath) : Decidable (Crosses t tok h) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A link of the chain of `tok` leaves the domain at `D` when it runs from inside `D` to outside,
as movement out of an island does. -/
def Escapes (D : TreePath) : Prop := ∃ x ∈ links t tok, D ≤ x.2 ∧ ¬ D ≤ x.1

instance (D : TreePath) : Decidable (Escapes t tok D) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem not_crosses_of_length_le_one (h : (chain t tok).length ≤ 1) (hd : TreePath) :
    ¬ Crosses t tok hd := by
  simp [Crosses, links_eq_nil_of_length_le_one t tok h]

theorem not_escapes_of_length_le_one (h : (chain t tok).length ≤ 1) (D : TreePath) :
    ¬ Escapes t tok D := by
  simp [Escapes, links_eq_nil_of_length_le_one t tok h]

end Minimalist
