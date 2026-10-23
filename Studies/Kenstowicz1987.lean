/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Fragments.Tangale.Phonology

/-!
# Kenstowicz (1987): The Phonology and Syntax of Wh-Expressions in Tangale

This file formalizes Kenstowicz's argument that the blocking of phrasal phonological rules
reveals surface syntax "that we did not already know". Tangale elision and
tonal delinking apply obligatorily between a verb and its object ((15b), (15e)) but are blocked
before a wh-object ((15c), (15f)); a sandhi rule sensitive to the [wh] feature is rejected both
on interface grounds and by the minimal pair (16), where a wh-possessor inside NP triggers
elision (*ayab noŋ* 'whose banana'). The solution is syntactic: wh-subjects obligatorily postpose
to a position with "the force of the English cleft" (18), the Focus position, and apparently
in-situ wh-objects occupy it string-vacuously, so a constituent boundary blocks the sandhi.
Elision then tracks government exactly (`elision_tracks_government`), and the [wh] feature does
not factor it (`elision_not_factor_through_wh`).

## References

* [kenstowicz-1987]
* [kidda-1985]
-/

@[expose] public section

namespace Kenstowicz1987

/-- The junctures at which the sandhi rules are tested
((4)–(5), (15)–(16)). -/
inductive Juncture where
  | headComplementNP
  | verbObject
  | verbAdjunct
  | subjectVP
  | verbWhObject
  | headWhPossessor
  deriving DecidableEq, Repr

/-- Whether elision (and delinking) is observed to apply at the juncture
((4a, b), (5a–c), (15c, f), (16a, b)). -/
def elides : Juncture → Bool
  | .headComplementNP => true
  | .verbObject       => true
  | .verbAdjunct      => false
  | .subjectVP        => false
  | .verbWhObject     => false
  | .headWhPossessor  => true

/-- Whether the juncture's second element is a wh-word. -/
def secondIsWh : Juncture → Bool
  | .verbWhObject | .headWhPossessor => true
  | _ => false

/-- Whether the juncture is a government configuration under the Focus-position analysis.
Head–complement and verb–object are, and adjuncts and subjects are not. A wh-object sits in the
postverbal Focus position across a constituent boundary (string-vacuous postposing, as with the
obligatorily postposed wh-subjects of (18)), and a wh-possessor has no NP-internal Focus
position and stays in situ. -/
def governed : Juncture → Bool
  | .headComplementNP => true
  | .verbObject       => true
  | .verbAdjunct      => false
  | .subjectVP        => false
  | .verbWhObject     => false
  | .headWhPossessor  => true

/-- Elision is not a function of the second word's [wh] feature ((15c, f) vs (16a, b)). -/
theorem elision_not_factor_through_wh : ¬ Function.FactorsThrough elides secondIsWh :=
  fun h ↦ absurd (@h .verbWhObject .headWhPossessor rfl) (by decide)

theorem elision_tracks_government : ∀ j, elides j = governed j := by
  intro j; cases j <;> rfl

/-- In (15d–f), the verb's blocked form before a wh-object differs audibly from its elided form, by
[kidda-1985]'s cascade. -/
theorem wh_object_cell_audible :
    Tangale.blockedForm ≠ Tangale.elidedForm :=
  Tangale.boundary_audible.1

end Kenstowicz1987
