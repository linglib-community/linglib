/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Syntax.Minimalist.SyntacticObject.ToTree
public import Linglib.Semantics.Composition.Tree

/-!
# The denotation of Voice

A thematic Voice head denotes the relation its instruction names between the individual it
introduces and an eventuality, of type `⟨e,⟨v,t⟩⟩`, and expletive Voice has no semantics. The
relations are a model's, one per instruction, so a study that interprets a Minimalist object
supplies the model, not the head's meaning. Merged with a verb phrase that denotes a predicate of
eventualities, a thematic head [adds its argument by Event
Identification](##Minimalist.Voice.Head.interp_toTree_leaf_mul), whatever the verb phrase
denotes: the external argument is not an argument of the verb.

## References

* [kratzer-1996]
* [alexiadou-anagnostopoulou-schaefer-2015]
-/

@[expose] public section

namespace Minimalist.Voice.Head

open Montague PhraseStructure ArgumentStructure

variable {E W : Type} {S : Sorts} (ρ : Instruction → E → S.eventuality → Prop)

/-- A thematic Voice head denotes the model's relation `ρ i` for its instruction `i`, of type
`⟨e,⟨v,t⟩⟩`; expletive Voice denotes nothing. -/
def denote (h : Head) : Option (Denotation E W Id S) :=
  h.thematic.map fun i ↦ ⟨.e ⇒ .v ⇒ .t, ρ i⟩

@[simp] theorem denote_of_thematic {h : Head} {i : Instruction} (hi : h.thematic = some i) :
    h.denote (W := W) ρ = some ⟨.e ⇒ .v ⇒ .t, ρ i⟩ := by
  simp [denote, hi]

theorem denote_eq_none_iff {h : Head} : h.denote (W := W) ρ = none ↔ ¬ h.IsThematic := by
  simp [denote, IsThematic, Option.isSome_iff_ne_none]

/-- A thematic head merged with a verb phrase that denotes the predicate `P` of eventualities
denotes its relation conjoined with `P` at the eventuality, by Event Identification. -/
theorem interp_toTree_leaf_mul {L : Type} (ι : L → ℕ) {lex : L → Option (Denotation E W Id S)}
    {g : Assignment E} {v : L} {vp : LinearizedSyntacticObject L} {h : Head} {i : Instruction}
    (hv : lex v = h.denote ρ) (hi : h.thematic = some i) {P : S.eventuality → Prop}
    (hvp : (vp.toTree ι).interp lex g = some ⟨.v ⇒ .t, P⟩) :
    ((LinearizedSyntacticObject.leaf v * vp).toTree ι).interp lex g =
      some ⟨.e ⇒ .v ⇒ .t, eventIdentification (ρ i) P⟩ := by
  simp [hv, hvp, denote_of_thematic ρ hi]

end Minimalist.Voice.Head
