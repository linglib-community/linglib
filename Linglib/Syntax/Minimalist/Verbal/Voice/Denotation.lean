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

Every Voice head has a denotation, read off its cell. Thematic Voice whose variable a specifier
saturates denotes the relation its instruction names between the individual it introduces and an
eventuality, of type `⟨e,⟨v,t⟩⟩`; thematic Voice without a specifier, the passive, binds its
variable existentially, a predicate of eventualities of type `⟨v,t⟩`; and expletive Voice adds no
semantics to the verb phrase it combines with, the identity on predicates of eventualities. The
relations are a model's, one per instruction, so a study that interprets a Minimalist object
supplies the model, not the head's meaning. Merged with a verb phrase that denotes a predicate `P`
of eventualities, whatever `P` is, a thematic head [adds its argument by Event
Identification](##Minimalist.Voice.Head.interp_toTree_leaf_mul), the passive head [conjoins the
existentially bound relation with `P`](##Minimalist.Voice.Head.interp_toTree_leaf_mul_of_implicit),
and an expletive head [leaves `P` as it
is](##Minimalist.Voice.Head.interp_toTree_leaf_mul_of_expletive): the external argument is not an
argument of the verb.

## References

* [kratzer-1996]
* [alexiadou-anagnostopoulou-schaefer-2015]
-/

@[expose] public section

namespace Minimalist.Voice.Head

open Montague PhraseStructure ArgumentStructure

variable {E W : Type} {S : Sorts} (ρ : Instruction → E → S.eventuality → Prop)

/-- A thematic Voice head with its variable saturated denotes the model's relation `ρ i` for its
instruction `i`, of type `⟨e,⟨v,t⟩⟩`, and with its variable implicit the relation existentially
closed, `λe. ∃x, ρ i x e`, of type `⟨v,t⟩`; expletive Voice denotes the identity on `⟨v,t⟩`
([alexiadou-anagnostopoulou-schaefer-2015]). -/
def denote (h : Head) : Denotation E W Id S :=
  match h.thematic with
  | some i => if h.implicit then ⟨.v ⇒ .t, fun e ↦ ∃ x, ρ i x e⟩ else ⟨.e ⇒ .v ⇒ .t, ρ i⟩
  | none => ⟨(.v ⇒ .t) ⇒ .v ⇒ .t, id⟩

@[simp] theorem denote_of_thematic {h : Head} {i : Instruction} (hi : h.thematic = some i)
    (hn : h.implicit = false) : h.denote (W := W) ρ = ⟨.e ⇒ .v ⇒ .t, ρ i⟩ := by
  simp [denote, hi, hn]

@[simp] theorem denote_of_implicit {h : Head} {i : Instruction} (hi : h.thematic = some i)
    (hn : h.implicit = true) : h.denote (W := W) ρ = ⟨.v ⇒ .t, fun e ↦ ∃ x, ρ i x e⟩ := by
  simp [denote, hi, hn]

@[simp] theorem denote_of_expletive {h : Head} (hi : h.thematic = none) :
    h.denote (W := W) ρ = ⟨(.v ⇒ .t) ⇒ .v ⇒ .t, id⟩ := by
  simp [denote, hi]

variable {L : Type} (ι : L → ℕ) {lex : L → Option (Denotation E W Id S)} {g : Assignment E} {v : L}
  {vp : LinearizedSyntacticObject L} {h : Head} {P : S.eventuality → Prop}

/-- A thematic head with its variable saturated, merged with a verb phrase that denotes the
predicate `P` of eventualities, denotes its relation conjoined with `P` at the eventuality, by
Event Identification. -/
theorem interp_toTree_leaf_mul {i : Instruction} (hv : lex v = some (h.denote ρ))
    (hi : h.thematic = some i) (hn : h.implicit = false)
    (hvp : (vp.toTree ι).interp lex g = some ⟨.v ⇒ .t, P⟩) :
    ((LinearizedSyntacticObject.leaf v * vp).toTree ι).interp lex g =
      some ⟨.e ⇒ .v ⇒ .t, eventIdentification (ρ i) P⟩ := by
  simp [hv, hvp, denote_of_thematic ρ hi hn]

/-- A thematic head with its variable implicit, merged with a verb phrase that denotes the
predicate `P` of eventualities, denotes the eventualities of `P` that its relation relates some
individual to, by Predicate Modification. -/
theorem interp_toTree_leaf_mul_of_implicit {i : Instruction} (hv : lex v = some (h.denote ρ))
    (hi : h.thematic = some i) (hn : h.implicit = true)
    (hvp : (vp.toTree ι).interp lex g = some ⟨.v ⇒ .t, P⟩) :
    ((LinearizedSyntacticObject.leaf v * vp).toTree ι).interp lex g =
      some ⟨.v ⇒ .t, fun e ↦ (∃ x, ρ i x e) ∧ P e⟩ := by
  simp [hv, hvp, denote_of_implicit ρ hi hn]
  rfl

/-- An expletive head merged with a verb phrase that denotes the predicate `P` of eventualities
denotes `P`. -/
theorem interp_toTree_leaf_mul_of_expletive (hv : lex v = some (h.denote ρ))
    (hi : h.thematic = none) (hvp : (vp.toTree ι).interp lex g = some ⟨.v ⇒ .t, P⟩) :
    ((LinearizedSyntacticObject.leaf v * vp).toTree ι).interp lex g = some ⟨.v ⇒ .t, P⟩ := by
  simp [hv, hvp, denote_of_expletive ρ hi]

end Minimalist.Voice.Head
