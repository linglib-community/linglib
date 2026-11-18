/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Semantics.ArgumentStructure.EventIdentification
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Mode.Basic
public import Linglib.Semantics.Composition.Sorts

/-!
# The denotation of Voice

Every Voice head has a semantic type and a denotation, read off its cell. Thematic Voice whose
variable a specifier saturates denotes the relation its instruction names between the individual
it introduces and an eventuality, of type `⟨e,⟨v,t⟩⟩`; thematic Voice without a specifier, the
passive, binds its variable existentially, a predicate of eventualities of type `⟨v,t⟩`; and
expletive Voice adds no semantics to the verb phrase it combines with, the identity on predicates
of eventualities. The relations are a model's, one per instruction, so a study that interprets a
Minimalist object supplies the model, not the head's meaning. With a verb phrase that denotes a
predicate of eventualities, the one rule that applies to a thematic head is [Event
Identification](##Minimalist.Voice.binary_thematic), which [adds its
argument](##Minimalist.Voice.funMap_thematic); to the passive head, [Predicate
Modification](##Minimalist.Voice.binary_implicit); and to an expletive head, [Functional
Application](##Minimalist.Voice.binary_expletive): the external argument is not an argument of
the verb.

## References

* [kratzer-1996]
* [alexiadou-anagnostopoulou-schaefer-2015]
-/

@[expose] public section

namespace Minimalist.Voice

open ManySorted Interpreter ArgumentStructure

/-- The semantic type of a Voice head with the given variable, implicit or not. -/
def tyOf : Option Instruction → Bool → Ty Base
  | some _, false => .evt
  | some _, true => .vt
  | none, _ => .vt ⇒ .vt

variable {E W : Type} {S : Sorts} (ρ : Instruction → E → S.eventuality → Prop)

/-- The denotation of a Voice head with the given variable, implicit or not, in a model `ρ` of
the instructions. -/
def valOf : (i : Option Instruction) → (b : Bool) → (tyOf i b).Domain E W S
  | some i, false => ρ i
  | some i, true => fun e ↦ ∃ x, ρ i x e
  | none, _ => id

/-- The semantic type of a Voice head: `⟨e,⟨v,t⟩⟩` for thematic Voice with its variable
saturated, `⟨v,t⟩` with its variable implicit, and `⟨⟨v,t⟩,⟨v,t⟩⟩` for expletive Voice. -/
def Head.ty (h : Head) : Ty Base := tyOf h.thematic h.implicit

/-- A thematic Voice head with its variable saturated denotes the model's relation `ρ i` for its
instruction `i`, and with its variable implicit the relation existentially closed,
`λe. ∃x, ρ i x e`; expletive Voice denotes the identity
([alexiadou-anagnostopoulou-schaefer-2015]). -/
def Head.denote (h : Head) : h.ty.Domain E W S := valOf ρ h.thematic h.implicit

/-- The rules by which a Voice head composes with its verb phrase: Functional Application,
Predicate Modification, and Event Identification of a relation of individuals to eventualities
with a predicate of eventualities ([kratzer-1996]). -/
abbrev grammar : ManySorted.Language (Ty Base) :=
  (application.sum predicateModification).sum (eventIdentification .e .v)

/-- A thematic head with its variable saturated and a predicate of eventualities combine by Event
Identification and no other rule. -/
theorem binary_thematic (i : Instruction) :
    (typeDriven (N := Unit) grammar).binary (tyOf (some i) false) .vt = [⟨.evt, .inr .left⟩] :=
  rfl

/-- Event Identification gives the head's relation conjoined with the verb phrase's predicate at
the eventuality, the individual left open. -/
theorem funMap_thematic (i : Instruction) (P : S.eventuality → Prop) :
    EventIdentification.eval (Base.Dom E W S) (.left (x := .e) (s := .v))
      (valOf ρ (some i) false) P = eventIdentification (ρ i) P :=
  rfl

/-- A thematic head with its variable implicit and a predicate of eventualities combine by
Predicate Modification and no other rule. -/
theorem binary_implicit (i : Instruction) :
    (typeDriven (N := Unit) grammar).binary (tyOf (some i) true) .vt = [⟨.vt, .inl (.inr .pm)⟩] :=
  rfl

/-- An expletive head takes a predicate of eventualities by Functional Application and no other
rule. -/
theorem binary_expletive (b : Bool) :
    (typeDriven (N := Unit) grammar).binary (tyOf none b) .vt = [⟨.vt, .inl (.inl .fa)⟩] := by
  cases b <;> rfl

end Minimalist.Voice
