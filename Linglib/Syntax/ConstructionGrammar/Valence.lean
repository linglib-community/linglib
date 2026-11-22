/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Form

/-!
# Valence and coinstantiation

A predicator has a valence set, whose members are its requirements. We define a `Requirement` by
its grammatical function, its intrinsic value, and the value of its own subject requirement when
it is a predicate phrase that does not realize its subject. A slot whose filler a construct gives
a value determines a requirement, `Slot.requirement`.

`Coinstantiates` says of a valence set that the unrealized subject of each complement is the
intrinsic value of another member, the subject in raising and subject control and the object in
object control.

## Implementation notes

Which values the slots of a construct share is not part of a form; it is stated of valence sets.
A valence set is a list, in which another member is one distinct from the complement.

## References

* [kay-fillmore-1999]
-/

@[expose] public section

namespace ConstructionGrammar

variable {E : Type*}

/-- A valence requirement as unification sees it ([kay-fillmore-1999]): its grammatical function,
its intrinsic value, `none` for the semantics `[ref ∅]`, and the value of its own subject
requirement when it is a predicate phrase that does not realize its subject. -/
structure Requirement (E : Type*) where
  /-- `gf` is the requirement's grammatical function. -/
  gf : Option GrammaticalFunction
  /-- `intrinsic` is the requirement's intrinsic value, `none` for `[ref ∅]`. -/
  intrinsic : Option E
  /-- `subj` is the value of the requirement's unrealized subject requirement. -/
  subj : Option E
  deriving DecidableEq

/-- The requirement of a slot whose filler a construct gives the value `v`, and whose unrealized
subject requirement it gives `sv`. A slot marked `[ref ∅]` binds the reference of nothing, so it
has no intrinsic value whatever the construct gives it. -/
def Slot.requirement {Lex : Type*} (s : Slot Lex) (v : E) (sv : Option E) : Requirement E :=
  ⟨s.gf, if .refEmpty ∈ s.constraints then none else some v, sv⟩

/-- Coinstantiation ([kay-fillmore-1999], Figure 13) satisfies the subject requirement of each
complement in a predicator's valence set by unifying it with the intrinsic value of another member
of the set: the subject in raising and subject control, the object in object control. The list
stands for a set, so another member is one distinct from the complement. -/
def Coinstantiates (val : List (Requirement E)) : Prop :=
  ∀ k ∈ val, k.gf = some .comp → ∀ v ∈ k.subj, ∃ c ∈ val, c ≠ k ∧ c.intrinsic = some v

instance [DecidableEq E] (val : List (Requirement E)) : Decidable (Coinstantiates val) := by
  unfold Coinstantiates; infer_instance

/-- In a valence set of a subject and one complement, coinstantiation makes the complement's
subject the subject's value, as in raising and subject control. -/
theorem coinstantiates_subj_comp_iff {x e s : E} :
    Coinstantiates [⟨some .subj, some x, none⟩, ⟨some .comp, some e, some s⟩] ↔ s = x := by
  simp [Coinstantiates, eq_comm]

end ConstructionGrammar
