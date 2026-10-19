/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Basic
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
public import Linglib.Syntax.WordOrder

/-!
# Valency frames

This file defines valency frames over dependency graphs: slot data,
standard frame schemas for the basic valences, the valency of a verb's
lexical `ArgumentFrame`, read off the argument roles of its core
arguments, and satisfaction of a frame by a position's dependents.

## Main definitions

* `Valency` is a word's valency as a list of slots, each a relation, a head direction and an
  optionality.
* `Valency.ofFrame` is the valency of an argument frame, a slot for each
  core argument by its argument role.
* `Frames n` is the per-position valency table.
* `Graph.SatisfiesFrames` is frame satisfaction: every filler on its
  slot's side of the head, required slots filled, and no unlicensed core
  arguments.

## Implementation notes

Frames are a side table (`Frames n`), not part of the graph carrier: the
frame is framework apparatus (like HPSG's ARG-ST), supplied alongside the
graph by the consumers that reason about valency and populated from the
lexical carrier (`Valency.ofFrame` of a verb's basic frame).

## References

* [tesniere-1959]
* [hudson-2010]
* [osborne-2019]
-/

@[expose] public section

namespace DependencyGrammar

/-! ### Slot data -/

/-- A single valency slot, recording which relation fills it, the direction of the head with
respect to the filler, and whether it must be filled. -/
structure Valency.Slot where
  /-- The UD relation of the filler. -/
  depType : UD.DepRel
  /-- The direction of the head with respect to the filler. -/
  direction : HeadDirection
  /-- Whether the slot must be filled. -/
  required : Bool := true
  deriving Repr, DecidableEq

/-- The valency of a word is the list of dependent slots it requires or allows. -/
abbrev Valency := List Valency.Slot

/-- The per-position frame table supplied alongside a `Graph n`. -/
abbrev Frames (n : ℕ) := Fin n → Option Valency

/-- A sparse frame table, in which positions not listed carry no frame. -/
def Frames.ofList {n : ℕ} (l : List (Fin n × Valency)) : Frames n :=
  fun i ↦ (l.find? (·.1 == i)).map (·.2)

/-! ### Standard schemas -/

/-- An intransitive verb takes its subject to the left. -/
def Valency.intransitive : Valency := [⟨.nsubj, .headFinal, true⟩]

/-- A transitive verb takes its subject to the left and its object to the right. -/
def Valency.transitive : Valency := [⟨.nsubj, .headFinal, true⟩, ⟨.obj, .headInitial, true⟩]

/-- A ditransitive verb takes its subject to the left and its indirect object and object to the
right. -/
def Valency.ditransitive : Valency :=
  [⟨.nsubj, .headFinal, true⟩, ⟨.iobj, .headInitial, true⟩, ⟨.obj, .headInitial, true⟩]

/-- A passive transitive verb takes its subject, the patient, to the left and an optional
by-phrase to the right. -/
def Valency.passiveTransitive : Valency := [⟨.nsubj, .headFinal, true⟩, ⟨.obl, .headInitial, false⟩]

/-! ### Valency of an argument frame -/

/-- The required slot of a core argument by its argument role. S and A are the subject, to the
left of the head; P and T the object and R the indirect object, to its right. -/
def Valency.Slot.ofRole : ArgumentRole → Valency.Slot
  | .S | .A => ⟨.nsubj, .headFinal, true⟩
  | .P | .T => ⟨.obj, .headInitial, true⟩
  | .R => ⟨.iobj, .headInitial, true⟩

/-- The valency of an argument frame has a slot for each core argument, by its argument role.
Clausal and adpositional complements have none, since UD's clausal relations and obliques are
not core arguments and `Graph.SatisfiesFrames` leaves them unconstrained. -/
def Valency.ofFrame (fr : ArgumentFrame) : Valency :=
  fr.coreSlots.filterMap fun s ↦ (fr.argumentRole s).map .ofRole

theorem Valency.ofFrame_intransitive : ofFrame .intransitive = .intransitive := rfl

theorem Valency.ofFrame_np : ofFrame .np = .transitive := rfl

theorem Valency.ofFrame_np_np : ofFrame .np_np = .ditransitive := rfl

/-! ### Argument-frame satisfaction -/

section Satisfaction

variable {n : ℕ}

/-- The dependents of `v` linked by relation `rel`. -/
def Graph.fillersOf (g : Graph n) (v : Fin n) (rel : UD.DepRel) : Finset (Fin n) :=
  {w ∈ g.children v | g.label v w = some rel}

/-- The graph satisfies a valency at head `v` when the head has the slot's direction with
respect to every filler of every slot, and required slots are filled. -/
def SatisfiesValency (g : Graph n) (v : Fin n) (val : Valency) : Prop :=
  ∀ slot ∈ val, (∀ w ∈ g.fillersOf v slot.depType, slot.direction.Orders v w) ∧
    (slot.required → (g.fillersOf v slot.depType).Nonempty)

instance (g : Graph n) (v : Fin n) (val : Valency) :
    Decidable (SatisfiesValency g v val) :=
  List.decidableBAll _ val

/-- Every nominal core-argument dependent of `v` is licensed by a slot of `val`, the closed-world
half of valency checking (`SatisfiesValency` only checks that required slots are filled). The
clausal core relations are licensed by clause-embedding frames, which `Valency.ofFrame` does not
schematize. -/
def CoreArgsLicensed (g : Graph n) (v : Fin n) (val : Valency) : Prop :=
  ∀ w ∈ g.children v, ∀ r ∈ g.label v w,
    r.kind = .cell .core .nominal → ∃ slot ∈ val, slot.depType = r

instance (g : Graph n) (v : Fin n) (val : Valency) :
    Decidable (CoreArgsLicensed g v val) :=
  Finset.decidableDforallFinset

/-- Each verb's dependents satisfy its frame, with required slots filled in the
    right direction (`SatisfiesValency`) and no unlicensed core arguments
    (`CoreArgsLicensed`). Verbs without a frame are unconstrained. -/
def Graph.SatisfiesFrames (g : Graph n) (frames : Frames n) : Prop :=
  ∀ v, (g.words v).cat = .VERB → ∀ val ∈ frames v,
    SatisfiesValency g v val ∧ CoreArgsLicensed g v val

instance (g : Graph n) (frames : Frames n) :
    Decidable (g.SatisfiesFrames frames) :=
  inferInstanceAs (Decidable (∀ _, _))

end Satisfaction

end DependencyGrammar
