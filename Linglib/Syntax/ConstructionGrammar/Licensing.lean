/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Basic
public import Linglib.Core.Data.List.Forall2
public import Linglib.Syntax.Tree.Basic
public import Linglib.Morphology.Word.Basic

/-!
# Constructional licensing

A constructional grammar licenses a structure when every constituent in it instantiates some
construction, as for Sag and for Goldberg. `Licenses` is the local version of that relation
over constituency trees whose leaves are word tokens: every internal node's daughters
instantiate, slot by slot, the typed form of some construction of an inventory
(`FormMatches`), and words are licensed lexically. A node is licensed by the form of one
construction alone, without the constraints it inherits from the constructions above it in a
network.

Matching reads each word's form, part of speech and features off the token itself. A `headed`
filler is checked against the immediate daughters, a flat approximation of headedness, and a
`semantic` filler, which the form cannot check, matches anything. Of the slot constraints only
`negMinus` bears on the daughter itself: it rejects a daughter of negative polarity, or one with
such a word among its daughters (`SlotConstraint.Allows`).

## Main declarations

- `SlotFiller.Matches`, `SlotConstraint.Allows`, `Slot.Admits`, `FormMatches`: matching daughters
  against a form
- `LicensedLocally`, `Licenses`: the licensing relation

## References

* [sag-2012]
* [goldberg-1995]
* [kay-fillmore-1999]
-/

@[expose] public section

namespace ConstructionGrammar

open PhraseStructure (Tree)
open Morphology (Word)

/-- A tree is the word of the given form and part of speech. -/
def IsWord (form : String) (cat : UD.UPOS) : Tree Unit Word → Prop
  | .terminal _ w => w.form = form ∧ w.cat = cat
  | _ => False

instance (form : String) (cat : UD.UPOS) : ∀ t, Decidable (IsWord form cat t)
  | .terminal _ w => inferInstanceAs (Decidable (w.form = form ∧ w.cat = cat))
  | RoseTree.node (.terminal _ _) (_ :: _) | RoseTree.node (.phrase _ _) _
  | RoseTree.node (.trace _ _) _ | RoseTree.node (.bind _ _) _ => isFalse id

/-- A tree is a word of negative polarity. -/
def IsNegative : Tree Unit Word → Prop
  | .terminal _ w => w.features .polarity = some .Neg
  | _ => False

instance : DecidablePred IsNegative
  | .terminal _ w => inferInstanceAs (Decidable (w.features .polarity = some .Neg))
  | RoseTree.node (.terminal _ _) (_ :: _) | RoseTree.node (.phrase _ _) _
  | RoseTree.node (.trace _ _) _ | RoseTree.node (.bind _ _) _ => isFalse id

/-- A daughter fills a fixed slot when it is a word of that form, an open slot when it is a word of
its part of speech, a phrasal slot when it is any phrase, a projection or an adjunction structure, and a
headed slot when it is a constituent with its head word, of its part of speech, among the daughters.
-/
def SlotFiller.Matches : SlotFiller String → Tree Unit Word → Prop
  | .fixed f, .terminal _ w => w.form = f
  | .open_ c, .terminal _ w => w.cat = c
  | .phrasal, .phrase _ _ _ => True
  | .headed h c, .phrase _ _ ts => ∃ t ∈ ts, IsWord h c t
  | .semantic _, _ => True
  | _, _ => False

instance : ∀ (f : SlotFiller String) (t : Tree Unit Word), Decidable (f.Matches t)
  | .fixed f, .terminal _ w => inferInstanceAs (Decidable (w.form = f))
  | .open_ c, .terminal _ w => inferInstanceAs (Decidable (w.cat = c))
  | .phrasal, .phrase _ _ _ => isTrue trivial
  | .headed h c, .phrase _ _ ts => inferInstanceAs (Decidable (∃ t ∈ ts, IsWord h c t))
  | .semantic _, _ => isTrue trivial
  | .fixed _, RoseTree.node (.terminal _ _) (_ :: _) | .fixed _, RoseTree.node (.phrase _ _) _
  | .fixed _, RoseTree.node (.trace _ _) _ | .fixed _, RoseTree.node (.bind _ _) _
  | .open_ _, RoseTree.node (.terminal _ _) (_ :: _) | .open_ _, RoseTree.node (.phrase _ _) _
  | .open_ _, RoseTree.node (.trace _ _) _ | .open_ _, RoseTree.node (.bind _ _) _
  | .phrasal, RoseTree.node (.terminal _ _) _ | .phrasal, RoseTree.node (.trace _ _) _
  | .phrasal, RoseTree.node (.bind _ _) _
  | .headed _ _, RoseTree.node (.terminal _ _) _ | .headed _ _, RoseTree.node (.trace _ _) _
  | .headed _ _, RoseTree.node (.bind _ _) _ => isFalse id

/-- A daughter respects a slot constraint. `negMinus` forbids negative polarity, on the daughter
or on a word among its daughters; `locMinus` and `refEmpty` concern the slot's external syntax
and semantics and are not checkable against the daughter itself. -/
def SlotConstraint.Allows : SlotConstraint → Tree Unit Word → Prop
  | .negMinus, .terminal _ w => w.features .polarity ≠ some .Neg
  | .negMinus, .phrase _ _ ts => ∀ t ∈ ts, ¬ IsNegative t
  | _, _ => True

instance : ∀ (c : SlotConstraint) (t : Tree Unit Word), Decidable (c.Allows t)
  | .negMinus, .terminal _ w => inferInstanceAs (Decidable (w.features .polarity ≠ some .Neg))
  | .negMinus, .phrase _ _ ts => inferInstanceAs (Decidable (∀ t ∈ ts, ¬ IsNegative t))
  | .negMinus, RoseTree.node (.terminal _ _) (_ :: _) | .negMinus, RoseTree.node (.trace _ _) _
  | .negMinus, RoseTree.node (.bind _ _) _ | .locMinus, _ | .refEmpty, _ => isTrue trivial

/-- A daughter instantiates a slot when it fills the slot and respects its constraints. -/
def Slot.Admits (s : Slot String) (t : Tree Unit Word) : Prop :=
  s.filler.Matches t ∧ ∀ c ∈ s.constraints, c.Allows t

instance (s : Slot String) (t : Tree Unit Word) : Decidable (s.Admits t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A daughter sequence instantiates a typed form, slot by slot. -/
def FormMatches (form : TypedForm String) (ts : List (Tree Unit Word)) : Prop :=
  List.Forall₂ Slot.Admits form ts

instance (form : TypedForm String) (ts : List (Tree Unit Word)) :
    Decidable (FormMatches form ts) :=
  inferInstanceAs (Decidable (List.Forall₂ _ form ts))

variable {Sem : Type*} (cxns : List (Construction Sem))

/-- A node is licensed locally when a word, or when its daughters instantiate the form of some
construction of the inventory; traces and binders are not. -/
def LicensedLocally : Tree Unit Word → Prop
  | .terminal _ _ => True
  | .phrase _ _ ts => ∃ c ∈ cxns, FormMatches c.form ts
  | _ => False

instance : ∀ t : Tree Unit Word, Decidable (LicensedLocally cxns t)
  | .terminal _ _ => isTrue trivial
  | .phrase _ _ ts => inferInstanceAs (Decidable (∃ c ∈ cxns, FormMatches c.form ts))
  | RoseTree.node (.terminal _ _) (_ :: _) | RoseTree.node (.trace _ _) _
  | RoseTree.node (.bind _ _) _ => isFalse id

/-- The inventory licenses a tree when every constituent in it is licensed locally. -/
def Licenses (t : Tree Unit Word) : Prop := ∀ s ∈ t.subtrees, LicensedLocally cxns s

instance (t : Tree Unit Word) : Decidable (Licenses cxns t) :=
  inferInstanceAs (Decidable (∀ s ∈ t.subtrees, _))

end ConstructionGrammar
