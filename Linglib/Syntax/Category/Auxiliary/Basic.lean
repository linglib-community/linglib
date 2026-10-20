/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Word.Basic
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Semantics.Modality.Basic

/-!
# Auxiliary

An auxiliary verb is an element on the continuum from lexical verb to functional affix that,
somewhat bleached, expresses a verbal category, most often aspect or modality but also tense,
negative polarity or voice, and forms a single clause with a lexical verb. No language-
independent criterion separates it from a lexical verb, so the class is drawn language by
language, English's by the constructions of negation, inversion, code and emphasis.

This file provides the entry of a member of such a class, a word form in the cells it is entered
for with the features those cells share and its register, and the entry of a modal auxiliary,
an auxiliary that is also a modal item, expressing force–flavor pairs. Per-language fragments
supply the entries.

## Main declarations

* `Auxiliary`: the entry.
* `ModalAuxiliary`: the entry of an auxiliary that is a modal item.
* `Auxiliary.toWord`: the `AUX` word it spells out.

## Implementation notes

An entry is a word form, not a lexeme: English *can* and *could* are two entries, as they are
two expressions of modal meaning, and English *were* is two, the preterite and the irrealis. A
syncretic entry, English *are* of the second person and the plurals, carries no person or
number, and the cells it realizes are read off the paradigm that has it.

## References

* [anderson-2006a]
* [huddleston-pullum-2002]
-/

@[expose] public section

open Morphology (Word Features)
open Modality (ModalItem)

/-- An auxiliary: a word form in the cells it is entered for, with the features those cells
share, at a register. -/
structure Auxiliary where
  form : String
  /-- The features the cells of the entry share. -/
  features : Features := ⊥
  register : SocialMeaning.Register := .neutral
  deriving DecidableEq

/-- A modal auxiliary: an auxiliary that is a modal item, with the force–flavor pairs it
expresses. -/
structure ModalAuxiliary extends Auxiliary, ModalItem
  deriving DecidableEq

instance : Coe ModalAuxiliary Auxiliary := ⟨ModalAuxiliary.toAuxiliary⟩

namespace Auxiliary

/-- The `AUX` word an auxiliary spells out. -/
def toWord (a : Auxiliary) : Word := { form := a.form, cat := .AUX, features := a.features }

@[simp] theorem toWord_cat (a : Auxiliary) : a.toWord.cat = .AUX := rfl

end Auxiliary
