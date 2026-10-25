module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Fragments.Bantu.Params

/-!
# Xhosa noun classes

This file defines the Xhosa noun-class system: the eleven classes, by their subject markers,
the five genders that pair a singular class with its plural ([carstens-1991]), and the semantic
core each gender bears ([carstens-2026]).

## References

* [carstens-1991]
* [carstens-2026]
* [taraldsen-et-al-2018]
-/

@[expose] public section

namespace Xhosa

open Bantu

/-! ### Classes -/

/-- The subject marker of a class on the verb; classes 11–14 and 16–18 are absent. -/
def subjPrefix : NounClass → Option String
  | .cl1 => some "u"    -- noun prefix um-, u-: umntu 'person'
  | .cl2 => some "ba"   -- aba-: abantu 'people'
  | .cl3 => some "u"    -- um-: umthi 'tree'
  | .cl4 => some "i"    -- imi-: imithi 'trees'
  | .cl5 => some "li"   -- i-: iqanda 'egg'
  | .cl6 => some "a"    -- ama-: amaqanda 'eggs'
  | .cl7 => some "si"   -- isi-: isitya 'dish'
  | .cl8 => some "zi"   -- izi-: izitya 'dishes'
  | .cl9 => some "i"    -- in-: inja 'dog'
  | .cl10 => some "zi"  -- iin-: iinja 'dogs'
  | .cl15 => some "ku"  -- uku-, the infinitive and gerund class: ukucula 'to sing'
  | _ => none

/-- The classes, those with a subject marker. -/
def classes : Finset NounClass := Finset.univ.filter fun c ↦ (subjPrefix c).isSome

/-! ### Genders -/

/-- The five genders, each pairing a singular class with its plural. -/
inductive Gender where
  /-- Classes 1/2. -/
  | genderA
  /-- Classes 3/4. -/
  | genderB
  /-- Classes 5/6. -/
  | genderC
  /-- Classes 7/8. -/
  | genderD
  /-- Classes 9/10. -/
  | genderE
  deriving DecidableEq, Repr, Fintype

def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9

def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10

theorem Gender.isSome_subjPrefix_pluralClass (g : Gender) : (subjPrefix g.pluralClass).isSome := by
  cases g <;> rfl

/-- The subject marker of a gender's plural class. -/
def Gender.plSubjPrefix (g : Gender) : String :=
  (subjPrefix g.pluralClass).get g.isSome_subjPrefix_pluralClass

/-- Gender A bears the core [human], D [inanimate] and E [animal], while B and C bear
none. -/
def Gender.status : Gender → GenderStatus
  | .genderA => .interpretable .human
  | .genderB => .uninterpretable
  | .genderC => .uninterpretable
  | .genderD => .interpretable .inanimate
  | .genderE => .interpretable .animal

end Xhosa
