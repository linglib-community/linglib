module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Fragments.Bantu.Params

/-!
# Shona noun classes

This file defines the Shona noun-class system: the fourteen classes with their subject markers,
the eight genders that pair a singular class with its plural, two of them sharing a plural
class, and the semantic core each gender bears ([carstens-2026]).

## References

* [carstens-2026]
-/

@[expose] public section

namespace Shona

open Bantu

/-! ### Classes -/

/-- The subject marker of a class on the verb; classes 15–18 are absent or unproductive. -/
def subjPrefix : NounClass → Option String
  | .cl1 => some "a"     -- noun prefix mu-: murume 'man'
  | .cl2 => some "va"    -- va-: varume 'men'
  | .cl3 => some "u"     -- mu-: muti 'tree'
  | .cl4 => some "i"     -- mi-: miti 'trees'
  | .cl5 => some "ri"    -- ri-, often unprefixed: zai 'egg'
  | .cl6 => some "a"     -- ma-: mazai 'eggs'
  | .cl7 => some "chi"   -- chi-: chingwa 'bread'
  | .cl8 => some "zvi"   -- zvi-: zvingwa 'loaves'
  | .cl9 => some "i"     -- n-: imbwa 'dog'
  | .cl10 => some "dzi"  -- n-, dzi-: imbwa 'dogs'
  | .cl11 => some "ru"   -- ru-: rukova 'stream'
  | .cl12 => some "ka"   -- ka-, the diminutive singular: kasikana 'small girl'
  | .cl13 => some "tu"   -- tu-, the diminutive plural: tusikana 'small girls'
  | .cl14 => some "hu"   -- hu-, u-: huchi 'honey'
  | _ => none

/-- The classes, those with a subject marker. -/
def classes : Finset NounClass := Finset.univ.filter fun c ↦ (subjPrefix c).isSome

/-! ### Genders -/

/-- The eight genders, each pairing a singular class with its plural; the plurals of classes 11
and 14 are those of classes 9 and 5. -/
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
  /-- Classes 11/10. -/
  | genderF
  /-- Classes 14/6. -/
  | genderG
  /-- Classes 12/13, the diminutives. -/
  | genderH
  deriving DecidableEq, Repr, Fintype

def Gender.singularClass : Gender → NounClass
  | .genderA => .cl1
  | .genderB => .cl3
  | .genderC => .cl5
  | .genderD => .cl7
  | .genderE => .cl9
  | .genderF => .cl11
  | .genderG => .cl14
  | .genderH => .cl12

def Gender.pluralClass : Gender → NounClass
  | .genderA => .cl2
  | .genderB => .cl4
  | .genderC => .cl6
  | .genderD => .cl8
  | .genderE => .cl10
  | .genderF => .cl10
  | .genderG => .cl6
  | .genderH => .cl13

/-- Gender A bears the core [human] and gender D [non-human], the core and default of everything
else; the other six bear none. -/
def Gender.status : Gender → GenderStatus
  | .genderA => .interpretable .human
  | .genderD => .interpretable .nonhuman
  | _ => .uninterpretable

end Shona
