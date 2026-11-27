/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Numeral.Basic

/-!
# Welsh numerals

The numerals of the Welsh Bible are built from fifteen words: the digits *un* to *naw*, *deg*
'ten', *deuddeg* 'twelve', *pymtheg* 'fifteen', *ugain* 'twenty', *cant* 'hundred' and *mil*
'thousand'. The words are given in their unmutated forms. The system counts in twenties, with
the numbers from sixteen to nineteen added to *pymtheg*.

## References

* [hurford-1975]
-/

@[expose] public section

namespace Welsh.Numerals

/-- *un* 'one'. -/
def un : Numeral := ⟨"un", 1⟩

/-- *dau* 'two'. -/
def dau : Numeral := ⟨"dau", 2⟩

/-- *tri* 'three'. -/
def tri : Numeral := ⟨"tri", 3⟩

/-- *pedwar* 'four'. -/
def pedwar : Numeral := ⟨"pedwar", 4⟩

/-- *pump* 'five'. -/
def pump : Numeral := ⟨"pump", 5⟩

/-- *chwech* 'six'. -/
def chwech : Numeral := ⟨"chwech", 6⟩

/-- *saith* 'seven'. -/
def saith : Numeral := ⟨"saith", 7⟩

/-- *wyth* 'eight'. -/
def wyth : Numeral := ⟨"wyth", 8⟩

/-- *naw* 'nine'. -/
def naw : Numeral := ⟨"naw", 9⟩

/-- *deg* 'ten'. -/
def deg : Numeral := ⟨"deg", 10⟩

/-- *deuddeg* 'twelve'. -/
def deuddeg : Numeral := ⟨"deuddeg", 12⟩

/-- *pymtheg* 'fifteen'. -/
def pymtheg : Numeral := ⟨"pymtheg", 15⟩

/-- *ugain* 'twenty'. -/
def ugain : Numeral := ⟨"ugain", 20⟩

/-- *cant* 'hundred'. -/
def cant : Numeral := ⟨"cant", 100⟩

/-- *mil* 'thousand'. -/
def mil : Numeral := ⟨"mil", 1000⟩

/-- The digits in counting order. -/
def digits : List Numeral := [un, dau, tri, pedwar, pump, chwech, saith, wyth, naw]

/-- The multipliers. -/
def multipliers : List Numeral := [deg, pymtheg, ugain, cant, mil]

end Welsh.Numerals
