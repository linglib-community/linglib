/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Numeral.Basic

/-!
# English numerals

English counts with the digits *one* to *nine* and builds its higher numerals on the multipliers
*ten*, which appears as *-ty* and *-teen*, *hundred*, *thousand* and *million*. *Eleven* and
*twelve* are single words that continue the counting sequence past *ten*.

## References

* [hurford-1975]
* [hurford-2007]
-/

@[expose] public section

namespace English.Numerals

/-- *one*. -/
def one : Numeral := ⟨"one", 1⟩

/-- *two*. -/
def two : Numeral := ⟨"two", 2⟩

/-- *three*. -/
def three : Numeral := ⟨"three", 3⟩

/-- *four*. -/
def four : Numeral := ⟨"four", 4⟩

/-- *five*. -/
def five : Numeral := ⟨"five", 5⟩

/-- *six*. -/
def six : Numeral := ⟨"six", 6⟩

/-- *seven*. -/
def seven : Numeral := ⟨"seven", 7⟩

/-- *eight*. -/
def eight : Numeral := ⟨"eight", 8⟩

/-- *nine*. -/
def nine : Numeral := ⟨"nine", 9⟩

/-- *ten*, the multiplier of *twenty* to *ninety*. -/
def ten : Numeral := ⟨"ten", 10⟩

/-- *eleven*. -/
def eleven : Numeral := ⟨"eleven", 11⟩

/-- *twelve*. -/
def twelve : Numeral := ⟨"twelve", 12⟩

/-- *hundred*. -/
def hundred : Numeral := ⟨"hundred", 100⟩

/-- *thousand*. -/
def thousand : Numeral := ⟨"thousand", 1000⟩

/-- *million*. -/
def million : Numeral := ⟨"million", 1000000⟩

/-- The digits in counting order. -/
def digits : List Numeral := [one, two, three, four, five, six, seven, eight, nine]

/-- The multipliers. -/
def multipliers : List Numeral := [ten, hundred, thousand, million]

end English.Numerals
