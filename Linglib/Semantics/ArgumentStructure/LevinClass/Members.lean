module

public import Linglib.Data.VerbClasses.Levin1993

/-!
# The member lists of the Levin classes

`LevinClass.entry` is a class's page in Part II of Levin's *English Verb Classes and Alternations*,
generated from the catalogue in `Data/VerbClasses/Levin1993`. `LevinClass.members` are a class's
members by citation form, and `LevinClass.ofNumberString?` reads a section number as the book prints
it, as the rows of `Data/Examples` record it.

## References

* [levin-1993]
-/

@[expose] public section

namespace ArgumentStructure.LevinClass

/-- The class's members by citation form. -/
def members (c : LevinClass) : List String := (entry c).members

/-- The members the book marks with a question mark. -/
def doubtfulMembers (c : LevinClass) : List String := (entry c).doubtful

/-- The class whose section number the book prints as `s`. -/
def ofNumberString? (s : String) : Option LevinClass :=
  LevinClass.enumList.find? fun c ↦ (entry c).number = s

end ArgumentStructure.LevinClass
