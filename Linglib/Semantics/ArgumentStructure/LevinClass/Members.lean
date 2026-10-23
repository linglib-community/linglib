module

public import Linglib.Semantics.ArgumentStructure.LevinClass.Basic
public import Linglib.Data.VerbClasses.Levin1993

/-!
# The member lists of the Levin classes

`LevinClass.entry` is a class's entry in Part II of Levin's *English Verb Classes and
Alternations*, read from `Data/VerbClasses/Levin1993`, whose classes come in the book's order, the
order of the constructors of `LevinClass` (`number_entry`). `LevinClass.members` are a class's
members by citation form, and `LevinClass.classesOf` the classes whose lists carry a form. An
English verb entry's `levinClasses` are the classes listing its form, less those that list it in a
sense the entry does not have, and `scripts/check_levin_classes.py` checks every entry in CI.

## References

* [levin-1993]
-/

@[expose] public section

namespace ArgumentStructure.LevinClass

open Data.VerbClasses

/-- The class's entry in Part II. -/
def entry (c : LevinClass) : VerbClass := Levin1993.classes.getD c.ctorIdx default

private theorem numbers_eq :
    Levin1993.classes.map (·.number) = LevinClass.enumList.map numberString := by
  decide +kernel

theorem number_entry (c : LevinClass) : (entry c).number = c.numberString := by
  have h := congrArg (·[c.ctorIdx]?) numbers_eq
  simp only [List.getElem?_map, LevinClass.enumList_getElem?_ctorIdx_eq, Option.map_some] at h
  obtain ⟨e, he, hn⟩ := Option.map_eq_some_iff.mp h
  rw [entry, List.getD_eq_getElem?_getD, he, Option.getD_some, hn]

/-- The class's members by citation form. -/
def members (c : LevinClass) : List String := (entry c).members

/-- The members the book marks with a question mark. -/
def doubtfulMembers (c : LevinClass) : List String := (entry c).doubtful

/-- The classes whose member lists carry the form. -/
def classesOf (form : String) : Finset LevinClass := Finset.univ.filter (form ∈ members ·)

@[simp] theorem mem_classesOf {form : String} {c : LevinClass} :
    c ∈ classesOf form ↔ form ∈ c.members := by
  simp [classesOf]

end ArgumentStructure.LevinClass
