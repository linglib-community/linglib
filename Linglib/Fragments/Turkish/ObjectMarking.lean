module

public import Linglib.Semantics.Reference.Definiteness

/-!
# Turkish object marking

This file defines the differential marking of the Turkish direct object as Göksel and Kerslake
describe it. The accusative suffix *-(y)I* is obligatory on a definite direct object and on a
specific indefinite one, partitives and possessive-marked objects among them, and absent on a
non-specific indefinite, which must then stand immediately before the verb; an indefinite object
elsewhere in the clause takes the suffix. Which kind of specificity the suffix tracks is debated:
Enç takes it to be partitivity, while von Heusinger, Kornfilt and Kizilkaya find the marking
orthogonal to partitivity and tied to scopal specificity. The pattern is the continuum of
definiteness cut at the specific indefinites, with no animacy dimension.

## Main definitions

* `Turkish.ObjectMarking.accusative`: the marked objects, the degrees of definiteness from the
  specific indefinites up
* `Turkish.ObjectMarking.MustBePreverbal`: the degrees of definiteness whose objects, being
  unmarked, stand immediately before the verb

## Main results

* `Turkish.ObjectMarking.mustBePreverbal_iff`: only a non-specific indefinite is confined to
  the preverbal position

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [J. Aissen, *Differential Object Marking: Iconicity vs. Economy* (2003)][aissen-2003]
* [K. von Heusinger, J. Kornfilt and S. Kizilkaya, *Differential Object Marking, Partitivity and
  Specificity in Turkish* (2019)][von-heusinger-et-al-2019]
-/

@[expose] public section

namespace Turkish.ObjectMarking

/-- The accusative marks a direct object that is definite or a specific indefinite, whatever its
animacy. -/
def accusative : Set DefinitenessDegree := Set.Ici .specific

instance : DecidablePred (· ∈ accusative) := fun d ↦
  inferInstanceAs (Decidable (d ∈ Set.Ici _))

/-- An object must stand immediately before the verb when it is unmarked. -/
def MustBePreverbal (d : DefinitenessDegree) : Prop := d ∉ accusative

instance : DecidablePred MustBePreverbal := fun d ↦ inferInstanceAs (Decidable (d ∉ accusative))

theorem mustBePreverbal_iff (d : DefinitenessDegree) : MustBePreverbal d ↔ d = .nonSpecific := by
  cases d <;> decide

end Turkish.ObjectMarking
