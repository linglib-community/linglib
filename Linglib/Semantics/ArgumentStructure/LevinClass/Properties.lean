module

public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Semantics.ArgumentStructure.LevinClass.Alternation

/-!
# The property tables of the Levin classes

`LevinClass.properties` is the property table of a class's entry in Part II of Levin's *English
Verb Classes and Alternations*: each line names an alternation of Part One by its section number,
or a further property, with the mark the book puts before it, the members it applies to and any
further qualifier. A line names an alternation (`PropertyLine.Names`) by its number, and stars it
(`PropertyLine.Stars`) when it carries an asterisk and names it or a section grouping it, a prefix
of its number. A class shows an alternation (`LevinClass.Participates`) when a line names it
unmarked, lacks it (`LevinClass.Stars`) when a line stars it, and tests it (`LevinClass.Tests`)
when it does either; a line speaks for a member when its scope applies to it.

## Implementation notes

* A starred family heading, such as "*Causative Alternations", denies each of the family's
  subsections, so a line stars every alternation whose number its own number begins. An attested
  family heading is entered as the subsection whose Part One list carries the class, so
  `Participates` reads the lines as they stand.
* A heading phrased as a denial ("not available", "not possible") is the alternation starred.
* A class may list related alternations under different bases: the spray/load class attests the
  other causative alternations of its locative variant and stars the causative alternations of its
  *with* variant, so `Participates` and `Stars` are not disjoint, and the qualifiers tell the lines
  apart.

## References

* [levin-1993]
-/

@[expose] public section

namespace Data.VerbClasses.PropertyLine

open ArgumentStructure

variable (l : PropertyLine) (a : DiathesisAlternation)

/-- The alternation of Part One a property line names, if it names one. -/
def alternation? : Option DiathesisAlternation :=
  l.heading.number? >>= DiathesisAlternation.ofNumber?

/-- The line names the alternation by its section number. -/
def Names : Prop := l.heading = .alternation a.number

instance : Decidable (l.Names a) := inferInstanceAs (Decidable (_ = _))

/-- The line stars the alternation: it carries an asterisk and names the alternation or a section
grouping it. -/
def Stars : Prop := l.judgment = .ungrammatical ∧ ∃ n ∈ l.heading.number?, n <+: a.number

instance : Decidable (l.Stars a) := inferInstanceAs (Decidable (_ ∧ ∃ _ ∈ _, _))

end Data.VerbClasses.PropertyLine

namespace ArgumentStructure.LevinClass

open Data.VerbClasses

/-- The property table of the class's entry, in the book's order. -/
def properties (c : LevinClass) : List PropertyLine := (entry c).properties

/-- The class's table names the alternation with the mark `j`. -/
def Lists (c : LevinClass) (a : DiathesisAlternation) (j : Judgment) : Prop :=
  ∃ l ∈ c.properties, l.Names a ∧ l.judgment = j

instance (c : LevinClass) (a : DiathesisAlternation) (j : Judgment) : Decidable (c.Lists a j) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The class shows the alternation when its table names it unmarked. -/
def Participates (c : LevinClass) (a : DiathesisAlternation) : Prop := c.Lists a .acceptable

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Participates a) :=
  inferInstanceAs (Decidable (c.Lists a .acceptable))

/-- The class lacks the alternation when a line of its table stars it. -/
def Stars (c : LevinClass) (a : DiathesisAlternation) : Prop := ∃ l ∈ c.properties, l.Stars a

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Stars a) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The class's table tests the alternation, attesting or starring it. -/
def Tests (c : LevinClass) (a : DiathesisAlternation) : Prop := c.Participates a ∨ c.Stars a

instance (c : LevinClass) (a : DiathesisAlternation) : Decidable (c.Tests a) :=
  inferInstanceAs (Decidable (_ ∨ _))

end ArgumentStructure.LevinClass
