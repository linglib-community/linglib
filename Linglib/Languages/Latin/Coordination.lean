module

public import Linglib.Syntax.Category.Coordinator

/-!
# Latin coordinators

Latin conjoins with the free word *et* 'and', before the second coordinand, with the enclitic
*-que*, attached to the first word of the second coordinand as in *senatus populusque*, and with
the emphatic *atque*, *ac* before consonants. *Et* on the first coordinand answered by *-que*
on the second is emphatic, *et singulis universisque* 'both for individuals and for all
together'. The enclitic also builds the universal pronoun *quisque* 'each' on the
interrogative. Disjunction is *aut* or *vel*; negative coordination is *neque*, *nec*, repeated
for 'neither … nor'; and the adversative coordinator is *sed*.

## Main definitions

* `Latin.Coordination.et`, `Latin.Coordination.que`, `Latin.Coordination.atque`: the
  conjunctive coordinators.
* `Latin.Coordination.aut`, `Latin.Coordination.vel`: the disjunctive coordinators.
* `Latin.Coordination.neque`, `Latin.Coordination.sed`: the negative and the adversative
  coordinator.

## References

* [haspelmath-2007]
* [mitrovic-sauerland-2016]
-/

@[expose] public section

namespace Latin.Coordination

/-- *et* 'and'. -/
def et : Coordinator :=
  { morph := .free "et", gloss := "and", role := .conjunctive }

/-- *-que* 'and', enclitic in the second coordinand, also the particle of *quisque* 'each',
`Latin.Determiners.quisque`. -/
def que : Coordinator :=
  { morph := .encl "que", gloss := "and", role := .conjunctive }

/-- *atque*, before consonants *ac*, 'and also'. -/
def atque : Coordinator :=
  { morph := .free "atque", gloss := "and also", role := .conjunctive }

/-- *neque*, *nec* 'and not', repeated for 'neither … nor'. -/
def neque : Coordinator :=
  { morph := .free "neque", gloss := "and not, nor", role := .negative }

/-- *aut* 'or'. -/
def aut : Coordinator :=
  { morph := .free "aut", gloss := "or", role := .disjunctive }

/-- *vel* 'or'. -/
def vel : Coordinator :=
  { morph := .free "vel", gloss := "or", role := .disjunctive }

/-- *sed* 'but'. -/
def sed : Coordinator :=
  { morph := .free "sed", gloss := "but", role := .adversative }

end Latin.Coordination
