module

public import Linglib.Syntax.Category.Coordinator

/-!
# Turkish coordinators

Turkish conjoins with the free word *ve* 'and', an Arabic loan, before the second coordinand,
and with the enclitic *de*, *da* by vowel harmony, which follows the first word of the second
coordinand, as in the example Haspelmath cites from Kornfilt. The enclitic is also the additive
particle 'too', `Turkish.FocusParticles.de`. Noun phrases are also conjoined by *-(y)lA*, the
comitative postposition 'with'. As a conjunction it attaches to the first conjunct, the two make a
constituent that cannot be broken up, and as a subject they take plural agreement; as a
postposition it follows the second noun phrase, which moves freely, and the verb agrees with the
subject alone, as Kornfilt (§1.3.1.4) and Göksel and Kerslake (§12.2.2.4, §28.3.1.1) describe.

## Main definitions

* `Turkish.Coordination.ve`, `Turkish.Coordination.de`, `Turkish.Coordination.ile`: the
  conjunctive coordinator, the additive enclitic and the comitative enclitic.

## References

* [goksel-kerslake-2005]
* [haspelmath-2007]
* [kornfilt-1997]
-/

@[expose] public section

namespace Turkish.Coordination

/-- *ve* 'and'. -/
def ve : Coordinator :=
  { morph := .free "ve", gloss := "and", role := .conjunctive }

/-- *de* 'and', enclitic in the second coordinand, also the additive particle
`Turkish.FocusParticles.de`. -/
def de : Coordinator :=
  { morph := .encl "de", gloss := "and", role := .conjunctive }

/-- *-(y)lA* 'and', enclitic on the first of two noun phrases; also the comitative postposition
`Turkish.Adpositions.ile`. -/
def ile : Coordinator :=
  { morph := .encl "(y)lA", gloss := "and", role := .conjunctive }

/-- The coordinators. -/
def allEntries : List Coordinator := [ve, de, ile]

end Turkish.Coordination
