module

public import Linglib.Syntax.Category.Coordinator

/-!
# Hindi-Urdu coordinators

Hindi-Urdu coordinates with free words that stand before the last coordinand, as most New
Indo-Aryan languages do. Conjunction is *aur* 'and', *rām, śyām, aur mohan ko* 'to Ram, Shyam,
and Mohan' in Masica's example. Disjunction has two words: *ya:* 'or', in declaratives and in
both yes/no and alternative questions, and *ki* 'or', only in alternative questions. The
adversative coordinator is *par* 'but'.

## Main definitions

* `HindiUrdu.Coordination.aur`: the conjunctive coordinator.
* `HindiUrdu.Coordination.ya`, `HindiUrdu.Coordination.ki`: the general and the
  alternative-question disjunctive coordinator.
* `HindiUrdu.Coordination.par`: the adversative coordinator.

## TODO

The emphatic coordinations, and whether the additive particle *bhii* coordinates when repeated
on each coordinand as Hungarian *is* does, await a reference grammar of Hindi-Urdu; none of the
sources cited here describes them.

## References

* [bhatt-dayal-2020]
* [haspelmath-1997]
* [masica-1991]
-/

@[expose] public section

namespace HindiUrdu.Coordination

/-- *aur* 'and'. -/
def aur : Coordinator :=
  { morph := .free "aur", gloss := "and", role := .conjunctive }

/-- *ya:* 'or', in declaratives and questions; with negation it is the *ya: nahĩ:* 'or not' of
polar alternative questions, `HindiUrdu.Particles.ya_nahi`. -/
def ya : Coordinator :=
  { morph := .free "ya:", gloss := "or", role := .disjunctive }

/-- *ki* 'or' of alternative questions, homophonous with the subordinator
`HindiUrdu.Particles.ki`. -/
def ki : Coordinator :=
  { morph := .free "ki", gloss := "or", role := .disjunctive }

/-- *par* 'but'. -/
def par : Coordinator :=
  { morph := .free "par", gloss := "but", role := .adversative }

end HindiUrdu.Coordination
