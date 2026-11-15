module

public import Linglib.Syntax.Case.Spatial
public import Linglib.Syntax.Clause.Alignment
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Functions of cases and adpositions

A case or an adposition marks its noun phrase for some of the functions the noun phrase can have in
a clause, and the functions, unlike the cases, are the same from language to language. Haspelmath
compares the datives and the instrumentals of different languages by the functions they cover.
The functions are not all semantic roles: the core arguments are the coding roles S, A and P, and
the predicative possessor and the passive agent are tied to a construction. A comparative case
value is named for functions, and [the four core values are named for roles that meet the
definitions of their markers](##Case.isMarker_roles_functions).

## Implementation notes

The recipient is the role `R`, the recipient of a transfer verb together with what is coded like
it. A spatial function is a direction with or without a localization. Functions with no name of
their own in the sources read carry the name of the case value, as `essive`.

`Case.functions` gives the positive half of a name: a case called nominative also has to leave P
unmarked, which is a fact about the other cases of its language (`Alignment.IsNominativeMarker`).
It names the allative and the ablative for the goal and the source with no localization, their
general use, and the oblique for no function.

## References

* [haspelmath-2003]
* [haspelmath-2010]
* [haspelmath-2011]
* [haspelmath-2022]
-/

@[expose] public section

namespace Case

open Spatial (Localization)
open Spatial.Path (Direction)

/-- The functions a case or an adposition marks, the nodes of [haspelmath-2003]'s maps of dative
and of instrumental functions among them. -/
inductive Function where
  /-- A core argument or an object of a transfer verb, the recipient as `R`. -/
  | argument (r : ArgumentRole)
  /-- Location at a place, or motion to, from or past it, in a localization of it or in none. -/
  | spatial (l : Option Localization) (d : Direction)
  /-- The limit a motion or a time reaches (*as far as*, *until*). -/
  | terminative
  /-- The possessor in a noun phrase (*Adam's apple*). -/
  | possessor
  /-- The possessor as a predicate (French *Ce chien est à moi* 'This dog is mine'). -/
  | predicativePossessor
  /-- The possessor coded as a dependent of the verb (French *On lui a cassé la jambe* 'They
  broke his leg'). -/
  | externalPossessor
  /-- The experiencer of a mental state (*This seems outrageous to me*). -/
  | experiencer
  /-- The one for whose benefit the action is done (*I'll buy a bike for you*). -/
  | beneficiary
  /-- The one in whose judgment a property holds, the *dativus judicantis* (German *Das ist mir
  zu warm* 'That's too warm for me'). -/
  | judicantis
  /-- The purpose of an action (*I left early to get home in time*). -/
  | purpose
  /-- The cause of a situation (*because of the mosquitoes*). -/
  | cause
  /-- The instrument of an action (*with a nutcracker*). -/
  | instrumental
  /-- The companion (*with Don Quijote*). -/
  | comitative
  /-- A companion that takes active part in the action (*fought with Y*). -/
  | coAgent
  /-- The second of two coordinated noun phrases (Nkore-Kiga *emeeza n'entebe* 'a table and a
  chair'). -/
  | conjunctive
  /-- The agent of a passive (*bitten by dogs*). -/
  | passiveAgent
  /-- The time of a situation. -/
  | temporal
  /-- The standard of a comparison (*than X*). -/
  | comparative
  /-- A temporary state or capacity (*as an X*). -/
  | essive
  /-- The state changed into (*into an X*). -/
  | translative
  /-- What the situation lacks (*without X*). -/
  | abessive
  /-- A part or an indeterminate quantity of the referent. -/
  | partitive
  /-- The addressee called. -/
  | vocative
  deriving DecidableEq, Repr, Fintype

namespace Function

/-- The direction of a spatial function, the goal for the terminative. -/
def direction? : Function → Option Direction
  | spatial _ d => some d
  | terminative => some .goal
  | _ => none

/-- The argument roles among a set of functions. -/
def roles (fs : Finset Function) : Set ArgumentRole := {r | argument r ∈ fs}

@[simp] theorem mem_roles {fs : Finset Function} {r : ArgumentRole} :
    r ∈ roles fs ↔ argument r ∈ fs := Iff.rfl

end Function

/-- The functions a comparative case value is named for. -/
def functions : Case → Finset Function
  | nom => {.argument .S, .argument .A}
  | acc => {.argument .P}
  | erg => {.argument .A}
  | abs => {.argument .S, .argument .P}
  | obl => ∅
  | dat => {.argument .R}
  | gen => {.possessor}
  | voc => {.vocative}
  | part => {.partitive}
  | inst => {.instrumental}
  | com => {.comitative}
  | ben => {.beneficiary}
  | caus => {.cause}
  | purp => {.purpose}
  | tem => {.temporal}
  | cmpr => {.comparative}
  | ess => {.essive}
  | transl => {.translative}
  | abess => {.abessive}
  | ter => {.terminative}
  | all => {.spatial none .goal}
  | abl => {.spatial none .source}
  | c => (c.dirOf.map (.spatial c.localizationOf)).toFinset

/-- A spatial value is named for functions of its direction. -/
theorem direction?_eq_dirOf_of_mem_functions (c : Case) :
    ∀ f ∈ c.functions, f.direction? = c.dirOf := by
  cases c <;> simp [functions, Function.direction?, dirOf, localizationOf]

open Alignment in
/-- The four core values are named for roles that meet [haspelmath-2022]'s definitions of the
nominative, accusative, ergative and absolutive markers. -/
theorem isMarker_roles_functions :
    IsNominativeMarker (Function.roles nom.functions) ∧
      IsAccusativeMarker (Function.roles acc.functions) ∧
      IsErgativeMarker (Function.roles erg.functions) ∧
      IsAbsolutiveMarker (Function.roles abs.functions) := by
  simp [IsNominativeMarker, IsAccusativeMarker, IsErgativeMarker, IsAbsolutiveMarker, functions]

end Case
