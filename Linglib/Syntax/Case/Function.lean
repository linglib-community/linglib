module

public import Linglib.Syntax.Feature.Case.Spatial
public import Linglib.Syntax.Clause.Alignment
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Functions of cases and adpositions

A case or an adposition marks a noun phrase for a *function* in the clause, such as recipient,
instrument or goal of motion. The cases of two languages rarely match, but their functions can be
compared. For example, the datives of two languages are compared by listing the functions that
each one covers.

This file defines the functions and the set of functions that a comparative case value is named
for. Not every function is a semantic role. The core arguments are the coding roles S, A and P,
and the predicative possessor and the passive agent belong to particular constructions.

## Main definitions

* `Case.Function`: the functions.
* `Case.Function.kind`: the type of case a function belongs to.
* `Case.functions`: the functions a case value is named for.
* `Locative.ofFunction`: the locative of a spatial function.

## Main results

* `Case.isMarker_roles_functions`: the four core case values are named for roles that satisfy
  the definitions of their markers.

## Implementation notes

The recipient is the role `R`: the recipient of a transfer verb, together with whatever is coded
like it. The general map of case functions of [malchukov-narrog-2009] also places A, P, T and R
beside the instrument, the beneficiary and the possessor.

A spatial function is a direction with or without a configuration. These are the two dimensions
of a system of spatial cases, and a system with a single series leaves the configuration
unspecified.

A function with no name of its own has the name of its case value, as `essive` does. The labels
of the peripheral cases are close enough to semantic roles for this.

`Case.functions` gives only the positive half of a name. A case called nominative must also leave
P unmarked, which is a fact about the other cases of its language. See
`Alignment.IsNominativeMarker`. The allative and the ablative are named for the goal and the
source with no configuration, and also for the goal and the source of the exterior, as in the
Uralic series. A language file states which of these its case has. The oblique is named for no
function.

## References

* [haspelmath-2003]
* [haspelmath-2009]
* [malchukov-narrog-2009]
* [creissels-2009]
* [haspelmath-2010]
* [haspelmath-2011]
* [haspelmath-2022]
-/

@[expose] public section

namespace Case

open Locative


/-- The functions a case or an adposition marks, the nodes of [haspelmath-2003]'s maps of dative
and of instrumental functions among them. -/
inductive Function where
  /-- A core argument or an object of a transfer verb, the recipient as `R`. -/
  | argument (r : ArgumentRole)
  /-- Location at a place, or motion to, from or past it, in a configuration of it or in none. -/
  | spatial (l : Option Configuration) (d : Direction)
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

/-- The configuration of a spatial function. -/
def configuration? : Function → Option Configuration
  | spatial l _ => l
  | _ => none

/-- The mode of a spatial function: a terminative path for the terminative, and the basic mode
of its direction otherwise. -/
def mode? : Function → Option Mode
  | spatial _ d => some d.mode
  | terminative => some (.directional .terminative)
  | _ => none

/-- The locative of a function, its configuration and the mode of its path, static where it has
no path. -/
def _root_.Locative.ofFunction (f : Function) : Locative :=
  { configuration := f.configuration?, mode := f.mode?.getD .static }

/-- The type of case a function belongs to: the arguments, the possessor, the partitive and the
vocative to the grammatical cases, as `Case.kind` has their values. -/
def kind : Function → Kind
  | argument _ | possessor | partitive | vocative => .grammatical
  | spatial _ _ | terminative => .spatial
  | _ => .semantic

/-- The pairs of a configuration and a direction among a set of functions. -/
def cells (fs : Finset Function) : Finset (Configuration × Direction) :=
  Finset.univ.filter fun p ↦ spatial (some p.1) p.2 ∈ fs

@[simp] theorem mem_cells {fs : Finset Function} {p : Configuration × Direction} :
    p ∈ cells fs ↔ spatial (some p.1) p.2 ∈ fs := by
  simp [cells]

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
  | all => {.spatial none .goal, .spatial (some .exterior) .goal}
  | abl => {.spatial none .source, .spatial (some .exterior) .source}
  | c => (c.dirOf.map (.spatial c.configurationOf)).toFinset

/-- A value is named for functions of its direction. -/
theorem direction?_eq_dirOf_of_mem_functions (c : Case) :
    ∀ f ∈ c.functions, f.direction? = c.dirOf := by
  cases c <;> simp [functions, Function.direction?, dirOf, configurationOf]

/-- A value is named for functions of the shape of its path. -/
theorem mode?_eq_of_mem_functions (c : Case) : ∀ f ∈ c.functions, f.mode? = c.mode? := by
  cases c <;> simp [functions, Function.mode?, mode?, dirOf, configurationOf]

/-- A value is named for functions of its type. -/
theorem kind_eq_of_mem_functions (c : Case) : ∀ f ∈ c.functions, f.kind = c.kind := by
  cases c <;> simp [functions, Function.kind, kind, dirOf, configurationOf]

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
