module

public import Linglib.Syntax.Case.Spatial
public import Linglib.Syntax.Clause.Alignment
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Functions of cases and adpositions

A case or an adposition marks its noun phrase for some of the functions the noun phrase can have in
a clause, and the functions, unlike the cases, are the same from language to language. Haspelmath
compares the datives and the instrumentals of different languages by the functions they cover, and
a comparative case value is named for functions: the nominative for S and A, the dative for the
recipient. So the names of the core values record an alignment, and [a marking of S, A and P by
values named for them is accusative exactly when S and A are
nominative](##Case.isAccusative_iff_of_mem_functions).

## Implementation notes

The argument functions are the comparative roles `ArgumentRole`, the recipient among them as `R`.
A spatial function is a direction with or without a localization, so Haspelmath's direction and
source are `spatial none .goal` and `spatial none .source`. Functions with no name of their own in
the sources read carry the name of the case value, as `essive`. `Case.functions` names the
allative and the ablative for the goal and the source with no localization, their general use;
the exterior series of the Finnic languages is stated by the fragment. The oblique is named for no
function.

## References

* [haspelmath-2003]
* [haspelmath-2010]
* [haspelmath-2011]
* [blake-2001]
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

/-- A spatial function locates or directs, with or without a limit. -/
def IsSpatial (f : Function) : Prop := f.direction?.isSome

instance : DecidablePred IsSpatial := fun f ↦ inferInstanceAs (Decidable (f.direction?.isSome))

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
  | loc => {.spatial none .place}
  | all => {.spatial none .goal}
  | abl => {.spatial none .source}
  | perl => {.spatial none .route}
  | ine => {.spatial (some .interior) .place}
  | ill => {.spatial (some .interior) .goal}
  | ela => {.spatial (some .interior) .source}
  | sup => {.spatial (some .surface) .place}
  | sub => {.spatial (some .surface) .goal}
  | del => {.spatial (some .surface) .source}
  | ade => {.spatial (some .exterior) .place}

/-- A spatial value is named for functions of its direction. -/
theorem direction?_eq_dirOf_of_mem_functions (c : Case) :
    ∀ f ∈ c.functions, f.direction? = c.dirOf := by
  cases c <;> simp [functions, Function.direction?, dirOf]

/-- The values named for spatial functions are the spatial ones. -/
theorem exists_isSpatial_mem_functions_iff (c : Case) :
    (∃ f ∈ c.functions, f.IsSpatial) ↔ c.kind = .spatial := by
  cases c <;> decide

/-! ### The core values and alignment -/

theorem argument_S_mem_functions_iff {c : Case} :
    .argument .S ∈ c.functions ↔ c = nom ∨ c = abs := by
  cases c <;> decide

theorem argument_A_mem_functions_iff {c : Case} :
    .argument .A ∈ c.functions ↔ c = nom ∨ c = erg := by
  cases c <;> decide

theorem argument_P_mem_functions_iff {c : Case} :
    .argument .P ∈ c.functions ↔ c = acc ∨ c = abs := by
  cases c <;> decide

section Alignment

variable {m : ArgumentRole → Case} (h : ∀ r ∈ ArgumentRole.core, .argument r ∈ (m r).functions)
include h

/-- A marking of S, A and P by values named for them is accusative exactly when S and A are
nominative. -/
theorem isAccusative_iff_of_mem_functions : Alignment.IsAccusative m ↔ m .S = nom ∧ m .A = nom := by
  have hS := argument_S_mem_functions_iff.1 (h .S (by simp))
  have hA := argument_A_mem_functions_iff.1 (h .A (by simp))
  have hP := argument_P_mem_functions_iff.1 (h .P (by simp))
  unfold Alignment.IsAccusative
  rcases hS with hS | hS <;> rcases hA with hA | hA <;> rcases hP with hP | hP <;>
    simp [hS, hA, hP]

/-- A marking of S, A and P by values named for them is ergative exactly when S and P are
absolutive. -/
theorem isErgative_iff_of_mem_functions : Alignment.IsErgative m ↔ m .S = abs ∧ m .P = abs := by
  have hS := argument_S_mem_functions_iff.1 (h .S (by simp))
  have hA := argument_A_mem_functions_iff.1 (h .A (by simp))
  have hP := argument_P_mem_functions_iff.1 (h .P (by simp))
  unfold Alignment.IsErgative
  rcases hS with hS | hS <;> rcases hA with hA | hA <;> rcases hP with hP | hP <;>
    simp [hS, hA, hP]

/-- No value is named for S, A and P together, or for A and P apart from S, so a marking by
values named for the roles is accusative, ergative or tripartite. -/
theorem not_isNeutral_of_mem_functions : ¬ Alignment.IsNeutral m := by
  have hS := argument_S_mem_functions_iff.1 (h .S (by simp))
  have hA := argument_A_mem_functions_iff.1 (h .A (by simp))
  have hP := argument_P_mem_functions_iff.1 (h .P (by simp))
  unfold Alignment.IsNeutral
  rcases hS with hS | hS <;> rcases hA with hA | hA <;> rcases hP with hP | hP <;>
    simp [hS, hA, hP]

theorem not_isHorizontal_of_mem_functions : ¬ Alignment.IsHorizontal m := by
  have hA := argument_A_mem_functions_iff.1 (h .A (by simp))
  have hP := argument_P_mem_functions_iff.1 (h .P (by simp))
  unfold Alignment.IsHorizontal
  rcases hA with hA | hA <;> rcases hP with hP | hP <;> simp [hA, hP]

end Alignment

end Case
