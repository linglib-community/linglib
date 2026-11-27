module

public import Linglib.Syntax.Category.Verb.Takes
public import Linglib.Syntax.Voice.Basic
public import Linglib.Syntax.Category.Verb.Deranking

/-!
# Romanian verbs and clause-typers

Romanian marks the mood of a finite complement both on the verb and on the particle that
introduces the clause, *să* with the subjunctive and *că* with the indicative. The attitude and
causative verbs here record the mood each selects in an affirmative declarative clause, the
Romanian data of [grano-2024]'s survey of mood choice: *a vrea* 'want', *a intenționa* 'intend'
and the causative *a face* take *să* and reject *că*, and *a spera* 'hope' takes either.

## Implementation notes

Whether *să* heads C or a mood projection below it is left open, as for Greek *na*; the entry
records only the coding of the clause it introduces.

## References

* [grano-2024]
* [pana-dindelegan-2013]
-/

@[expose] public section

namespace Romanian.Verbs

open ArgumentStructure Morphology

/-! ### Voice -/

/-- The passive of a frame with the auxiliary *fi* 'be' and the participle. -/
def fiPassive (fr : ArgumentFrame := .np) : Voice := (Voice.passive fr).marked [.free "fi"]

/-- The passive of a frame with the reflexive clitic *se*. -/
def sePassive (fr : ArgumentFrame := .np) : Voice :=
  (Voice.passive fr).marked [.procl "se"]

/-! ### Clause-typers -/

/-- *să* introduces a subjunctive clause. -/
def sa : Complementizer where
  morphs := [.free "să"]
  coding := {.subjunctive}

/-- *că* introduces an indicative declarative clause. -/
def ca : Complementizer where
  morphs := [.free "că"]
  coding := {.indicative}
  types := {.declarative}

/-- The clause-typers of finite complements. -/
def complementizers : List Complementizer := [sa, ca]

/-! ### Attitude and causative verbs -/

/-- A finite subjunctive complement, the clause *să* introduces. -/
def saClause : ArgumentFrame := ⟨some .nominal, [.clausal { coding := {.subjunctive} }]⟩

/-- *a vrea* 'want' takes a *să* clause. -/
def a_vrea : Verb where
  morphs := [.free "a", .root "vrea"]
  valency := .ofFrame saClause
  -- with a clause it takes the passive with *se* and not the one with *fi* 'be'
  -- ([pana-dindelegan-2013] §3.4.1.1)
  voices := [(fiPassive saClause, .excluded), (sePassive saClause, .optional)]
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- *a spera* 'hope' takes a *să* clause or a *că* clause. -/
def a_spera : Verb where
  morphs := [.free "a", .root "spera"]
  valency := .ofFrames [saClause, ArgumentFrame.finiteClause]
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- *a intenționa* 'intend' takes a *să* clause. -/
def a_intentiona : Verb where
  morphs := [.free "a", .root "intenționa"]
  valency := .ofFrame saClause
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- The causative *a face* 'make' takes an object and a *să* clause. -/
def a_face : Verb where
  morphs := [.free "a", .root "face"]
  valency := .ofFrame (⟨some .nominal, [.nominal, .clausal { coding := {.subjunctive} }]⟩)

theorem a_spera_takes_both :
    a_spera.Takes sa ∧ a_spera.Takes ca ∧ a_vrea.Takes sa ∧ ¬ a_vrea.Takes ca := by
  decide

/-- The entry of *a vrea* has the value the map of [haspelmath-2013-want] gives Romanian. -/
theorem lookup_wals_want :
    Data.WALS.F124A.allData.lookup "rom" = a_vrea.wantComplementSubject := by
  decide +kernel

end Romanian.Verbs
