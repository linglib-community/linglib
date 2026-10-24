module

public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes

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
-/

@[expose] public section

namespace Romanian.Verbs

open ArgumentStructure Morphology

/-! ### Clause-typers -/

/-- *să* introduces a subjunctive clause. -/
def sa : Complementizer where
  morphs := [.free "să"]
  coding := some .subjunctive

/-- *că* introduces an indicative declarative clause. -/
def ca : Complementizer where
  morphs := [.free "că"]
  coding := some .indicative
  types := .only .declarative

/-- The clause-typers of finite complements. -/
def complementizers : List Complementizer := [sa, ca]

/-! ### Attitude and causative verbs -/

/-- A finite subjunctive complement, the clause *să* introduces. -/
def saClause : ArgumentFrame := ⟨some .nominal, [.clausal (coding := some .subjunctive)]⟩

/-- *a vrea* 'want' takes a *să* clause. -/
def a_vrea : Verb where
  morphs := [.free "a", .root "vrea"]
  valency := .ofFrame saClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- *a spera* 'hope' takes a *să* clause or a *că* clause. -/
def a_spera : Verb where
  morphs := [.free "a", .root "spera"]
  valency := .ofFrames [saClause, ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- *a intenționa* 'intend' takes a *să* clause. -/
def a_intentiona : Verb where
  morphs := [.free "a", .root "intenționa"]
  valency := .ofFrame saClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- The causative *a face* 'make' takes an object and a *să* clause. -/
def a_face : Verb where
  morphs := [.free "a", .root "face"]
  valency := .ofFrame (⟨some .nominal, [.nominal, .clausal (coding := some .subjunctive)]⟩)

theorem a_spera_takes_both :
    a_spera.Takes sa ∧ a_spera.Takes ca ∧ a_vrea.Takes sa ∧ ¬ a_vrea.Takes ca := by
  decide

end Romanian.Verbs
