module

public import Linglib.Data.Statistics.Schema

/-!
# MartinRoseNichols2025: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/MartinRoseNichols2025.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

The corpus survey of thirty-seven frequent English causative verbs in their concrete sense: for each
verb, whether it enters the causative alternation, its class in Levin's catalogue as the paper gives
it, whether it is thick, and whether the enTenTen21 corpus has it with an adjectival strong
resultative and with an omission or quality subject.

## References

* [martin-rose-nichols-2025]
-/

@[expose] public section

namespace MartinRoseNichols2025

open Data.Statistics

/-- The verbs of the survey, in the order of Table 3. -/
inductive Verb where
  /-- activate: *activate* -/
  | activate
  /-- affect: *affect* -/
  | affect
  /-- change: *change* -/
  | change
  /-- close: *close* -/
  | close
  /-- cool: *cool* -/
  | cool
  /-- damage: *damage* -/
  | damage
  /-- destroy: *destroy* -/
  | destroy
  /-- dry: *dry* -/
  | dry
  /-- eliminate: *eliminate* -/
  | eliminate
  /-- enhance: *enhance* -/
  | enhance
  /-- extend: *extend* -/
  | extend
  /-- hurt: *hurt* -/
  | hurt
  /-- kill: *kill* -/
  | kill
  /-- lower: *lower* -/
  | lower
  /-- open: *open* -/
  | open
  /-- put: *put* -/
  | put
  /-- restore: *restore* -/
  | restore
  /-- set: *set* -/
  | set
  /-- slow: *slow* -/
  | slow
  /-- start: *start* -/
  | start
  /-- stop: *stop* -/
  | stop
  /-- trigger: *trigger* -/
  | trigger
  /-- turn: *turn* -/
  | turn
  /-- wake up: *wake up* -/
  | wakeUp
  /-- break: *break* -/
  | break
  /-- bury: *bury* -/
  | bury
  /-- burn: *burn* -/
  | burn
  /-- cut: *cut* -/
  | cut
  /-- drop: *drop* -/
  | drop
  /-- lift: *lift* -/
  | lift
  /-- lock: *lock* -/
  | lock
  /-- melt: *melt* -/
  | melt
  /-- mix: *mix* -/
  | mix
  /-- shut: *shut* -/
  | shut
  /-- spread: *spread* -/
  | spread
  /-- stretch: *stretch* -/
  | stretch
  /-- switch: *switch* -/
  | switch
  deriving DecidableEq, Repr, Fintype

/-- The verb types of Levin's catalogue under the names Table 3 prints. -/
inductive LevinType where
  /-- amuse verbs: amuse verbs -/
  | amuse
  /-- turn verbs: turn verbs -/
  | turn
  /-- cos verbs (others): cos verbs (others) -/
  | otherChangeOfState
  /-- destroy verbs: destroy verbs -/
  | destroy
  /-- verbs of removing: verbs of removing -/
  | removing
  /-- verbs of existence: verbs of existence -/
  | existence
  /-- hurt verbs: hurt verbs -/
  | hurt
  /-- verbs of killing: verbs of killing -/
  | killing
  /-- verbs of putting: verbs of putting -/
  | putting
  /-- put verbs: put verbs -/
  | put
  /-- contribute verbs: contribute verbs -/
  | contribute
  /-- aspectual verbs: aspectual verbs -/
  | aspectual
  /-- break verbs: break verbs -/
  | break
  /-- verbs of calibratable cos: verbs of calibratable cos -/
  | calibratableChangeOfState
  /-- tape verbs: tape verbs -/
  | tape
  /-- mix verbs: mix verbs -/
  | mix
  /-- verbs of spatial configuration: verbs of spatial configuration -/
  | spatialConfiguration
  deriving DecidableEq, Repr, Fintype

/-- The codes of the column for adjectival strong resultatives. -/
inductive Resultative where
  /-- N: not found with an adjectival strong resultative -/
  | no
  /-- Y: found with an adjectival strong resultative -/
  | yes
  /-- Y*: found with an adjectival strong resultative, and lexicalizing no state of its own -/
  | only
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 3: the coding of a verb of the sample. -/
structure Survey where
  /-- The annotators judged the verb to enter the causative alternation. -/
  alternating : Bool
  /-- The verb type in Levin's catalogue, `none` where the table prints *not listed*. -/
  levin : Option LevinType
  /-- The verb is thick: it was judged to specify a way of causing. -/
  thick : Bool
  /-- Whether the verb was found with an adjectival strong resultative. -/
  resultative : Resultative
  /-- The verb was found with an omission or quality subject in its concrete sense. -/
  omission : Bool
  deriving DecidableEq, Repr

/-- The cells of Table 3, by verb; counted in a corpus; checked against the page images. -/
def survey : Verb → Survey
  | .activate => ⟨true, none, false, .no, true⟩
  | .affect => ⟨false, some .amuse, false, .no, true⟩
  | .change => ⟨true, some .turn, false, .no, true⟩
  | .close => ⟨true, some .otherChangeOfState, false, .no, false⟩
  | .cool => ⟨false, some .otherChangeOfState, false, .no, true⟩
  | .damage => ⟨false, none, false, .no, true⟩
  | .destroy => ⟨false, some .destroy, false, .no, true⟩
  | .dry => ⟨true, some .otherChangeOfState, false, .no, true⟩
  | .eliminate => ⟨false, some .removing, false, .no, true⟩
  | .enhance => ⟨false, none, false, .no, true⟩
  | .extend => ⟨true, some .existence, false, .no, true⟩
  | .hurt => ⟨false, some .hurt, false, .no, true⟩
  | .kill => ⟨false, some .killing, false, .no, true⟩
  | .lower => ⟨true, some .putting, false, .no, false⟩
  | .open => ⟨true, some .otherChangeOfState, false, .no, true⟩
  | .put => ⟨false, some .put, false, .no, true⟩
  | .restore => ⟨false, some .contribute, false, .no, true⟩
  | .set => ⟨false, some .put, false, .only, true⟩
  | .slow => ⟨true, some .otherChangeOfState, false, .no, true⟩
  | .start => ⟨true, some .aspectual, false, .no, true⟩
  | .stop => ⟨true, some .aspectual, false, .no, true⟩
  | .trigger => ⟨false, none, false, .only, true⟩
  | .turn => ⟨true, some .turn, false, .only, true⟩
  | .wakeUp => ⟨true, none, false, .no, true⟩
  | .break => ⟨true, some .break, true, .yes, false⟩
  | .bury => ⟨false, none, true, .no, false⟩
  | .burn => ⟨true, some .hurt, true, .yes, true⟩
  | .cut => ⟨false, some .break, true, .yes, false⟩
  | .drop => ⟨true, some .calibratableChangeOfState, true, .yes, false⟩
  | .lift => ⟨false, some .putting, true, .yes, true⟩
  | .lock => ⟨true, some .tape, true, .yes, true⟩
  | .melt => ⟨true, some .otherChangeOfState, true, .yes, true⟩
  | .mix => ⟨true, some .mix, true, .yes, false⟩
  | .shut => ⟨true, some .otherChangeOfState, true, .yes, false⟩
  | .spread => ⟨true, some .existence, true, .yes, false⟩
  | .stretch => ⟨true, some .spatialConfiguration, true, .yes, false⟩
  | .switch => ⟨true, none, true, .yes, false⟩

end MartinRoseNichols2025
