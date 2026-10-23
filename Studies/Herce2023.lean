module

public import Linglib.Data.Examples.Herce2023
public import Linglib.Morphology.Paradigm.Morphome
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype

/-!
# Herce (2023): The Typological Diversity of Morphomes

This file formalizes two morphomes of [herce-2023] as instances of `Morphology.IsMorphome`,
the book's working definition of a morphome as a systematic syncretism that is not a natural
class (§1.4), with a natural class one coextensive with a value or conjunction of values,
`Morphology.IsValueConjunction`. The Spanish L-morphome of Table 1.2, the first person
singular of the present indicative together with the whole present subjunctive, is the
syncretism class of the velar stems of *venir* and *nacer* and of the suppletive stem of
*caber* (`venir_morphome`); the Darma syncretism of Table 4.32, the first person plural with
the second person, is the class of the non-past suffix *-he-n* and of the past suffix *-n-su*
of *ra* 'come' (`nonpast_morphome`). Each class is a value conjunction of none of its
paradigm's features (`Lset_not_natural`), and its recurrence under distinct exponents is the
systematicity the definition asks for.

## Implementation notes

* The paradigms are Table 1.2 and Table 4.32 as printed, stems and suffixes typed as the
  tables segment them: *venir* has the diphthongized stem in the second and third singular
  and third plural of the indicative, the optional final *-i* of the Darma second person
  plural non-past is dropped, and the transitive allomorph *-de* is prose.

## References

* [herce-2023]
* [aronoff-1994]
-/

@[expose] public section

namespace Herce2023

open Morphology

/-! ### The Spanish L-morphome (Table 1.2) -/

/-- The moods of the present tense. -/
inductive Mood where
  | ind
  | sbjv
  deriving DecidableEq, Fintype

/-- Grammatical person. -/
inductive Per where
  | first
  | second
  | third
  deriving DecidableEq, Fintype

/-- Grammatical number. -/
inductive Num where
  | sg
  | pl
  deriving DecidableEq, Fintype

/-- A present-tense cell: mood, person and number. -/
abbrev SpCell := Mood × Per × Num

/-- The features of a present-tense cell. -/
inductive SpFeature where
  | mood
  | person
  | number
  deriving DecidableEq, Fintype

/-- The partition of the present-tense cells a feature induces. -/
def spFeatures : SpFeature → Setoid SpCell
  | .mood => Setoid.ker Prod.fst
  | .person => Setoid.ker λ c => c.2.1
  | .number => Setoid.ker λ c => c.2.2

instance (i : SpFeature) : DecidableRel (spFeatures i) := by
  cases i <;> exact Setoid.ker.decidableRel _

/-- The stems of Table 1.2: *venir* with /ven/, diphthongized /vjen/ and velar /veng/; *nacer*
with /naθ/ and velar /naθk/; *caber* with /kab/ and weakly suppletive /kep/. -/
inductive Stem where
  | ven
  | vjen
  | veng
  | naθ
  | naθk
  | kab
  | kep
  deriving DecidableEq, Fintype

/-- The stem of *venir* 'come' in each present-tense cell. -/
def venir : SpCell → Stem
  | (.ind, .first, .sg) => .veng
  | (.ind, .second, .sg) => .vjen
  | (.ind, .third, .sg) => .vjen
  | (.ind, .third, .pl) => .vjen
  | (.ind, _, .pl) => .ven
  | (.sbjv, _, _) => .veng

/-- The stem of *nacer* 'be born' in each present-tense cell. -/
def nacer : SpCell → Stem
  | (.ind, .first, .sg) => .naθk
  | (.sbjv, _, _) => .naθk
  | _ => .naθ

/-- The stem of *caber* 'fit' in each present-tense cell. -/
def caber : SpCell → Stem
  | (.ind, .first, .sg) => .kep
  | (.sbjv, _, _) => .kep
  | _ => .kab

/-- The cells of the L-morphome: the first person singular of the present indicative and the
whole present subjunctive. -/
def Lset : Finset SpCell := insert (.ind, .first, .sg) (Finset.univ.filter (·.1 = .sbjv))

theorem venir_formCells : formCells venir .veng = Lset := by decide

theorem nacer_formCells : formCells nacer .naθk = Lset := by decide

theorem caber_formCells : formCells caber .kep = Lset := by decide

theorem Lset_not_natural : ¬ IsValueConjunction spFeatures ↑Lset := by
  rw [isValueConjunction_coe_iff]
  decide

theorem venir_morphome : IsMorphome venir (IsValueConjunction spFeatures) ↑Lset :=
  isMorphome_of_formCells venir (.ind, .first, .sg) _ venir_formCells (by decide)
    Lset_not_natural

theorem nacer_morphome : IsMorphome nacer (IsValueConjunction spFeatures) ↑Lset :=
  isMorphome_of_formCells nacer (.ind, .first, .sg) _ nacer_formCells (by decide)
    Lset_not_natural

theorem caber_morphome : IsMorphome caber (IsValueConjunction spFeatures) ↑Lset :=
  isMorphome_of_formCells caber (.ind, .first, .sg) _ caber_formCells (by decide)
    Lset_not_natural

/-! ### The Darma first person plural and second person (§4.2.2.4, Table 4.32) -/

/-- A Darma agreement cell: person and number. -/
abbrev DCell := Per × Num

/-- The features of an agreement cell. -/
inductive DFeature where
  | person
  | number
  deriving DecidableEq, Fintype

/-- The partition of the agreement cells a feature induces. -/
def dFeatures : DFeature → Setoid DCell
  | .person => Setoid.ker Prod.fst
  | .number => Setoid.ker Prod.snd

instance (i : DFeature) : DecidableRel (dFeatures i) := by
  cases i <;> exact Setoid.ker.decidableRel _

/-- The agreement suffixes of *ra* 'come' in Table 4.32: non-past *-hi*, *-he-n* and *-ni*,
past *-ju*, *-n-su* and *-ɟu*. -/
inductive Suffix where
  | hi
  | hen
  | ni
  | ju
  | nsu
  | «ɟu»
  deriving DecidableEq, Fintype

/-- The non-past suffix of each agreement cell. -/
def nonpast : DCell → Suffix
  | (.first, .sg) => .hi
  | (.first, .pl) => .hen
  | (.second, _) => .hen
  | (.third, _) => .ni

/-- The past suffix of each agreement cell. -/
def past : DCell → Suffix
  | (.first, .sg) => .ju
  | (.first, .pl) => .nsu
  | (.second, _) => .nsu
  | (.third, _) => .«ɟu»

/-- The syncretic cells: the first person plural and the second person. -/
def Dset : Finset DCell := {(.first, .pl), (.second, .sg), (.second, .pl)}

theorem nonpast_formCells : formCells nonpast .hen = Dset := by decide

theorem past_formCells : formCells past .nsu = Dset := by decide

theorem Dset_not_natural : ¬ IsValueConjunction dFeatures ↑Dset := by
  rw [isValueConjunction_coe_iff]
  decide

theorem nonpast_morphome : IsMorphome nonpast (IsValueConjunction dFeatures) ↑Dset :=
  isMorphome_of_formCells nonpast (.second, .sg) _ nonpast_formCells (by decide)
    Dset_not_natural

theorem past_morphome : IsMorphome past (IsValueConjunction dFeatures) ↑Dset :=
  isMorphome_of_formCells past (.second, .sg) _ past_formCells (by decide) Dset_not_natural

end Herce2023
