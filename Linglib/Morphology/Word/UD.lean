/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.PEquiv
public import Linglib.Morphology.Word.Features

/-!
# Universal Dependencies annotation of tokens

Each analytical inventory of person, number, gender and case realizes as a Universal Dependencies
tag where one exists, and each tag ingests as a value. The two directions are not inverse: the
annotation has no tag for clusivity, for minimal and augmented number or for animacy genders, and
it tags the oblique case `Acc`. A token's features realize as an annotation record, and an
annotation ingests as features.

## Main definitions

* `Person.toUD`, `Number.toUD`, `Gender.Label.toUD`, `Case.toUD`: realization as a tag.
* `Person.fromUD`, `Number.fromUD`, `Gender.Label.fromUD`, `Case.fromUD`: ingestion of a tag.
* `Number.toUDPEquiv`: realization and ingestion of number, a partial equivalence.
* `Morphology.Features.toUD`, `Morphology.Features.ofUD`: realization and ingestion of a token's
  features.

## Main results

* `Person.fromUD_toUD`: ingestion after realization forgets clusivity.
* `Gender.Label.isPartialInv_fromUD_toUD`: realization is a partial inverse of ingestion.
* `Case.fromUD_toUD`: ingestion after realization is the identity except on the oblique.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

/-! ### Person -/

namespace Person

/-- Realization as a tag collapses clusivity to the first person. -/
def toUD : Person → UD.Person
  | .first | .firstInclusive | .firstExclusive => .first
  | .second => .second
  | .third => .third

/-- Ingest an annotation; the impersonal `Person=0` is the absence of a person. -/
def fromUD : UD.Person → Option Person
  | .first => some .first
  | .second => some .second
  | .third => some .third
  | .zero => none

/-- Realization is a partial inverse of ingestion up to clusivity, which has no tag. -/
theorem fromUD_toUD (p : Person) : fromUD p.toUD = some p.coarsen := by cases p <;> decide

@[simp] theorem toUD_fromUD {u : UD.Person} {p : Person} (h : fromUD u = some p) :
    p.toUD = u := by
  cases u <;> simp only [fromUD, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem ud_conflates_clusivity : Person.firstInclusive.toUD = Person.firstExclusive.toUD := rfl

end Person

/-! ### Number -/

namespace Number

/-- Realize as an annotation; general, minimal, augmented, unit augmented and global plural
have no tag. -/
def toUD : Number → Option UD.Number
  | .general => none
  | .singular => some .Sing
  | .dual => some .Dual
  | .trial => some .Tri
  | .paucal => some .Pauc
  | .plural => some .Plur
  | .greaterPaucal => some .Grpa
  | .greaterPlural => some .Grpl
  | .minimal => none
  | .augmented => none
  | .unitAugmented => none
  | .globalPlural => none

/-- Ingest an annotation; the inverse, collective and count tags have no value. -/
def fromUD : UD.Number → Option Number
  | .Sing => some .singular
  | .Plur => some .plural
  | .Dual => some .dual
  | .Tri => some .trial
  | .Pauc => some .paucal
  | .Grpa => some .greaterPaucal
  | .Grpl => some .greaterPlural
  | .Inv => none
  | .Coll => none
  | .Count => none

/-- Realization and ingestion of number are a partial equivalence: a value has a tag exactly when
that tag ingests as the value. -/
def toUDPEquiv : Number ≃. UD.Number where
  toFun := toUD
  invFun := fromUD
  inv a b := by cases a <;> cases b <;> decide

end Number

/-! ### Gender -/

namespace Gender.Label

/-- Realize as an annotation; the animacy labels have no tag. -/
def toUD : Label → Option UD.Gender
  | .masculine => some .Masc
  | .feminine => some .Fem
  | .neuter => some .Neut
  | .common => some .Com
  | .animate => none
  | .inanimate => none

/-- Ingest an annotation. -/
def fromUD : UD.Gender → Label
  | .Masc => .masculine
  | .Fem => .feminine
  | .Neut => .neuter
  | .Com => .common

/-- Realization is a partial inverse of ingestion. -/
theorem isPartialInv_fromUD_toUD : Function.IsPartialInv fromUD toUD :=
  fun x y ↦ by cases x <;> cases y <;> decide

@[simp] theorem toUD_fromUD (u : UD.Gender) : (fromUD u).toUD = some u :=
  isPartialInv_fromUD_toUD.eq u

theorem fromUD_of_toUD_eq_some {g : Label} {u : UD.Gender} (h : g.toUD = some u) :
    fromUD u = g :=
  (isPartialInv_fromUD_toUD u g).1 h

end Gender.Label

/-! ### Case -/

namespace Case

/-- Realize as an annotation. -/
def toUD : Case → UD.Case
  | .nom => .Nom
  | .acc => .Acc
  | .gen => .Gen
  | .dat => .Dat
  | .inst => .Ins
  | .loc => .Loc
  | .voc => .Voc
  | .abl => .Abl
  | .erg => .Erg
  | .abs => .Abs
  | .obl => .Acc
  | .part => .Par
  | .ess => .Ess
  | .transl => .Tra
  | .com => .Com
  | .ade => .Ade
  | .ine => .Ine
  | .ill => .Ill
  | .ela => .Ela
  | .all => .All
  | .sub => .Sub
  | .sup => .Sup
  | .del => .Del
  | .ter => .Ter
  | .tem => .Tem
  | .caus => .Cau
  | .ben => .Ben
  | .perl => .Per
  | .abess => .Abe

/-- Ingest an annotation. -/
def fromUD : UD.Case → Case
  | .Nom => .nom
  | .Acc => .acc
  | .Gen => .gen
  | .Dat => .dat
  | .Ins => .inst
  | .Loc => .loc
  | .Voc => .voc
  | .Abl => .abl
  | .Erg => .erg
  | .Abs => .abs
  | .Par => .part
  | .Ess => .ess
  | .Tra => .transl
  | .Com => .com
  | .Ade => .ade
  | .Ine => .ine
  | .Ill => .ill
  | .Ela => .ela
  | .All => .all
  | .Sub => .sub
  | .Sup => .sup
  | .Del => .del
  | .Ter => .ter
  | .Tem => .tem
  | .Cau => .caus
  | .Ben => .ben
  | .Per => .perl
  | .Abe => .abess

/-- Ingestion after realization is the identity but on the oblique, which realizes as `Acc`, the
tag UD's guidelines give the oblique of a language with a direct and an oblique case only, and
ingests as the accusative. -/
theorem fromUD_toUD (c : Case) : fromUD c.toUD = if c = .obl then .acc else c := by
  cases c <;> rfl

theorem toUD_fromUD (u : UD.Case) : (fromUD u).toUD = u := by cases u <;> rfl

end Case

/-! ### Tokens -/

namespace Morphology.Features

/-- The annotation of a token's features. -/
def toUD (f : Features) : UD.MorphFeatures where
  person := (f .person).map Person.toUD
  number := (f .number).bind Number.toUD
  gender := (f .gender).bind Gender.Label.toUD
  case_ := (f .case).map Case.toUD
  definite := f .definiteness
  degree := f .degree
  pronType := f .pronType
  reflex := (f .reflex).isSome
  verbForm := f .verbForm
  tense := f .tense
  aspect := f .aspect
  mood := f .mood
  voice := f .voice
  polarity := f .polarity

/-- The features an annotation ingests as. -/
def ofUD (m : UD.MorphFeatures) : Features
  | .person => m.person.bind Person.fromUD
  | .number => m.number.bind Number.fromUD
  | .gender => m.gender.map Gender.Label.fromUD
  | .case => m.case_.map Case.fromUD
  | .definiteness => m.definite
  | .degree => m.degree
  | .pronType => m.pronType
  | .reflex => if m.reflex then some () else none
  | .verbForm => m.verbForm
  | .tense => m.tense
  | .aspect => m.aspect
  | .mood => m.mood
  | .voice => m.voice
  | .polarity => m.polarity

end Morphology.Features
