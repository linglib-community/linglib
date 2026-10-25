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

Each analytical inventory of person, number and case realizes as Universal Dependencies tags
where they exist, and each tag ingests as a value where one exists. A first person realizes with
its clusivity, so ingestion inverts the realization of person. The annotation has no tag for
five values of number and tags the oblique case `Acc`; the analytical inventories have no value
for the zero and the fourth person, four tags of number and six of case. A token's features
realize as an annotation, which leaves the written-token flags unset, and an annotation ingests
as features, which drops them.

## Main definitions

* `Person.toUD`, `Number.toUD`, `Case.toUD`: realization as tags.
* `Person.fromUD`, `Number.fromUD`, `Case.fromUD`: ingestion of tags.
* `Person.toUDPEquiv`, `Number.toUDPEquiv`: realization and ingestion of person and of number,
  partial equivalences.
* `Morphology.Features.toUD`, `Morphology.Features.ofUD`: realization and ingestion of a token's
  features.

## Main results

* `Person.fromUD_toUD`: ingestion after realization is the identity, clusivity included.
* `Case.fromUD_toUD`: ingestion after realization is the identity except on the oblique.
* `Morphology.Features.ofUD_toUD`: for a token, ingestion after realization is the identity
  except at case and number.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

/-! ### Person -/

namespace Person

/-- Realization as a person tag and, for an inclusive or exclusive first person, a clusivity
tag. -/
def toUD : Person → UD.Person × Option UD.Clusivity
  | .first => (.first, none)
  | .firstInclusive => (.first, some .In)
  | .firstExclusive => (.first, some .Ex)
  | .second => (.second, none)
  | .third => (.third, none)

/-- Ingest a person tag with a clusivity tag, which only the first person takes; the zero and the
fourth person have no value. -/
def fromUD : UD.Person × Option UD.Clusivity → Option Person
  | (.first, none) => some .first
  | (.first, some .In) => some .firstInclusive
  | (.first, some .Ex) => some .firstExclusive
  | (.second, none) => some .second
  | (.third, none) => some .third
  | _ => none

/-- Realization and ingestion of person are a partial equivalence: a person has its tags exactly
when they ingest as it. -/
def toUDPEquiv : Person ≃. UD.Person × Option UD.Clusivity where
  toFun p := some p.toUD
  invFun := fromUD
  inv p u := by obtain ⟨_ | _ | _ | _ | _, _ | _ | _⟩ := u <;> cases p <;> decide

theorem fromUD_toUD (p : Person) : fromUD p.toUD = some p := by cases p <;> rfl

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

/-- Ingest an annotation; the inverse, collective, count and plurale tantum tags have no value. -/
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
  | .Ptan => none

/-- Realization and ingestion of number are a partial equivalence: a value has a tag exactly when
that tag ingests as the value. -/
def toUDPEquiv : Number ≃. UD.Number where
  toFun := toUD
  invFun := fromUD
  inv a b := by cases a <;> cases b <;> decide

end Number

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

/-- Ingest an annotation; the comparative, considerative, distributive, equative, additive and
lative tags have no value. -/
def fromUD : UD.Case → Option Case
  | .Abs => some .abs
  | .Acc => some .acc
  | .Erg => some .erg
  | .Nom => some .nom
  | .Abe => some .abess
  | .Ben => some .ben
  | .Cau => some .caus
  | .Com => some .com
  | .Dat => some .dat
  | .Gen => some .gen
  | .Ins => some .inst
  | .Par => some .part
  | .Tem => some .tem
  | .Tra => some .transl
  | .Voc => some .voc
  | .Abl => some .abl
  | .Ade => some .ade
  | .All => some .all
  | .Del => some .del
  | .Ela => some .ela
  | .Ess => some .ess
  | .Ill => some .ill
  | .Ine => some .ine
  | .Loc => some .loc
  | .Per => some .perl
  | .Sub => some .sub
  | .Sup => some .sup
  | .Ter => some .ter
  | .Cmp | .Cns | .Dis | .Equ | .Add | .Lat => none

/-- Ingestion after realization is the identity but on the oblique, which realizes as `Acc`, the
tag UD's guidelines give the oblique of a language with a direct and an oblique case only, and
ingests as the accusative. -/
theorem fromUD_toUD (c : Case) : fromUD c.toUD = some (if c = .obl then .acc else c) := by
  cases c <;> rfl

theorem toUD_fromUD {u : UD.Case} {c : Case} (h : fromUD u = some c) : c.toUD = u := by
  cases u <;> cases h <;> rfl

end Case

/-! ### Tokens -/

namespace Morphology.Features

/-- The annotation of a token's features; the foreign, abbreviation and typo flags of the
written token are no features and stay unset. -/
def toUD (f : Features) : UD.MorphFeatures where
  pronType := f .pronType
  numType := f .numType
  poss := (f .poss).isSome
  reflex := (f .reflex).isSome
  gender := f .gender
  animacy := f .animacy
  number := (f .number).bind Number.toUD
  case := (f .case).map Case.toUD
  definite := f .definiteness
  degree := f .degree
  verbForm := f .verbForm
  mood := f .mood
  tense := f .tense
  aspect := f .aspect
  voice := f .voice
  evident := f .evident
  polarity := f .polarity
  person := (f .person).map (·.toUD.1)
  clusivity := (f .person).bind (·.toUD.2)
  polite := f .polite

/-- The features an annotation ingests as. -/
def ofUD (m : UD.MorphFeatures) : Features
  | .person => m.person.bind fun u ↦ Person.fromUD (u, m.clusivity)
  | .number => m.number.bind Number.fromUD
  | .gender => m.gender
  | .animacy => m.animacy
  | .case => m.case.bind Case.fromUD
  | .definiteness => m.definite
  | .degree => m.degree
  | .pronType => m.pronType
  | .numType => m.numType
  | .poss => if m.poss then some () else none
  | .reflex => if m.reflex then some () else none
  | .verbForm => m.verbForm
  | .tense => m.tense
  | .aspect => m.aspect
  | .mood => m.mood
  | .voice => m.voice
  | .evident => m.evident
  | .polarity => m.polarity
  | .polite => m.polite

/-- Ingestion inverts realization except at case and number: the oblique case returns as the
accusative, and a number value without a tag returns as `none`. -/
theorem ofUD_toUD (f : Features) (t : Feature) :
    ofUD (toUD f) t =
      match t with
      | .case => (f .case).map fun c ↦ if c = .obl then .acc else c
      | .number => (f .number).bind fun n ↦ if n.toUD = none then none else some n
      | t => f t := by
  cases t
  case person => rcases h : f .person with - | p <;> simp only [ofUD, toUD, h] <;>
    [rfl; (cases p <;> rfl)]
  case number => rcases h : f .number with - | n <;> simp only [ofUD, toUD, h] <;>
    [rfl; (cases n <;> rfl)]
  case case => rcases h : f .case with - | c <;> simp only [ofUD, toUD, h] <;>
    [rfl; (cases c <;> rfl)]
  case poss => rcases h : f .poss with - | ⟨⟩ <;> simp only [ofUD, toUD, h] <;> rfl
  case reflex => rcases h : f .reflex with - | ⟨⟩ <;> simp only [ofUD, toUD, h] <;> rfl
  all_goals rfl

end Morphology.Features
