module

public import Linglib.Semantics.Quantification.Counting
public import Linglib.Data.Examples.Gasparri2025

/-!
# Gasparri (2025): Bare Singular Names and Genericity

This file formalizes [gasparri-2025]'s reply to the argument that bare singular names, unlike the
definite singulars predicativism equates them with ([matushansky-2008], [fara-2015]), never take
generic readings ([delgado-2024]). The paper's data show that they do, in simple generics as well
as under quantificational adverbs, though more grudgingly than common-noun definites: out of the
blue a bare name resists the generic reading, and a naming-convention context, a locative, a
modifier or binding recovers it. Kind-level generics are the one case that stays closed to bare
names and open to quoted ones, a gap common nouns share.

The rows are the paper's judgments and the theorems the generalizations it draws from them:
`recalcitrance` against parity with definite singulars, `bareName_simple_generic` against the
categorical ban. The paper's theoretical point, that a generic use calls for predicative content,
is `referentialist_generic_is_token`: a referential name shifted to its identity property
([partee-1987]) and fed to the generic operator yields nothing but the token reading, so the shift
a referentialist needs must introduce the naming predicate itself.

## Implementation notes

* The generic operator is *most* over the restrictor, the proportional reading the paper's
  genericity diagnostics presuppose; the paper itself stays neutral on the semantics of Gen.
* A sentence the paper marks `??` without listing a reading is recorded with a questionable
  generic reading, the reading at issue; a reading the paper does not list is absent.

## References

* [gasparri-2025]
* [partee-1987]
* [matushansky-2008]
* [fara-2015]
* [delgado-2024]
-/

@[expose] public section

namespace Gasparri2025

open Quantifier Quantifier.GQ Quantifier.NP

theorem referentialist_generic_is_token {E : Type} [Fintype E] [DecidableEq E] (j : E)
    (VP : E → Prop) :
    most (ident j) VP ↔ VP j :=
  most_singleton_iff j VP

/-! ### The paper's judgments -/

/-- The subject of a sentence, as the paper classifies it. -/
inductive Subject
  | bareName | modifiedName | pluralName | quotedName | definiteName
  | definiteCommon | modifiedCommon | bareCommonPlural
  deriving DecidableEq, Repr

/-- What the sentence is embedded in: nothing, a locative adjunct, a discourse about naming
conventions, a binding quantifier, a discourse with kinds in focus, or a contrastive adjunct. -/
inductive Context
  | outOfTheBlue | locative | naming | binding | focusedKinds | contrast
  deriving DecidableEq, Repr

/-- Whether the predicate is characterizing or kind-level. -/
inductive Level
  | characterizing | kindLevel
  deriving DecidableEq, Repr

/-- A sentence of the paper with the judgment of its generic reading, if the paper lists one. -/
structure Row where
  subject : Subject
  context : Context
  qadv : Bool
  level : Level
  generic : Option Judgment
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let subject ← ex.parse? "subject" [("bareName", Subject.bareName),
    ("modifiedName", .modifiedName), ("pluralName", .pluralName), ("quotedName", .quotedName),
    ("definiteName", .definiteName), ("definiteCommon", .definiteCommon),
    ("modifiedCommon", .modifiedCommon), ("bareCommonPlural", .bareCommonPlural)]
  let context ← ex.parse? "context" [("outOfTheBlue", Context.outOfTheBlue),
    ("locative", .locative), ("naming", .naming), ("binding", .binding),
    ("focusedKinds", .focusedKinds), ("contrast", .contrast)]
  let qadv ← ex.parse? "qadv" [("yes", true), ("no", false)]
  let level ← ex.parse? "level" [("characterizing", Level.characterizing),
    ("kindLevel", .kindLevel)]
  pure ⟨subject, context, qadv, level, ex.readings.lookup "generic"⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem recalcitrance : ∀ r ∈ rows, r.subject = .bareName → r.context = .outOfTheBlue →
    r.generic ≠ some .acceptable := by
  decide

theorem definiteCommon_simple_generic : ∃ r ∈ rows, r.subject = .definiteCommon ∧
    r.context = .outOfTheBlue ∧ r.qadv = false ∧ r.generic = some .acceptable := by
  decide

theorem bareName_simple_generic :
    ∃ r ∈ rows, r.subject = .bareName ∧ r.qadv = false ∧ r.generic = some .acceptable := by
  decide

theorem bareName_quantificational_generic :
    ∃ r ∈ rows, r.subject = .bareName ∧ r.qadv = true ∧ r.generic = some .acceptable := by
  decide

theorem bareName_kindLevel : ∀ r ∈ rows, r.subject = .bareName → r.level = .kindLevel →
    r.generic ≠ some .acceptable := by
  decide

theorem quotedName_kindLevel : ∀ r ∈ rows, r.subject = .quotedName → r.level = .kindLevel →
    r.generic = some .acceptable := by
  decide

theorem definiteCommon_kindLevel_both :
    (∃ r ∈ rows, r.subject = .definiteCommon ∧ r.level = .kindLevel ∧
      r.generic = some .acceptable) ∧
    ∃ r ∈ rows, r.subject = .definiteCommon ∧ r.level = .kindLevel ∧
      r.generic ≠ some .acceptable := by
  decide

end Gasparri2025
