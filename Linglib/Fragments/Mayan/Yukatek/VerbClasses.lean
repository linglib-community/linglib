module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Aspect.Defs

/-!
# Yukatek Maya verb classes and status

A Yukatek Maya verb is inflected for status, a suffixal category of aspect and mood with
four values, the incompletive, the completive, the subjunctive, which Hofling calls the
dependent, and the imperative. The allomorphs of the status suffixes sort verb stems into five
classes: the active intransitives, unmarked in the incompletive, the inactive intransitives,
unmarked in the completive, the inchoatives derived from stative roots, the positionals of
spatial configurations, and the transitives. The status also fixes which set of person
markers cross-references the sole argument of an intransitive, the split that
`Yukatek.markerSet` records. Bohnemeyer's tables of status semantics and status
patterns and Hofling's Yucatecan sketch are the sources.

## Main definitions

* `Yukatek.StatusCategory`, `Yukatek.VerbStemClass`, `Yukatek.statusSuffix`: the four statuses,
  the five stem classes, and the status suffix of each class.

## Implementation notes

The suffixes are written as Bohnemeyer prints them, *V* for the harmonic vowel and a slash
between allomorphs; the imperfective reading of the incompletive and the perfective reading of
the completive and the subjunctive are his glosses of the statuses.

## References

* [bohnemeyer-2004]
* [hofling-2017]
-/

@[expose] public section

namespace Yukatek

open Aspect (Perfectivity)

/-! ### Status -/

/-- The four status categories. -/
inductive StatusCategory where
  | incompletive
  | completive
  | subjunctive
  | imperative
  deriving DecidableEq, Repr, Fintype

/-- The viewpoint aspect a status expresses, imperfective in the incompletive and perfective in
the completive and the subjunctive; the imperative expresses none. -/
def StatusCategory.viewpointAspect : StatusCategory → Option Perfectivity
  | .incompletive => some .imperfective
  | .completive | .subjunctive => some .perfective
  | .imperative => none

/-! ### Stem classes -/

/-- The five verb stem classes, distinguished by their status allomorphs. -/
inductive VerbStemClass where
  | active
  | inactive
  | inchoative
  | positional
  | transitiveActive
  deriving DecidableEq, Repr, Fintype

/-- The status suffix of each stem class, `none` where the class has no form in the status. -/
def statusSuffix : VerbStemClass → StatusCategory → Option String
  | .active, .incompletive => some "-ø"
  | .active, .completive => some "-nah"
  | .active, .subjunctive => some "-nak"
  | .active, .imperative => some "-nen"
  | .inactive, .incompletive => some "-Vl"
  | .inactive, .completive => some "-ø"
  | .inactive, .subjunctive => some "-Vk"
  | .inactive, .imperative => some "-en"
  | .inchoative, .incompletive => some "-tal"
  | .inchoative, .completive => some "-chah"
  | .inchoative, .subjunctive => some "-chahak"
  | .inchoative, .imperative => none
  | .positional, .incompletive => some "-tal"
  | .positional, .completive => some "-lah"
  | .positional, .subjunctive => some "-l(ah)ak"
  | .positional, .imperative => some "-len"
  | .transitiveActive, .incompletive => some "-ik"
  | .transitiveActive, .completive => some "-ah"
  | .transitiveActive, .subjunctive => some "-ø/-eh"
  | .transitiveActive, .imperative => some "-ø/-eh"

end Yukatek
