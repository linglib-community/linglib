module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Morphology.Morph

/-!
# Yukatek Maya verb classes and status

A Yukatek Maya verb is inflected for status, a suffixal category of aspect and mood with
four values, the incompletive, the completive, the subjunctive, which Hofling calls the
dependent, and the imperative. The allomorphs of the status suffixes sort verb stems into five
classes: the active intransitives, the inactive intransitives, the inchoatives derived from
stative roots, the positionals of spatial configurations, and the transitives. The active class
is the one with no suffix in the incompletive and the inactive class the one with none in the
completive, and [no other class is unmarked in any status](##Yukatek.statusSuffix_eq_some_nil_iff).
The status also fixes which set of person markers cross-references the sole argument of an
intransitive, the split that `Yukatek.markerSet` records.

## Implementation notes

The four statuses, the five classes and the reading of the statuses as viewpoint aspects are
Bohnemeyer's. The suffixes are those of Hofling's conjugation tables for Yucatec, in his
orthography and segmentation, as the person markers of `Yukatek/Agreement.lean` are; Bohnemeyer's
table of status patterns gives the same suffixes unsegmented, with *h* for *j*. *V* is a vowel
harmonic with the root's. Each cell holds one allomorph. The inactive completive is also *-ij*
before a zero Set B and *-aj*; the transitive subjunctive and imperative *-ej* is zero before an
overt Set B, *il-∅-en* 'see me!'; and the inchoative incompletive is also *-ch-aj-al*. Hofling's
fifth status, the perfect, which Bohnemeyer notes does not occur in main clauses, is not
recorded.

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

/-- The status suffix of each stem class as a sequence of morphs, empty where the class is
unmarked and `none` where it has no form in the status ([hofling-2017] Tables 24.53, 24.55,
24.62–24.64; [bohnemeyer-2004] Table 3). -/
def statusSuffix : VerbStemClass → StatusCategory → Option (List Morphology.Morph)
  | .active, .incompletive => some []
  | .active, .completive => some [.suff "n", .suff "aj"]
  | .active, .subjunctive => some [.suff "n", .suff "ak"]
  | .active, .imperative => some [.suff "n", .suff "en"]
  | .inactive, .incompletive => some [.suff "Vl"]
  | .inactive, .completive => some []
  | .inactive, .subjunctive => some [.suff "Vk"]
  | .inactive, .imperative => some [.suff "en"]
  | .inchoative, .incompletive => some [.suff "tal"]
  | .inchoative, .completive => some [.suff "ch", .suff "aj"]
  | .inchoative, .subjunctive => some [.suff "ch", .suff "aj", .suff "ak"]
  | .inchoative, .imperative => none
  | .positional, .incompletive => some [.suff "tal"]
  | .positional, .completive => some [.suff "l", .suff "aj"]
  | .positional, .subjunctive => some [.suff "l", .suff "ak"]
  | .positional, .imperative => some [.suff "l", .suff "en"]
  | .transitiveActive, .incompletive => some [.suff "ik"]
  | .transitiveActive, .completive => some [.suff "aj"]
  | .transitiveActive, .subjunctive => some [.suff "ej"]
  | .transitiveActive, .imperative => some [.suff "ej"]

/-- A class is unmarked in a status exactly when it is the active class in the incompletive or
the inactive class in the completive ([bohnemeyer-2004] p. 80). -/
theorem statusSuffix_eq_some_nil_iff (c : VerbStemClass) (s : StatusCategory) :
    statusSuffix c s = some [] ↔
      c = .active ∧ s = .incompletive ∨ c = .inactive ∧ s = .completive := by
  cases c <;> cases s <;> decide

end Yukatek
