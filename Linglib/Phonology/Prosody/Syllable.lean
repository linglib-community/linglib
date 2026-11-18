module

public import Mathlib.Data.PNat.Defs
public import Linglib.Phonology.Segmental.Basic

/-!
# Syllables

This file defines nucleus-headed syllables. A nucleus-headed syllable is an onset over a spine
of morae whose first mora is the nucleus, and its weight is its number of morae.

## Main definitions

* `Syllable`: a nucleus-headed syllable, with an `onset`, the `nucleus` that bears its first
  mora, and the `tail` of further morae.
* `Syllable.moraCount`, `weight`, `IsHeavy`, `IsLight`: the number of morae and the weight
  predicates.
* `Syllable.ofVowel`, `ofLongVowel`: the open syllables of a short and of a long vowel.
* `nucleusSplit`: a string split at its first run of syllabic segments.
* `Syllable.Weight`, `Yield`: a mora count, and the weight profile of a string of syllables.

## Implementation notes

* A `Syllable` is the special case of a syllable of a `MoraicForm` in which the nucleus bears
  the first mora, so that every syllable is at least light. [vasquez-aguilar-etal-2026] shows
  that a language need not observe it: in Shiwilu a syllable whose nucleus is the interior vowel
  takes its only mora from its coda.
* `Syllable.Weight` is `Nat`, the mora count, and `Weight.light`, `heavy`, and `superheavy`
  name one, two, and three morae.

## TODO

* Read `Syllable` off the syllables of a `MoraicForm` that the nucleus heads, and its weight off
  `MoraicForm.weight`.

## References

* [L. M. Hyman, *A Theory of Phonological Weight* (1985)][hyman-1985]
* [B. Hayes, *Compensatory Lengthening in Moraic Phonology* (1989)][hayes-1989]
* [J. J. McCarthy and A. Prince, *Prosodic Morphology: Constraint Interaction and
  Satisfaction* (1993)][mccarthy-prince-1993]
* [H. Dolatian, *Computational Locality of Cyclic Phonology in Armenian* (2020)][dolatian-2020]
* [A. Vásquez-Aguilar, M. K. Gordon, A. Katsika and S. Th. Gries, *Moraicity, gemination and
  syllable well-formedness in Shiwilu* (2026)][vasquez-aguilar-etal-2026]
-/

@[expose] public section

namespace Prosody

open Phonology (Segment)

/-! ### Syllables -/

/-- A nucleus-headed syllable: a non-moraic `onset`, the `nucleus`, which bears the first mora,
and the `tail` of further morae, those of a long vowel and of a moraic coda, each given by the
melody it dominates. -/
structure Syllable where
  /-- The non-moraic onset melody. -/
  onset : List Segment
  /-- The nucleus, the melody of the first mora. -/
  nucleus : List Segment
  /-- The melodies of the further morae. -/
  tail : List (List Segment)
  deriving DecidableEq

namespace Syllable

/-- Syllable weight is the mora count; `Weight.light`, `heavy`, and `superheavy` name one, two,
and three morae. -/
abbrev Weight := Nat

namespace Weight
abbrev light : Weight := 1
abbrev heavy : Weight := 2
abbrev superheavy : Weight := 3
end Weight

/-- The number of morae: the nucleus mora and the tail. -/
def moraCount (σ : Syllable) : Nat := σ.tail.length + 1

/-- The weight of a syllable, its mora count: the weight units of [hyman-1985] and the morae of
[hayes-1989]. -/
abbrev weight (σ : Syllable) : Weight := σ.moraCount

theorem moraCount_pos (σ : Syllable) : 0 < σ.moraCount := Nat.succ_pos _

/-- The mora count as a positive natural. -/
def pnatMoraCount (σ : Syllable) : ℕ+ := ⟨σ.moraCount, σ.moraCount_pos⟩

/-- A syllable is heavy when it has at least two morae. -/
def IsHeavy (σ : Syllable) : Prop := Weight.heavy ≤ σ.weight
/-- A syllable is light when it has exactly one mora. -/
def IsLight (σ : Syllable) : Prop := σ.weight = Weight.light

instance (σ : Syllable) : Decidable σ.IsHeavy := by unfold IsHeavy; infer_instance
instance (σ : Syllable) : Decidable σ.IsLight := by unfold IsLight; infer_instance

/-- The open syllable of an onset and a short vowel has one mora. -/
def ofVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, [v], []⟩

/-- The open syllable of an onset and a long vowel has two morae dominating the same melody
([hayes-1989]). -/
def ofLongVowel (onset : List Segment) (v : Segment) : Syllable := ⟨onset, [v], [[v]]⟩

@[simp] theorem moraCount_ofVowel (onset : List Segment) (v : Segment) :
    (ofVowel onset v).moraCount = 1 := rfl

@[simp] theorem moraCount_ofLongVowel (onset : List Segment) (v : Segment) :
    (ofLongVowel onset v).moraCount = 2 := rfl

end Syllable

/-! ### The nucleus of a string -/

/-- A string split at its first maximal run of syllabic segments: what precedes the run, the run,
    and what follows it. In a monosyllable the run is the nucleus, a diphthong included, and the
    rest is the material before and after it. -/
def nucleusSplit (w : List Segment) : List Segment × List Segment × List Segment :=
  let (pre, rest) := w.span fun x ↦ !decide x.IsSyllabic
  let (nuc, post) := rest.span fun x ↦ decide x.IsSyllabic
  (pre, nuc, post)

/-- The three parts of `nucleusSplit` spell out the string. -/
theorem nucleusSplit_append (w : List Segment) :
    (nucleusSplit w).1 ++ (nucleusSplit w).2.1 ++ (nucleusSplit w).2.2 = w := by
  simp only [nucleusSplit, List.span_eq_takeWhile_dropWhile, List.append_assoc,
    List.takeWhile_append_dropWhile]

/-! ### Yields -/

/-- A *yield* is the string of syllable weights of a prosodic structure, the unparsed input or
    the leaves of a prosodic `Tree`. Unlike a prosodic word, which is a headed constituent, a
    yield has no head and no constituency. -/
abbrev Yield := List Syllable.Weight

namespace Yield

/-- The weight profile of a string of syllables. -/
def ofSyllables (σs : List Syllable) : Yield := σs.map Syllable.weight

/-- The total mora count of a yield. -/
def moraCount (y : Yield) : Nat := y.sum

/-- A minimal-word condition: the yield has at least `minMorae` morae, by default two, the
    bimoraic minimum that [mccarthy-prince-1993] derives from the Prosodic Hierarchy and Foot
    Binarity. The condition does not ask for a foot, since some languages show no evidence for
    feet, as [dolatian-2020] reports of Armenian. -/
abbrev satisfiesMinWord (y : Yield) (minMorae : Nat := 2) : Prop := minMorae ≤ y.moraCount

end Yield

end Prosody
