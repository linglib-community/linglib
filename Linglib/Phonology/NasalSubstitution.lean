module

public import Linglib.Phonology.Segmental.FeatureClass
public import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Nasal place assimilation and nasal substitution

This file defines the assimilation of a nasal to the place of a following consonant, and nasal
substitution, in which the consonant is in addition not realized.

Many Austronesian languages have prefixes that end in a nasal. The nasal takes the place of a
stem-initial obstruent, and in nasal substitution the two surface as one nasal at that place, as
in Tagalog *mamigáj* from *maŋ-* and *bigáj*. Following Donohue, substitution is assimilation
together with the loss of the obstruent. A language fixes which consonants trigger assimilation
and which substitute.

## Main definitions

* `placeAssimilation`: a nasal takes the place class of a following segment of a trigger class.
* `nonstrident`, `nonlateral`, `defaultPlace`: the rules that keep the assimilated nasal a
  possible nasal.
* `assimilate`: the four rules in sequence, over a whole word.
* `substitute`: the nasal that a nasal and a following consonant surface as under substitution.

## Main results

* `length_assimilate`, `length_substitute`: assimilation preserves the length of a word, and
  substitution yields one segment.

## Implementation notes

The place class contains [strident] and [lateral], which the PHOIBLE chart specifies on coronals
alone. A nasal assimilated to a sibilant or a lateral copies `+` for them, so `nonstrident` and
`nonlateral` reset it, and a nasal assimilated to a consonant with no oral articulator, such as
a glottal stop, loses its place, which `defaultPlace` restores.

## References

* [B. P. Hayes, *Introductory Phonology* (2009)][hayes-2009]
* [M. Donohue, *Phonotactics and morphophonology* (2024)][donohue-2024]
* [J. Pater, *Austronesian nasal substitution revisited: what's wrong with \*NC (and what's
  not)* (2001)][pater-2001]
* [K. Zuraw, *A model of lexical variation and the grammar with application to Tagalog nasal
  substitution* (2010)][zuraw-2010]
-/

@[expose] public section

namespace Phonology.NasalSubstitution

open Subregular.LocalRewrite

/-- A nasal takes the place of a following segment of the class `trigger`. -/
def placeAssimilation (trigger : Segment) : Rule where
  target := Segment.ofSpecs [(.nasal, true)]
  effect := .copyRight FeatureClass.place
  rightContext := [.seg trigger]

/-- A nasal is not strident. -/
def nonstrident : Rule where
  target := Segment.ofSpecs [(.nasal, true), (.strident, true)]
  effect := .changeFeatures (Segment.ofSpecs [(.strident, false)])

/-- A nasal is not lateral. -/
def nonlateral : Rule where
  target := Segment.ofSpecs [(.nasal, true), (.lateral, true)]
  effect := .changeFeatures (Segment.ofSpecs [(.lateral, false)])

/-- A nasal with no oral articulator is the nasal `N`. -/
def defaultPlace (N : Segment) : Rule where
  target := Segment.ofSpecs [(.nasal, true), (.labial, false), (.coronal, false), (.dorsal, false)]
  effect := .replace N

/-- The rules of nasal place assimilation, for the triggers `trigger` and the default nasal
`N`. -/
def rules (trigger N : Segment) : List Rule :=
  [placeAssimilation trigger, nonstrident, nonlateral, defaultPlace N]

/-- `assimilate trigger N w` is the word `w` with each nasal assimilated to a following segment
of the class `trigger`. -/
def assimilate (trigger N : Segment) : List Segment → List Segment := derive (rules trigger N)

/-- `substitute trigger N x` is what the nasal `N` and a following `x` surface as under nasal
substitution, which is the assimilated nasal alone. -/
def substitute (trigger N x : Segment) : List Segment := (assimilate trigger N [N, x]).take 1

/-- Assimilation neither deletes nor inserts a segment. -/
theorem length_assimilate (trigger N : Segment) (w : List Segment) :
    (assimilate trigger N w).length = w.length :=
  length_derive (by simp [rules, placeAssimilation, nonstrident, nonlateral, defaultPlace]) w

/-- Substitution yields one segment. -/
theorem length_substitute (trigger N x : Segment) : (substitute trigger N x).length = 1 := by
  simp [substitute, length_assimilate]

end Phonology.NasalSubstitution
