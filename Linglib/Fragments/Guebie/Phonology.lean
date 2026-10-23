/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Guébie vowels

Guébie (Kru; Côte d'Ivoire) has ten vowels, five [+ATR] vowels /i e ə o u/ paired with five
[−ATR] vowels /ɪ ɛ a ɔ ʊ/, as Sande describes them. The pairs agree in backness and rounding,
and in height except for /ə a/. Vowels within a morpheme agree in [ATR], and affixes harmonize
with roots.

The feature values come from the PHOIBLE chart, which codes the tongue-root contrast by
[tense], so a vowel is the segment of its chart entry's tongue-root reading. The chart's /ə/
is [−tense], and Guébie's /ə/ departs from it in being [+ATR].

## Main definitions

* `Guebie.i`, `Guebie.schwa` and the like: the ten vowels, and `Guebie.vowels` the set of them.
* `Guebie.atr`: a segment's [ATR] value.
* `Guebie.withATR`: the member of a vowel's pair with a given [ATR] value.

## Main results

* `Guebie.withATR_atr`: a segment's own [ATR] value leaves it unchanged.
* `Guebie.atr_withATR`: the member of a vowel's pair with a value has that value.

## References

* [sande-2022]
* [moran-mccloy-2019]
-/

@[expose] public section

namespace Guebie

open Phonology

/-- A vowel is the segment of its chart entry's tongue-root reading, with its departure. -/
def vowel (m : Data.PHOIBLE.FeatureMatrix) (departure : Segment := ⊥) : Segment :=
  .ofChart m.tenseAsATR departure

/-- The advanced high front vowel /i/. -/
def i : Segment := vowel .«i»

/-- The advanced mid front vowel /e/. -/
def e : Segment := vowel .«e»

/-- The advanced mid central vowel /ə/. -/
def schwa : Segment := vowel .«ə» (.ofSpecs [(.atr, true)])

/-- The advanced mid back vowel /o/. -/
def o : Segment := vowel .«o»

/-- The advanced high back vowel /u/. -/
def u : Segment := vowel .«u»

/-- The unadvanced high front vowel /ɪ/. -/
def smallCapitalI : Segment := vowel .«ɪ»

/-- The unadvanced mid front vowel /ɛ/. -/
def epsilon : Segment := vowel .«ɛ»

/-- The unadvanced low vowel /a/. -/
def a : Segment := vowel .«a»

/-- The unadvanced mid back vowel /ɔ/. -/
def openO : Segment := vowel .«ɔ»

/-- The unadvanced high back vowel /ʊ/. -/
def upsilon : Segment := vowel .«ʊ»

/-- The ten vowels, pairwise distinct. -/
def vowels : Finset Segment :=
  ⟨↑[i, e, schwa, o, u, smallCapitalI, epsilon, a, openO, upsilon], by decide⟩

/-- A segment's [ATR] value, `true` for [+ATR]. -/
def atr (x : Segment) : Bool := decide (x.HasValue .atr true)

theorem atr_iff : ∀ x ∈ vowels, atr x = true ↔ x ∈ ({i, e, schwa, o, u} : Finset Segment) := by
  decide

/-- The ±ATR pairs, the [+ATR] member first, are /i ɪ/, /e ɛ/, /ə a/, /o ɔ/ and /u ʊ/. -/
def pairs : List (Segment × Segment) :=
  [(i, smallCapitalI), (e, epsilon), (schwa, a), (o, openO), (u, upsilon)]

/-- The member of a vowel's pair with the given [ATR] value. The pair /ə a/ differs in height
too, so this is not `Segment.setFeature .atr`. A segment in no pair is left unchanged. -/
def withATR (x : Segment) (b : Bool) : Segment :=
  match pairs.find? fun p ↦ p.1 = x ∨ p.2 = x with
  | some p => if b then p.1 else p.2
  | none => x

@[simp] theorem withATR_atr (x : Segment) : withATR x (atr x) = x := by
  unfold withATR
  split
  · next p hp =>
    have hx := List.find?_some hp
    simp only [decide_eq_true_eq] at hx
    have hmem := List.mem_of_find?_eq_some hp
    simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rcases hx with rfl | rfl <;> decide
  · rfl

theorem atr_withATR : ∀ x ∈ vowels, ∀ b, atr (withATR x b) = b := by decide

end Guebie
