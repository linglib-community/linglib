/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Wordlist.Bybee1995
public import Linglib.Fragments.English.Phonology
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Linglib.Phonology.Prosody.Syllable
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Bybee (1995): Regular morphology and the lexicon

This file formalizes [bybee-1995]'s network model of productivity, in which schemas emerge
over stored forms and the productivity of a schema is determined by two things: its type
frequency, the number of distinct forms instantiating it, and the openness of its variables.
Token frequency does the opposite work, strengthening an individual form's own entry. Over a
corpus of tokens, a schema's type frequency counts the distinct forms it relates and its token
frequency counts every occurrence (`typeFrequency_le_tokenFrequency`), and a more general
schema has the larger type frequency (`typeFrequency_mono`). What a schema generates depends
on the corpus only through its types, since the lexicon of its roles is the corpus's set of
types, so repetition of a stored form leaves its generative capacity unchanged. Openness is the
other determinant: a schema generates every instance whatever is stored exactly when all of
its variables are open (`Schema.isProductive_iff_forall_generates_iff`), which is what makes
the English past in *-ed* fully productive (`edSchema_isProductive`).

Schemas are product-oriented: generalizations over the derived forms themselves, not over
pairs of base and derived form. The class of *strung* is the shape of its past tenses, and the
dialectal new members *struck*, *snuck* and *drug* fit that shape (`struck_instantiates`) while
their bases lack the vowel a source-oriented pairing from *string* would demand
(`not_sourceOriented_pairs`), the finding of [bybee-moder-1983].

## Implementation notes

* A corpus is a multiset of forms; the lexicon of a schema's roles is its set of types.
* The forms of `Data/Wordlist/Bybee1995.json` are read through the English transcription and
  split at the nucleus, so the slot before the nucleus also holds the *s* of *str-*, which core
  syllabification leaves outside the onset, and the nucleus of *strike* is its diphthong.
* The counts of Table 8.1, the French conjugations children overgeneralize by type rather than
  token frequency, and the German participle and plural cases are not formalized.

## References

* [bybee-1995]
* [bybee-2007]
* [bybee-moder-1983]
-/

@[expose] public section

namespace Bybee1995

open ConstructionMorphology
open Phonology (Segment)

variable {P α : Type*} [PartialOrder α] [OrderBot α]

/-! ### Type frequency and token frequency -/

section Frequency
variable [DecidableEq (P → α)]

/-- The type frequency of a schema over a corpus: the number of distinct forms instantiating
it. -/
def typeFrequency (s : Schema P α) [DecidablePred s.Instantiates] (c : Multiset (P → α)) :
    ℕ :=
  c.dedup.countP s.Instantiates

/-- The token frequency of a schema over a corpus: the number of occurrences of forms
instantiating it. -/
def tokenFrequency (s : Schema P α) [DecidablePred s.Instantiates] (c : Multiset (P → α)) :
    ℕ :=
  c.countP s.Instantiates

theorem typeFrequency_le_tokenFrequency (s : Schema P α) [DecidablePred s.Instantiates]
    (c : Multiset (P → α)) : typeFrequency s c ≤ tokenFrequency s c :=
  Multiset.countP_le_of_le _ (Multiset.dedup_le c)

theorem typeFrequency_mono {s t : Schema P α} [DecidablePred s.Instantiates]
    [DecidablePred t.Instantiates] (h : t.body ≤ s.body) (c : Multiset (P → α)) :
    typeFrequency s c ≤ typeFrequency t c := by
  unfold typeFrequency
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card
    (Multiset.monotone_filter_right _ fun _ hw ↦ Schema.body_le_body_iff.1 h hw)

end Frequency

/-! ### Openness -/

/-- The English past in *-ed*, over a base slot and an affix slot: the base open, so totally
open in the sense of `Schema.isProductive_iff_forall_generates_iff`. -/
def edSchema : Schema (Fin 2) (Flat String) := Schema.productive ![⊥, ↑"ed"]

theorem edSchema_isProductive : edSchema.IsProductive := Schema.isProductive_productive _

/-! ### The product-oriented class of *strung* -/

/-- A form read through its English segments as what precedes its nucleus, the nucleus and the
coda, or as `⊥` throughout if a glyph is not English. -/
def syllable {C : Type*} (f : CLDF.Wordlist.Form C) : Fin 3 → Flat (List Segment) :=
  (English.Phonology.transcribe f.segments).elim ⊥ fun w ↦
    ![↑(Prosody.nucleusSplit w).1, ↑(Prosody.nucleusSplit w).2.1, ↑(Prosody.nucleusSplit w).2.2]

/-- Every form is in the English transcription, so `syllable` reads none as `⊥`. -/
theorem transcribe_ne_none :
    ∀ f ∈ Wordlist.all, English.Phonology.transcribe f.segments ≠ none := by
  decide

/-- The product-oriented schema of the *strung* class over onset, nucleus and coda: the
nucleus pinned to /ʌ/, the onset open, the coda a closed variable filled from the class. -/
def strungSchema : Schema (Fin 3) (Flat (List Segment)) :=
  ⟨![⊥, ↑[English.Phonology.wedge], ⊥], {0}, by rintro _ rfl; rfl⟩

/-- The stored members of the class. -/
def strungClass : Set (Fin 3 → Flat (List Segment)) :=
  {syllable Wordlist.strung, syllable Wordlist.stung, syllable Wordlist.flung,
    syllable Wordlist.hung}

theorem struck_instantiates :
    strungSchema.Instantiates (syllable Wordlist.struck) ∧
      strungSchema.Instantiates (syllable Wordlist.snuck) ∧
      strungSchema.Instantiates (syllable Wordlist.drug) := by
  decide

/-- The variables of a source-oriented pairing of base and past: the shared onset and coda,
and the two nuclei. -/
inductive PairVar
  | onset
  | coda
  | base
  | past
  deriving DecidableEq

/-- A source-oriented schema pairing a base in /ɪ/ with a past in /ʌ/ over a shared onset and
coda: the generalization over pairs such as *string*, *strung*. -/
def sourceOriented : Schema PairVar (Flat (List Segment)) :=
  ⟨fun
    | .base => ↑[English.Phonology.smallCapitalI]
    | .past => ↑[English.Phonology.wedge]
    | _ => ⊥, {.onset, .coda},
    by rintro _ (rfl | rfl) <;> rfl⟩

/-- The subscripting of the base's positions. -/
def baseSub : Fin 3 → PairVar := ![.onset, .base, .coda]

/-- The subscripting of the past's positions. -/
def pastSub : Fin 3 → PairVar := ![.onset, .past, .coda]

theorem string_strung_pairs :
    sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
      (Sum.elim (syllable Wordlist.string) (syllable Wordlist.strung)) := by
  decide

theorem not_sourceOriented_pairs :
    ¬ sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
        (Sum.elim (syllable Wordlist.strike) (syllable Wordlist.struck)) ∧
      ¬ sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
        (Sum.elim (syllable Wordlist.sneak) (syllable Wordlist.snuck)) ∧
      ¬ sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
        (Sum.elim (syllable Wordlist.drag) (syllable Wordlist.drug)) := by
  decide

end Bybee1995
