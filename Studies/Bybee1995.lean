/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Wordlist.Bybee1995
public import Linglib.Morphology.ConstructionMorphology.Schema
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

variable {P α : Type*} [PartialOrder α]

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

/-- Types are at most tokens. -/
theorem typeFrequency_le_tokenFrequency (s : Schema P α) [DecidablePred s.Instantiates]
    (c : Multiset (P → α)) : typeFrequency s c ≤ tokenFrequency s c :=
  Multiset.countP_le_of_le _ (Multiset.dedup_le c)

/-- A more general schema has the larger type frequency. -/
theorem typeFrequency_mono {s t : Schema P α} [DecidablePred s.Instantiates]
    [DecidablePred t.Instantiates] (h : t.body ≤ s.body) (c : Multiset (P → α)) :
    typeFrequency s c ≤ typeFrequency t c := by
  unfold typeFrequency
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card
    (Multiset.monotone_filter_right _ λ _ hw => Schema.body_le_body_iff.1 h hw)

end Frequency

/-! ### Openness -/

/-- The English past in *-ed*, over a base slot and an affix slot: the base open, so totally
open in the sense of `Schema.isProductive_iff_forall_generates_iff`. -/
def edSchema : Schema (Fin 2) (Flat String) := Schema.productive ![⊥, ↑"ed"]

theorem edSchema_isProductive : edSchema.IsProductive := Schema.isProductive_productive _

/-! ### The product-oriented class of *strung* -/

/-- The product-oriented schema of the *strung* class over onset, nucleus and coda: the
nucleus pinned to /ʌ/, the onset open, the coda a closed variable filled from the class. -/
def strungSchema : Schema (Fin 3) (Flat String) := ⟨![⊥, ↑"ʌ", ⊥], {0}⟩

/-- The stored members of the class. -/
def strungClass : Set (Fin 3 → Flat String) :=
  {Wordlist.strung.slots, Wordlist.stung.slots, Wordlist.flung.slots, Wordlist.hung.slots}

/-- The dialectal new members fit the shape of the class. -/
theorem struck_instantiates :
    strungSchema.Instantiates Wordlist.struck.slots ∧
      strungSchema.Instantiates Wordlist.snuck.slots ∧
      strungSchema.Instantiates Wordlist.drug.slots := by
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
def sourceOriented : Schema PairVar (Flat String) :=
  ⟨λ | .base => ↑"ɪ" | .past => ↑"ʌ" | _ => ⊥, {.onset, .coda}⟩

/-- The subscripting of the base's positions. -/
def baseSub : Fin 3 → PairVar := ![.onset, .base, .coda]

/-- The subscripting of the past's positions. -/
def pastSub : Fin 3 → PairVar := ![.onset, .past, .coda]

/-- *string* and *strung* are a paired instantiation of the source-oriented schema. -/
theorem string_strung_pairs :
    sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
      (Sum.elim Wordlist.string.slots Wordlist.strung.slots) :=
  ⟨λ | .onset => ↑"str" | .coda => ↑"ŋ" | .base => ↑"ɪ" | .past => ↑"ʌ",
    λ v => by cases v <;> decide,
    funext λ p => by rcases p with p | p <;> fin_cases p <;> decide⟩

/-- The new members are not: their bases lack /ɪ/, so no source-oriented schema pairs them,
while the product-oriented schema admits them. -/
theorem not_sourceOriented_pairs :
    ¬ sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
        (Sum.elim Wordlist.strike.slots Wordlist.struck.slots) ∧
      ¬ sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
        (Sum.elim Wordlist.sneak.slots Wordlist.snuck.slots) ∧
      ¬ sourceOriented.InstantiatesAt (Sum.elim baseSub pastSub)
        (Sum.elim Wordlist.drag.slots Wordlist.drug.slots) := by
  refine ⟨λ h => ?_, λ h => ?_, λ h => ?_⟩ <;>
    exact absurd (Flat.coe_le_iff.1 ((Schema.instantiatesAt_elim_iff.1 h).1 1)) (by decide)

end Bybee1995
