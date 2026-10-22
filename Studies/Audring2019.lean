/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Wordlist.Audring2019
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Linglib.Core.Logic.Function.FactorsThrough
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Audring (2019): Mothers or sisters? The encoding of morphological knowledge

This file formalizes Audring's division of labour between mother schemas and sister links
in a full-entry lexicon. A generalization over stored words can be encoded by a mother schema
dominating them or by sister links, coindices between the words themselves. A sister link is a
subscripting through which the pair of words factors, so it captures relations of sameness:
*boyish* and *childish* are sisters at the affix (`ish_affix_sisters`) but cannot be coindexed
at the base, where their fillers differ (`not_base_sisters`). The mother `[N -ish]A` of (8)
relates every member of the family through one variable (`ishSchema_relates`), which is what
states that different bases serve the same function. The mother also carries productivity: it
generates *Trumpish* over an empty lexicon (`ishSchema_generates_trumpish`), whereas a fully
specified word generates nothing but itself (`word_generates_iff`).

The second-order schema `[N -ful]A ≈ [N -less]A` of (14) is a sister link between mother
schemas, one description over a shared base variable read through two subscriptings. The
coindexed base pairs *careful* with *careless* and not with *clueless*
(`careful_careless_pairs`, `not_careful_clueless_pairs`). A mother of the two schemas would be
the meet of their descriptions, which over these slots is empty (`fulLess_mother_eq_bot`) and
so is instantiated by every word (`fulLess_mother_instantiates`): it states nothing the sisters
do not, and cannot state the pairing they do.

## Implementation notes

* The words are the CLDF forms of `Data/Wordlist/Audring2019.json`, read as slot-indexed segments
  by `Data.Wordlist.Form.slots`: a base slot and an affix slot on the flat carrier, one tier of the
  paper's three; the same subscripting mechanism coindexes across tiers. The paper's remaining
  cases for a mother, an antonymic scale and the feature matrix of an inflectional paradigm,
  are not formalized.

## References

* [audring-2019]
* [booij-2019]
-/

@[expose] public section

namespace Audring2019

open ConstructionMorphology

/-- A word with base `b` and affix `a` over the two slots base and affix. -/
def word (b a : String) : Fin 2 → Flat String := ![↑b, ↑a]

/-! ### The *-ish* family: sister links and their mother -/

/-- The mother schema `[N -ish]A` of (8) has its affix pinned and its base an open variable. -/
def ishSchema : Schema (Fin 2) (Flat String) := Schema.productive ![⊥, ↑"ish"]

/-- The stored family of (8). -/
def ishFamily : Set (Fin 2 → Flat String) :=
  {Wordlist.boyish.slots, Wordlist.foolish.slots, Wordlist.childish.slots}

/-- Any word whose affix is *-ish* instantiates the mother. -/
theorem ishSchema_instantiates {w : Fin 2 → Flat String} (h : w 1 = ↑"ish") :
    ishSchema.Instantiates w := by
  intro i
  fin_cases i
  · exact bot_le
  · exact h.ge

/-- The variables of a sister link coindexing the affixes of two words. -/
inductive AffixLink
  | base₁
  | base₂
  | affix
  deriving DecidableEq

/-- The sister link at the affix makes the two affix slots share a variable and leaves the bases
apart. -/
def affixLink : Fin 2 ⊕ Fin 2 → AffixLink := Sum.elim ![.base₁, .affix] ![.base₂, .affix]

/-- The variables of a sister link coindexing the bases of two words. -/
inductive BaseLink
  | base
  | affix₁
  | affix₂
  deriving DecidableEq

/-- The sister link at the base makes the two base slots share a variable and leaves the affixes
apart. -/
def baseLink : Fin 2 ⊕ Fin 2 → BaseLink := Sum.elim ![.base, .affix₁] ![.base, .affix₂]

/-- *boyish* and *childish* are sisters at the affix, since the pair factors through the link. -/
theorem ish_affix_sisters :
    (Sum.elim Wordlist.boyish.slots Wordlist.childish.slots).FactorsThrough affixLink := by
  decide

/-- *boyish* and *childish* cannot be coindexed at the base. The relation between *boy* and
*child* is equivalence of function, not sameness, and no sister link states it. -/
theorem not_base_sisters :
    ¬ (Sum.elim Wordlist.boyish.slots Wordlist.childish.slots).FactorsThrough baseLink := by
  decide

/-- The mother relates every member of the family through its one variable. -/
theorem ishSchema_relates {w : Fin 2 → Flat String} (hw : w ∈ ishFamily) :
    ishSchema.Relates ishFamily w := by
  refine ⟨hw, ?_⟩
  simp only [ishFamily, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> exact ishSchema_instantiates (by decide)

/-- The mother is productive, since its one variable is open. -/
theorem ishSchema_isProductive : ishSchema.IsProductive := Schema.isProductive_productive _

/-- The mother generates the novel *Trumpish* with nothing stored. -/
theorem ishSchema_generates_trumpish : ishSchema.Generates ∅ Wordlist.trumpish.slots :=
  ishSchema_isProductive.generates_iff.2 (ishSchema_instantiates (by decide))

/-- A fully specified word, taken as a schema, generates nothing but itself. A sister link
between stored words therefore licenses no novel word, and productivity needs a mother's
variable. -/
theorem word_generates_iff (b a : String) {Λ : Set (Fin 2 → Flat String)}
    {w : Fin 2 → Flat String} :
    (⟨word b a, ∅⟩ : Schema (Fin 2) (Flat String)).Generates Λ w ↔ w = word b a := by
  have hmax : ∀ v, IsMax (word b a v) := fun v ↦ by fin_cases v <;> exact Flat.isMax_coe _
  refine ⟨fun h ↦ (Schema.instantiates_iff_eq_of_forall_isMax hmax).1 h.instantiates, ?_⟩
  rintro rfl
  exact ⟨le_rfl, fun v hv _ ↦ by fin_cases v <;> exact absurd hv Flat.coe_ne_bot⟩

/-! ### The second-order schema `[N -ful]A ≈ [N -less]A` -/

/-- The variables of (14) are the base shared by the two schemas and the two affixes. -/
inductive FulLessVar
  | base
  | ful
  | less
  deriving DecidableEq

/-- The second-order schema (14) is the two schemas with their coindexed base as one
description. -/
def fulLess : Schema FulLessVar (Flat String) :=
  ⟨fun | .base => ⊥ | .ful => ↑"ful" | .less => ↑"less", {.base}⟩

/-- The subscripting of the slots of `[N -ful]A` by the variables of (14). -/
def fulSub : Fin 2 → FulLessVar := ![.base, .ful]

/-- The subscripting of the slots of `[N -less]A` by the variables of (14). -/
def lessSub : Fin 2 → FulLessVar := ![.base, .less]

/-- The schema `[N -ful]A` is the description of (14) read at its own slots. -/
def fulSchema : Schema (Fin 2) (Flat String) := fulLess.comap fulSub

/-- The schema `[N -less]A` is the description of (14) read at its own slots. -/
def lessSchema : Schema (Fin 2) (Flat String) := fulLess.comap lessSub

/-- The variables of (14) filled by base `b`. -/
def fulLessWord (b : String) : FulLessVar → Flat String
  | .base => ↑b
  | .ful => ↑"ful"
  | .less => ↑"less"

/-- *careful* and *careless* are a paired instantiation of (14), with the same base and sister
affixes. -/
theorem careful_careless_pairs :
    fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim Wordlist.careful.slots Wordlist.careless.slots) :=
  ⟨fulLessWord "care", fun v ↦ by cases v <;> first | exact bot_le | exact le_rfl,
    funext fun p ↦ by rcases p with p | p <;> fin_cases p <;> decide⟩

/-- *careful* and *clueless* are not a paired instantiation, since the coindexed base is filled
differently. -/
theorem not_careful_clueless_pairs :
    ¬ fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim Wordlist.careful.slots Wordlist.clueless.slots) :=
  fun h ↦ absurd ((Schema.instantiatesAt_elim_iff.1 h).2.2.2.2 0 0 rfl) (by decide)

/-- A mother of the two schemas would be the meet of their descriptions, which over these slots
is empty. It holds nothing but the categories, which the slots do not record. -/
theorem fulLess_mother_eq_bot : fulSchema.body ⊓ lessSchema.body = ⊥ := by
  funext v
  fin_cases v <;> decide

/-- The mother is instantiated by every word, so it states nothing the sisters do not. -/
theorem fulLess_mother_instantiates (w : Fin 2 → Flat String) :
    (⟨fulSchema.body ⊓ lessSchema.body, ∅⟩ : Schema (Fin 2) (Flat String)).Instantiates
      w := by
  show fulSchema.body ⊓ lessSchema.body ≤ w
  rw [fulLess_mother_eq_bot]
  exact bot_le

end Audring2019
