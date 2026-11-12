/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Wordlist.Audring2019
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic.FinCases

/-!
# Audring (2019): Mothers or sisters? The encoding of morphological knowledge

A generalization over stored words can be encoded by a mother schema that dominates them or by
sister links, coindices between the words themselves. This file formalizes the division of labour
that [audring-2019] draws between the two in a full-entry lexicon.

A sister link states sameness. The adjectives *boyish*, *foolish* and *childish*
[share their affix and differ in their bases](##same_affix_contrast), so that no coindex between
them states what the bases have in common, which is a function. The mother `[N -ish]A` states it
with a variable. It is [the greatest description that every sister instantiates](##isGLB_ishFamily),
and the variable also carries productivity, since
[a stored word generates nothing but itself](##word_generates_iff).

The second-order schema `[N -ful]A ≈ [N -less]A` is a sister link between mother schemas, which
[pairs the two adjectives of one base](##fulLess_pairs_iff). The pairing is
[no product of conditions on single words](##fulLess_ne_prod), so a mother of the two schemas
cannot state it. Second-order schemas are also the subject of [booij-2019].

## Implementation notes

* The words are the CLDF forms of `Data/Wordlist/Audring2019.json`, read by `slots` as a base
  slot and an affix slot on the flat carrier. This is one tier of the paper's three; the same
  coindexation links the tiers.
* A sister link between two words is `ConstructionMorphology.Contrast`, sameness outside a set of
  slots and incompatible fillers inside it.
* Not formalized: the mother as a relational hub for a large family, the lexical mother *child*
  of *childish* and *childless*, sister schemas that are not productive in both directions
  (*clueless* without *clueful*), and the two further cases for a mother, an antonymic scale and
  the feature matrix of an inflectional paradigm.

## References

* [audring-2019]
* [booij-2019]
-/

@[expose] public section

namespace Audring2019

open ConstructionMorphology CLDF.Wordlist

/-- The morphs of a form read as a base slot and an affix slot, with `⊥` where a morph is
missing. -/
def slots (f : Form Wordlist.Cell) (i : Fin 2) : Flat String := f.morphs[i.val]?.elim ⊥ Flat.some

/-! ### The *-ish* family: sister links and their mother -/

/-- (8): The mother schema `[N -ish]A` has its affix pinned and its base an open variable. -/
def ishSchema : Schema (Fin 2) (Flat String) := .productive ![⊥, ↑"ish"]

/-- (8): The stored family. -/
def ishFamily : Set (Fin 2 → Flat String) :=
  {slots Wordlist.boyish, slots Wordlist.foolish, slots Wordlist.childish}

/-- The sisters of the *-ish* family are the same at the affix and fill the base differently, so
a sister link coindexes their affixes and cannot coindex their bases. -/
theorem same_affix_contrast : ∀ r ∈ Wordlist.relations, r.relation = "same_affix" →
    Contrast (slots r.form) (slots r.target) {0} := by
  decide

-- (10), (11): *childish* and *childless* are sisters at the base
theorem same_stem_contrast : ∀ r ∈ Wordlist.relations, r.relation = "same_stem" →
    Contrast (slots r.form) (slots r.target) {1} := by
  decide

-- (8): the meet of any two sisters is already the mother
theorem inf_eq_ishSchema_body : ∀ r ∈ Wordlist.relations, r.relation = "same_affix" →
    slots r.form ⊓ slots r.target = ishSchema.body := by
  decide

-- (8): the variable of the mother stands where the sisters differ, and each base fills it
theorem ishSchema_instantiation {r : FormRelation (Form Wordlist.Cell)}
    (hr : r ∈ Wordlist.relations) (h : r.relation = "same_affix") :
    Instantiation ishSchema.body (slots r.form) {0} ∧
      Instantiation ishSchema.body (slots r.target) {0} :=
  ⟨inf_eq_ishSchema_body r hr h ▸ (same_affix_contrast r hr h).instantiation_inf,
    (inf_comm _ _).trans (inf_eq_ishSchema_body r hr h) ▸
      (same_affix_contrast r hr h).symm.instantiation_inf⟩

/-- The mother is the greatest description that every stored sister instantiates, so it states
what the family shares and nothing more. -/
theorem isGLB_ishFamily : IsGLB ishFamily ishSchema.body := by
  have h : ishSchema.body =
      slots Wordlist.boyish ⊓ (slots Wordlist.foolish ⊓ slots Wordlist.childish) := by
    decide
  exact h ▸ isGLB_pair.insert _

theorem ishSchema_relates {w : Fin 2 → Flat String} (hw : w ∈ ishFamily) :
    ishSchema.Relates ishFamily w :=
  ⟨hw, isGLB_ishFamily.1 hw⟩

-- §4.1: the open variable accepts the novel *Trumpish* with nothing stored
theorem ishSchema_generates_trumpish : ishSchema.Generates ∅ (slots Wordlist.trumpish) :=
  (Schema.isProductive_productive _).generates_iff.2 (by decide)

/-- A stored word, taken as a schema, generates nothing but itself, so a systematically
productive pattern needs a mother with a variable. -/
theorem word_generates_iff {Λ : Set (Fin 2 → Flat String)} {u : Fin 2 → Flat String} :
    ∀ f ∈ Wordlist.all, (Schema.nonproductive (slots f)).Generates Λ u ↔ u = slots f :=
  fun f hf ↦ Schema.generates_iff_eq_of_forall_ne_bot
    ((by decide : ∀ f ∈ Wordlist.all, ∀ v, slots f v ≠ ⊥) f hf)

/-! ### The second-order schema `[N -ful]A ≈ [N -less]A` -/

/-- The variables of (14) are the base shared by the two schemas and the two affixes. -/
inductive FulLessVar
  | base
  | ful
  | less
  deriving DecidableEq

/-- (14): The second-order schema is the two schemas with their coindexed base as one
description. -/
def fulLess : Schema FulLessVar (Flat String) :=
  .productive fun | .base => ⊥ | .ful => ↑"ful" | .less => ↑"less"

/-- The subscripting of the slots of `[N -ful]A` by the variables of (14). -/
def fulSub : Fin 2 → FulLessVar := ![.base, .ful]

/-- The subscripting of the slots of `[N -less]A` by the variables of (14). -/
def lessSub : Fin 2 → FulLessVar := ![.base, .less]

/-- The schema `[N -ful]A` is the description of (14) read at its own slots. -/
def fulSchema : Schema (Fin 2) (Flat String) := fulLess.comap fulSub

/-- The schema `[N -less]A` is the description of (14) read at its own slots. -/
def lessSchema : Schema (Fin 2) (Flat String) := fulLess.comap lessSub

/-- The second-order schema pairs an *-ful* adjective with a *-less* adjective exactly when the
two have the same base. -/
theorem fulLess_pairs_iff {p q : Fin 2 → Flat String} :
    fulLess.InstantiatesAt (Sum.elim fulSub lessSub) (Sum.elim p q) ↔
      ∃ b, p = ![b, ↑"ful"] ∧ q = ![b, ↑"less"] := by
  rw [Schema.instantiatesAt_elim_iff_exists_fill]
  refine ⟨fun ⟨x, hp, hq⟩ ↦ ⟨x .base, ?_, ?_⟩, fun ⟨b, hp, hq⟩ ↦ ⟨fun _ ↦ b, ?_, ?_⟩⟩ <;>
  · subst_vars
    funext i
    fin_cases i <;> rfl

-- (12), §5: *helpful* with *helpless* and *careful* with *careless*
theorem second_order_pairs : ∀ r ∈ Wordlist.relations, r.relation = "second_order_schema" →
    fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim (slots r.form) (slots r.target)) := by
  decide

-- the coindexed base is filled differently
theorem not_careful_clueless_pairs :
    ¬ fulLess.InstantiatesAt (Sum.elim fulSub lessSub)
      (Sum.elim (slots Wordlist.careful) (slots Wordlist.clueless)) := by
  decide

/-- No conditions on the *-ful* and the *-less* adjectives separately pair them as the
second-order schema does, so neither a mother of the two schemas nor any other schema over single
words states the pairing. -/
theorem fulLess_ne_prod (A B : Set (Fin 2 → Flat String)) :
    {(x, y) : (Fin 2 → Flat String) × (Fin 2 → Flat String) |
      fulLess.InstantiatesAt (Sum.elim fulSub lessSub) (Sum.elim x y)} ≠ A ×ˢ B :=
  Schema.setOf_instantiatesAt_elim_ne_prod (s := fulLess) (pos₁ := fulSub) (pos₂ := lessSub)
    (w₁ := slots Wordlist.careful) (w₂ := slots Wordlist.careless)
    (w₁' := slots Wordlist.helpful) (w₂' := slots Wordlist.helpless)
    (by decide) (by decide) (a := 0) (b := 0) rfl (by decide) A B

-- (14): a mother of the two schemas holds nothing but the categories, which the slots do not
-- record
theorem fulLess_mother_eq_bot : fulSchema.body ⊓ lessSchema.body = ⊥ := by
  decide

theorem fulLess_mother_instantiates (w : Fin 2 → Flat String) :
    (Schema.nonproductive (fulSchema.body ⊓ lessSchema.body)).Instantiates w :=
  Schema.instantiates_iff.2 (fulLess_mother_eq_bot.trans_le bot_le)

end Audring2019
