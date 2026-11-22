module

public import Linglib.Data.Statistics.Bybee1985
public import Linglib.Morphology.Morphotactics.RelevanceHierarchy
public import Mathlib.Algebra.BigOperators.Expect

/-!
# Bybee 1985: relevance and lexical strength

[bybee-1985] codes the verbal morphology of a stratified sample of fifty languages
([perkins-1980]'s) for valence, voice, aspect, tense, mood and number, person and gender
agreement. `Category.relevance` sends each coded category to its place on the relevance
hierarchy, the agreement categories all to `RelevanceHierarchy.agreement`.

For two categories `a` and `b` we write `closerCount a b` for the number of languages in which
the marker of `a` stands closer to the verb stem than the marker of `b`, and `Closer a b` when
`closerCount b a < closerCount a b`. The counts are reported for aspect, tense, mood and person.
On those four categories `Closer` is the relevance order: `closerEmbedding` is a relation
embedding of `Closer` into `<` on the hierarchy, so `Closer` is a strict total order there.

The share of languages that express a category on the verb, inflectionally or derivationally, is
greatest for valence, which has the smallest share once only inflection is counted
(`morphological_le_valence`, `valence_inflectional_le`).

The modern descendants of the Old English Strong Verbs of classes I, II and VII in [sweet-1882]
are listed with their token frequencies in [francis-kucera-1982]. In each class the verbs that
have regularized have the lower mean frequency, over all forms and over the Past Tense form
(`expect_regularized_lt_expect_strong`).

## Implementation notes

`Closer` compares the two counts of a pair and does not record which order the hierarchy
predicts, so that `closerEmbedding` is a statement about the counts. It is stated on the tested
categories, the finite set `tested`, because `Category.relevance` identifies the agreement
categories, of which only person was tested; number markers mostly share a portmanteau with
person markers.

## TODO

The implications among inflectional aspect, tense, mood and subject agreement in the sample are
reported without the per-language coding they quantify over, and the comparison of fusion with
the stem is reported without counts; neither is formalized.

## References

* [bybee-1985]
* [francis-kucera-1982]
* [perkins-1980]
* [sweet-1882]
-/

@[expose] public section

namespace Bybee1985

open Morphology
open scoped BigOperators

/-! ### Relevance -/

/-- The place of a coded category on the relevance hierarchy. -/
def Category.relevance : Category → RelevanceHierarchy
  | .valence => .valence
  | .voice => .voice
  | .aspect => .aspect
  | .tense => .tense
  | .mood => .mood
  | .number | .person | .objectPerson | .gender => .agreement

/-! ### Frequency of expression -/

/-- No category is expressed on the verb, inflectionally or derivationally, in more languages
than valence is. -/
theorem morphological_le_valence (c : Category) :
    (expression c).morphological ≤ (expression .valence).morphological := by
  revert c; decide

/-- No category has inflectional expression in fewer languages than valence has. -/
theorem valence_inflectional_le (c : Category) :
    (expression .valence).inflectional ≤ (expression c).inflectional := by
  revert c; decide

theorem gender_morphological_le (c : Category) :
    (expression .gender).morphological ≤ (expression c).morphological := by
  revert c; decide

theorem inflectional_le_morphological (c : Category) :
    (expression c).inflectional ≤ (expression c).morphological := by
  revert c; decide

-- §5, end: no derivational expression of an agreement category other than number
theorem morphological_eq_inflectional_of_agreement {c : Category}
    (hc : c.relevance = .agreement) (hn : c ≠ .number) :
    (expression c).morphological = (expression c).inflectional := by
  revert c; decide

/-! ### Order of morphemes -/

/-- The number of languages in which the marker of `a` stands closer to the verb stem than the
marker of `b`. -/
def closerCount (a b : Category) : ℕ :=
  (order.map fun p ↦
    if p.first = a ∧ p.second = b then p.firstCloser
    else if p.first = b ∧ p.second = a then p.secondCloser else 0).sum

/-- The marker of `a` stands closer to the stem than the marker of `b` in more languages than
the reverse. -/
def Closer (a b : Category) : Prop :=
  closerCount b a < closerCount a b

instance : DecidableRel Closer := fun a b ↦ Nat.decLt (closerCount b a) (closerCount a b)

/-- The categories whose order with another category is counted. -/
def tested : Finset Category :=
  (order.map (·.first) ++ order.map (·.second)).toFinset

theorem tested_eq : tested = {.aspect, .tense, .mood, .person} := by decide

theorem relevance_injOn : Set.InjOn Category.relevance tested := by
  have : ∀ a ∈ tested, ∀ b ∈ tested, a.relevance = b.relevance → a = b := by decide
  exact fun a ha b hb ↦ this a ha b hb

/-- A tested category is the more relevant of two exactly when its marker stands closer to the
stem in more languages. -/
theorem relevance_lt_iff_closer {a b : Category} (ha : a ∈ tested) (hb : b ∈ tested) :
    a.relevance < b.relevance ↔ Closer a b := by
  revert a b; decide

/-- On the tested categories, being closer to the stem in more languages is being more relevant:
`Category.relevance` as a relation embedding. -/
def closerEmbedding :
    (Subtype.val ⁻¹'o Closer : tested → tested → Prop) ↪r
      ((· < ·) : RelevanceHierarchy → RelevanceHierarchy → Prop) where
  toFun c := c.1.relevance
  inj' a b h := Subtype.ext (relevance_injOn a.2 b.2 h)
  map_rel_iff' {a b} := relevance_lt_iff_closer a.2 b.2

@[simp] theorem closerEmbedding_apply (c : tested) :
    closerEmbedding c = c.1.relevance := rfl

/-- On the tested categories, the majority order of markers is a strict total order. -/
instance : IsStrictTotalOrder tested (Subtype.val ⁻¹'o Closer) :=
  closerEmbedding.isStrictTotalOrder

-- §6: aspect is never further from the stem than tense or mood
theorem closerCount_aspect_eq_zero :
    closerCount .tense .aspect = 0 ∧ closerCount .mood .aspect = 0 := by
  decide

-- §6: the order of mood and person is the freest, with five languages against one elsewhere
theorem one_lt_secondCloser_iff :
    ∀ p ∈ order, 1 < p.secondCloser ↔ p.first = .mood ∧ p.second = .person := by
  decide

/-! ### Lexical strength -/

/-- The verbs of a class that have regularized (`r = true`) or stayed Strong (`r = false`). -/
def verbs (c : StrongClass) (r : Bool) : Finset Verb :=
  {v | (strongVerbs v).strongClass = c ∧ (strongVerbs v).regularized = r}

/-- In each class the regularized verbs have a lower mean token frequency than the verbs that
stayed Strong, over all forms and over the Past Tense form. -/
theorem expect_regularized_lt_expect_strong (c : StrongClass) :
    𝔼 v ∈ verbs c true, ((strongVerbs v).allForms : ℚ) <
        𝔼 v ∈ verbs c false, ((strongVerbs v).allForms : ℚ) ∧
      𝔼 v ∈ verbs c true, ((strongVerbs v).past : ℚ) <
        𝔼 v ∈ verbs c false, ((strongVerbs v).past : ℚ) := by
  revert c; decide +kernel

end Bybee1985
