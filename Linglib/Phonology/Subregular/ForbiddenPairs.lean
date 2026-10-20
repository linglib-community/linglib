/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.TierStrictlyLocal
public import Linglib.Core.Data.List.Factors
public import Linglib.Core.Data.List.Chain

/-!
# Forbidden-pair TSL_2 grammars

A tier-based strictly 2-local schema: for a *forbidden-pair* relation `R : α → α → Prop` and
tier predicate `p`, `TierStrictlyLocalGrammar.ofForbiddenPairs R p` bans any string whose tier
projection has an adjacent pair `(a, b)` with `R a b`. The canonical instance is the OCP
(`R := (· = ·)`); OCP-Feature and single-tier harmony (with `p` carrying blocking and
transparency) are other choices of `R`.

## Main definitions

* `Subregular.TierStrictlyLocalGrammar.ofForbiddenPairs R p`: the TSL_2 grammar above.

## Main results

* `Subregular.TierStrictlyLocalGrammar.mem_ofForbiddenPairs_language_iff`: membership reduces to
  an `IsChain (¬ R · ·)` check on the tier-projected string.
* `Subregular.TierStrictlyLocalGrammar.ofForbiddenPairs_language_congr`: the language depends
  only on the tier and on `R` between on-tier symbols.
* `Subregular.TierStrictlyLocalGrammar.map_mem_ofForbiddenPairs_language_iff`: a word's image
  under a letter map is in the language exactly when the word is in the language of the
  pulled-back grammar.

## Implementation notes

\*Lapse and \*Clash (SL_2 over a syllable alphabet) and \*Coda (SL_1) need a richer than
segmental alphabet, and similarity-graded and interval-conditioned (ITSL) harmony and cross-tier
dependencies (MTSL) need more than one relation on one tier, so all fall outside this
constructor.

## References

* [heinz-rawal-tanner-2011]
* [mccarthy-1986]
* [mcmullin-2016]
* [hansson-2010]
-/

@[expose] public section

namespace Subregular

variable {α : Type*} (R : α → α → Prop)

/-- The forbidden 2-factors induced by `R` are the pairs `[some a, some b]` with `R a b`. -/
def forbiddenPairs : Set (Augmented α) :=
  { f | ∃ a b, R a b ∧ f = [some a, some b] }

/-- A list has no forbidden 2-factor iff each adjacent pair is permitted, a boundary `none`
permitting anything. -/
private lemma forbiddenPairFree_iff_isChain (xs : Augmented α) :
    (∀ f ∈ List.kFactors 2 xs, f ∉ forbiddenPairs R) ↔
      xs.IsChain (fun u v ↦ ∀ a ∈ u, ∀ b ∈ v, ¬ R a b) := by
  induction xs with
  | nil => simp
  | cons a rest ih => cases rest with
    | nil => simp
    | cons b rest' =>
      rw [List.kFactors_two_cons_cons, List.forall_mem_cons, List.isChain_cons_cons, ih]
      exact and_congr_left' (by cases a <;> cases b <;> simp [forbiddenPairs])

/-- The TSL_2 grammar banning tier-adjacent pairs satisfying `R` has tier `p` and permits
everything but `forbiddenPairs R`. -/
def TierStrictlyLocalGrammar.ofForbiddenPairs (p : α → Prop) [DecidablePred p] :
    TierStrictlyLocalGrammar 2 α where
  tier := p
  permitted := (forbiddenPairs R)ᶜ

namespace TierStrictlyLocalGrammar

variable {R}

/-- Membership in `ofForbiddenPairs R p` reduces to an `IsChain (¬ R · ·)` check on the
tier-projected string, the characterization all forbidden-pair constraints inherit. -/
lemma mem_ofForbiddenPairs_language_iff {p : α → Prop} [DecidablePred p] {w : List α} :
    w ∈ (ofForbiddenPairs R p).language ↔
      (w.filter (fun x ↦ decide (p x))).IsChain (fun a b ↦ ¬ R a b) := by
  rw [mem_language]
  simp only [ofForbiddenPairs, Set.mem_compl_iff]
  rw [forbiddenPairFree_iff_isChain]
  simp [boundary, List.isChain_cons, List.isChain_append, List.isChain_map]

/-- Membership in `(ofForbiddenPairs R p).language` is decidable, via the `IsChain`
characterization. -/
instance decidableMemOfForbiddenPairsLanguage [DecidableRel R] (p : α → Prop)
    [DecidablePred p] (w : List α) : Decidable (w ∈ (ofForbiddenPairs R p).language) :=
  decidable_of_iff _ mem_ofForbiddenPairs_language_iff.symm

/-- The language depends only on which symbols project and on `R` between on-tier symbols. -/
lemma ofForbiddenPairs_language_congr {R' : α → α → Prop} {p p' : α → Prop} [DecidablePred p]
    [DecidablePred p'] (hp : ∀ a, p a ↔ p' a) (hR : ∀ a b, p a → p b → (R a b ↔ R' a b)) :
    (ofForbiddenPairs R p).language = (ofForbiddenPairs R' p').language := by
  ext w
  simp only [mem_ofForbiddenPairs_language_iff]
  rw [List.filter_congr fun a _ ↦ decide_eq_decide.2 (hp a)]
  have h (a) (ha : a ∈ w.filter (p' ·)) : p a :=
    (hp a).2 (of_decide_eq_true (List.mem_filter.1 ha).2)
  exact List.IsChain.iff_of_mem_imp fun a b ha hb ↦ (hR a b (h a ha) (h b hb)).not

/-- A word's image under a letter-to-letter map is in a forbidden-pair language exactly when
the word is in the language of the grammar with the pulled-back relation and tier. -/
lemma map_mem_ofForbiddenPairs_language_iff {β : Type*} {f : β → α} {p : α → Prop}
    [DecidablePred p] {w : List β} :
    w.map f ∈ (ofForbiddenPairs R p).language ↔
      w ∈ (ofForbiddenPairs (fun x y ↦ R (f x) (f y)) (fun x ↦ p (f x))).language := by
  simp only [mem_ofForbiddenPairs_language_iff, List.filter_map, List.isChain_map]
  rfl

/-- Forbidding `R₁ ∨ R₂` on one tier is conjunctive membership in the two languages.
Cross-tier composition needs MTSL, not this constructor. -/
lemma mem_ofForbiddenPairs_or_language_iff {R₁ R₂ : α → α → Prop} {p : α → Prop}
    [DecidablePred p] {w : List α} :
    w ∈ (ofForbiddenPairs (fun a b ↦ R₁ a b ∨ R₂ a b) p).language ↔
      w ∈ (ofForbiddenPairs R₁ p).language ∧ w ∈ (ofForbiddenPairs R₂ p).language := by
  simp only [mem_ofForbiddenPairs_language_iff, not_or, List.isChain_and_iff]

end TierStrictlyLocalGrammar

end Subregular
