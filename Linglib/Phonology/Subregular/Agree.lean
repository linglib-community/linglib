/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Subregular.StrictlyPiecewise
public import Linglib.Phonology.Subregular.ForbiddenPairs

/-!
# AGREE as a tier-based strictly 2-local language

This file characterizes AGREE-style markedness as a tier-based strictly 2-local (TSL₂) language.
AGREE requires tier-adjacent symbols to be equal, so it is the dual of the OCP, which requires them
to differ. Both are forbidden-pair grammars `TierStrictlyLocalGrammar.ofForbiddenPairs R p`, AGREE
with `R := (· ≠ ·)` and the OCP with `R := (· = ·)`. Consonant harmony, vowel harmony, and tone
spreading factor through `TierStrictlyLocalGrammar.agree`, and asymmetric patterns instantiate the
generic constructor with their own relation.

A forbidden-pair language is also strictly piecewise exactly when its permitted pairs are
transitive on the tier, and the tier projection is then dispensable. Equality is transitive, so
AGREE is strictly 2-piecewise, as is agreement in a feature value, and transparent long-distance
harmony can be described either way, as McMullin observes. Inequality is not, so the OCP is
strictly piecewise only on a tier with at most one symbol.

## Main definitions

* `TierStrictlyLocalGrammar.agree`: the TSL₂ grammar of AGREE.
* `StrictlyPiecewiseGrammar.ofForbiddenPairs`, `StrictlyPiecewiseGrammar.agree`: the strictly
  2-piecewise grammars banning a pair of on-tier symbols however far apart.

## Main results

* `TierStrictlyLocalGrammar.ofForbiddenPairs_language_eq_strictlyPiecewise`: when the permitted
  pairs are transitive on the tier, the tier-based and subsequence-based grammars generate the
  same language; `TierStrictlyLocalGrammar.agree_language_eq_strictlyPiecewise` is the AGREE
  instance.
* `TierStrictlyLocalGrammar.ofForbiddenPairs_language_isStrictlyPiecewise_iff`: a forbidden-pair
  language is strictly piecewise exactly when its permitted pairs are transitive on the tier.
* `TierStrictlyLocalGrammar.ofForbiddenPairs_eq_language_isStrictlyPiecewise_iff`: the OCP is
  strictly piecewise only on a tier with at most one symbol.

## References

* [mcmullin-2016]
-/

@[expose] public section

namespace Subregular

variable {α : Type*}

/-- The TSL₂ grammar of AGREE forbids two adjacent distinct symbols on the tier defined by `p`,
so every tier-adjacent pair agrees. It is the inequality instance of
`TierStrictlyLocalGrammar.ofForbiddenPairs`. -/
def TierStrictlyLocalGrammar.agree [DecidableEq α] (p : α → Prop) [DecidablePred p] :
    TierStrictlyLocalGrammar 2 α :=
  TierStrictlyLocalGrammar.ofForbiddenPairs (α := α) (· ≠ ·) p

/-! ### Strictly piecewise forbidden-pair languages

When the permitted pairs `¬ R` are transitive on the tier, "every tier-*adjacent* pair is
permitted" and "every pair of on-tier symbols is permitted, however far apart" are the same
condition. The latter reads subsequences, which are blind to the intervening material the tier
projection deletes, so the language is SP₂ as well as TSL₂ ([mcmullin-2016]). Conversely, three
on-tier symbols `a b c` with `a b` and `b c` permitted and `a c` forbidden make a legal word with
an illegal subsequence, so no subsequence-closed language is the forbidden-pair language. -/

section Piecewise

open List

/-- The SP₂ grammar dual to `TierStrictlyLocalGrammar.ofForbiddenPairs R p` permits every
subsequence except an `R`-related pair of on-tier symbols, and permits shorter subsequences
outright. -/
def StrictlyPiecewiseGrammar.ofForbiddenPairs (R : α → α → Prop) (p : α → Prop) :
    StrictlyPiecewiseGrammar α :=
  {s | ∀ a b, s = [a, b] → p a → p b → ¬ R a b}

/-- The SP₂ grammar dual to `TierStrictlyLocalGrammar.agree p` permits every subsequence except
a pair of disagreeing on-tier symbols. -/
def StrictlyPiecewiseGrammar.agree (p : α → Prop) : StrictlyPiecewiseGrammar α :=
  StrictlyPiecewiseGrammar.ofForbiddenPairs (· ≠ ·) p

section ForbiddenPairs

variable {R : α → α → Prop} {p : α → Prop} [DecidablePred p] {k : ℕ}

section Transitive

variable (hR : ∀ a b c, p a → p b → p c → ¬ R a b → ¬ R b c → ¬ R a c)
include hR
/-- If the permitted pairs are transitive on the tier, membership is permission of *all* pairs
of on-tier symbols, not just the tier-adjacent ones. -/
theorem TierStrictlyLocalGrammar.mem_ofForbiddenPairs_language_iff_forall_sublist_pair
    (w : List α) :
    w ∈ (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language ↔
      ∀ a b, [a, b] <+ w → p a → p b → ¬ R a b := by
  rw [mem_ofForbiddenPairs_language_iff]
  have hp : ∀ x ∈ w.filter (p ·), p x := fun x hx ↦ of_decide_eq_true (mem_filter.mp hx).2
  have hchain : (w.filter (p ·)).IsChain (¬ R · ·) ↔ (w.filter (p ·)).Pairwise (¬ R · ·) := by
    refine ⟨fun h ↦ ?_, Pairwise.isChain⟩
    have : IsTrans (Subtype p) (fun x y ↦ ¬ R x y) := ⟨fun a b c ↦ hR a b c a.2 b.2 c.2⟩
    rw [← unattach_attachWith (p := p) (H := hp), unattach, isChain_map] at h
    rw [← unattach_attachWith (p := p) (H := hp), unattach, pairwise_map]
    exact h.pairwise
  rw [hchain, pairwise_iff_forall_sublist]
  refine ⟨fun h a b hab ha hb ↦ h (by simpa [ha, hb] using hab.filter fun x ↦ decide (p x)),
    fun h a b hab ↦ h a b (hab.trans filter_sublist) ?_ ?_⟩
  · exact hp a (hab.mem mem_cons_self)
  · exact hp b (hab.mem (mem_cons_of_mem _ mem_cons_self))

/-- The tier-based and subsequence-based descriptions generate the same language when the
permitted pairs are transitive on the tier. -/
theorem TierStrictlyLocalGrammar.ofForbiddenPairs_language_eq_strictlyPiecewise :
    (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language =
      (StrictlyPiecewiseGrammar.ofForbiddenPairs R p).language 2 :=
  Set.ext fun w ↦ (mem_ofForbiddenPairs_language_iff_forall_sublist_pair hR w).trans
    ⟨fun h s _ hs a b hab ha hb ↦ h a b (hab ▸ hs) ha hb,
      fun h a b hab ↦ h [a, b] (by simp) hab a b rfl⟩

theorem TierStrictlyLocalGrammar.ofForbiddenPairs_language_isStrictlyPiecewise :
    (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language.IsStrictlyPiecewise 2 :=
  Language.isStrictlyPiecewise_iff.mpr ⟨_, (ofForbiddenPairs_language_eq_strictlyPiecewise hR).symm⟩

end Transitive

/-- A forbidden-pair language is strictly piecewise exactly when its permitted pairs are
transitive on the tier. -/
theorem TierStrictlyLocalGrammar.ofForbiddenPairs_language_isStrictlyPiecewise_iff
    (hk : 2 ≤ k) :
    (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language.IsStrictlyPiecewise k ↔
      ∀ a b c, p a → p b → p c → ¬ R a b → ¬ R b c → ¬ R a c := by
  refine ⟨fun h a b c ha hb hc hab hbc hac ↦ ?_,
    fun hR ↦ (ofForbiddenPairs_language_isStrictlyPiecewise hR).mono hk⟩
  have hmem : [a, b, c] ∈ (TierStrictlyLocalGrammar.ofForbiddenPairs R p).language := by
    rw [mem_ofForbiddenPairs_language_iff]
    simp [ha, hb, hc, hab, hbc]
  have := h.mem_of_sublist (v := [a, c]) (by simp) hmem
  rw [mem_ofForbiddenPairs_language_iff] at this
  simp [ha, hc, hac] at this

/-- The OCP is strictly piecewise only on a tier with at most one symbol. For distinct on-tier
`a` and `b`, the word `a b a` is legal and its subsequence `a a` is not. -/
theorem TierStrictlyLocalGrammar.ofForbiddenPairs_eq_language_isStrictlyPiecewise_iff
    [DecidableEq α] (hk : 2 ≤ k) :
    (TierStrictlyLocalGrammar.ofForbiddenPairs (· = ·) p).language.IsStrictlyPiecewise k ↔
      ∀ a b, p a → p b → a = b := by
  rw [ofForbiddenPairs_language_isStrictlyPiecewise_iff hk]
  exact ⟨fun h a b ha hb ↦ by_contra fun hab ↦ h a b a ha hb ha hab (Ne.symm hab) rfl,
    fun h a b _ ha hb _ hab _ ↦ (hab (h a b ha hb)).elim⟩

end ForbiddenPairs

private theorem not_ne_trans {p : α → Prop} (a b c : α) (_ : p a) (_ : p b) (_ : p c)
    (hab : ¬ a ≠ b) (hbc : ¬ b ≠ c) : ¬ a ≠ c :=
  not_ne_iff.2 ((not_ne_iff.1 hab).trans (not_ne_iff.1 hbc))

section Agree

variable [DecidableEq α] (p : α → Prop) [DecidablePred p]

/-- Membership in the AGREE language is agreement of *all* pairs of on-tier symbols,
not just the tier-adjacent ones. -/
theorem TierStrictlyLocalGrammar.mem_agree_language_iff_forall_sublist_pair (w : List α) :
    w ∈ (TierStrictlyLocalGrammar.agree p).language ↔ ∀ a b, [a, b] <+ w → p a → p b → a = b :=
  (mem_ofForbiddenPairs_language_iff_forall_sublist_pair not_ne_trans w).trans <| by
    simp only [ne_eq, not_not]

/-- The tier-based and subsequence-based descriptions of agreement generate the same language,
for any tier predicate. -/
theorem TierStrictlyLocalGrammar.agree_language_eq_strictlyPiecewise :
    (TierStrictlyLocalGrammar.agree p).language = (StrictlyPiecewiseGrammar.agree p).language 2 :=
  ofForbiddenPairs_language_eq_strictlyPiecewise not_ne_trans

/-- Every AGREE language is strictly 2-piecewise. -/
theorem TierStrictlyLocalGrammar.agree_language_isStrictlyPiecewise :
    ((TierStrictlyLocalGrammar.agree p).language).IsStrictlyPiecewise 2 :=
  ofForbiddenPairs_language_isStrictlyPiecewise not_ne_trans

end Agree

end Piecewise

end Subregular
