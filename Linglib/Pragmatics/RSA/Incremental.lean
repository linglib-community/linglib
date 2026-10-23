/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.Kernel.Defs

/-!
# Incremental RSA: string meanings and the chain rule

Incremental rational speech act models run the pipeline word by word. In the model of Cohn-Gordon,
Goodman and Potts an incomplete string gets its meaning from the complete utterances that continue
it, and the probability of an utterance is the product of the speaker's word choices along it.
With graded word meanings the value of an utterance is the product of the values of its words, as
in the models of Waldon and Degen and of Schlotterbeck and Wang.

## Main definitions

* `RSA.prodMeaning lex us w`: the product over the words `us` of their values `lex u w`.
* `RSA.continuations utts pfx`, `RSA.stringMeaning utts m pfx`: the complete utterances that
  continue a prefix, and the mean of the utterance meaning `m` over them.
* `RSA.chain S r ctx us`: the product of a word-level speaker's choices along the words `us`.

## Main results

* `RSA.prodMeaning_perm`: the value of an utterance does not depend on the order of its words.

## References

* [R. Cohn-Gordon, N. D. Goodman, C. Potts, *An incremental iterated response model of
  pragmatics*][cohn-gordon-goodman-potts-2019]
* [J. Degen et al., *When redundancy is useful: a Bayesian approach to "overinformative"
  referring expressions*][degen-etal-2020]
* [B. Waldon, J. Degen, *Modeling cross-linguistic production of referring expressions*
  ][waldon-degen-2021]
* [F. Schlotterbeck, H. Wang, *An incremental RSA model for adjective ordering preferences in
  referential visual context*][schlotterbeck-wang-2023]
-/

@[expose] public section

namespace RSA

variable {U W R : Type*}

section CommMonoid

variable [CommMonoid R]

/-- The value of a word sequence is the product of the values of its words. -/
def prodMeaning (lex : U → W → R) (us : List U) (w : W) : R :=
  (us.map (lex · w)).prod

@[simp] theorem prodMeaning_nil (lex : U → W → R) (w : W) : prodMeaning lex [] w = 1 := rfl

@[simp] theorem prodMeaning_cons (lex : U → W → R) (u : U) (us : List U) (w : W) :
    prodMeaning lex (u :: us) w = lex u w * prodMeaning lex us w := by
  simp [prodMeaning]

theorem prodMeaning_perm {lex : U → W → R} {us us' : List U} (h : us.Perm us') (w : W) :
    prodMeaning lex us w = prodMeaning lex us' w :=
  (h.map _).prod_eq

end CommMonoid

section Order

variable [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem prodMeaning_nonneg {lex : U → W → R} (h : ∀ u w, 0 ≤ lex u w) (us : List U) (w : W) :
    0 ≤ prodMeaning lex us w :=
  List.prod_nonneg (List.forall_mem_map.2 fun u _ ↦ h u w)

end Order

section Bounded

variable [CommMonoid R] [Preorder R] [MulLeftMono R]

theorem prodMeaning_le_one {lex : U → W → R} (h : ∀ u w, lex u w ≤ 1) (us : List U) (w : W) :
    prodMeaning lex us w ≤ 1 := by
  induction us with
  | nil => exact (prodMeaning_nil lex w).le
  | cons u us ih => exact (prodMeaning_cons lex u us w).trans_le (Left.mul_le_one (h u w) ih)

end Bounded

/-! ### String meanings -/

section StringMeaning

variable [DecidableEq U] {utts : List (List U)} {m : List U → W → ℝ} {pfx u : List U}

/-- The complete utterances of a closed set that continue a prefix. -/
def continuations (utts : List (List U)) (pfx : List U) : List (List U) :=
  utts.filter (pfx <+: ·)

/-- The meaning of a prefix is the mean of the utterance meaning over the complete utterances
that continue it. A prefix with no continuation has meaning zero. -/
noncomputable def stringMeaning (utts : List (List U)) (m : List U → W → ℝ) (pfx : List U)
    (r : W) : ℝ :=
  ((continuations utts pfx).map (m · r)).sum / (continuations utts pfx).length

theorem stringMeaning_nonneg {r : W} (hm : ∀ u ∈ utts, 0 ≤ m u r) :
    0 ≤ stringMeaning utts m pfx r :=
  div_nonneg (List.sum_nonneg fun x hx ↦ by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    exact hm u (List.mem_filter.1 hu).1) (Nat.cast_nonneg _)

theorem stringMeaning_pos {r : W} (hm : ∀ u ∈ utts, 0 ≤ m u r) (hu : u ∈ continuations utts pfx)
    (h : 0 < m u r) : 0 < stringMeaning utts m pfx r :=
  div_pos (h.trans_le (List.single_le_sum (fun x hx ↦ by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact hm v (List.mem_filter.1 hv).1) _ (List.mem_map.2 ⟨u, hu, rfl⟩)))
    (Nat.cast_pos.2 (List.length_pos_of_mem hu))

theorem stringMeaning_of_continuations_eq_nil (h : continuations utts pfx = []) (r : W) :
    stringMeaning utts m pfx r = 0 := by
  simp [stringMeaning, h]

theorem stringMeaning_of_continuations_eq_singleton (h : continuations utts pfx = [u]) (r : W) :
    stringMeaning utts m pfx r = m u r := by
  simp [stringMeaning, h]

theorem stringMeaning_eq_of_perm_map {U' W' : Type*} [DecidableEq U'] {utts' : List (List U')}
    {m' : List U' → W' → ℝ} {pfx' : List U'} {r : W} {r' : W'} (φ : List U → List U')
    (hperm : utts'.Perm (utts.map φ)) (hpfx : ∀ u ∈ utts, pfx' <+: φ u ↔ pfx <+: u)
    (hm : ∀ u ∈ utts, m' (φ u) r' = m u r) :
    stringMeaning utts' m' pfx' r' = stringMeaning utts m pfx r := by
  have hc : (continuations utts' pfx').Perm ((continuations utts pfx).map φ) := by
    rw [continuations, continuations]
    refine (hperm.filter _).trans (List.Perm.of_eq ?_)
    rw [List.filter_map]
    exact congrArg _ (List.filter_congr fun u hu ↦ by simpa using hpfx u hu)
  rw [stringMeaning, stringMeaning, (hc.map _).sum_eq, hc.length_eq, List.map_map,
    List.length_map]
  congr 2
  exact List.map_congr_left fun u hu ↦ hm u (List.mem_filter.1 hu).1

end StringMeaning

/-! ### The chain rule -/

section Chain

variable [MeasurableSpace U] [MeasurableSpace W]

/-- The probability that a word-level speaker `S`, who chooses each word given the words so far,
continues the context `ctx` with the words `us` for the referent `r`. -/
noncomputable def chain (S : List U → ProbabilityTheory.Kernel W U) (r : W) :
    List U → List U → ℝ
  | _, [] => 1
  | ctx, u :: us => (S ctx r).real {u} * chain S r (ctx ++ [u]) us

@[simp] theorem chain_nil (S : List U → ProbabilityTheory.Kernel W U) (r : W) (ctx : List U) :
    chain S r ctx [] = 1 := rfl

@[simp] theorem chain_cons (S : List U → ProbabilityTheory.Kernel W U) (r : W) (ctx : List U)
    (u : U) (us : List U) :
    chain S r ctx (u :: us) = (S ctx r).real {u} * chain S r (ctx ++ [u]) us := rfl

end Chain

end RSA
