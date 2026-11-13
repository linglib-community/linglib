/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Processing.LanguageModel.Autoregressive
public import Linglib.Core.Probability.Kernel.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Data.List.ReduceOption

/-!
# Incremental RSA: string meanings and the incremental speaker

Incremental rational speech act models run the pipeline word by word. In the model of Cohn-Gordon,
Goodman and Potts an incomplete string gets its meaning from the complete utterances that continue
it, the speaker chooses each word, or the end of the utterance, against a listener of the string so
far, and the probability of an utterance is the product of her choices along it: she is an
autoregressive sequence model. With graded word meanings the value of an utterance is the product
of the values of its words, as in the models of Waldon and Degen and of Schlotterbeck and Wang.

## Main definitions

* `RSA.prodMeaning lex us w`: the product over the words `us` of their values `lex u w`.
* `RSA.continuations utts pfx`, `RSA.stringMeaning utts m pfx`: the complete utterances that
  continue a prefix, and the mean of the utterance meaning `m` over them.
* `RSA.stopped u`, `RSA.incrementalMeaning utts m c o`: a complete utterance closed by the end
  symbol `none`, and the string meaning of the context `c` followed by the next symbol `o`.
* `RSA.incrementalSpeaker S r`: the autoregressive sequence model of the word-level speaker `S`.

## Main results

* `RSA.prodMeaning_perm`: the value of an utterance does not depend on the order of its words.
* `RSA.next_incrementalSpeaker_apply_some`: the incremental speaker chooses each word as the
  word-level speaker does.

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

/-- The value of a word sequence does not depend on the order of its words. -/
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

/-! ### The end of the utterance -/

section Stop

/-- A complete utterance closed by the end symbol `none`. -/
def stopped (u : List U) : List (Option U) := u.map some ++ [none]

@[simp] theorem length_stopped (u : List U) : (stopped u).length = u.length + 1 := by
  simp [stopped]

@[simp] theorem reduceOption_stopped (u : List U) : (stopped u).reduceOption = u := by
  induction u with
  | nil => rfl
  | cons a u ih => simpa [stopped] using ih

/-- A context `c` followed by the symbol `o` begins the closed utterance `u` when `o` ends it and
`u` is `c`, or `o` is a word that continues `c` along `u`. -/
theorem map_some_append_prefix_stopped_iff {c u : List U} {o : Option U} :
    c.map some ++ [o] <+: stopped u ↔ o = none ∧ u = c ∨ ∃ a, o = some a ∧ c ++ [a] <+: u := by
  induction c generalizing u with
  | nil => cases u <;> cases o <;> simp [stopped, eq_comm]
  | cons x c ih =>
    cases u with
    | nil => simp [stopped]
    | cons b u =>
      simp only [stopped, List.map_cons, List.cons_append, List.cons_prefix_cons, Option.some.injEq,
        List.cons.injEq] at ih ⊢
      rw [ih]
      constructor
      · rintro ⟨rfl, h | ⟨a, rfl, h⟩⟩
        · exact .inl ⟨h.1, rfl, h.2⟩
        · exact .inr ⟨a, rfl, rfl, h⟩
      · rintro (⟨h, rfl, rfl⟩ | ⟨a, rfl, rfl, h⟩)
        · exact ⟨rfl, .inl ⟨h, rfl⟩⟩
        · exact ⟨rfl, .inr ⟨a, rfl, h⟩⟩

@[simp] theorem map_some_append_none_prefix_stopped_iff {c u : List U} :
    c.map some ++ [none] <+: stopped u ↔ u = c := by
  simp [map_some_append_prefix_stopped_iff]

@[simp] theorem map_some_append_some_prefix_stopped_iff {c u : List U} {a : U} :
    c.map some ++ [some a] <+: stopped u ↔ c ++ [a] <+: u := by
  simp [map_some_append_prefix_stopped_iff]

theorem exists_map_some_append_prefix_stopped_iff {c u : List U} :
    (∃ o, c.map some ++ [o] <+: stopped u) ↔ c <+: u := by
  simp only [map_some_append_prefix_stopped_iff]
  constructor
  · rintro ⟨o, ⟨-, rfl⟩ | ⟨a, -, h⟩⟩
    · exact List.prefix_refl _
    · exact (List.prefix_append _ _).trans h
  · rintro ⟨_ | ⟨a, t⟩, rfl⟩
    · exact ⟨none, .inl ⟨rfl, by simp⟩⟩
    · exact ⟨some a, .inr ⟨a, rfl, by simp⟩⟩

/-- The incremental meaning of the context `c` followed by `o`, the next word or the end of the
utterance, is its string meaning among the complete utterances closed by the end symbol. -/
noncomputable def incrementalMeaning [DecidableEq U] (utts : List (List U)) (m : List U → W → ℝ)
    (c : List U) (o : Option U) (r : W) : ℝ :=
  stringMeaning (utts.map stopped) (fun s ↦ m s.reduceOption) (c.map some ++ [o]) r

end Stop

/-! ### The incremental speaker -/

section Speaker

open MeasureTheory ProbabilityTheory

variable [MeasurableSpace U] [Countable U] [MeasurableSpace W]
  {S : List U → Kernel W (Option U)} {r : W} {c : List U}

open Classical in
/-- The incremental speaker for `r` is the autoregressive sequence model whose choice after each
context `c` is the word-level speaker's, `S c r`, over the next word and the end of the
utterance. A context where she has no choice ends the string. -/
noncomputable def incrementalSpeaker (S : List U → Kernel W (Option U)) (r : W) :
    AutoregressiveSequenceModel U where
  next := Kernel.ofFunOfCountable fun c ↦
    if IsProbabilityMeasure (S c r) then S c r else Measure.dirac none
  isMarkovKernel_next := ⟨fun c ↦ by
    rw [Kernel.ofFunOfCountable_apply]
    split_ifs with h
    exacts [h, inferInstance]⟩

theorem next_incrementalSpeaker [IsProbabilityMeasure (S c r)] :
    (incrementalSpeaker S r).next c = S c r := by
  classical
  rw [incrementalSpeaker, Kernel.ofFunOfCountable_apply, ite_eq_left ‹_›]

theorem next_incrementalSpeaker_of_ne_zero [IsZeroOrProbabilityMeasure (S c r)] (h : S c r ≠ 0) :
    (incrementalSpeaker S r).next c = S c r :=
  have : IsProbabilityMeasure (S c r) := ⟨IsZeroOrProbabilityMeasure.measure_univ.resolve_left
    fun h0 ↦ h (Measure.measure_univ_eq_zero.1 h0)⟩
  next_incrementalSpeaker

/-- The incremental speaker chooses each word as the word-level speaker does. -/
theorem next_incrementalSpeaker_apply_some [MeasurableSingletonClass U]
    [IsZeroOrProbabilityMeasure (S c r)] (a : U) :
    (incrementalSpeaker S r).next c {some a} = S c r {some a} := by
  rcases eq_or_ne (S c r) 0 with h | h
  · classical
    rw [incrementalSpeaker, Kernel.ofFunOfCountable_apply, h,
      ite_eq_right fun h' ↦ by simpa using h'.measure_univ]
    simp [Measure.dirac_apply' _ (measurableSet_singleton _)]
  · rw [next_incrementalSpeaker_of_ne_zero h]

end Speaker

end RSA
