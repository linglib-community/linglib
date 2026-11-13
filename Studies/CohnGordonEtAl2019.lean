module

public import Linglib.Processing.LanguageModel.Tight
public import Linglib.Pragmatics.Probabilistic.Incremental
public import Linglib.Pragmatics.Probabilistic.Uniform

/-!
# Cohn-Gordon, Goodman and Potts (2019): An Incremental Iterated Response Model of Pragmatics

A prefix followed by a word, or by the end of the utterance, means the share of its complete
continuations true of a referent, and the chain rule over the word-level speaker's choices makes
her an autoregressive sequence model whose string law, like the global speaker's, is [a
distribution over complete utterances](##ReferenceGame.stringMeasure_incS1_setOf_true); her
[greedy unrolling is weakly informative](##ReferenceGame.IsGreedy.isWeaklyInformative). The two
speakers [disagree about the red dress](##global_prefers_red_dress_incremental_prefers_dress) and
about redundant adjectives in English but [agree in Spanish](##Spanish.incremental_eq_global),
and the listener who hears *red* [anticipates the red hat](##listener_anticipation).

## Implementation notes

* The paper's STOP token is the end symbol `none` of the sequence model, so a complete utterance
  may begin another and no game needs a stop word.
* A context that continues toward no utterance true of any referent, which no string of positive
  probability reaches, ends the string; the paper does not define the speaker there.
* The cost of one per word is generalized to any `c`; before the utterance can end, a cost that
  every word shares cancels, so Sedivy's display is evaluated at every `c`.

## TODO

* §4 compares the two speakers' optimal two-word utterances over the TUNA trials, which needs the
  corpus coded by attributes.

## References

* [cohn-gordon-goodman-potts-2019]
* [rubio-fernandez-2016]
* [sedivy-2007]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA AutoregressiveSequenceModel
open scoped ENNReal

namespace CohnGordonEtAl2019

section Cost

variable {U : Type*}

/-- The cost of §3.1: `c` for each word and nothing for the end symbol. -/
def wordCost (c : ℝ) : Option U → ℝ := fun o ↦ o.elim 0 fun _ ↦ c

@[simp] theorem wordCost_none (c : ℝ) : wordCost c (none : Option U) = 0 := rfl

@[simp] theorem wordCost_some (c : ℝ) (a : U) : wordCost c (some a) = c := rfl

end Cost

/-! ### Reference games and the incremental semantics -/

/-- A reference game has a closed set of complete utterances over the words `U` and a global
semantics giving the referents each complete utterance is true of. -/
structure ReferenceGame (U W : Type*) where
  /-- The available complete utterances. -/
  utterances : List (List U)
  /-- The global semantics `⟦·⟧`: the referents a complete utterance is true of. -/
  sem : List U → Finset W

namespace ReferenceGame

variable {U W : Type*}

/-- A game whose semantics is word-conjunctive, from the extension of each word. -/
def ofLexicon [Fintype W] [DecidableEq W] (ext : U → Finset W) (utts : List (List U)) :
    ReferenceGame U W :=
  ⟨utts, fun u ↦ Finset.univ.filter fun r ↦ ∀ a ∈ u, r ∈ ext a⟩

private theorem sum_map_ite {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map fun a ↦ if p a then (1 : ℝ) else 0).sum = l.countP (p ·) := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih, add_comm]

variable [DecidableEq U] [DecidableEq W] (g : ReferenceGame U W) {c : List U} {o : Option U}
  {r : W}

/-- The number of complete utterances true of `r` that `c` followed by `o` begins. -/
def trueExts (c : List U) (o : Option U) (r : W) : ℕ :=
  g.utterances.countP fun u ↦ c.map some ++ [o] <+: stopped u ∧ r ∈ g.sem u

/-- The number of complete utterances true of some referent that `c` followed by `o` begins. -/
def viableExts (c : List U) (o : Option U) : ℕ :=
  g.utterances.countP fun u ↦ c.map some ++ [o] <+: stopped u ∧ (g.sem u).Nonempty

theorem trueExts_le_viableExts (c : List U) (o : Option U) (r : W) :
    g.trueExts c o r ≤ g.viableExts c o :=
  List.countP_mono_left fun _ _ h ↦ by
    simp only [decide_eq_true_eq] at h ⊢
    exact ⟨h.1, r, h.2⟩

theorem trueExts_ne_zero_iff :
    g.trueExts c o r ≠ 0 ↔ ∃ u ∈ g.utterances, c.map some ++ [o] <+: stopped u ∧ r ∈ g.sem u := by
  rw [trueExts, ← Nat.pos_iff_ne_zero, List.countP_pos_iff]
  simp only [decide_eq_true_eq]

omit [DecidableEq W] in
theorem viableExts_ne_zero_iff :
    g.viableExts c o ≠ 0 ↔
      ∃ u ∈ g.utterances, c.map some ++ [o] <+: stopped u ∧ (g.sem u).Nonempty := by
  rw [viableExts, ← Nat.pos_iff_ne_zero, List.countP_pos_iff]
  simp only [decide_eq_true_eq]

/-- The incremental semantics `⟦c + o⟧(r)` (§2.2) is the incremental meaning of `c` followed by
`o` among the complete utterances true of some referent: the fraction of them that are true of
`r`. -/
noncomputable def incSem (c : List U) (o : Option U) (r : W) : ℝ≥0∞ :=
  ENNReal.ofReal (incrementalMeaning (g.utterances.filter fun u ↦ (g.sem u).Nonempty)
    (fun u r ↦ if r ∈ g.sem u then 1 else 0) c o r)

theorem incSem_eq_div (c : List U) (o : Option U) (r : W) :
    g.incSem c o r = (g.trueExts c o r : ℝ≥0∞) / (g.viableExts c o : ℝ≥0∞) := by
  set p := c.map some ++ [o]
  have hc : continuations ((g.utterances.filter fun u ↦ (g.sem u).Nonempty).map stopped) p =
      (g.utterances.filter fun u ↦ p <+: stopped u ∧ (g.sem u).Nonempty).map stopped := by
    rw [continuations, List.filter_map, List.filter_filter]
    congr 1
  have ht : ((continuations ((g.utterances.filter fun u ↦ (g.sem u).Nonempty).map stopped) p).map
      fun s ↦
      if r ∈ g.sem s.reduceOption then (1 : ℝ) else 0).sum = g.trueExts c o r := by
    rw [hc, List.map_map]
    simp only [Function.comp_def, reduceOption_stopped]
    rw [sum_map_ite, List.countP_filter, trueExts]
    exact congrArg _ (List.countP_congr fun u _ ↦ by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, r, h.2⟩⟩)
  have hv : (continuations ((g.utterances.filter fun u ↦ (g.sem u).Nonempty).map stopped)
      p).length = g.viableExts c o := by
    rw [hc, List.length_map, viableExts, List.countP_eq_length_filter]
  rw [incSem, incrementalMeaning, stringMeaning, ht, hv]
  rcases Nat.eq_zero_or_pos (g.viableExts c o) with h0 | hpos
  · have : g.trueExts c o r = 0 := Nat.le_zero.mp (h0 ▸ g.trueExts_le_viableExts c o r)
    simp [h0, this]
  · rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hpos), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]

/-- A context is a dead end for `r` (§2.2) when no continuation of it is true of `r`. -/
def DeadEnd (c : List U) (r : W) : Prop :=
  ∀ o, g.trueExts c o r = 0

theorem not_deadEnd_iff : ¬ g.DeadEnd c r ↔ ∃ u ∈ g.utterances, c <+: u ∧ r ∈ g.sem u := by
  rw [DeadEnd, not_forall]
  constructor
  · rintro ⟨o, ho⟩
    obtain ⟨u, hu, h, hr⟩ := (g.trueExts_ne_zero_iff).1 ho
    exact ⟨u, hu, exists_map_some_append_prefix_stopped_iff.1 ⟨o, h⟩, hr⟩
  · rintro ⟨u, hu, hp, hr⟩
    obtain ⟨o, h⟩ := exists_map_some_append_prefix_stopped_iff.2 hp
    exact ⟨o, (g.trueExts_ne_zero_iff).2 ⟨u, hu, h, hr⟩⟩

theorem not_deadEnd_append_of_trueExts_ne_zero {a : U} (h : g.trueExts c (some a) r ≠ 0) :
    ¬ g.DeadEnd (c ++ [a]) r := by
  obtain ⟨u, hu, hp, hr⟩ := (g.trueExts_ne_zero_iff).1 h
  exact (g.not_deadEnd_iff).2 ⟨u, hu, map_some_append_some_prefix_stopped_iff.1 hp, hr⟩

theorem mem_of_trueExts_none_ne_zero (h : g.trueExts c none r ≠ 0) :
    c ∈ g.utterances ∧ r ∈ g.sem c := by
  obtain ⟨u, hu, hp, hr⟩ := (g.trueExts_ne_zero_iff).1 h
  obtain rfl := map_some_append_none_prefix_stopped_iff.1 hp
  exact ⟨hu, hr⟩

theorem trueExts_none_eq_zero (hc : c ∉ g.utterances) (r : W) : g.trueExts c none r = 0 :=
  not_not.1 fun h ↦ hc (g.mem_of_trueExts_none_ne_zero h).1

/-- The symbols that continue `c` toward a complete utterance true of some referent. -/
def viableNext [Fintype U] (c : List U) : Finset (Option U) :=
  Finset.univ.filter fun o ↦ g.viableExts c o ≠ 0

variable [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]

/-! ### The global model (§2.1) -/

/-- The complete utterances of the game, as a type. -/
abbrev Complete : Type _ := {u : List U // u ∈ g.utterances}

instance : Fintype g.Complete :=
  Fintype.subtype g.utterances.toFinset fun _ ↦ List.mem_toFinset

instance : DiscreteMeasurableSpace g.Complete :=
  ⟨fun s ↦ ⟨Subtype.val '' s, trivial, Set.preimage_image_eq _ Subtype.val_injective⟩⟩

/-- The global literal listener (eq. 1) is uniform on the referents the utterance is true of. -/
noncomputable def globalL0 : Kernel g.Complete W :=
  listener (uniformOn Set.univ) (truthful fun u : g.Complete ↦ (g.sem u.val : Set W))

instance : IsFiniteKernel g.globalL0 := inferInstanceAs (IsFiniteKernel (listener _ _))

theorem globalL0_apply (u : g.Complete) (r : W) :
    g.globalL0 u {r} = if r ∈ g.sem u.val then ((g.sem u.val).card : ℝ≥0∞)⁻¹ else 0 :=
  listener_uniformOn_truthful_apply_singleton (fun u : g.Complete ↦ g.sem u.val) u r

/-- An utterance is weakly informative about `r` (§2.4) when the global literal listener gives
`r` at least chance probability. -/
def IsWeaklyInformative (u : g.Complete) (r : W) : Prop :=
  (Fintype.card W : ℝ≥0∞)⁻¹ ≤ g.globalL0 u {r}

theorem isWeaklyInformative_of_mem {u : g.Complete} (h : r ∈ g.sem u.val) :
    g.IsWeaklyInformative u r := by
  rw [IsWeaklyInformative, globalL0_apply, ite_eq_left h]
  exact ENNReal.inv_le_inv.2 (by exact_mod_cast Finset.card_le_univ _)

/-- An utterance costs the sum of the costs of its words and of the end symbol (§3.1). -/
def uttCost (cost : Option U → ℝ) (u : List U) : ℝ := ((stopped u).map cost).sum

omit [DecidableEq U] in
@[simp] theorem uttCost_wordCost (c : ℝ) (u : List U) : uttCost (wordCost c) u = u.length * c := by
  induction u with
  | nil => simp [uttCost, stopped]
  | cons a u ih => simp_all [uttCost, stopped]; ring

/-- The global pragmatic speaker (eq. 2) soft-maximizes the global literal listener's
probability of the referent less the utterance's cost. -/
noncomputable def globalS1 (cost : Option U → ℝ) : Kernel W g.Complete :=
  speaker 1 (fun u ↦ uttCost cost u.val) g.globalL0 Measure.dirac

instance (cost : Option U → ℝ) : IsFiniteKernel (g.globalS1 cost) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

omit [DecidableEq W] in
theorem globalS1_zero : g.globalS1 0 = speaker 1 0 g.globalL0 Measure.dirac := by
  rw [globalS1]
  congr 1
  funext u
  simp [uttCost, Pi.zero_def]

theorem globalS1_real_of_pair {cost : Option U → ℝ} {u u' : g.Complete} (huu' : u ≠ u')
    (hu : r ∈ g.sem u.val)
    (hu' : r ∈ g.sem u'.val) (hcard : (g.sem u.val).card = (g.sem u'.val).card)
    (hsupp : ∀ v : g.Complete, r ∈ g.sem v.val → v = u ∨ v = u') :
    (g.globalS1 cost r).real {u} = Real.sigmoid (uttCost cost u'.val - uttCost cost u.val) := by
  have hne (v : g.Complete) (hv : r ∈ g.sem v.val) : g.globalL0 v {r} ≠ 0 := by
    rw [globalL0_apply, ite_eq_left hv]
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  rw [globalS1, speaker_dirac_real_singleton_of_pair one_pos huu' (hne u hu) (hne u' hu')
    fun v hv ↦ hsupp v (not_not.1 fun h ↦ hv (by rw [globalL0_apply, ite_eq_right h]))]
  rw [globalL0_apply, globalL0_apply, ite_eq_left hu, ite_eq_left hu', hcard]
  congr 1
  ring

omit [DecidableEq W] in
theorem map_globalS1_apply_singleton {cost : Option U → ℝ} {x : List U} (hx : x ∈ g.utterances) :
    (g.globalS1 cost r).map Subtype.val {x} = g.globalS1 cost r {⟨x, hx⟩} := by
  rw [Measure.map_apply .of_discrete (measurableSet_singleton x)]
  congr 1
  ext v
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ h ▸ rfl⟩

/-! ### The word-level pipeline (eqs. 4–6) -/

variable [Fintype U] [MeasurableSpace U] [DiscreteMeasurableSpace U]

/-- The incremental literal listener at the context `c` (eq. 4) reweights the uniform prior by
`⟦c + o⟧`. -/
noncomputable def l0 (c : List U) : Kernel (Option U) W :=
  Kernel.ofDensity (uniformOn Set.univ) fun o ↦ g.incSem c o

instance (c : List U) : IsFiniteKernel (g.l0 c) :=
  inferInstanceAs (IsFiniteKernel (Kernel.ofDensity _ _))

theorem l0_apply (c : List U) (o : Option U) (r : W) :
    g.l0 c o {r} = (g.trueExts c o r : ℝ≥0∞) / (∑ r', g.trueExts c o r' : ℕ) := by
  have : Nonempty W := ⟨r⟩
  rw [l0, Kernel.ofDensity_uniformOn_apply_singleton]
  simp_rw [g.incSem_eq_div]
  push_cast
  rcases Nat.eq_zero_or_pos (g.viableExts c o) with hv | hv
  · have ht : ∀ r' : W, g.trueExts c o r' = 0 := fun r' ↦
      Nat.le_zero.mp (hv ▸ g.trueExts_le_viableExts c o r')
    simp [ht]
  · simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
    exact ENNReal.mul_div_mul_right _ _
      (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast hv.ne'))

theorem l0_apply_ne_zero (ht : g.trueExts c o r ≠ 0) : g.l0 c o {r} ≠ 0 := by
  rw [l0_apply, ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by exact_mod_cast ht, ENNReal.natCast_ne_top _⟩

theorem l0_apply_eq_zero (ht : g.trueExts c o r = 0) : g.l0 c o {r} = 0 := by
  rw [l0_apply, ht, Nat.cast_zero, ENNReal.zero_div]

theorem l0_real (c : List U) (o : Option U) (r : W) :
    (g.l0 c o {r}).toReal = (g.trueExts c o r : ℝ) / (∑ r', g.trueExts c o r' : ℕ) := by
  rw [l0_apply, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

instance (c : List U) (r : W) : Decidable (g.DeadEnd c r) :=
  inferInstanceAs (Decidable (∀ o, g.trueExts c o r = 0))

/-- At a dead end the speaker spreads her choice evenly over the symbols that continue toward a
complete utterance true of some referent (§2.2), and ends a string that has none. -/
noncomputable def deadEndChoice (c : List U) : Measure (Option U) :=
  if (g.viableNext c).Nonempty then uniformOn ↑(g.viableNext c) else Measure.dirac none

instance (c : List U) : IsProbabilityMeasure (g.deadEndChoice c) := by
  rw [deadEndChoice]
  split_ifs with h
  · exact isProbabilityMeasure_uniformOn (Finset.finite_toSet _) (Finset.coe_nonempty.2 h)
  · infer_instance

/-- The word-level speaker at the context `c` (eq. 5) best responds to the incremental literal
listener, and away from her referent's utterances makes the dead-end choice. -/
noncomputable def s1 (cost : Option U → ℝ) (c : List U) : Kernel W (Option U) :=
  Kernel.ofFunOfCountable fun r ↦
    if g.DeadEnd c r then g.deadEndChoice c else speaker 1 cost (g.l0 c) Measure.dirac r

variable {cost : Option U → ℝ}

theorem s1_apply (hnd : ¬ g.DeadEnd c r) :
    g.s1 cost c r = speaker 1 cost (g.l0 c) Measure.dirac r := by
  rw [s1, Kernel.ofFunOfCountable_apply, ite_eq_right hnd]

theorem s1_apply_deadEnd (hd : g.DeadEnd c r) : g.s1 cost c r = g.deadEndChoice c := by
  rw [s1, Kernel.ofFunOfCountable_apply, ite_eq_left hd]

instance (cost : Option U → ℝ) (c : List U) : IsMarkovKernel (g.s1 cost c) := ⟨fun r ↦ by
  by_cases hd : g.DeadEnd c r
  · rw [s1_apply_deadEnd g hd]; infer_instance
  · rw [s1_apply g hd]
    obtain ⟨o, ho⟩ := not_forall.1 hd
    exact isProbabilityMeasure_speaker_dirac zero_le_one _ _ ⟨o, g.l0_apply_ne_zero ho⟩⟩

/-- The incremental pragmatic listener at the context `c` (eq. 6) inverts the word-level speaker
against the uniform prior. -/
noncomputable def l1 (cost : Option U → ℝ) (c : List U) : Kernel (Option U) W :=
  listener (uniformOn Set.univ) (g.s1 cost c)

instance (cost : Option U → ℝ) (c : List U) : IsFiniteKernel (g.l1 cost c) :=
  inferInstanceAs (IsFiniteKernel (listener _ _))

/-- The utterance-level incremental speaker for `r` (eq. 7) chooses each word, and the end of the
utterance, as the word-level speaker does, so that the probability of an utterance is the
chain-rule product of her choices. -/
noncomputable def incS1 (cost : Option U → ℝ) (r : W) : AutoregressiveSequenceModel U :=
  incrementalSpeaker (g.s1 cost) r

@[simp] theorem next_incS1 (cost : Option U → ℝ) (r : W) (c : List U) :
    (g.incS1 cost r).next c = g.s1 cost c r :=
  next_incrementalSpeaker

/-! ### The speaker produces true utterances, and only finitely long ones -/

theorem trueExts_ne_zero_of_s1_ne_zero (hnd : ¬ g.DeadEnd c r) (h : g.s1 cost c r {o} ≠ 0) :
    g.trueExts c o r ≠ 0 := by
  refine fun ht ↦ h ?_
  rw [s1_apply g hnd]
  exact speaker_dirac_apply_singleton_eq_zero one_pos (g.l0_apply_eq_zero ht)

theorem mem_of_stringProb_ne_zero (hr : ∃ u ∈ g.utterances, r ∈ g.sem u) {x : List U}
    (h : (g.incS1 cost r).stringProb x ≠ 0) : x ∈ g.utterances ∧ r ∈ g.sem x := by
  obtain ⟨u, hu, hr⟩ := hr
  rw [stringProb, prefixProb, next_incS1] at h
  have hx : ¬ g.DeadEnd x r := by
    simpa using (g.incS1 cost r).induction_of_condPrefixProb_ne_zero (P := (¬ g.DeadEnd · r))
      (fun c a hc ha ↦ g.not_deadEnd_append_of_trueExts_ne_zero
        (g.trueExts_ne_zero_of_s1_ne_zero hc (by rwa [next_incS1] at ha)))
      ((g.not_deadEnd_iff).2 ⟨u, hu, List.nil_prefix, hr⟩) (left_ne_zero_of_mul h)
  exact g.mem_of_trueExts_none_ne_zero
    (g.trueExts_ne_zero_of_s1_ne_zero hx (right_ne_zero_of_mul h))

theorem exists_prefix_of_s1_ne_zero {a : U} (h : g.s1 cost c r {some a} ≠ 0) :
    ∃ u ∈ g.utterances, c ++ [a] <+: u := by
  by_cases hd : g.DeadEnd c r
  · rw [s1_apply_deadEnd g hd, deadEndChoice] at h
    split_ifs at h with hn
    · have hm : some a ∈ g.viableNext c := by
        by_contra hm
        exact h (by rw [uniformOn_finset_apply_singleton, ite_eq_right hm])
      obtain ⟨u, hu, hp, -⟩ := (g.viableExts_ne_zero_iff).1 (Finset.mem_filter.1 hm).2
      exact ⟨u, hu, map_some_append_some_prefix_stopped_iff.1 hp⟩
    · exact absurd (by simp) h
  · obtain ⟨u, hu, hp, -⟩ := (g.trueExts_ne_zero_iff).1 (g.trueExts_ne_zero_of_s1_ne_zero hd h)
    exact ⟨u, hu, map_some_append_some_prefix_stopped_iff.1 hp⟩

theorem isTight_incS1 (cost : Option U → ℝ) (r : W) : (g.incS1 cost r).IsTight := by
  refine (g.incS1 cost r).isTight_of_survival_eq_zero
    (n := (g.utterances.map List.length).sum + 1)
    (ENNReal.tsum_eq_zero.2 fun ⟨x, hx⟩ ↦ not_not.1 fun h ↦ ?_)
  obtain h' | ⟨u, hu, hp⟩ := (g.incS1 cost r).induction_of_condPrefixProb_ne_zero
    (P := fun c ↦ c = [] ∨ ∃ u ∈ g.utterances, c <+: u)
    (fun c a _ ha ↦ .inr (g.exists_prefix_of_s1_ne_zero (by rwa [next_incS1] at ha))) (.inl rfl) h
  · obtain rfl : x = [] := h'
    simp at hx
  · have := hp.length_le.trans (List.le_sum_of_mem (List.mem_map_of_mem hu))
    rw [List.nil_append, hx] at this
    omega

/-- When some utterance is true of `r`, the utterance-level incremental speaker is, like the
global speaker, a probability distribution over the complete utterances true of `r` (§2.4). -/
theorem stringMeasure_incS1_setOf_true (hr : ∃ u ∈ g.utterances, r ∈ g.sem u) :
    (g.incS1 cost r).stringMeasure {x | x ∈ g.utterances ∧ r ∈ g.sem x} = 1 := by
  have := (g.incS1 cost r).isTight_iff_isProbabilityMeasure.1 (g.isTight_incS1 cost r)
  refine (prob_compl_eq_zero_iff .of_discrete).1 (ae_iff.1 (ae_iff_of_countable.2 fun x hx ↦ ?_))
  rw [stringMeasure_singleton] at hx
  exact g.mem_of_stringProb_ne_zero hr hx

/-! ### Greedy unrolling (§2.3–2.4) -/

/-- A string is the greedy unrolling for `r` (§2.3) when each of its words, and the end that
closes it, is a most probable choice of the word-level speaker after the words before it. -/
def IsGreedy (cost : Option U → ℝ) (r : W) (x : List U) : Prop :=
  ∀ i : Fin (stopped x).length, ∀ o,
    g.s1 cost (x.take i) r {o} ≤ g.s1 cost (x.take i) r {(stopped x)[i]}

private theorem apply_ne_zero_of_forall_le {α : Type*} [MeasurableSpace α] [Countable α]
    {μ : Measure α} [IsProbabilityMeasure μ] {a : α} (h : ∀ b, μ {b} ≤ μ {a}) : μ {a} ≠ 0 :=
  fun h0 ↦ let ⟨b, hb⟩ := Measure.exists_measure_singleton_ne_zero μ
  hb (nonpos_iff_eq_zero.1 (h0 ▸ h b))

theorem IsGreedy.stringProb_ne_zero {x : List U} (h : g.IsGreedy cost r x) :
    (g.incS1 cost r).stringProb x ≠ 0 := by
  rw [stringProb, prefixProb, condPrefixProb_eq_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_) ?_
  · have := h ⟨i, by simp [Nat.lt_succ_of_lt i.2]⟩
    simp only [stopped] at this
    simpa using apply_ne_zero_of_forall_le this
  · have := h ⟨x.length, by simp⟩
    simp only [stopped, List.take_length] at this
    rw [next_incS1]
    exact apply_ne_zero_of_forall_le (by simpa using this)

/-- A greedily unrolled utterance is a complete utterance true of its referent, and so weakly
informative about it (§2.4). -/
theorem IsGreedy.isWeaklyInformative (hr : ∃ u ∈ g.utterances, r ∈ g.sem u) {x : List U}
    (h : g.IsGreedy cost r x) : ∃ hx : x ∈ g.utterances, g.IsWeaklyInformative ⟨x, hx⟩ r :=
  have h' := g.mem_of_stringProb_ne_zero hr h.stringProb_ne_zero
  ⟨h'.1, g.isWeaklyInformative_of_mem h'.2⟩

/-! ### Evaluation lemmas -/

theorem s1_real_singleton (hnd : ¬ g.DeadEnd c r) (o : Option U) :
    (g.s1 cost c r).real {o} = (g.l0 c o {r}).toReal * Real.exp (-cost o)
      / ∑ o', (g.l0 c o' {r}).toReal * Real.exp (-cost o') := by
  rw [s1_apply g hnd, speaker_dirac_real_singleton zero_le_one]
  simp only [ENNReal.rpow_one, one_mul]

theorem s1_real_counts (hnd : ¬ g.DeadEnd c r) (o : Option U) :
    (g.s1 0 c r).real {o}
      = ((g.trueExts c o r : ℝ) / (∑ r', g.trueExts c o r' : ℕ))
        / ∑ o', ((g.trueExts c o' r : ℝ) / (∑ r', g.trueExts c o' r' : ℕ)) := by
  rw [s1_real_singleton g hnd]
  simp_rw [Pi.zero_apply, neg_zero, Real.exp_zero, mul_one, l0_real]

theorem s1_apply_eq_zero (hnd : ¬ g.DeadEnd c r) (ht : g.trueExts c o r = 0) :
    g.s1 cost c r {o} = 0 := by
  rw [s1_apply g hnd]
  exact speaker_dirac_apply_singleton_eq_zero one_pos (g.l0_apply_eq_zero ht)

theorem s1_apply_ne_zero (ht : g.trueExts c o r ≠ 0) : g.s1 cost c r {o} ≠ 0 := by
  rw [s1_apply g fun hd ↦ ht (hd o)]
  exact speaker_dirac_apply_singleton_ne_zero zero_le_one (g.l0_apply_ne_zero ht)

theorem s1_apply_eq_one (ht : g.trueExts c o r ≠ 0) (hother : ∀ o' ≠ o, g.trueExts c o' r = 0) :
    g.s1 cost c r {o} = 1 := by
  rw [s1_apply g fun hd ↦ ht (hd o)]
  exact speaker_dirac_apply_singleton_eq_one one_pos (g.l0_apply_ne_zero ht)
    fun o' ho' ↦ g.l0_apply_eq_zero (hother o' ho')

theorem s1_wordCost (hc : c ∉ g.utterances) (k : ℝ) : g.s1 (wordCost k) c = g.s1 0 c := by
  have : speaker 1 (wordCost k) (g.l0 c) Measure.dirac = speaker 1 0 (g.l0 c) Measure.dirac := by
    rw [speaker_dirac_eq_softmax, speaker_dirac_eq_softmax]
    refine Kernel.softmax_eq_of_add (k := fun _ ↦ -k) fun r o ↦ ?_
    cases o with
    | none => simp [g.l0_apply_eq_zero (g.trueExts_none_eq_zero hc r)]
    | some a => simp [sub_eq_add_neg]
  simp only [s1, this]

theorem l1_real_lt_iff {o : Option U} {r r' : W} :
    (g.l1 cost c o).real {r} < (g.l1 cost c o).real {r'} ↔
      (g.s1 cost c r).real {o} < (g.s1 cost c r').real {o} :=
  listener_uniformOn_real_lt_iff _ o r r'

theorem l1_real_singleton (o : Option U) (r : W) :
    (g.l1 cost c o).real {r} = (g.s1 cost c r).real {o} / ∑ r', (g.s1 cost c r').real {o} := by
  have : Nonempty W := ⟨r⟩
  simpa [l1] using listener_uniformOn_univ_real_finset (g.s1 cost c) o {r}

theorem s1_real_deadEnd (hd : g.DeadEnd c r) (hn : (g.viableNext c).Nonempty) (o : Option U) :
    (g.s1 cost c r).real {o} = if o ∈ g.viableNext c then ((g.viableNext c).card : ℝ)⁻¹ else 0 := by
  rw [s1_apply_deadEnd g hd, deadEndChoice, ite_eq_left hn, uniformOn_finset_real_singleton]

theorem l0_congr {o' : Option U} (h : g.trueExts c o r = g.trueExts c o' r)
    (h' : ∑ r', g.trueExts c o r' = ∑ r', g.trueExts c o' r') : g.l0 c o {r} = g.l0 c o' {r} := by
  rw [l0_apply, l0_apply, h, h']

theorem l1_wordCost (hc : c ∉ g.utterances) (k : ℝ) : g.l1 (wordCost k) c = g.l1 0 c := by
  rw [l1, l1, g.s1_wordCost hc]

theorem s1_real_eq_one (ht : g.trueExts c o r ≠ 0) (hother : ∀ o' ≠ o, g.trueExts c o' r = 0) :
    (g.s1 cost c r).real {o} = 1 := by
  rw [measureReal_def, g.s1_apply_eq_one ht hother, ENNReal.toReal_one]

theorem s1_real_eq_zero (hnd : ¬ g.DeadEnd c r) (ht : g.trueExts c o r = 0) :
    (g.s1 cost c r).real {o} = 0 := by
  rw [measureReal_def, g.s1_apply_eq_zero hnd ht, ENNReal.toReal_zero]

theorem s1_real_of_pair {o o' : Option U} (hoo' : o ≠ o') (ho : g.trueExts c o r ≠ 0)
    (heq : g.l0 c o {r} = g.l0 c o' {r}) (hsupp : ∀ v, g.trueExts c v r ≠ 0 → v = o ∨ v = o') :
    (g.s1 cost c r).real {o} = Real.sigmoid (cost o' - cost o) := by
  have ho' : g.l0 c o' {r} ≠ 0 := heq ▸ g.l0_apply_ne_zero ho
  rw [s1_apply g fun hd ↦ ho (hd o), speaker_dirac_real_singleton_of_pair one_pos hoo'
    (g.l0_apply_ne_zero ho) ho' fun v hv ↦ hsupp v fun ht ↦ hv (g.l0_apply_eq_zero ht), heq]
  congr 1
  ring

theorem stringMeasure_incS1_eq_map_globalS1 (hr : ∃ u ∈ g.utterances, r ∈ g.sem u)
    (h : ∀ u : g.Complete, r ∈ g.sem u.val →
      (g.incS1 cost r).stringMeasure.real {u.val} = (g.globalS1 cost r).real {u}) :
    (g.incS1 cost r).stringMeasure = (g.globalS1 cost r).map Subtype.val := by
  have := (g.incS1 cost r).isTight_iff_isProbabilityMeasure.1 (g.isTight_incS1 cost r)
  refine Measure.ext_of_singleton fun x ↦ ?_
  by_cases hm : x ∈ g.utterances
  · rw [map_globalS1_apply_singleton g hm]
    by_cases hx : r ∈ g.sem x
    · exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
        (h ⟨x, hm⟩ hx)
    · rw [stringMeasure_singleton,
        not_not.1 (mt (g.mem_of_stringProb_ne_zero hr) fun h ↦ hx h.2), globalS1,
        speaker_dirac_apply_singleton_eq_zero one_pos (by rw [globalL0_apply, ite_eq_right hx])]
  · rw [stringMeasure_singleton,
      Measure.map_apply .of_discrete (measurableSet_singleton x),
      show (Subtype.val ⁻¹' {x} : Set g.Complete) = ∅ from
        Set.eq_empty_of_forall_notMem fun v hv ↦ hm (hv ▸ v.2),
      measure_empty, not_not.1 (mt (g.mem_of_stringProb_ne_zero hr) fun h ↦ hm h.1)]

end ReferenceGame

/-! ### Figure 1: the reference game -/

/-- The words of Figure 1a. -/
inductive Word
  | red | dress | object
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The referents of Figure 1a are the red dress R1, the blue dress R2 and the red hat R3. -/
inductive Referent
  | redDress | blueDress | redHat
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- Figure 1a: *dress*, *red dress* and *red object*, with word-conjunctive semantics. -/
def figureOne : ReferenceGame Word Referent :=
  .ofLexicon
    (fun
      | .red => {.redDress, .redHat}
      | .dress => {.redDress, .blueDress}
      | .object => .univ)
    [[.dress], [.red, .dress], [.red, .object]]

private theorem sum_word {M : Type*} [AddCommMonoid M] (f : Option Word → M) :
    ∑ o, f o = f none + (f (some .red) + (f (some .dress) + f (some .object))) := by
  rw [Fintype.sum_option, show (Finset.univ : Finset Word) = {.red, .dress, .object} from by
    decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem nil_counts :
    figureOne.trueExts [] none .redDress = 0 ∧
    figureOne.trueExts [] (some .red) .redDress = 2 ∧
    ∑ r, figureOne.trueExts [] (some .red) r = 3 ∧
    figureOne.trueExts [] (some .dress) .redDress = 1 ∧
    ∑ r, figureOne.trueExts [] (some .dress) r = 2 ∧
    figureOne.trueExts [] (some .object) .redDress = 0 := by
  decide

private theorem red_counts :
    figureOne.trueExts [.red] none .redDress = 0 ∧
    figureOne.trueExts [.red] (some .red) .redDress = 0 ∧
    figureOne.trueExts [.red] (some .dress) .redDress = 1 ∧
    ∑ r, figureOne.trueExts [.red] (some .dress) r = 1 ∧
    figureOne.trueExts [.red] (some .object) .redDress = 1 ∧
    ∑ r, figureOne.trueExts [.red] (some .object) r = 2 := by
  decide

-- Figure 1c
theorem s1_figureOne_values :
    (figureOne.s1 0 [] .redDress).real {some .red} = 4 / 7 ∧
    (figureOne.s1 0 [] .redDress).real {some .dress} = 3 / 7 ∧
    (figureOne.s1 0 [.red] .redDress).real {some .dress} = 2 / 3 ∧
    (figureOne.s1 0 [.red] .redDress).real {some .object} = 1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [figureOne.s1_real_counts (by decide), sum_word]
  · norm_num [nil_counts]
  · norm_num [nil_counts]
  · norm_num [red_counts]
  · norm_num [red_counts]

-- Figure 1c
theorem uniform_after_red_for_r2 :
    (figureOne.s1 0 [.red] .blueDress).real {some .dress} = 1 / 2 ∧
    (figureOne.s1 0 [.red] .blueDress).real {some .object} = 1 / 2 := by
  constructor <;> rw [figureOne.s1_real_deadEnd (by decide) (by decide), ite_eq_left (by decide),
    show (figureOne.viableNext [.red]).card = 2 from by decide] <;> norm_num

private theorem forced_r1 :
    (figureOne.s1 0 [.dress] .redDress).real {none} = 1 ∧
    (figureOne.s1 0 [.red, .dress] .redDress).real {none} = 1 ∧
    (figureOne.s1 0 [.red, .object] .redDress).real {none} = 1 :=
  ⟨figureOne.s1_real_eq_one (by decide) (by decide),
    figureOne.s1_real_eq_one (by decide) (by decide),
    figureOne.s1_real_eq_one (by decide) (by decide)⟩

-- Figure 1e
theorem figureOne_incremental_values :
    (figureOne.incS1 0 .redDress).stringMeasure.real {[.dress]} = 3 / 7 ∧
    (figureOne.incS1 0 .redDress).stringMeasure.real {[.red, .dress]} = 8 / 21 ∧
    (figureOne.incS1 0 .redDress).stringMeasure.real {[.red, .object]} = 4 / 21 := by
  obtain ⟨h1, h2, h3, h4⟩ := s1_figureOne_values
  obtain ⟨e1, e2, e3⟩ := forced_r1
  simp only [stringMeasure_real_singleton, prefixProb, toReal_condPrefixProb_cons,
    condPrefixProb_nil, ENNReal.toReal_one, ReferenceGame.next_incS1, List.nil_append,
    List.cons_append, h1, h2, h3, h4,
    e1, e2, e3]
  norm_num

/-- For the red dress the global speaker prefers the fully informative *red dress* to *dress*,
while the incremental speaker prefers *dress*. -/
theorem global_prefers_red_dress_incremental_prefers_dress :
    (figureOne.globalS1 0 .redDress).real {⟨[.dress], by decide⟩}
        < (figureOne.globalS1 0 .redDress).real {⟨[.red, .dress], by decide⟩} ∧
      (figureOne.incS1 0 .redDress).stringMeasure.real {[.red, .dress]}
        < (figureOne.incS1 0 .redDress).stringMeasure.real {[.dress]} := by
  refine ⟨?_, ?_⟩
  · rw [ReferenceGame.globalS1_zero]
    exact speaker_uniformOn_dirac_real_singleton_lt_of_card_lt
      (fun u : figureOne.Complete ↦ figureOne.sem u.val) one_pos (by decide) (by decide)
      (by decide)
  · rw [figureOne_incremental_values.1, figureOne_incremental_values.2.1]
    norm_num

/-- Hearing *red*, the incremental pragmatic listener favours the red hat at 7/11 over the red
dress at 4/11: the speaker referring to the red dress could have said *dress*. -/
theorem listener_anticipation :
    (figureOne.l1 0 [] (some .red)).real {.redHat} = 7 / 11 ∧
    (figureOne.l1 0 [] (some .red)).real {.redDress} = 4 / 11 := by
  have hR2 : (figureOne.s1 0 [] .blueDress).real {some .red} = 0 :=
    figureOne.s1_real_eq_zero (by decide) (by decide)
  have hR3 : (figureOne.s1 0 [] .redHat).real {some .red} = 1 :=
    figureOne.s1_real_eq_one (by decide) (by decide)
  have hsum : ∑ r, (figureOne.s1 0 [] r).real {some Word.red} = 11 / 7 := by
    rw [show (Finset.univ : Finset Referent) = {.redDress, .blueDress, .redHat} from by decide,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      s1_figureOne_values.1, hR2, hR3]
    norm_num
  constructor <;> rw [figureOne.l1_real_singleton, hsum]
  · rw [hR3]; norm_num
  · rw [s1_figureOne_values.1]; norm_num

-- §2.3, §2.4
theorem isGreedy_red_dress : figureOne.IsGreedy 0 .redDress [.red, .dress] := by
  obtain ⟨h1, h2, h3, h4⟩ := s1_figureOne_values
  have z (c : List Word) (o : Option Word) (hnd : ¬ figureOne.DeadEnd c .redDress)
      (ht : figureOne.trueExts c o .redDress = 0) : (figureOne.s1 0 c .redDress).real {o} = 0 :=
    figureOne.s1_real_eq_zero hnd ht
  intro i o
  fin_cases i
  · refine (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
    change (figureOne.s1 0 [] .redDress).real {o} ≤ (figureOne.s1 0 [] .redDress).real {some .red}
    rcases o with _ | (_ | _ | _)
    · rw [z [] none (by decide) (by decide), h1]; norm_num
    · exact le_rfl
    · rw [h1, h2]; norm_num
    · rw [z [] _ (by decide) (by decide), h1]; norm_num
  · refine (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
    change (figureOne.s1 0 [.red] .redDress).real {o}
      ≤ (figureOne.s1 0 [.red] .redDress).real {some .dress}
    rcases o with _ | (_ | _ | _)
    · rw [z [.red] none (by decide) (by decide), h3]; norm_num
    · rw [z [.red] _ (by decide) (by decide), h3]; norm_num
    · exact le_rfl
    · rw [h3, h4]; norm_num
  · change figureOne.s1 0 [.red, .dress] .redDress {o}
      ≤ figureOne.s1 0 [.red, .dress] .redDress {none}
    rw [figureOne.s1_apply_eq_one (o := none) (by decide) (by decide)]
    exact prob_le_one

-- §2.3
theorem not_isGreedy_dress : ¬ figureOne.IsGreedy 0 .redDress [.dress] := fun h ↦ by
  have := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2
    (h ⟨0, by decide⟩ (some .red))
  change (figureOne.s1 0 [] .redDress).real {some .red}
    ≤ (figureOne.s1 0 [] .redDress).real {some .dress} at this
  rw [s1_figureOne_values.1, s1_figureOne_values.2.1] at this
  norm_num at this

/-! ### Figure 3: the abstract two-letter game -/

/-- The two letters. -/
inductive Letter
  | A | B
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Letter := ⊤
instance : DiscreteMeasurableSpace Letter := ⟨fun _ ↦ trivial⟩

/-- The two worlds. -/
inductive AbstractWorld
  | W1 | W2
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace AbstractWorld := ⊤
instance : DiscreteMeasurableSpace AbstractWorld := ⟨fun _ ↦ trivial⟩

/-- Figure 3: four two-letter utterances, all true except *AB* at W1, a table that is not
word-conjunctive. -/
def figureThree : ReferenceGame Letter AbstractWorld where
  utterances := [[.A, .A], [.A, .B], [.B, .A], [.B, .B]]
  sem u := if u = [.A, .B] then {.W2} else .univ

private theorem sum_letter {M : Type*} [AddCommMonoid M] (f : Option Letter → M) :
    ∑ o, f o = f none + (f (some .A) + f (some .B)) := by
  rw [Fintype.sum_option, show (Finset.univ : Finset Letter) = {.A, .B} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem fig3_counts :
    figureThree.trueExts [] none .W1 = 0 ∧
    figureThree.trueExts [] (some .A) .W1 = 1 ∧ ∑ r, figureThree.trueExts [] (some .A) r = 3 ∧
    figureThree.trueExts [] (some .B) .W1 = 2 ∧ ∑ r, figureThree.trueExts [] (some .B) r = 4 ∧
    figureThree.trueExts [.B] none .W1 = 0 ∧
    figureThree.trueExts [.B] (some .A) .W1 = 1 ∧ ∑ r, figureThree.trueExts [.B] (some .A) r = 2 ∧
    figureThree.trueExts [.B] (some .B) .W1 = 1 ∧
    ∑ r, figureThree.trueExts [.B] (some .B) r = 2 := by
  decide

-- Figure 3
theorem figureThree_incremental_values :
    (figureThree.incS1 0 .W1).stringMeasure.real {[.A, .A]} = 2 / 5 ∧
    (figureThree.incS1 0 .W1).stringMeasure.real {[.A, .B]} = 0 ∧
    (figureThree.incS1 0 .W1).stringMeasure.real {[.B, .A]} = 3 / 10 ∧
    (figureThree.incS1 0 .W1).stringMeasure.real {[.B, .B]} = 3 / 10 := by
  have hA : (figureThree.s1 0 [] .W1).real {some .A} = 2 / 5 := by
    rw [figureThree.s1_real_counts (by decide), sum_letter]; norm_num [fig3_counts]
  have hB : (figureThree.s1 0 [] .W1).real {some .B} = 3 / 5 := by
    rw [figureThree.s1_real_counts (by decide), sum_letter]; norm_num [fig3_counts]
  have hBA : (figureThree.s1 0 [.B] .W1).real {some .A} = 1 / 2 := by
    rw [figureThree.s1_real_counts (by decide), sum_letter]; norm_num [fig3_counts]
  have hBB : (figureThree.s1 0 [.B] .W1).real {some .B} = 1 / 2 := by
    rw [figureThree.s1_real_counts (by decide), sum_letter]; norm_num [fig3_counts]
  have hAA : (figureThree.s1 0 [.A] .W1).real {some .A} = 1 :=
    figureThree.s1_real_eq_one (by decide) (by decide)
  have hAB : (figureThree.s1 0 [.A] .W1).real {some .B} = 0 :=
    figureThree.s1_real_eq_zero (by decide) (by decide)
  have e1 : (figureThree.s1 0 [.A, .A] .W1).real {none} = 1 :=
    figureThree.s1_real_eq_one (by decide) (by decide)
  have e2 : (figureThree.s1 0 [.B, .A] .W1).real {none} = 1 :=
    figureThree.s1_real_eq_one (by decide) (by decide)
  have e3 : (figureThree.s1 0 [.B, .B] .W1).real {none} = 1 :=
    figureThree.s1_real_eq_one (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [stringMeasure_real_singleton, prefixProb, toReal_condPrefixProb_cons,
      condPrefixProb_nil, ENNReal.toReal_one, ReferenceGame.next_incS1, List.nil_append,
      List.cons_append, hA, hB, hAA, hAB, hBA, hBB, e1, e2, e3] <;>
    norm_num

-- Figure 3
theorem figureThree_global_indifferent :
    figureThree.globalS1 0 .W1 {⟨[.A, .A], by decide⟩}
      = figureThree.globalS1 0 .W1 {⟨[.B, .A], by decide⟩} ∧
    figureThree.globalS1 0 .W1 {⟨[.B, .A], by decide⟩}
      = figureThree.globalS1 0 .W1 {⟨[.B, .B], by decide⟩} := by
  have h (u v : figureThree.Complete) (h : figureThree.sem u.val = figureThree.sem v.val) :
      figureThree.globalS1 0 .W1 {u} = figureThree.globalS1 0 .W1 {v} := by
    rw [ReferenceGame.globalS1_zero, speaker_dirac_zero_apply_singleton,
      speaker_dirac_zero_apply_singleton, figureThree.globalL0_apply, figureThree.globalL0_apply,
      h]
  exact ⟨h _ _ (by decide), h _ _ (by decide)⟩

/-! ### Over-modification and the end of the utterance (§3.1)

English speakers add redundant colour adjectives more often than Spanish speakers
[rubio-fernandez-2016]. -/

namespace English

/-- English puts the adjective before the noun. -/
inductive Word
  | dress | red | hat | blue
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The referents are a red dress and a blue hat. -/
inductive Referent
  | redDress | blueHat
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- The English game: *dress*, *red dress*, *hat* and *blue hat*. -/
def game : ReferenceGame Word Referent :=
  .ofLexicon
    (fun
      | .dress | .red => {.redDress}
      | .hat | .blue => {.blueHat})
    [[.dress], [.red, .dress], [.hat], [.blue, .hat]]

-- §3.1
theorem incremental_indifferent (c : ℝ) :
    (game.incS1 (wordCost c) .redDress).stringMeasure.real {[.dress]} = 1 / 2 ∧
    (game.incS1 (wordCost c) .redDress).stringMeasure.real {[.red, .dress]} = 1 / 2 := by
  have hd : (game.s1 (wordCost c) [] .redDress).real {some .dress} = 1 / 2 := by
    rw [game.s1_real_of_pair (o' := some .red) (by decide) (by decide)
      (game.l0_congr (by decide) (by decide)) (by decide)]
    norm_num [Real.sigmoid_zero]
  have hr : (game.s1 (wordCost c) [] .redDress).real {some .red} = 1 / 2 := by
    rw [game.s1_real_of_pair (o' := some .dress) (by decide) (by decide)
      (game.l0_congr (by decide) (by decide)) (by decide)]
    norm_num [Real.sigmoid_zero]
  have e1 : (game.s1 (wordCost c) [.dress] .redDress).real {none} = 1 :=
    game.s1_real_eq_one (by decide) (by decide)
  have e2 : (game.s1 (wordCost c) [.red] .redDress).real {some .dress} = 1 :=
    game.s1_real_eq_one (by decide) (by decide)
  have e3 : (game.s1 (wordCost c) [.red, .dress] .redDress).real {none} = 1 :=
    game.s1_real_eq_one (by decide) (by decide)
  constructor <;>
    simp only [stringMeasure_real_singleton, prefixProb, toReal_condPrefixProb_cons,
      condPrefixProb_nil, ENNReal.toReal_one, ReferenceGame.next_incS1, List.nil_append,
      List.cons_append, hd, hr, e1, e2, e3] <;>
    norm_num

-- §3.1
theorem global_values (c : ℝ) :
    (game.globalS1 (wordCost c) .redDress).real {⟨[.dress], by decide⟩} = Real.sigmoid c ∧
    (game.globalS1 (wordCost c) .redDress).real {⟨[.red, .dress], by decide⟩}
      = Real.sigmoid (-c) := by
  have hs : ∀ v : game.Complete, Referent.redDress ∈ game.sem v.val →
      v = ⟨[.dress], by decide⟩ ∨ v = ⟨[.red, .dress], by decide⟩ := by decide
  constructor
  · rw [game.globalS1_real_of_pair (u' := ⟨[.red, .dress], by decide⟩) (by decide) (by decide)
      (by decide) (by decide) hs]
    congr 1
    simp only [ReferenceGame.uttCost_wordCost, List.length_cons, List.length_nil]
    push_cast
    ring
  · rw [game.globalS1_real_of_pair (u' := ⟨[.dress], by decide⟩) (by decide) (by decide)
      (by decide) (by decide) fun v hv ↦ (hs v hv).symm]
    congr 1
    simp only [ReferenceGame.uttCost_wordCost, List.length_cons, List.length_nil]
    push_cast
    ring

-- §3.1
theorem incremental_ne_global {c : ℝ} (hc : c ≠ 0) :
    (game.incS1 (wordCost c) .redDress).stringMeasure
      ≠ (game.globalS1 (wordCost c) .redDress).map Subtype.val := fun h ↦ by
  have := congrArg (fun μ : Measure (List Word) ↦ μ.real {[Word.dress]}) h
  rw [(incremental_indifferent c).1, measureReal_def,
    game.map_globalS1_apply_singleton (by decide), ← measureReal_def, (global_values c).1] at this
  exact hc (Real.sigmoid_strictMono.injective (by rw [Real.sigmoid_zero, ← this]; norm_num))

end English

namespace Spanish

/-- Spanish puts the adjective after the noun. -/
inductive Word
  | vestido | rojo | sombrero | azul
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The Spanish game over the same referents: *vestido*, *vestido rojo*, *sombrero* and
*sombrero azul*. -/
def game : ReferenceGame Word English.Referent :=
  .ofLexicon
    (fun
      | .vestido | .rojo => {.redDress}
      | .sombrero | .azul => {.blueHat})
    [[.vestido], [.vestido, .rojo], [.sombrero], [.sombrero, .azul]]

private theorem incremental_real (c : ℝ) {r : English.Referent} {n a : Word}
    (h0 : game.trueExts [] (some n) r ≠ 0) (h0' : ∀ o ≠ some n, game.trueExts [] o r = 0)
    (h1 : game.trueExts [n] none r ≠ 0) (h2 : game.trueExts [n] (some a) r ≠ 0)
    (hl : game.l0 [n] none {r} = game.l0 [n] (some a) {r})
    (hs : ∀ v, game.trueExts [n] v r ≠ 0 → v = none ∨ v = some a)
    (h3 : game.trueExts [n, a] none r ≠ 0) (h3' : ∀ o ≠ none, game.trueExts [n, a] o r = 0) :
    (game.incS1 (wordCost c) r).stringMeasure.real {[n]} = Real.sigmoid c ∧
    (game.incS1 (wordCost c) r).stringMeasure.real {[n, a]} = Real.sigmoid (-c) := by
  have e0 := game.s1_real_eq_one (cost := wordCost c) h0 h0'
  have e3 := game.s1_real_eq_one (cost := wordCost c) h3 h3'
  have hn := game.s1_real_of_pair (cost := wordCost c) (o' := some a) (by simp) h1 hl hs
  have ha := game.s1_real_of_pair (cost := wordCost c) (o' := none) (by simp) h2 hl.symm
    fun v hv ↦ (hs v hv).symm
  constructor <;>
    simp only [stringMeasure_real_singleton, prefixProb, toReal_condPrefixProb_cons,
      condPrefixProb_nil, ENNReal.toReal_one, ReferenceGame.next_incS1, List.nil_append,
      List.cons_append, e0, e3, hn, ha] <;>
    simp

private theorem global_real (c : ℝ) {r : English.Referent} {u u' : game.Complete}
    (hl : u.val.length = 1) (hl' : u'.val.length = 2) (huu' : u ≠ u') (hu : r ∈ game.sem u.val)
    (hu' : r ∈ game.sem u'.val) (hcard : (game.sem u.val).card = (game.sem u'.val).card)
    (hs : ∀ v : game.Complete, r ∈ game.sem v.val → v = u ∨ v = u') :
    (game.globalS1 (wordCost c) r).real {u} = Real.sigmoid c ∧
    (game.globalS1 (wordCost c) r).real {u'} = Real.sigmoid (-c) := by
  rw [game.globalS1_real_of_pair huu' hu hu' hcard hs,
    game.globalS1_real_of_pair huu'.symm hu' hu hcard.symm fun v hv ↦ (hs v hv).symm]
  simp only [ReferenceGame.uttCost_wordCost, hl, hl']
  constructor <;> congr 1 <;> push_cast <;> ring

/-- In Spanish the incremental speaker is the global speaker: after the noun she may end the
utterance, so the choice between *vestido* and *vestido rojo* is the global one, the sigmoid of
the adjective's cost, 0.73 at the paper's cost of one. -/
theorem incremental_eq_global (c : ℝ) (r : English.Referent) :
    (game.incS1 (wordCost c) r).stringMeasure = (game.globalS1 (wordCost c) r).map Subtype.val := by
  refine game.stringMeasure_incS1_eq_map_globalS1 (by cases r <;> decide) fun u hu ↦ ?_
  cases r
  · have hs : ∀ v : game.Complete, English.Referent.redDress ∈ game.sem v.val →
        v = ⟨[.vestido], by decide⟩ ∨ v = ⟨[.vestido, .rojo], by decide⟩ := by decide
    obtain ⟨i1, i2⟩ := incremental_real c (r := .redDress) (n := .vestido) (a := .rojo)
      (by decide) (by decide) (by decide) (by decide) (game.l0_congr (by decide) (by decide))
      (by decide) (by decide) (by decide)
    obtain ⟨g1, g2⟩ := global_real c rfl rfl (by decide) (by decide) (by decide) (by decide) hs
    rcases hs u hu with rfl | rfl
    · exact i1.trans g1.symm
    · exact i2.trans g2.symm
  · have hs : ∀ v : game.Complete, English.Referent.blueHat ∈ game.sem v.val →
        v = ⟨[.sombrero], by decide⟩ ∨ v = ⟨[.sombrero, .azul], by decide⟩ := by decide
    obtain ⟨i1, i2⟩ := incremental_real c (r := .blueHat) (n := .sombrero) (a := .azul)
      (by decide) (by decide) (by decide) (by decide) (game.l0_congr (by decide) (by decide))
      (by decide) (by decide) (by decide)
    obtain ⟨g1, g2⟩ := global_real c rfl rfl (by decide) (by decide) (by decide) (by decide) hs
    rcases hs u hu with rfl | rfl
    · exact i1.trans g1.symm
    · exact i2.trans g2.symm

end Spanish

/-! ### The anticipatory implicature in Sedivy's display (§3.2)

Listeners who hear *tall* in a display of a tall and a short cup, a tall pitcher and a key look
to the tall cup before the noun [sedivy-2007]. -/

namespace Sedivy

/-- The scene's words are two scalar adjectives and three nouns. -/
inductive Word
  | tall | short | cup | pitcher | key
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Word := ⊤
instance : DiscreteMeasurableSpace Word := ⟨fun _ ↦ trivial⟩

/-- The four objects on display. -/
inductive Referent
  | tallCup | shortCup | tallPitcher | key
  deriving DecidableEq, Fintype, Repr

instance : MeasurableSpace Referent := ⊤
instance : DiscreteMeasurableSpace Referent := ⟨fun _ ↦ trivial⟩

/-- Sedivy's display: *tall cup*, *short cup*, *tall pitcher*, *cup*, *pitcher* and *key*. -/
def game : ReferenceGame Word Referent :=
  .ofLexicon
    (fun
      | .tall => {.tallCup, .tallPitcher}
      | .short => {.shortCup}
      | .cup => {.tallCup, .shortCup}
      | .pitcher => {.tallPitcher}
      | .key => {.key})
    [[.tall, .cup], [.short, .cup], [.tall, .pitcher], [.cup], [.pitcher], [.key]]

private theorem sum_word {M : Type*} [AddCommMonoid M] (f : Option Word → M) :
    ∑ o, f o = f none + (f (some .tall) + (f (some .short) + (f (some .cup)
      + (f (some .pitcher) + f (some .key))))) := by
  rw [Fintype.sum_option, show (Finset.univ : Finset Word) = {.tall, .short, .cup, .pitcher, .key}
    from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

private theorem sum_referent {M : Type*} [AddCommMonoid M] (f : Referent → M) :
    ∑ r, f r = f .tallCup + (f .shortCup + (f .tallPitcher + f .key)) := by
  rw [show (Finset.univ : Finset Referent) = {.tallCup, .shortCup, .tallPitcher, .key} from by
    decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]

private theorem tall_counts :
    game.trueExts [] none .tallCup = 0 ∧ game.trueExts [] none .tallPitcher = 0 ∧
    game.trueExts [] (some .tall) .tallCup = 1 ∧ game.trueExts [] (some .tall) .tallPitcher = 1 ∧
    ∑ r, game.trueExts [] (some .tall) r = 2 ∧
    game.trueExts [] (some .short) .tallCup = 0 ∧ game.trueExts [] (some .short) .tallPitcher = 0 ∧
    game.trueExts [] (some .cup) .tallCup = 1 ∧ game.trueExts [] (some .cup) .tallPitcher = 0 ∧
    ∑ r, game.trueExts [] (some .cup) r = 2 ∧
    game.trueExts [] (some .pitcher) .tallCup = 0 ∧
    game.trueExts [] (some .pitcher) .tallPitcher = 1 ∧
    ∑ r, game.trueExts [] (some .pitcher) r = 1 ∧
    game.trueExts [] (some .key) .tallCup = 0 ∧ game.trueExts [] (some .key) .tallPitcher = 0 := by
  decide

-- §3.2
theorem s1_tall_values :
    (game.s1 0 [] .tallCup).real {some .tall} = 1 / 2 ∧
    (game.s1 0 [] .tallPitcher).real {some .tall} = 1 / 3 ∧
    (game.s1 0 [] .shortCup).real {some .tall} = 0 ∧
    (game.s1 0 [] .key).real {some .tall} = 0 := by
  refine ⟨?_, ?_, game.s1_real_eq_zero (by decide) (by decide),
    game.s1_real_eq_zero (by decide) (by decide)⟩ <;>
    rw [game.s1_real_counts (by decide), sum_word] <;> norm_num [tall_counts]

-- §3.2
theorem listener_tall_values (c : ℝ) :
    (game.l1 (wordCost c) [] (some .tall)).real {.tallCup} = 3 / 5 ∧
    (game.l1 (wordCost c) [] (some .tall)).real {.tallPitcher} = 2 / 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := s1_tall_values
  have hsum : ∑ r, (game.s1 0 [] r).real {some Word.tall} = 5 / 6 := by
    rw [sum_referent, h1, h2, h3, h4]
    norm_num
  rw [game.l1_wordCost (c := []) (by decide)]
  constructor <;> rw [game.l1_real_singleton, hsum]
  · rw [h1]; norm_num
  · rw [h2]; norm_num

/-- The listener who has heard *tall* and then hears *pitcher*, with her posterior after *tall*
as her prior. -/
noncomputable def afterTallPitcher (c : ℝ) : Measure Referent :=
  listener (game.l1 (wordCost c) [] (some .tall)) (game.s1 (wordCost c) [.tall]) (some .pitcher)

-- §3.2
theorem afterTallPitcher_eq_one (c : ℝ) : afterTallPitcher c {.tallPitcher} = 1 := by
  rw [afterTallPitcher, game.l1_wordCost (c := []) (by decide),
    game.s1_wordCost (c := [.tall]) (by decide)]
  have hcup : game.s1 0 [.tall] .tallCup {some .pitcher} = 0 :=
    game.s1_apply_eq_zero (by decide) (by decide)
  have hpit : game.s1 0 [.tall] .tallPitcher {some .pitcher} = 1 :=
    game.s1_apply_eq_one (by decide) (by decide)
  have hprior (r : Referent) (hr : r = .shortCup ∨ r = .key) :
      game.l1 0 [] (some .tall) {r} = 0 := by
    rcases hr with rfl | rfl <;>
      exact listener_apply_singleton_eq_zero (game.s1_apply_eq_zero (by decide) (by decide))
  have hpos : game.l1 0 [] (some .tall) {Referent.tallPitcher} ≠ 0 :=
    listener_apply_singleton_ne_zero (uniformOn_univ_singleton_ne_zero _)
      (game.s1_apply_ne_zero (by decide))
  rw [listener_apply_singleton_eq_div, Measure.comp_apply_singleton, sum_referent, hcup, hpit,
    hprior .shortCup (.inl rfl), hprior .key (.inr rfl)]
  simp only [mul_zero, zero_mul, mul_one, zero_add, add_zero]
  exact ENNReal.div_self hpos (measure_ne_top _ _)

-- §3.2, eq. (6)
theorem l1_tall_pitcher (c : ℝ) :
    (game.l1 (wordCost c) [.tall] (some .pitcher)).real {.tallPitcher} = 1 / 2 := by
  have hdead (r : Referent) (hd : game.DeadEnd [.tall] r) :
      (game.s1 0 [.tall] r).real {some .pitcher} = 1 / 2 := by
    rw [game.s1_real_deadEnd hd (by decide), ite_eq_left (by decide),
      show (game.viableNext [.tall]).card = 2 from by decide]
    norm_num
  have hpit : (game.s1 0 [.tall] .tallPitcher).real {some .pitcher} = 1 :=
    game.s1_real_eq_one (by decide) (by decide)
  have hsum : ∑ r, (game.s1 0 [.tall] r).real {some Word.pitcher} = 2 := by
    rw [sum_referent, game.s1_real_eq_zero (r := .tallCup) (by decide) (by decide),
      hdead .shortCup (by decide), hpit, hdead .key (by decide)]
    norm_num
  rw [game.l1_wordCost (c := [.tall]) (by decide), game.l1_real_singleton, hsum, hpit]

end Sedivy

end CohnGordonEtAl2019
