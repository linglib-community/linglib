/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.ContextFreeGrammar.Probabilistic
public import Linglib.Core.Probability.BranchingProcess.GaltonWatson

/-!
# The derivation measure of a probabilistic context-free grammar

A PCFG is a multitype Galton–Watson process whose types are the symbols: a terminal has no
offspring, and a nonterminal's offspring is the right-hand side of a rule at it chosen with its
weight. The law of the family tree is the law of the derivation tree, and the product of rule
weights `PCFG.derivProb` is the Galton–Watson weight of the tree, so it is derived from the
generation process rather than stipulated. Total mass one at the start symbol is tightness in the
sense of [booth-thompson-1973] and [chi-1999], consistency in older terminology: the grammar
almost surely produces a finite derivation. A grammar estimated by relative frequency from a
treebank is tight in this sense ([chi-geman-1998]).

## Main definitions

* `PCFG.galtonWatson`: the offspring kernel of a PCFG.
* `PCFG.derivationMeasure`: the law of the derivation tree at each symbol, as a kernel.

## Main results

* `PCFG.galtonWatson_weight`: the Galton–Watson weight of a tree is `derivProb`.
* `PCFG.isMarkovKernel_galtonWatson`: when every nonterminal has a rule, the offspring kernel is
  Markov.
* `PCFG.derivationMeasure_singleton`: a tree rooted at `s` has probability `derivProb` under the
  derivation measure at `s`, and trees rooted elsewhere have probability `0`.
* `PCFG.derivationMeasure_apply_univ_le_one`: the derivation measure is a sub-probability
  kernel, a probability measure at a symbol exactly when the grammar is tight there.
* `PCFG.derivationMeasure_nonterminal_univ`: the termination probabilities satisfy the
  first-step equations of the grammar.
* `PCFG.sum_mul_lintegral_offspring_ofCounts`: relative frequencies match the moments of the
  counts they are estimated from.
* `PCFG.isProbabilityMeasure_derivationMeasure_relFreq`: the relative-frequency estimate from a
  corpus of licensed trees is tight at the root symbol of every tree of the corpus.

## References

* [booth-thompson-1973]
* [chi-geman-1998]
* [chi-1999]
* [kozen-1981]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RoseTree
open scoped ENNReal

instance {T N : Type*} : MeasurableSpace (ContextFreeRule T N) := ⊤
instance {T N : Type*} : MeasurableSpace (Symbol T N) := ⊤

namespace PCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

/-- The rule distribution at nonterminal `A`, as a measure on rules. -/
noncomputable def ruleMeasure (A : G.NT) : Measure (ContextFreeRule T G.NT) :=
  ∑ r ∈ G.rules.filter (·.input = A), W.weight r • Measure.dirac r

theorem ruleMeasure_apply (A : G.NT) (s : Set (ContextFreeRule T G.NT)) :
    W.ruleMeasure A s = ∑ r ∈ G.rules.filter (·.input = A), W.weight r * s.indicator 1 r := by
  simp [ruleMeasure, Measure.finsetSum_apply, Measure.dirac_apply' _ .of_discrete]

/-- The offspring of a symbol: none at a terminal, and at a nonterminal the right-hand side of a
rule chosen with its weight. -/
noncomputable def offspring : Symbol T G.NT → Measure (List (Symbol T G.NT))
  | .terminal _ => Measure.dirac []
  | .nonterminal A => (W.ruleMeasure A).map ContextFreeRule.output

theorem offspring_singleton (s : Symbol T G.NT) (syms : List (Symbol T G.NT)) :
    W.offspring s {syms} = W.symbolWeight s syms := by
  classical
  cases s with
  | terminal a =>
    cases syms <;> simp [offspring, Measure.dirac_apply' _ .of_discrete]
  | nonterminal A =>
    rw [offspring, Measure.map_apply .of_discrete .of_discrete, ruleMeasure_apply,
      symbolWeight_nonterminal,
      Finset.sum_congr rfl fun r hr ↦
        show W.weight r * (ContextFreeRule.output ⁻¹' {syms}).indicator 1 r =
          if r = ⟨A, syms⟩ then W.weight r else 0 from ?_, Finset.sum_ite_eq']
    · split_ifs with h
      · rfl
      · rw [W.weight_eq_zero_of_not_mem _ fun h' ↦ h (Finset.mem_filter.mpr ⟨h', rfl⟩)]
    · obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hr
      by_cases hs : r.output = syms
      · rw [Set.indicator_of_mem (by simpa using hs), ite_eq_left (by cases r; simp_all)]
        simp
      · rw [Set.indicator_of_notMem (by simpa using hs),
          ite_eq_right fun h ↦ hs (congrArg ContextFreeRule.output h)]
        simp

theorem offspring_nonterminal_univ (A : G.NT) :
    W.offspring (.nonterminal A) Set.univ = ∑ r ∈ G.rules.filter (·.input = A), W.weight r := by
  rw [offspring, Measure.map_apply .of_discrete .univ, Set.preimage_univ, ruleMeasure_apply]
  simp

theorem offspring_univ_le_one (s : Symbol T G.NT) : W.offspring s Set.univ ≤ 1 := by
  cases s with
  | terminal a => simp [offspring]
  | nonterminal A => exact (W.offspring_nonterminal_univ A).trans_le (W.sum_weight_le_one A)

variable [Countable T] [Countable G.NT]

/-- The branching process of a PCFG: the offspring kernel on symbols. -/
noncomputable def galtonWatson : Kernel (Symbol T G.NT) (List (Symbol T G.NT)) :=
  Kernel.ofFunOfCountable W.offspring

@[simp] theorem galtonWatson_apply (s : Symbol T G.NT) : W.galtonWatson s = W.offspring s := rfl

/-- A grammar with a rule at every nonterminal has a Markov offspring kernel. -/
theorem isMarkovKernel_galtonWatson (h : ∀ A, A ∈ G.rules.image (·.input)) :
    IsMarkovKernel W.galtonWatson :=
  ⟨fun s ↦ ⟨by
    cases s with
    | terminal a => simp [offspring]
    | nonterminal A => exact (W.offspring_nonterminal_univ A).trans (W.sum_weight A (h A))⟩⟩

/-- The Galton–Watson weight of a derivation tree is the product of its rule weights. -/
theorem galtonWatson_weight (t : RoseTree (Symbol T G.NT)) :
    GaltonWatson.weight W.galtonWatson t = W.derivProb t := by
  simp only [GaltonWatson.weight, derivProb, galtonWatson_apply, offspring_singleton]

/-- The law of the derivation tree at each symbol: the law of the family tree of the grammar's
branching process. -/
noncomputable def derivationMeasure : Kernel (Symbol T G.NT) (RoseTree (Symbol T G.NT)) :=
  GaltonWatson.law W.galtonWatson

theorem derivationMeasure_singleton_value (t : RoseTree (Symbol T G.NT)) :
    W.derivationMeasure t.value {t} = W.derivProb t :=
  (GaltonWatson.law_singleton_value W.galtonWatson t).trans (W.galtonWatson_weight t)

theorem derivationMeasure_singleton_of_ne {t : RoseTree (Symbol T G.NT)} {s : Symbol T G.NT}
    (h : t.value ≠ s) : W.derivationMeasure s {t} = 0 :=
  GaltonWatson.law_singleton_of_ne W.galtonWatson h

open scoped Classical in
/-- Under the derivation measure at `s`, a tree has probability `derivProb` when rooted at `s`
and `0` otherwise. -/
theorem derivationMeasure_singleton (t : RoseTree (Symbol T G.NT)) (s : Symbol T G.NT) :
    W.derivationMeasure s {t} = if t.value = s then W.derivProb t else 0 := by
  rw [derivationMeasure, GaltonWatson.law_singleton, galtonWatson_weight]
  split_ifs <;> rfl

/-- The derivation measure is a sub-probability measure at every symbol. -/
theorem derivationMeasure_apply_univ_le_one (s : Symbol T G.NT) :
    W.derivationMeasure s Set.univ ≤ 1 :=
  GaltonWatson.law_univ_le_one W.offspring_univ_le_one s

instance : IsFiniteKernel W.derivationMeasure :=
  ⟨⟨1, ENNReal.one_lt_top, W.derivationMeasure_apply_univ_le_one⟩⟩

/-! ### Expectations over the offspring -/

omit [Countable T] [Countable G.NT] in
theorem lintegral_offspring_nonterminal (A : G.NT) (F : List (Symbol T G.NT) → ℝ≥0∞) :
    ∫⁻ l, F l ∂W.offspring (.nonterminal A) =
      ∑ r ∈ G.rules.filter (·.input = A), W.weight r * F r.output := by
  rw [offspring, lintegral_map .of_discrete .of_discrete, ruleMeasure,
    lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- A derivation from a nonterminal terminates when the rule chosen there has a right-hand side
all of whose symbols found terminating derivations. -/
theorem derivationMeasure_nonterminal_univ (A : G.NT) :
    W.derivationMeasure (.nonterminal A) Set.univ =
      ∑ r ∈ G.rules.filter (·.input = A),
        W.weight r * (r.output.map fun s ↦ W.derivationMeasure s Set.univ).prod :=
  (GaltonWatson.extinctionProb_eq_lintegral W.galtonWatson _).trans
    (W.lintegral_offspring_nonterminal A _)

/-! ### Relative frequencies -/

section RelFreq

variable [DecidableEq T]

omit [Countable T] [Countable G.NT] in
/-- Relative frequencies match moments: totalled over the rule applications counted by `x`, the
expectation of a statistic of the right-hand side under the relative frequencies of `x` is its
total over the right-hand sides applied. -/
theorem sum_mul_lintegral_offspring_ofCounts (x : ContextFreeRule T G.NT → ℕ)
    (F : List (Symbol T G.NT) → ℝ≥0∞) :
    ∑ r ∈ G.rules, (x r : ℝ≥0∞) * ∫⁻ l, F l ∂(ofCounts x).offspring (.nonterminal r.input) =
      ∑ r ∈ G.rules, (x r : ℝ≥0∞) * F r.output := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := ContextFreeRule.input) fun r hr ↦
      Finset.mem_image_of_mem _ hr,
    ← Finset.sum_fiberwise_of_maps_to (s := G.rules) (g := ContextFreeRule.input)
      (f := fun r ↦ (x r : ℝ≥0∞) * F r.output) fun r hr ↦ Finset.mem_image_of_mem _ hr]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  by_cases hn : ∑ r ∈ G.rules.filter (·.input = A), x r = 0
  · have hx : ∀ r ∈ G.rules.filter (·.input = A), x r = 0 := fun r hr ↦
      Nat.eq_zero_of_le_zero <|
        (Finset.single_le_sum (f := x) (fun _ _ ↦ Nat.zero_le _) hr).trans_eq hn
    rw [Finset.sum_eq_zero fun r hr ↦ by rw [hx r hr, Nat.cast_zero, zero_mul],
      Finset.sum_eq_zero fun r hr ↦ by rw [hx r hr, Nat.cast_zero, zero_mul]]
  have hn0 : ∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞) ≠ 0 := by
    rw [← Nat.cast_sum]; exact_mod_cast hn
  have hntop : ∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞) ≠ ⊤ := by
    rw [← Nat.cast_sum]; exact ENNReal.natCast_ne_top _
  calc ∑ r ∈ G.rules.filter (·.input = A),
        (x r : ℝ≥0∞) * ∫⁻ l, F l ∂(ofCounts x).offspring (.nonterminal r.input)
      = (∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞)) *
          ∫⁻ l, F l ∂(ofCounts x).offspring (.nonterminal A) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r hr ↦ by rw [(Finset.mem_filter.mp hr).2]
    _ = ∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞) * F r.output := by
        rw [lintegral_offspring_nonterminal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr ↦ ?_
        obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hr
        rw [ofCounts_weight hmem hn, ← mul_assoc, ENNReal.mul_div_cancel hn0 hntop]

variable {D : Multiset (RoseTree (Symbol T G.NT))}

/-- **Relative-frequency grammars are tight** ([chi-geman-1998]): under the PCFG estimated from a
corpus of licensed derivation trees, a derivation from the root symbol of any tree of the corpus
terminates almost surely, since the node counts of the corpus are a finite excessive measure for
the estimated branching process. Nonterminals the corpus does not use carry arbitrary weights,
uniform ones under `relFreq`, and derivations from them need not terminate. -/
theorem isProbabilityMeasure_derivationMeasure_relFreq (hD : ∀ t ∈ D, t.Licensed G.Licenses)
    {t : RoseTree (Symbol T G.NT)} (ht : t ∈ D) :
    IsProbabilityMeasure ((relFreq D).derivationMeasure t.value) := by
  let ν : Measure (Symbol T G.NT) := (D.map fun t' ↦ (t'.values.map Measure.dirac).sum).sum
  have hint (f : Symbol T G.NT → ℝ≥0∞) :
      ∫⁻ s, f s ∂ν = (D.map fun t' ↦ (t'.values.map f).sum).sum := by
    simp only [ν, Measure.lintegral_multisetSum_measure, Measure.lintegral_listSum_measure,
      Multiset.map_map, List.map_map, Function.comp_def, lintegral_dirac]
  have hfin : IsFiniteMeasure ν := ⟨by
    rw [← lintegral_one, hint]
    simpa [Nat.cast_multiset_sum, Multiset.map_map, Function.comp_def] using
      ENNReal.natCast_lt_top (D.map fun t' ↦ t'.values.length).sum⟩
  have hν : ∀ᵐ s ∂ν, (relFreq D).galtonWatson s Set.univ = 1 := by
    rw [ae_iff, ← lintegral_indicator_one .of_discrete, hint]
    refine Multiset.sum_eq_zero fun y hy ↦ ?_
    obtain ⟨t', ht', rfl⟩ := Multiset.mem_map.mp hy
    refine List.sum_eq_zero fun z hz ↦ ?_
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hz
    refine Set.indicator_of_notMem (not_not.mpr ?_) _
    rw [← t'.map_fst_localTrees] at hs
    obtain ⟨⟨s, ks⟩, hp, rfl⟩ := List.mem_map.mp hs
    have hlic := licensed_iff_forall_mem_localTrees.mp (hD t' ht') _ hp
    cases s with
    | terminal a => simp [offspring]
    | nonterminal A =>
      exact ((relFreq D).offspring_nonterminal_univ A).trans
        ((relFreq D).sum_weight A (Finset.mem_image.mpr ⟨_, hlic, rfl⟩))
  have h : Measure.dirac t.value + GaltonWatson.mean (relFreq D).galtonWatson ∘ₘ ν ≤ ν := by
    refine Measure.le_iff.mpr fun S hS ↦ ?_
    rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS, lintegral_add_measure,
      lintegral_dirac, Measure.lintegral_bind (Kernel.aemeasurable _) .of_discrete, hint, hint]
    simp only [RoseTree.sum_map_values (S.indicator 1), Multiset.sum_map_add]
    simp only [GaltonWatson.lintegral_mean, galtonWatson_apply, ← RoseTree.map_fst_localTrees,
      List.map_map, Function.comp_def]
    refine add_le_add (Multiset.single_le_sum (fun _ _ ↦ zero_le) _
      (Multiset.mem_map_of_mem (fun t' ↦ S.indicator 1 t'.value) ht)) (le_of_eq ?_)
    rw [RoseTree.sum_map_localTrees_eq_sum_ruleCounts hD
        (F := fun p ↦ ∫⁻ l, (l.map (S.indicator 1)).sum ∂(relFreq D).offspring p.1)
        fun a ↦ by simp [offspring],
      RoseTree.sum_map_localTrees_eq_sum_ruleCounts hD
        (F := fun p ↦ (p.2.map (S.indicator 1)).sum) fun a ↦ by simp]
    simp only [nsmul_eq_mul]
    exact sum_mul_lintegral_offspring_ofCounts _ _
  have hae := GaltonWatson.ae_extinctionProb_eq_one (relFreq D).offspring_univ_le_one hν h
  exact ⟨(ae_dirac_iff (p := fun s ↦ (relFreq D).derivationMeasure s Set.univ = 1)
    .of_discrete).mp hae⟩

end RelFreq

end PCFG
