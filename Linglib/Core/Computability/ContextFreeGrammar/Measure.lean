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
* `PCFG.IsTight`: total mass one at every symbol, which is more than tightness at the start
  symbol.

## Main results

* `PCFG.galtonWatson_weight`: the Galton–Watson weight of a tree is `derivProb`.
* `PCFG.isMarkovKernel_galtonWatson`: when every nonterminal has a rule, the offspring kernel is
  Markov.
* `PCFG.derivationMeasure_singleton`: a tree rooted at `s` has probability `derivProb` under the
  derivation measure at `s`, and trees rooted elsewhere have probability `0`.
* `PCFG.derivationMeasure_apply_univ_le_one`: the derivation measure is a sub-probability
  kernel; `PCFG.isTight_iff` says it is Markov exactly when the grammar is tight.
* `PCFG.derivationMeasure_nonterminal_univ`: the termination probabilities satisfy the
  first-step equations of the grammar.
* `PCFG.derivationMeasure_relFreq_univ`: the relative-frequency estimate from a corpus of
  licensed trees terminates almost surely from the root symbol of every tree of the corpus.

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

/-- A PCFG is tight when the derivation measure has total mass one at every symbol: the grammar
almost surely produces a finite derivation from every nonterminal. Total mass one at the start
symbol alone, which Booth and Thompson call consistency, is weaker: it constrains only the
nonterminals a derivation from the start symbol reaches. -/
def IsTight : Prop := ∀ s, GaltonWatson.extinctionProb W.galtonWatson s = 1

theorem isTight_iff : W.IsTight ↔ IsMarkovKernel W.derivationMeasure :=
  ⟨fun h ↦ ⟨fun s ↦ ⟨h s⟩⟩, fun h s ↦ (h.isProbabilityMeasure s).measure_univ⟩

/-! ### Termination probabilities -/

/-- A terminal is a finished derivation. -/
@[simp] theorem derivationMeasure_terminal_univ (a : T) :
    W.derivationMeasure (.terminal a) Set.univ = 1 := by
  show GaltonWatson.extinctionProb W.galtonWatson _ = 1
  rw [GaltonWatson.extinctionProb_eq_lintegral]
  simp [offspring]

/-- A derivation from a nonterminal terminates when the rule chosen there has a right-hand side
all of whose symbols found terminating derivations. -/
theorem derivationMeasure_nonterminal_univ (A : G.NT) :
    W.derivationMeasure (.nonterminal A) Set.univ =
      ∑ r ∈ G.rules.filter (·.input = A),
        W.weight r * (r.output.map fun s ↦ W.derivationMeasure s Set.univ).prod := by
  show GaltonWatson.extinctionProb W.galtonWatson _ = _
  rw [GaltonWatson.extinctionProb_eq_lintegral, galtonWatson_apply, offspring,
    lintegral_map .of_discrete .of_discrete, ruleMeasure, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rfl

/-- Independent events of probabilities `f a` fail jointly with probability at most the sum of
bounds `g a` on their failure probabilities. -/
private theorem one_le_prod_add_sum {α : Type*} {f g : α → ℝ≥0∞} :
    ∀ {l : List α}, (∀ a ∈ l, f a ≤ 1) → (∀ a ∈ l, 1 ≤ f a + g a) →
      1 ≤ (l.map f).prod + (l.map g).sum
  | [], _, _ => by simp
  | a :: l, hf, hfg => by
    have ih := one_le_prod_add_sum (l := l) (fun b hb ↦ hf b (.tail _ hb))
      fun b hb ↦ hfg b (.tail _ hb)
    calc 1 ≤ f a + g a := hfg a (.head _)
      _ ≤ f a * ((l.map f).prod + (l.map g).sum) + g a := by
        gcongr; exact le_mul_of_one_le_right' ih
      _ ≤ f a * (l.map f).prod + (l.map g).sum + g a := by
        rw [mul_add]; gcongr; exact mul_le_of_le_one_left' (hf a (.head _))
      _ = ((a :: l).map f).prod + ((a :: l).map g).sum := by
        rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons, add_assoc,
          add_comm (List.sum _)]

/-- The probability that a derivation from a nonterminal fails to terminate is at most the
expected sum of those probabilities over the right-hand side of the rule chosen there. -/
theorem one_sub_derivationMeasure_nonterminal_univ_le {A : G.NT}
    (hA : A ∈ G.rules.image (·.input)) :
    1 - W.derivationMeasure (.nonterminal A) Set.univ ≤
      ∑ r ∈ G.rules.filter (·.input = A),
        W.weight r * (r.output.map fun s ↦ 1 - W.derivationMeasure s Set.univ).sum := by
  have he1 := W.derivationMeasure_apply_univ_le_one
  refine (ENNReal.add_le_add_iff_left (ne_top_of_le_ne_top ENNReal.one_ne_top
    (he1 (.nonterminal A)))).mp ?_
  rw [add_tsub_cancel_of_le (he1 _), derivationMeasure_nonterminal_univ, ← Finset.sum_add_distrib]
  refine (W.sum_weight A hA).ge.trans (Finset.sum_le_sum fun r _ ↦ ?_)
  rw [← mul_add]
  exact le_mul_of_one_le_right' (one_le_prod_add_sum (fun s _ ↦ he1 s) fun s _ ↦
    (add_tsub_cancel_of_le (he1 s)).ge)

section RelFreq

variable [DecidableEq T]

local notation "q[" W "]" => fun s ↦ 1 - derivationMeasure W s Set.univ

/-- Under relative frequencies of rule counts, the counts weight the non-termination
probabilities of left-hand sides by no more than those of right-hand sides. -/
private theorem sum_ofCounts_mul_le (x : ContextFreeRule T G.NT → ℕ) :
    ∑ r ∈ G.rules, (x r : ℝ≥0∞) * q[ofCounts x] (.nonterminal r.input) ≤
      ∑ r ∈ G.rules, (x r : ℝ≥0∞) * (r.output.map q[ofCounts x]).sum := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := (·.input)) fun r hr ↦ Finset.mem_image_of_mem _ hr,
    ← Finset.sum_fiberwise_of_maps_to (s := G.rules) (g := (·.input))
      (f := fun r ↦ (x r : ℝ≥0∞) * (r.output.map q[ofCounts x]).sum)
      fun r hr ↦ Finset.mem_image_of_mem _ hr]
  refine Finset.sum_le_sum (N := ℝ≥0∞) fun A hA ↦ ?_
  by_cases hn : ∑ r ∈ G.rules.filter (·.input = A), x r = 0
  · refine (Finset.sum_eq_zero fun r hr ↦ ?_).trans_le zero_le
    rw [Nat.eq_zero_of_le_zero <| (Finset.single_le_sum (f := x) (fun _ _ ↦ Nat.zero_le _)
      hr).trans_eq hn, Nat.cast_zero, zero_mul]
  have hn0 : ∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞) ≠ 0 := by
    rw [← Nat.cast_sum]; exact_mod_cast hn
  have hntop : ∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞) ≠ ⊤ := by
    rw [← Nat.cast_sum]; exact ENNReal.natCast_ne_top _
  calc ∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞) * q[ofCounts x] (.nonterminal r.input)
      = (∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞)) *
          q[ofCounts x] (.nonterminal A) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r hr ↦ by rw [(Finset.mem_filter.mp hr).2]
    _ ≤ (∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞)) *
          ∑ r ∈ G.rules.filter (·.input = A),
            (ofCounts x).weight r * (r.output.map q[ofCounts x]).sum :=
        mul_le_mul_right ((ofCounts x).one_sub_derivationMeasure_nonterminal_univ_le hA) _
    _ = ∑ r ∈ G.rules.filter (·.input = A), (x r : ℝ≥0∞) * (r.output.map q[ofCounts x]).sum := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr ↦ ?_
        obtain ⟨hmem, rfl⟩ := Finset.mem_filter.mp hr
        rw [ofCounts_weight hmem hn, ← mul_assoc, ENNReal.mul_div_cancel hn0 hntop]

variable {D : Multiset (RoseTree (Symbol T G.NT))}

/-- **Relative-frequency grammars are tight** ([chi-geman-1998]): under the PCFG estimated from a
corpus of licensed derivation trees, a derivation from the root symbol of any tree of the corpus
terminates almost surely. Nonterminals the corpus does not use carry arbitrary weights, uniform
ones under `relFreq`, and derivations from them need not terminate, so the estimate need not be
`IsTight`. -/
theorem derivationMeasure_relFreq_univ (hD : ∀ t ∈ D, t.Licensed G.Licenses)
    {t : RoseTree (Symbol T G.NT)} (ht : t ∈ D) :
    (relFreq D).derivationMeasure t.value Set.univ = 1 := by
  show (ofCounts (RoseTree.ruleCounts D)).derivationMeasure t.value Set.univ = 1
  have he1 := (ofCounts (RoseTree.ruleCounts D)).derivationMeasure_apply_univ_le_one
  have hle := sum_ofCounts_mul_le (G := G) (RoseTree.ruleCounts D)
  have hid := RoseTree.sum_ruleCounts_nsmul_input hD
    (q := q[ofCounts (RoseTree.ruleCounts D)]) fun a ↦ by
      simp only [derivationMeasure_terminal_univ, tsub_self]
  simp only [nsmul_eq_mul] at hid
  have hfin : ∑ r ∈ G.rules, (RoseTree.ruleCounts D r : ℝ≥0∞) *
      (r.output.map q[ofCounts (RoseTree.ruleCounts D)]).sum ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun r _ ↦ ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) <|
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) <|
        (List.sum_le_length_nsmul _ 1 fun y hy ↦ by
          obtain ⟨s, -, rfl⟩ := List.mem_map.mp hy
          exact tsub_le_self).trans_eq (nsmul_one _)
  rw [hid] at hle
  have hroot := le_zero_iff.mp <|
    (ENNReal.add_le_add_iff_left hfin).mp (hle.trans_eq (add_zero _).symm)
  have hq : 1 - (ofCounts (RoseTree.ruleCounts D)).derivationMeasure t.value Set.univ = 0 :=
    Multiset.sum_eq_zero_iff.mp hroot _ (Multiset.mem_map.mpr ⟨t, ht, rfl⟩)
  exact le_antisymm (he1 _) (tsub_eq_zero_iff_le.mp hq)

/-- Under the grammar estimated from a corpus of licensed trees, the derivations from the root
symbol of a tree of the corpus form a probability space. -/
theorem isProbabilityMeasure_derivationMeasure_relFreq (hD : ∀ t ∈ D, t.Licensed G.Licenses)
    {t : RoseTree (Symbol T G.NT)} (ht : t ∈ D) :
    IsProbabilityMeasure ((relFreq D).derivationMeasure t.value) :=
  ⟨derivationMeasure_relFreq_univ hD ht⟩

end RelFreq

end PCFG
