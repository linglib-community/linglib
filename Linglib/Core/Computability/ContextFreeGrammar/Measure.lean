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
generation process rather than stipulated. Total mass one is tightness in the sense of
[booth-thompson-1973] and [chi-1999], consistency in older terminology: the grammar almost surely
produces a finite derivation from every symbol.

## Main definitions

* `PCFG.galtonWatson`: the offspring kernel of a PCFG.
* `PCFG.derivationMeasure`: the law of the derivation tree at each symbol, as a kernel.
* `PCFG.IsTight`: total mass one at every symbol.

## Main results

* `PCFG.galtonWatson_weight`: the Galton–Watson weight of a tree is `derivProb`.
* `PCFG.isMarkovKernel_galtonWatson`: when every nonterminal has a rule, the offspring kernel is
  Markov.
* `PCFG.derivationMeasure_singleton`: a tree rooted at `s` has probability `derivProb` under the
  derivation measure at `s`, and trees rooted elsewhere have probability `0`.
* `PCFG.derivationMeasure_apply_univ_le_one`: the derivation measure is a sub-probability
  kernel; `PCFG.isTight_iff` says it is Markov exactly when the grammar is tight.

## References

* [booth-thompson-1973]
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

theorem isMarkovKernel_galtonWatson (h : ∀ A, A ∈ G.rules.image (·.input)) :
    IsMarkovKernel W.galtonWatson :=
  ⟨fun s ↦ ⟨by
    cases s with
    | terminal a => simp [offspring]
    | nonterminal A => exact (W.offspring_nonterminal_univ A).trans (W.sum_weight A (h A))⟩⟩

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
theorem derivationMeasure_singleton (t : RoseTree (Symbol T G.NT)) (s : Symbol T G.NT) :
    W.derivationMeasure s {t} = if t.value = s then W.derivProb t else 0 := by
  rw [derivationMeasure, GaltonWatson.law_singleton, galtonWatson_weight]
  split_ifs <;> rfl

theorem derivationMeasure_apply_univ_le_one (s : Symbol T G.NT) :
    W.derivationMeasure s Set.univ ≤ 1 :=
  GaltonWatson.law_univ_le_one W.offspring_univ_le_one s

instance : IsFiniteKernel W.derivationMeasure :=
  ⟨⟨1, ENNReal.one_lt_top, W.derivationMeasure_apply_univ_le_one⟩⟩

/-- A PCFG is tight when the derivation measure has total mass one at every symbol: the grammar
almost surely produces a finite derivation from every nonterminal. Booth and Thompson call this
consistency. -/
def IsTight : Prop := ∀ s, GaltonWatson.extinctionProb W.galtonWatson s = 1

theorem isTight_iff : W.IsTight ↔ IsMarkovKernel W.derivationMeasure :=
  ⟨fun h ↦ ⟨fun s ↦ ⟨h s⟩⟩, fun h s ↦ (h.isProbabilityMeasure s).measure_univ⟩

end PCFG
