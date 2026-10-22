/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Processing.Surprisal.PrefixProbability

/-!
# Hale (2001): A Probabilistic Earley Parser as a Psycholinguistic Model

This file formalizes the linking hypothesis of [hale-2001]. Cognitive load is the total probability
of the structural analyses incompatible with the input so far (section 4), `disconfirmed`, which for
a consistent grammar is one minus the prefix probability (`disconfirmed_eq_one_sub`), and
word-by-word reading time is proportional to the log of the ratio of the prefix probability before
the word to the one after it, the word's surprisal (`surprisal_next_eq_log_div`), where the prefix
probability is [stolcke-1995]'s, computed by a probabilistic Earley parser that is
strong-competence, frequency-sensitive, and eager (Principles 1 to 3). The parser computes every
parse, so the theory is one of total parallelism (section 3): garden-pathing needs no reanalysis and
happens exactly at words where the disconfirmed analyses comprise most of the probability mass
(`log_le_surprisal_next`), which is how the paper reads the spike at *fell* in *the horse raced
past the barn fell*, where grammar (1) puts the prefix probability before the word at more than ten
times the one after it (section 6.1), and the subject and object relative asymmetry of grammar (3)
(section 6.3). The two levels of the linking hypothesis agree, since prefix-level load only grows
along a sentence (`disconfirmed_mono`) and word-level surprisals telescope to the negative log of
the sentence's prefix mass (`totalSurprisal_nil_eq`).

## Implementation notes

The demonstrations' numerics, grammars (1) to (3) and the reading-time figures, require
Stolcke's Earley chart over recursive probabilistic context-free grammars and await an Earley
substrate; the theorems here are the grammar-independent content of the linking hypothesis,
stated for any probability measure over structures with string yields.

The paper defines a word's surprisal as the log ratio of prefix probabilities. Here it is the
library's surprisal of the word under the next-word law of the grammar's language model,
`(ofMeasure (P.map str)).next`, the negative log of its conditional probability, and the paper's
ratio is a theorem about it.

## References

* [hale-2001]
* [stolcke-1995]
* [levy-2008]
-/

@[expose] public section

namespace Hale2001

open InformationTheory MeasureTheory ProbabilityTheory Surprisal AutoregressiveSequenceModel
open scoped ENNReal

variable {T W : Type*} [MeasurableSpace T] (P : Measure T) (str : T → List W) (ws : List W)
  (w : W)

/-- Prefix-level cognitive load (section 4): the total probability of the structural analyses
incompatible with the prefix. -/
noncomputable def disconfirmed : ℝ≥0∞ := P (consistent str ws)ᶜ

/-- No analysis has been disconfirmed before any input is seen. -/
@[simp] theorem disconfirmed_nil : disconfirmed P str [] = 0 := by
  simp [disconfirmed]

/-- Disconfirmed mass grows along a sentence: an extension has disconfirmed at least what its
prefix has, so prefix-level load never decreases. -/
theorem disconfirmed_mono {ws ws' : List W} (h : ws <+: ws') :
    disconfirmed P str ws ≤ disconfirmed P str ws' :=
  measure_mono (Set.compl_subset_compl.2 (consistent_anti str h))

/-- For a consistent grammar the disconfirmed mass is one minus the prefix probability
(section 3). -/
theorem disconfirmed_eq_one_sub [DiscreteMeasurableSpace T] [IsProbabilityMeasure P] :
    disconfirmed P str ws = 1 - P (consistent str ws) :=
  prob_compl_eq_one_sub .of_discrete

variable [MeasurableSpace W]

/-- The surprisals of the words of `rest`, read one by one after the prefix `acc`. -/
noncomputable def totalSurprisal : List W → List W → ℝ
  | _, [] => 0
  | acc, w :: rest =>
    surprisal ((ofMeasure (P.map str)).next acc) (some w) + totalSurprisal (acc ++ [w]) rest

variable [DiscreteMeasurableSpace T] [MeasurableSingletonClass W]

/-- Word-level cognitive load (section 4): a word's surprisal is the log of the ratio of the
prefix probability before the word to the prefix probability after it. -/
theorem surprisal_next_eq_log_div :
    surprisal ((ofMeasure (P.map str)).next ws) (some w) =
      Real.log (P.real (consistent str ws) / P.real (consistent str (ws ++ [w]))) := by
  rw [surprisal, measureReal_def, next_ofMeasure_map_apply_some,
    cond_apply_of_subset .of_discrete (consistent_anti str (List.prefix_append ws [w])),
    ENNReal.toReal_div, ← Real.log_inv, inv_div]
  rfl

/-- Surprisal in disconfirmation form: the log of one plus the ratio of the mass disconfirmed
at the word to the mass surviving it. -/
theorem surprisal_next_eq_log_one_add (ha : 0 < P.real (consistent str (ws ++ [w]))) :
    surprisal ((ofMeasure (P.map str)).next ws) (some w) =
      Real.log (1 + (P.real (consistent str ws) - P.real (consistent str (ws ++ [w])))
        / P.real (consistent str (ws ++ [w]))) := by
  rw [surprisal_next_eq_log_div]
  congr 1
  field_simp
  ring

/-- Garden-pathing (section 6.1): if the mass disconfirmed at a word is at least `k` times
the surviving mass, the word's surprisal is at least `log (1 + k)`; difficulty spikes exactly
where the disconfirmable analyses comprise a great amount of probability. -/
theorem log_le_surprisal_next {k : ℝ} (hk : 0 ≤ k)
    (ha : 0 < P.real (consistent str (ws ++ [w])))
    (hdis : k * P.real (consistent str (ws ++ [w])) ≤
      P.real (consistent str ws) - P.real (consistent str (ws ++ [w]))) :
    Real.log (1 + k) ≤ surprisal ((ofMeasure (P.map str)).next ws) (some w) := by
  rw [surprisal_next_eq_log_one_add P str ws w ha]
  refine Real.log_le_log (by linarith) ?_
  have hdiv : k ≤ (P.real (consistent str ws) - P.real (consistent str (ws ++ [w])))
      / P.real (consistent str (ws ++ [w])) :=
    (le_div_iff₀ ha).mpr hdis
  linarith

/-! ### Load along a sentence -/

variable [IsProbabilityMeasure P]

/-- Word surprisals telescope: reading `rest` after `acc` costs the log of the ratio of the
masses before and after, whenever the whole string has positive mass. -/
theorem totalSurprisal_eq {acc rest : List W}
    (hpos : 0 < P.real (consistent str (acc ++ rest))) :
    totalSurprisal P str acc rest =
      Real.log (P.real (consistent str acc)) -
        Real.log (P.real (consistent str (acc ++ rest))) := by
  induction rest generalizing acc with
  | nil => simp [totalSurprisal]
  | cons w rest ih =>
    rw [totalSurprisal]
    have hpos' : 0 < P.real (consistent str (acc ++ [w] ++ rest)) := by
      rwa [List.append_assoc, List.singleton_append]
    have h₁ : 0 < P.real (consistent str (acc ++ [w])) :=
      hpos'.trans_le (measureReal_mono (consistent_anti str (List.prefix_append _ rest)))
    have h₀ : 0 < P.real (consistent str acc) :=
      h₁.trans_le (measureReal_mono (consistent_anti str (List.prefix_append acc [w])))
    rw [ih hpos', List.append_assoc, List.singleton_append, surprisal_next_eq_log_div,
      Real.log_div h₀.ne' h₁.ne']
    ring

/-- The linking hypothesis at the sentence level (section 4): the total surprisal of a sentence
is the negative log of its prefix mass, the whole disconfirmed mass paid out word by word. -/
theorem totalSurprisal_nil_eq {ws : List W} (hpos : 0 < P.real (consistent str ws)) :
    totalSurprisal P str [] ws = -Real.log (P.real (consistent str ws)) := by
  rw [totalSurprisal_eq P str (by simpa using hpos), consistent_nil, probReal_univ]
  simp

end Hale2001
