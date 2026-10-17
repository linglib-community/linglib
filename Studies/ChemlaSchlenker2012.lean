module

public import Studies.Schlenker2009
public import Linglib.Data.Experiments.ChemlaSchlenker2012

/-!
# Chemla & Schlenker (2012): Incremental vs. symmetric accounts of presupposition projection

This file formalizes the paper's predictions and its experimental results. The paper takes a
trivalent theory in which a sentence is presuppositionally acceptable when its supervaluation is
defined at every world of the context (its (9), the symmetric condition, `SupervaluationAcceptable`
of Schlenker's appendix on the symmetric version), and an incremental condition that also completes
the sentence after each trigger by every good final without triggers (its (10), the incremental
version). The Incremental Theory lets (10) alone govern projection; the Strict Symmetric Theory lets
(9) alone govern it; the Mixed Theory prefers (10) but lets a presupposition satisfied only by (9)
through at a cost.

The experiments test sentences with the anaphoric trigger *too* in *if*-, *or*- and
*unless*-sentences, with the clause that can satisfy the presupposition before the trigger
(canonical order) or after it (inverse order) ((48)–(49), `target`). In the canonical order both
conditions predict the conditional presupposition `if p, q` ((13a)–(15a),
`supervaluationAcceptable_incremental_canonical`, `supervaluationAcceptable_symmetric_canonical`).
In the inverse order the incremental condition predicts the unconditional presupposition `q`
(`supervaluationAcceptable_incremental_inverse`), while the symmetric condition still predicts
`if p, q` ((13b)–(15b), `supervaluationAcceptable_symmetric_inverse`).

The results are `Data/Experiments/ChemlaSchlenker2012`. The conditional inference is endorsed more
than the unconditional one for every tested sentence (Tables 4 and 7,
`experiment1_conditional_gt_unconditional`, `experiment4_conditional_gt_unconditional`), including
the inverse order, where the Incremental Theory predicts the unconditional presupposition and so an
unconditional inference (`supervaluationAcceptable_incremental_inverse_subset`) and the symmetric
condition does not (`exists_supervaluationAcceptable_symmetric_inverse_not_subset`). And every
target sentence of Experiment 2 is rated above the control that forces local accommodation with
*too* (Table 5, `experiment2_targets_gt_control`), so the inverse order is not unacceptable.

## Implementation notes

* Conditionals are material implications and *unless F, G* is *if not F, G*, as the paper assumes
  (§1.4).
* The properties of *too* that the paper's argument uses to separate the Incremental from the Mixed
  Theory's predictions for inferences (§2.2, §2.3) are not formalized, and neither is the Mixed
  Theory's cost, so the fit of the theories to the ratings is not stated here.

## References

* [chemla-schlenker-2012]
* [schlenker-2009]
-/

@[expose] public section

namespace ChemlaSchlenker2012

open Presupposition Schlenker2009

variable {Atom W : Type*} (I : Atom → Set W)

/-! ### The predictions of §1.4 -/

/-- *Unless F, G* means *if not F, G* (§1.4). -/
def unlessThen (F G : Formula Atom) : Formula Atom := .bin .cond (.not F) G

/-- The target sentence of a construction in an order, with the clause `p` that can satisfy the
presupposition `q` of the trigger `qq'` ((48)–(49), p. 200). -/
def target (p q q' : Atom) : Construction → Order → Formula Atom
  | .ifSentence, .canonical => .bin .cond (.atom p) (.trigger q q')
  | .ifSentence, .inverse => .bin .cond (.not (.trigger q q')) (.not (.atom p))
  | .orSentence, .canonical => .bin .disj (.not (.atom p)) (.trigger q q')
  | .orSentence, .inverse => .bin .disj (.trigger q q') (.not (.atom p))
  | .unlessSentence, .canonical => unlessThen (.not (.atom p)) (.trigger q q')
  | .unlessSentence, .inverse => unlessThen (.trigger q q') (.not (.atom p))

variable {p q q' : Atom} {C : Set W}

private theorem supervaluationAcceptable_incremental_iff_forall {F : Formula Atom} :
    SupervaluationAcceptable I .incremental C F ↔ ∀ w ∈ C, F.middleKleene I w ≠ 0 :=
  (supervaluationAcceptable_incremental_iff I C F).trans Iff.rfl

private theorem supervaluationAcceptable_symmetric_iff_forall {F : Formula Atom}
    (hF : (F.triggers.map Prod.snd).Nodup) :
    SupervaluationAcceptable I .symmetric C F ↔ ∀ w ∈ C, F.strongKleene I w ≠ 0 :=
  (supervaluationAcceptable_symmetric_iff I C F).trans
    (forall₂_congr fun _ _ ↦ supervaluationDefined_iff_of_nodup I hF)

/-- In the canonical order the incremental condition predicts the conditional presupposition
`if p, q` ((13a)–(15a), p. 185). -/
theorem supervaluationAcceptable_incremental_canonical (k : Construction) :
    SupervaluationAcceptable I .incremental C (target p q q' k .canonical) ↔
      C ⊆ {w | w ∈ I p → w ∈ I q} := by
  rw [supervaluationAcceptable_incremental_iff_forall]
  refine forall₂_congr fun w _ ↦ ?_
  cases k <;> simp [target, unlessThen, Formula.middleKleene, Formula.eval]

/-- In the canonical order the symmetric condition predicts the conditional presupposition `if p, q`
((13a)–(15a), p. 185). -/
theorem supervaluationAcceptable_symmetric_canonical (k : Construction) :
    SupervaluationAcceptable I .symmetric C (target p q q' k .canonical) ↔
      C ⊆ {w | w ∈ I p → w ∈ I q} := by
  cases k <;>
    rw [supervaluationAcceptable_symmetric_iff_forall I
      (by simp [target, unlessThen, Formula.triggers])] <;>
    refine forall₂_congr fun w _ ↦ ?_ <;>
    simp [target, unlessThen, Formula.strongKleene, Formula.eval] <;> tauto

/-- In the inverse order the incremental condition predicts the unconditional presupposition `q`
((13b)–(15b), p. 185). -/
theorem supervaluationAcceptable_incremental_inverse (k : Construction) :
    SupervaluationAcceptable I .incremental C (target p q q' k .inverse) ↔ C ⊆ I q := by
  rw [supervaluationAcceptable_incremental_iff_forall]
  refine forall₂_congr fun w _ ↦ ?_
  cases k <;> simp [target, unlessThen, Formula.middleKleene, Formula.eval]

/-- In the inverse order the symmetric condition still predicts the conditional presupposition
`if p, q` ((13b)–(15b), p. 185). -/
theorem supervaluationAcceptable_symmetric_inverse (k : Construction) :
    SupervaluationAcceptable I .symmetric C (target p q q' k .inverse) ↔
      C ⊆ {w | w ∈ I p → w ∈ I q} := by
  cases k <;>
    rw [supervaluationAcceptable_symmetric_iff_forall I
      (by simp [target, unlessThen, Formula.triggers])] <;>
    refine forall₂_congr fun w _ ↦ ?_ <;>
    simp [target, unlessThen, Formula.strongKleene, Formula.eval] <;> tauto

/-- In the inverse order, any context that the Incremental Theory accepts entails the unconditional
presupposition (§2.3.2). -/
theorem supervaluationAcceptable_incremental_inverse_subset (k : Construction)
    (h : SupervaluationAcceptable I .incremental C (target p q q' k .inverse)) : C ⊆ I q :=
  (supervaluationAcceptable_incremental_inverse I k).1 h

/-- The symmetric condition accepts the inverse order in a context that does not entail the
unconditional presupposition, one with a world where `p` and `q` both fail. -/
theorem exists_supervaluationAcceptable_symmetric_inverse_not_subset (k : Construction) {w : W}
    (hp : w ∉ I p) (hq : w ∉ I q) :
    SupervaluationAcceptable I .symmetric {w} (target p q q' k .inverse) ∧ ¬ {w} ⊆ I q := by
  refine ⟨(supervaluationAcceptable_symmetric_inverse I k).2 fun v hv hpv ↦ ?_, fun h ↦ hq (h rfl)⟩
  rw [Set.mem_singleton_iff] at hv
  exact absurd (hv ▸ hpv) hp

/-! ### The results -/

/-- In Experiment 1, for every tested sentence, the conditional inference is endorsed more than the
unconditional one (Table 4, p. 206). -/
theorem experiment1_conditional_gt_unconditional :
    ∀ r ∈ experiment1Inferences, r.inference = .conditional →
      ∃ r' ∈ experiment1Inferences, r'.construction = r.construction ∧ r'.order = r.order ∧
        r'.inference = .unconditional ∧ r'.mean.toRat < r.mean.toRat := by
  decide +kernel

/-- In Experiment 4, for every tested sentence, the conditional inference is endorsed more than the
unconditional one (Table 7, p. 212). -/
theorem experiment4_conditional_gt_unconditional :
    ∀ r ∈ experiment4Inferences, r.inference = .conditional →
      ∃ r' ∈ experiment4Inferences, r'.construction = r.construction ∧ r'.order = r.order ∧
        r'.inference = .unconditional ∧ r'.mean.toRat < r.mean.toRat := by
  decide +kernel

/-- Every target sentence of Experiment 2 is rated above the control sentence that forces local
accommodation with *too* (Table 5, p. 209). -/
theorem experiment2_targets_gt_control :
    ∀ r ∈ experiment2Targets,
      (experiment2Controls .localAccommodationToo).mean.toRat < r.mean.toRat := by
  decide +kernel

end ChemlaSchlenker2012
