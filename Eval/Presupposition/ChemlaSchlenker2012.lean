module

public import Eval.Presupposition.Map
public import Mathlib.Tactic.IntervalCases

/-!
# Scoring the accounts on Chemla & Schlenker (2012)

Chemla and Schlenker's inferential experiments rate, for *if*-, *or*- and *unless*-sentences with
*too*, whether the conditional or the unconditional presupposition follows. Each cell is scored in
four steps. The fact is the inference rated higher in the cell, where the test comparing the two
ratings is significant at the .05 level (`advantage`). Its parse is the target sentence, a formula
of the propositional fragment that every theory reads (`target`). The theory says which contexts
accept that formula (`Theory.accepts`). The linking hypothesis, that subjects infer the
presupposition a sentence is predicted to carry, turns the acceptance conditions into a predicted
inference: the unconditional one if the theory predicts it, otherwise the conditional one if the
theory predicts that, and nothing if it predicts neither (`predicted`). A theory, registered or
under development, that accepts a target sentence exactly where the context entails `if p, q`
predicts the conditional inference (`predicted_of_accepts_iff_conditional`).

Every account accepts a target sentence iff the context entails `if p, q`, except that the
incremental accounts, which coincide on the fragment
(`Account.antisymmRel_filtering_of_mem_incremental`), require the unconditional `q` in the inverse
order (`accepts_target_iff`). In Experiment 1 the conditional inference is rated higher in every
tested cell (`observed_experiment1`), so every incremental account is wrong on each inverse-order
sentence and right on each canonical one, and every other account, the symmetric ones and Limited
Symmetry, is right on all (`verdict_experiment1`). Experiment 4 replicates this in part: the
differences on the inverse *if*- and *or*-sentences are not significant (`observed_experiment4`),
so every account is silent there and the incremental accounts are wrong on the inverse
*unless*-sentence alone (`verdict_experiment4`).

## Implementation notes

* The inferences are the presuppositions, so `q` entails `if p, q`, and a theory that predicts the
  unconditional inference also predicts the conditional one; `predicted` credits it with the
  unconditional one, the reversal the paper predicts for the Incremental Theory. The paper's
  conditional inference, *studying abroad would be stupid of Jeanne*, is stronger than the
  conditional presupposition, so that neither inference entails the other.
* The symmetric accounts are the paper's Strict Symmetric Theory, which predicts the conditional
  inference from any trigger. The paper argues for a Mixed Theory, on which symmetric satisfaction
  comes at a cost that the preference of *too* for anaphoric resolution outweighs; neither the cost
  nor the anaphoricity of *too* is formalized, and neither are the acceptability experiments.

## References

* [chemla-schlenker-2012]
* [schlenker-2009]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Eval.Presupposition.ChemlaSchlenker2012

open _root_.Presupposition Account SyntacticEnvironment Kalomoiros2023 _root_.ChemlaSchlenker2012
  Data.Statistics

/-! ### Acceptance of the target sentences -/

variable {W : Type} (I : Fin 3 → Set W) {C : Set W}

private theorem transparency_symmetric_target (k : Construction) (o : Order) :
    Schlenker2009.Transparency .symmetric C (Formula.occurrences I (target 0 1 2 k o)) ↔
      C ⊆ {w | w ∈ I 0 → w ∈ I 1} := by
  have tf (K : SyntacticEnvironment (Fin 3)) :
      ∀ f ∈ ({K.truth I} : Set (Set W → Set W)), IsTruthFunctional f :=
    fun _ hf ↦ hf ▸ isTruthFunctional_truth I K
  cases k <;> cases o <;>
    simp only [Schlenker2009.Transparency, Formula.forall_mem_occurrences, Occurrence.Transparent,
      SyntacticEnvironment.occurrence, Schlenker2009.Version.parsingPoint, continuations_top,
      target, unlessThen, Formula.triggers, List.map_cons, List.map_nil, List.nil_append,
      List.singleton_append, List.append_nil, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true] <;>
    rw [transparent_iff_subset (tf _)] <;>
    simp [Set.subset_def, DependsAt, SyntacticEnvironment.truth, Step.truth, Connective.eval,
      Formula.truth]

private theorem limitedSymmetry_target (k : Construction) (o : Order) :
    LimitedSymmetry C (Formula.occurrences I (target 0 1 2 k o)) ↔
      C ⊆ {w | w ∈ I 0 → w ∈ I 1} := by
  cases k <;> cases o <;>
    rw [limitedSymmetry_of_triggers I (a := 2) rfl] <;>
    dsimp only [List.nil_append, List.cons_append] <;>
    rw [limitedSymmetryAt_iff_funs] <;>
    refine forall₂_congr fun w _ ↦ ?_ <;>
    (by_cases hq : w ∈ I 1
     · simp [hq]
     · by_cases hp : w ∈ I 0
       · refine iff_of_false (fun h ↦ ?_) (by simp [hp, hq])
         have := h hq _ le_rfl
         simp [rightItems, funs, stepFuns, evalB, val, Formula.truth, Step.rightItems,
           Connective.rightItems, hp] at this
       · refine iff_of_true (fun _ n hn ↦ ?_) (by simp [hp])
         simp only [rightItems_cons, rightItems_nil, Step.rightItems, Connective.rightItems] at hn
         interval_cases n <;>
           simp_all [funs, stepFuns, evalB, val, Formula.truth, Step.rightItems,
             Connective.rightItems, compat])

/-- Every account accepts a target sentence iff the context entails the conditional
presupposition `if p, q`, except that an incremental account requires the unconditional `q` in
the inverse order. -/
theorem accepts_target_iff (a : Account) (k : Construction) (o : Order) :
    a.Accepts I C (target 0 1 2 k o) ↔
      C ⊆ (if a ∈ incremental ∧ o = .inverse then I 1 else {w | w ∈ I 0 → w ∈ I 1}) := by
  by_cases ha : a ∈ incremental
  · have h := antisymmRel_filtering_of_mem_incremental ha
    have : a.Accepts I C (target 0 1 2 k o) ↔
        Schlenker2009.SupervaluationAcceptable I .incremental C (target 0 1 2 k o) :=
      ⟨fun hC ↦ filtering_stronger_supervaluationIncremental _ _ I C _ (h.1 _ _ I C _ hC),
        fun hC ↦ h.2 _ _ I C _ (supervaluationIncremental_stronger_filtering _ _ I C _ hC)⟩
    rw [this]
    cases o
    · simpa using supervaluationAcceptable_incremental_canonical I k
    · simpa [ha] using supervaluationAcceptable_incremental_inverse I k
  · simp only [ha, false_and, ite_false]
    have hsuper : Schlenker2009.SupervaluationAcceptable I .symmetric C (target 0 1 2 k o) ↔
        C ⊆ {w | w ∈ I 0 → w ∈ I 1} := by
      cases o
      · exact supervaluationAcceptable_symmetric_canonical I k
      · exact supervaluationAcceptable_symmetric_inverse I k
    cases a <;> simp [incremental] at ha
    · exact transparency_symmetric_target I k o
    · exact (Schlenker2009.satisfaction_iff_transparency I .symmetric C _).trans
        (transparency_symmetric_target I k o)
    · refine (Schlenker2009.strongKleeneAcceptable_symmetric_iff I C _).trans (Iff.trans ?_ hsuper)
      exact (forall₂_congr fun w _ ↦
        (Schlenker2009.supervaluationDefined_iff_of_nodup I (nodup_triggers_target k o)).symm).trans
        (Schlenker2009.supervaluationAcceptable_symmetric_iff I C _).symm
    · exact hsuper
    · exact limitedSymmetry_target I k o

/-! ### Predictions -/

open Classical in
/-- The linking hypothesis of the experiments as a rule. A theory predicts that subjects endorse
the unconditional inference `q` from the target sentence of a cell if it predicts that inference,
and otherwise the conditional inference `if p, q` if it predicts that one (§2.3.1, Table 1). A
theory that predicts neither predicts nothing about the cell. -/
noncomputable def predicted (T : Theory) (k : Construction) (o : Order) : Option Inference :=
  if T.Predicts (target (0 : Fin 3) 1 2 k o) fun I ↦ I 1 then some .unconditional
  else if T.Predicts (target (0 : Fin 3) 1 2 k o) fun I ↦ {w | w ∈ I 0 → w ∈ I 1} then
    some .conditional
  else none

/-- A theory that accepts a target sentence exactly where the context entails the conditional
presupposition predicts the conditional inference: a context where `p` fails everywhere accepts
the sentence without entailing `q`. -/
theorem predicted_of_accepts_iff_conditional {T : Theory} {k : Construction} {o : Order}
    (h : ∀ (W : Type) (I : Fin 3 → Set W) (C : Set W),
      T.accepts I C (target 0 1 2 k o) ↔ C ⊆ {w | w ∈ I 0 → w ∈ I 1}) :
    predicted T k o = some .conditional := by
  refine (ite_eq_right fun hq ↦ ?_).trans (ite_eq_left fun W I C ↦ (h W I C).1)
  exact hq Unit (fun _ ↦ ∅) Set.univ ((h _ _ _).2 fun _ _ hp ↦ hp.elim) (Set.mem_univ ())

theorem predicted_eq (a : Account) (k : Construction) (o : Order) :
    predicted a.theory k o =
      some (if a ∈ incremental ∧ o = .inverse then .unconditional else .conditional) := by
  split_ifs with h
  · exact ite_eq_left fun W I C hC ↦ by
      simpa only [ite_eq_left h] using (accepts_target_iff I a k o).1 hC
  · exact predicted_of_accepts_iff_conditional fun W I C ↦
      (accepts_target_iff I a k o).trans (by rw [ite_eq_right h])

/-! ### Observations and verdicts -/

/-- The inference rated higher in a cell, from the mean ratings `c` of the conditional and `u` of
the unconditional inference and the p-value of the test comparing them, if the test is
significant at the .05 level. -/
def advantage (c u : ℚ) (p : PValue) : Option Inference :=
  if p.Significant (1 / 20) then
    if u < c then some .conditional else if c < u then some .unconditional else none
  else none

/-- The inference rated higher in a cell of Experiment 1 (Table 4). -/
def observed1 (k : Construction) (o : Order) : Option Inference := do
  let mean i := (experiment1Inferences.find? fun r ↦
    r.construction = k ∧ r.order = o ∧ r.inference = i).map (·.mean.toRat)
  let t ← experiment1Tests.find? fun t ↦ t.construction = k ∧ t.order = o
  advantage (← mean .conditional) (← mean .unconditional) t.p

/-- The inference rated higher in a cell of Experiment 4 (Table 7). -/
def observed4 (k : Construction) (o : Order) : Option Inference := do
  let mean i := (experiment4Inferences.find? fun r ↦
    r.construction = k ∧ r.order = o ∧ r.inference = i).map (·.mean.toRat)
  let t ← experiment4Tests.find? fun t ↦ t.construction = k ∧ t.order = o
  advantage (← mean .conditional) (← mean .unconditional) t.p

/-- Experiment 1 of [chemla-schlenker-2012], whose inferences are rated in Table 4. -/
noncomputable def experiment1 : Experiment Theory (Construction × Order) Inference where
  observed c := observed1 c.1 c.2
  predicted T c := predicted T c.1 c.2

/-- Experiment 4 of [chemla-schlenker-2012], whose inferences are rated in Table 7. -/
noncomputable def experiment4 : Experiment Theory (Construction × Order) Inference where
  observed c := observed4 c.1 c.2
  predicted T c := predicted T c.1 c.2

/-- By Table 4, the conditional inference is rated significantly higher in every tested cell, and
the *unless*-sentence in the canonical order was not tested. -/
theorem observed_experiment1 (k : Construction) (o : Order) :
    experiment1.observed (k, o) =
      if k = .unlessSentence ∧ o = .canonical then none else some .conditional := by
  cases k <;> cases o <;> decide +kernel

/-- By Table 7, the conditional inference is rated significantly higher on the canonical *if*- and
*or*-sentences and the inverse *unless*-sentence. On the inverse *if*- and *or*-sentences it is
rated higher, but not significantly (§3.3.3), and the canonical *unless*-sentence was not
tested. -/
theorem observed_experiment4 (k : Construction) (o : Order) :
    experiment4.observed (k, o) =
      if (k = .unlessSentence ↔ o = .canonical) then none else some .conditional := by
  cases k <;> cases o <;> decide +kernel

/-- Where an experiment finds the conditional inference rated higher, an incremental account is
wrong on an inverse-order sentence and right on a canonical one, and every other account is
right. -/
private theorem verdict_of_observed {X : Experiment Theory (Construction × Order) Inference}
    (hp : ∀ T c, X.predicted T c = predicted T c.1 c.2) {k : Construction} {o : Order}
    {Q : Prop} [Decidable Q] (ho : X.observed (k, o) = if Q then none else some .conditional)
    (a : Account) :
    X.verdict a.theory (k, o) =
      if Q then .silent else if a ∈ incremental ∧ o = .inverse then .wrong else .correct := by
  rw [Experiment.verdict, hp, ho, predicted_eq]
  split_ifs <;> simp_all [Verdict.of]

/-- On Experiment 1, every incremental account is wrong on each inverse-order sentence and right
on each canonical one, and every other account is right on all. -/
theorem verdict_experiment1 (a : Account) (k : Construction) (o : Order) :
    experiment1.verdict a.theory (k, o) = if k = .unlessSentence ∧ o = .canonical then .silent
      else if a ∈ incremental ∧ o = .inverse then .wrong else .correct :=
  verdict_of_observed (fun _ _ ↦ rfl) (observed_experiment1 k o) a

/-- On Experiment 4, every account is silent on the inverse *if*- and *or*-sentences; an
incremental account is wrong on the inverse *unless*-sentence and right on the canonical ones, and
every other account is right on all three. -/
theorem verdict_experiment4 (a : Account) (k : Construction) (o : Order) :
    experiment4.verdict a.theory (k, o) = if (k = .unlessSentence ↔ o = .canonical) then .silent
      else if a ∈ incremental ∧ o = .inverse then .wrong else .correct :=
  verdict_of_observed (fun _ _ ↦ rfl) (observed_experiment4 k o) a

end Eval.Presupposition.ChemlaSchlenker2012
