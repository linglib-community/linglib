module

public import Eval.Presupposition.Account
public import Eval.Presupposition.Map
public import Mathlib.Tactic.IntervalCases

/-!
# Scoring the accounts on Chemla & Schlenker (2012)

Chemla and Schlenker's inferential experiments rate, for *if*-, *or*- and *unless*-sentences with
*too*, whether the conditional or the unconditional presupposition follows. Each cell is scored in
four steps. The fact is the inference endorsed more in the cell (`observed`). Its parse is the
target sentence, a formula of the propositional fragment that every theory reads (`target`). The
theory says which contexts accept that formula (`Theory.accepts`). The linking hypothesis, that
subjects infer the presupposition a sentence is predicted to carry (the paper's §2.3.1), turns the
acceptance conditions into a predicted inference: the unconditional one if the theory predicts it,
otherwise the conditional one if the theory predicts that, and nothing if it predicts neither
(`predicted`). Each experiment scores a theory cell by cell (`experiment1`, `experiment4`), for a
registered account or for a theory under development alike.

Every account accepts a target sentence iff the context entails `if p, q`, except that the
incremental accounts, which coincide on the fragment (`Eval.Presupposition.edges`), require the
unconditional `q` in the inverse order (`accepts_target_iff`). The conditional inference is
endorsed more in every tested cell of both experiments (`observed_experiment1`,
`observed_experiment4`). So every incremental account is wrong on
each inverse-order sentence and right on each canonical one, and every other account, the
symmetric ones and Limited Symmetry, is right on all (`verdict_experiment1`,
`verdict_experiment4`).

## References

* [chemla-schlenker-2012]
* [schlenker-2009]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Eval.Presupposition.ChemlaSchlenker2012

open _root_.Presupposition Account SyntacticEnvironment Kalomoiros2023
open _root_.ChemlaSchlenker2012 (Construction Order Inference target experiment1Inferences
  experiment4Inferences)

/-- The incremental accounts. -/
def incremental : List Account :=
  [dynamic, filtering, transparencyIncremental, satisfactionIncremental, kleeneIncremental,
    supervaluationIncremental]

/-! ### Acceptance of the target sentences -/

variable {W : Type} (I : Fin 3 → Set W) {C : Set W}

/-- The target sentences carry one trigger. -/
theorem triggers_target (k : Construction) (o : Order) :
    ((target (0 : Fin 3) 1 2 k o).triggers.map Prod.snd).Nodup := by
  cases k <;> cases o <;> simp [target, _root_.ChemlaSchlenker2012.unlessThen, Formula.triggers]

private theorem accepts_iff_supervaluationAcceptable_incremental {a : Account}
    (ha : a ∈ incremental) (F : Formula (Fin 3)) :
    a.Accepts I C F ↔ Schlenker2009.SupervaluationAcceptable I .incremental C F := by
  have hf : a.Stronger filtering ∧ filtering.Stronger a := by
    simp only [incremental, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨dynamic_stronger_filtering, filtering_stronger_dynamic⟩
    · exact ⟨.refl _, .refl _⟩
    · exact ⟨transparencyIncremental_stronger_dynamic.trans dynamic_stronger_filtering,
        filtering_stronger_dynamic.trans dynamic_stronger_transparencyIncremental⟩
    · exact ⟨(satisfactionIncremental_stronger_transparencyIncremental.trans
          transparencyIncremental_stronger_dynamic).trans dynamic_stronger_filtering,
        (filtering_stronger_dynamic.trans dynamic_stronger_transparencyIncremental).trans
          transparencyIncremental_stronger_satisfactionIncremental⟩
    · exact ⟨kleeneIncremental_stronger_filtering, filtering_stronger_kleeneIncremental⟩
    · exact ⟨supervaluationIncremental_stronger_filtering,
        filtering_stronger_supervaluationIncremental⟩
  exact ⟨fun h ↦ filtering_stronger_supervaluationIncremental _ _ I C F (hf.1 _ _ I C F h),
    fun h ↦ hf.2 _ _ I C F (supervaluationIncremental_stronger_filtering _ _ I C F h)⟩

open SyntacticEnvironment Kalomoiros2023 in
/-- Evaluate Limited Symmetry at every parsing point of a concrete environment. -/
local macro "ls_points" : tactic =>
  `(tactic| (intro n hn
             simp only [rightItems_cons, rightItems_nil, Step.rightItems, Connective.rightItems]
               at hn
             interval_cases n <;>
               simp_all [funs, stepFuns, evalB, val, Formula.truth, Step.rightItems,
                 Connective.rightItems, compat, Connective.eval]))

private theorem transparency_symmetric_target (k : Construction) (o : Order) :
    Schlenker2009.Transparency .symmetric C (Formula.occurrences I (target 0 1 2 k o)) ↔
      C ⊆ {w | w ∈ I 0 → w ∈ I 1} := by
  have tf (K : SyntacticEnvironment (Fin 3)) :
      ∀ f ∈ ({K.truth I} : Set (Set W → Set W)), IsTruthFunctional f :=
    fun _ hf ↦ hf ▸ isTruthFunctional_truth I K
  cases k <;> cases o <;>
    simp only [Schlenker2009.Transparency, Formula.forall_mem_occurrences, Occurrence.Transparent,
      SyntacticEnvironment.occurrence, Schlenker2009.Version.parsingPoint, continuations_top,
      target, _root_.ChemlaSchlenker2012.unlessThen, Formula.triggers, List.map_cons, List.map_nil, List.nil_append, List.singleton_append,
      List.append_nil, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      and_true] <;>
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
       · refine iff_of_true (fun _ ↦ ?_) (by simp [hp])
         ls_points)

/-- Every account accepts a target sentence iff the context entails the conditional
presupposition `if p, q`, except that an incremental account requires the unconditional `q` in
the inverse order. -/
theorem accepts_target_iff (a : Account) (k : Construction) (o : Order) :
    a.Accepts I C (target 0 1 2 k o) ↔
      C ⊆ (if a ∈ incremental ∧ o = .inverse then I 1 else {w | w ∈ I 0 → w ∈ I 1}) := by
  by_cases ha : a ∈ incremental
  · rw [accepts_iff_supervaluationAcceptable_incremental I ha]
    cases o
    · simpa using _root_.ChemlaSchlenker2012.supervaluationAcceptable_incremental_canonical I k
    · simpa [ha] using _root_.ChemlaSchlenker2012.supervaluationAcceptable_incremental_inverse I k
  · simp only [ha, false_and, ite_false]
    have hsuper : Schlenker2009.SupervaluationAcceptable I .symmetric C (target 0 1 2 k o) ↔
        C ⊆ {w | w ∈ I 0 → w ∈ I 1} := by
      cases o
      · exact _root_.ChemlaSchlenker2012.supervaluationAcceptable_symmetric_canonical I k
      · exact _root_.ChemlaSchlenker2012.supervaluationAcceptable_symmetric_inverse I k
    cases a <;> simp [incremental] at ha
    · exact transparency_symmetric_target I k o
    · exact (Schlenker2009.satisfaction_iff_transparency I .symmetric C _).trans
        (transparency_symmetric_target I k o)
    · refine (Schlenker2009.strongKleeneAcceptable_symmetric_iff I C _).trans (Iff.trans ?_ hsuper)
      exact (forall₂_congr fun w _ ↦
        (Schlenker2009.supervaluationDefined_iff_of_nodup I (triggers_target k o)).symm).trans
        (Schlenker2009.supervaluationAcceptable_symmetric_iff I C _).symm
    · exact hsuper
    · exact limitedSymmetry_target I k o

/-! ### Predictions, observations and verdicts -/

open Classical in
/-- The linking hypothesis of the experiments as a rule. A theory predicts that subjects endorse
the unconditional inference `q` from the target sentence of a cell if it predicts that inference,
and otherwise the conditional inference `if p, q` if it predicts that one. A theory that predicts
neither predicts nothing about the cell. -/
noncomputable def predicted (T : Theory) (k : Construction) (o : Order) : Option Inference :=
  if T.Predicts (target (0 : Fin 3) 1 2 k o) fun I ↦ I 1 then some .unconditional
  else if T.Predicts (target (0 : Fin 3) 1 2 k o) fun I ↦ {w | w ∈ I 0 → w ∈ I 1} then
    some .conditional
  else none

theorem predicted_eq (a : Account) (k : Construction) (o : Order) :
    predicted a.theory k o =
      some (if a ∈ incremental ∧ o = .inverse then .unconditional else .conditional) := by
  have hcond : a.theory.Predicts (target (0 : Fin 3) 1 2 k o) fun I ↦ {w | w ∈ I 0 → w ∈ I 1} :=
    fun W I C hC w hw ↦ by
      have := (accepts_target_iff I a k o).1 hC hw
      split_ifs at this
      · exact fun _ ↦ this
      · exact this
  unfold predicted
  by_cases h : a ∈ incremental ∧ o = .inverse
  · have hu : a.theory.Predicts (target (0 : Fin 3) 1 2 k o) fun I ↦ I 1 :=
      fun W I C hC ↦ by simpa [h] using (accepts_target_iff I a k o).1 hC
    rw [ite_eq_left_of_eq_true _ _ (eq_true hu), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · have hu : ¬ a.theory.Predicts (target (0 : Fin 3) 1 2 k o) fun I ↦ I 1 := fun hall ↦ by
      have hacc : a.Accepts (fun _ : Fin 3 ↦ (∅ : Set Unit)) Set.univ (target 0 1 2 k o) :=
        (accepts_target_iff _ a k o).2 (by simp [h])
      exact (hall Unit _ _ hacc (Set.mem_univ ())).elim
    rw [ite_eq_right_of_eq_false _ _ (eq_false hu), ite_eq_left_of_eq_true _ _ (eq_true hcond),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The inference endorsed more in a cell, among rows recording the mean rating of an inference in
a cell, if the cell was tested and the two means differ. -/
def observedIn {R : Type} (rows : List R) (cell : R → Construction × Order)
    (inference : R → Inference) (mean : R → ℚ) (k : Construction) (o : Order) :
    Option Inference :=
  match rows.find? (fun r ↦ cell r = (k, o) ∧ inference r = .conditional),
      rows.find? (fun r ↦ cell r = (k, o) ∧ inference r = .unconditional) with
  | some c, some u =>
    if mean u < mean c then some .conditional
    else if mean c < mean u then some .unconditional else none
  | _, _ => none

/-- The inference endorsed more in a cell of Experiment 1 (Table 4). -/
def observed1 : Construction → Order → Option Inference :=
  observedIn experiment1Inferences (fun r ↦ (r.construction, r.order)) (·.inference)
    (·.mean.toRat)

/-- The inference endorsed more in a cell of Experiment 4 (Table 7). -/
def observed4 : Construction → Order → Option Inference :=
  observedIn experiment4Inferences (fun r ↦ (r.construction, r.order)) (·.inference)
    (·.mean.toRat)

/-- Experiment 1 of [chemla-schlenker-2012], whose inferences are rated in Table 4. -/
noncomputable def experiment1 : Experiment Theory (Construction × Order) Inference where
  observed c := observed1 c.1 c.2
  predicted T c := predicted T c.1 c.2

/-- Experiment 4 of [chemla-schlenker-2012], whose inferences are rated in Table 7. -/
noncomputable def experiment4 : Experiment Theory (Construction × Order) Inference where
  observed c := observed4 c.1 c.2
  predicted T c := predicted T c.1 c.2

/-- By Table 4, the conditional inference is endorsed more in every tested cell, and the
*unless*-sentence in the canonical order was not tested. -/
theorem observed_experiment1 (k : Construction) (o : Order) :
    experiment1.observed (k, o) =
      if k = .unlessSentence ∧ o = .canonical then none else some .conditional := by
  cases k <;> cases o <;> decide +kernel

/-- By Table 7, the conditional inference is endorsed more in every tested cell, and the
*unless*-sentence in the canonical order was not tested. -/
theorem observed_experiment4 (k : Construction) (o : Order) :
    experiment4.observed (k, o) =
      if k = .unlessSentence ∧ o = .canonical then none else some .conditional := by
  cases k <;> cases o <;> decide +kernel

/-- Where the conditional inference is endorsed more in every tested cell, every incremental
account is wrong on each inverse-order sentence and right on each canonical one, and every other
account is right on all. -/
private theorem verdict_of_observed {X : Experiment Theory (Construction × Order) Inference}
    (hp : ∀ T c, X.predicted T c = predicted T c.1 c.2)
    (ho : ∀ k o, X.observed (k, o) =
      if k = .unlessSentence ∧ o = .canonical then none else some .conditional)
    (a : Account) (k : Construction) (o : Order) :
    X.verdict a.theory (k, o) = if k = .unlessSentence ∧ o = .canonical then .silent
      else if a ∈ incremental ∧ o = .inverse then .wrong else .correct := by
  rw [Experiment.verdict, hp, ho, predicted_eq]
  by_cases hk : k = .unlessSentence ∧ o = .canonical
  · simp [hk, Eval.Verdict.of]
  · by_cases ha : a ∈ incremental ∧ o = .inverse <;> simp [hk, ha, Eval.Verdict.of]

/-- On Experiment 1, every incremental account is wrong on each inverse-order sentence and right
on each canonical one, and every other account is right on all. -/
theorem verdict_experiment1 (a : Account) (k : Construction) (o : Order) :
    experiment1.verdict a.theory (k, o) = if k = .unlessSentence ∧ o = .canonical then .silent
      else if a ∈ incremental ∧ o = .inverse then .wrong else .correct :=
  verdict_of_observed (fun _ _ ↦ rfl) observed_experiment1 a k o

/-- On Experiment 4, as on Experiment 1, every incremental account is wrong on each inverse-order
sentence and right on each canonical one, and every other account is right on all. -/
theorem verdict_experiment4 (a : Account) (k : Construction) (o : Order) :
    experiment4.verdict a.theory (k, o) = if k = .unlessSentence ∧ o = .canonical then .silent
      else if a ∈ incremental ∧ o = .inverse then .wrong else .correct :=
  verdict_of_observed (fun _ _ ↦ rfl) observed_experiment4 a k o

end Eval.Presupposition.ChemlaSchlenker2012
