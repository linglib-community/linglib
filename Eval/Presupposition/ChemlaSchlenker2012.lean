module

public import Eval.Presupposition.Map
public import Eval.Endorsement
public import Mathlib.Tactic.IntervalCases

/-!
# Scoring the accounts on Chemla & Schlenker (2012)

Chemla and Schlenker's inferential experiments rate, for *if*-, *or*- and *unless*-sentences with
*too*, how far the conditional and the unconditional inference follow. Each tested contrast between
the two is scored with both auxiliaries named (`Eval.Contrasts`). The parse of a target sentence is
a formula of the propositional fragment that every theory reads (`target`), and the theory says
which contexts accept it (`accepts_target_iff`). The response options are formulas too
(`lf`): the unconditional inference is `q`, and the conditional one is the conditional
presupposition strengthened by the causal link `r` from the antecedent of *too* to `q`, so that
neither entails the other (`not_entails`). A theory predicts an option when every context that
accepts the target entails it, once global accommodation adds `r` where *too* finds its antecedent,
that is where the antecedent can satisfy the presupposition (`reading`). Every incremental account
then predicts the unconditional inference alone in the inverse order, and every account the
conditional inference alone elsewhere (`predicted_reading`).

A decision rule reads each contrast's record: significance at .05 by the paper's ANOVA, or by its
non-parametric test (`anova`, `nonparametric`). A linking hypothesis turns the reading into the
predicted sign of the contrast; the verdicts below hold for every linking hypothesis that favors
the predicted option (`Endorsement.FavorsPredicted`). On Experiment 1 every incremental account is
wrong on each inverse-order sentence and right on each canonical one, and every other account is
right on all, under either test (`verdict_experiment1`). On Experiment 4 the ANOVA leaves the
inverse *if*- and *or*-sentences inconclusive (`verdict_experiment4`), while the non-parametric
test establishes the inverse *or*-sentence alone (`verdict_experiment4_nonparametric`). The design
separates the incremental accounts from every other in the inverse order under every such linking
hypothesis (`crucial_inverse`). It would not with the bare conditional presupposition as the
conditional option: `q` entails it, and a preference for the weaker inference makes the incremental
accounts right too (`not_crucial_material`).

## Implementation notes

* *Too* finds its antecedent exactly where the theory does not require `q` outright: anaphora
  resolution goes with presupposition satisfaction, as the paper argues for incremental theories.
* The symmetric accounts are the paper's Strict Symmetric Theory, which predicts the conditional
  inference at no cost. The paper argues for a Mixed Theory, on which symmetric satisfaction has a
  cost that the anaphoricity of *too* outweighs; neither is formalized, and neither are the
  acceptability experiments.

## References

* [chemla-schlenker-2012]
* [schlenker-2009]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Eval.Presupposition.ChemlaSchlenker2012

open _root_.Presupposition Account SyntacticEnvironment Kalomoiros2023 _root_.ChemlaSchlenker2012
  Data.Statistics Endorsement

/-! ### Acceptance of the target sentences -/

section Acceptance

variable {W : Type} (I : Fin 4 → Set W) {C : Set W}

private theorem transparency_symmetric_target (k : Construction) (o : Order) :
    Schlenker2009.Transparency .symmetric C (Formula.occurrences I (target 0 1 2 k o)) ↔
      C ⊆ {w | w ∈ I 0 → w ∈ I 1} := by
  have tf (K : SyntacticEnvironment (Fin 4)) :
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

end Acceptance

/-! ### The contrasts and their readings -/

/-- The contrasts the inferential experiments tested: each construction in each order, except the
canonical *unless*-sentence. -/
inductive Cell where
  | ifCanonical
  | ifInverse
  | orCanonical
  | orInverse
  | unlessInverse
  deriving DecidableEq, Repr, Fintype

namespace Cell

/-- The construction of a contrast's target sentence. -/
def construction : Cell → Construction
  | ifCanonical | ifInverse => .ifSentence
  | orCanonical | orInverse => .orSentence
  | unlessInverse => .unlessSentence

/-- The order of a contrast's target sentence. -/
def order : Cell → Order
  | ifCanonical | orCanonical => .canonical
  | ifInverse | orInverse | unlessInverse => .inverse

/-- The target sentence of a contrast, over the atoms `p`, `q`, `q'` and `r`. -/
def target (c : Cell) : Formula (Fin 4) :=
  _root_.ChemlaSchlenker2012.target 0 1 2 c.construction c.order

end Cell

/-- The cells are the contrasts that Tables 4 and 7 test. -/
theorem cell_tested :
    (∀ c : Cell, (∃ t ∈ experiment1Tests, t.construction = c.construction ∧ t.order = c.order) ∧
      ∃ t ∈ experiment4Tests, t.construction = c.construction ∧ t.order = c.order) ∧
    (∀ t ∈ experiment1Tests, ∃ c : Cell, t.construction = c.construction ∧ t.order = c.order) ∧
    ∀ t ∈ experiment4Tests, ∃ c : Cell, t.construction = c.construction ∧ t.order = c.order := by
  decide +kernel

/-- The logical form of each response option of (56), over the atoms `p` (Ann decides to study
abroad), `q` (Ann makes a stupid decision), `q'` (her brother makes a stupid decision) and `r`
(studying abroad would be stupid of Ann): the unconditional inference is `q`, and the conditional
inference is the conditional presupposition with the causal link from the antecedent of *too* to
`q`, `(if p, q) and r` (§2.1.2). -/
def lf : Inference → Formula (Fin 4)
  | .unconditional => .atom 1
  | .conditional => .bin .conj (.bin .cond (.atom 0) (.atom 1)) (.atom 3)

/-- The conditional presupposition itself as the conditional option, `if p, q`. -/
def lfMaterial : Inference → Formula (Fin 4)
  | .unconditional => .atom 1
  | .conditional => .bin .cond (.atom 0) (.atom 1)

/-- Whether *too* finds its antecedent `p` under a theory: where `p` can satisfy its presupposition,
so that the theory does not require `q` outright. -/
def HasAntecedent (T : Theory) (c : Cell) : Prop :=
  ¬ T.Predicts c.target fun I ↦ I 1

open Classical in
/-- What a theory says about a contrast whose options have the logical forms `φ`, when global
accommodation adds `extra T c` to the presupposition: it predicts an option when every context that
accepts the target, with that addition, entails the option. -/
noncomputable def readingOf (φ : Inference → Formula (Fin 4))
    (extra : Theory → Cell → ∀ W : Type, (Fin 4 → Set W) → Set W) (T : Theory) (c : Cell) :
    Endorsement Inference where
  predicted := {i | ∀ (W : Type) (I : Fin 4 → Set W) (C : Set W),
    T.accepts I C c.target → C ∩ extra T c W I ⊆ (φ i).truth I}
  entails i j := ∀ (W : Type) (I : Fin 4 → Set W), (φ i).truth I ⊆ (φ j).truth I

open Classical in
/-- What a theory says about a contrast: the options of (56), with the causal link `r` added where
*too* finds its antecedent (§2.1.2). -/
noncomputable def reading : Theory → Cell → Endorsement Inference :=
  readingOf lf fun T c _ I ↦ if HasAntecedent T c then I 3 else .univ

/-- What a theory says about a contrast if the conditional option were the bare conditional
presupposition, and accommodation added nothing. -/
noncomputable def readingMaterial : Theory → Cell → Endorsement Inference :=
  readingOf lfMaterial fun _ _ _ _ ↦ .univ

/-- An interpretation of the atoms at one world: true exactly the atoms of `s`. -/
private def interp (s : Finset (Fin 4)) : Fin 4 → Set Unit := fun k ↦ {_u | k ∈ s}

/-- Neither response option entails the other (§2.6). -/
theorem not_entails (T : Theory) (c : Cell) :
    ¬ (reading T c).entails .unconditional .conditional ∧
      ¬ (reading T c).entails .conditional .unconditional := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    change ∀ (W : Type) (I : Fin 4 → Set W), (lf _).truth I ⊆ (lf _).truth I at h
  · have := h Unit (interp {1})
      (show () ∈ (lf .unconditional).truth (interp {1}) by simp [lf, Formula.truth, interp])
    simp [lf, Formula.truth, Connective.eval, interp] at this
  · have := h Unit (interp {3}) (show () ∈ (lf .conditional).truth (interp {3}) by
      simp [lf, Formula.truth, Connective.eval, interp])
    simp [lf, Formula.truth, interp] at this

/-- An account requires `q` outright exactly where it is incremental and the trigger comes first. -/
theorem predicts_unconditional_iff (a : Account) (c : Cell) :
    a.theory.Predicts c.target (fun I ↦ I 1) ↔ a ∈ incremental ∧ c.order = .inverse := by
  refine ⟨fun h ↦ by_contra fun hn ↦ ?_, fun h W I C hC ↦ ?_⟩
  · exact absurd (h Unit (interp ∅) .univ ((accepts_target_iff _ a _ _).2 (by simp [hn, interp]))
      (Set.mem_univ ())) (by simp [interp])
  · simpa [h] using (accepts_target_iff I a _ _).1 hC

/-- An account predicts the unconditional inference alone where it is incremental and the trigger
comes first, and the conditional inference alone elsewhere. -/
theorem predicted_reading (a : Account) (c : Cell) :
    (reading a.theory c).predicted =
      {if a ∈ incremental ∧ c.order = .inverse then .unconditional else .conditional} := by
  have hant : HasAntecedent a.theory c ↔ ¬ (a ∈ incremental ∧ c.order = .inverse) :=
    not_congr (predicts_unconditional_iff a c)
  classical
  ext i
  change (∀ (W : Type) (I : Fin 4 → Set W) (C : Set W), a.theory.accepts I C c.target →
      C ∩ (if HasAntecedent a.theory c then I 3 else .univ) ⊆ (lf i).truth I) ↔ i ∈ ({_} : Set _)
  rw [Set.mem_singleton_iff]
  by_cases h : a ∈ incremental ∧ c.order = .inverse
  · have ha : ¬ HasAntecedent a.theory c := fun ha ↦ hant.1 ha h
    simp only [ha, ite_false, Set.inter_univ, h, and_self, ite_true]
    cases i
    · simp only [reduceCtorEq, iff_false, not_forall]
      refine ⟨Unit, interp {1}, .univ, (accepts_target_iff _ a _ _).2 (by simp [h, interp]),
        fun hs ↦ ?_⟩
      simpa [lf, Formula.truth, Connective.eval, interp] using hs (Set.mem_univ ())
    · simp only [iff_true]
      exact fun W I C hC ↦ by simpa [h, lf, Formula.truth] using (accepts_target_iff I a _ _).1 hC
  · have ha : HasAntecedent a.theory c := hant.2 h
    simp only [ha, ite_true, h, ite_false]
    cases i
    · simp only [iff_true]
      intro W I C hC w hw
      have := (accepts_target_iff I a c.construction c.order).1 hC hw.1
      rw [ite_eq_right h] at this
      show (w ∈ I 0 → w ∈ I 1) ∧ w ∈ I 3
      exact ⟨this, hw.2⟩
    · simp only [reduceCtorEq, iff_false, not_forall]
      refine ⟨Unit, interp {3}, .univ, (accepts_target_iff _ a _ _).2 (by simp [h, interp]),
        fun hs ↦ ?_⟩
      simpa [lf, Formula.truth, interp] using
        hs (show () ∈ Set.univ ∩ interp {3} 3 by simp [interp])

/-! ### Records and decision rules -/

/-- The tests the paper reports for a contrast. -/
inductive Method where
  /-- The one-way ANOVA of Tables 4 and 7. -/
  | anova
  /-- The non-parametric test of fn. 21 and §3.3.3. -/
  | nonparametric
  deriving DecidableEq, Repr

/-- What the paper records about a contrast: the mean rating of the conditional inference minus that
of the unconditional one, and the p-value of each test it reports. -/
structure Record where
  /-- The difference of the mean ratings. -/
  difference : ℚ
  /-- The p-value of the test by a method, if the paper reports one. -/
  p : Method → Option PValue

/-- The decision rule of significance at the .05 level by one of the paper's tests. -/
def rule (m : Method) (r : Record) : Set SignType := significance (1 / 20) (r.difference, r.p m)

/-- The mean rating of an inference in a contrast of Experiment 1 (Table 4). -/
def mean1 (c : Cell) (i : Inference) : ℚ :=
  ((experiment1Inferences.find? fun r ↦ r.construction = c.construction ∧ r.order = c.order ∧
    r.inference = i).map (·.mean.toRat)).getD 0

/-- The mean rating of an inference in a contrast of Experiment 4 (Table 7). -/
def mean4 (c : Cell) (i : Inference) : ℚ :=
  ((experiment4Inferences.find? fun r ↦ r.construction = c.construction ∧ r.order = c.order ∧
    r.inference = i).map (·.mean.toRat)).getD 0

/-- The record of a contrast of Experiment 1: Table 4 and fn. 21. -/
def record1 (c : Cell) : Record where
  difference := mean1 c .conditional - mean1 c .unconditional
  p
    | .anova => (experiment1Tests.find? fun t ↦
        t.construction = c.construction ∧ t.order = c.order).map (·.p)
    | .nonparametric => (experiment1BootstrapTests.find? fun t ↦
        t.construction = c.construction ∧ t.order = c.order).map (·.p)

/-- The record of a contrast of Experiment 4: Table 7 and §3.3.3. -/
def record4 (c : Cell) : Record where
  difference := mean4 c .conditional - mean4 c .unconditional
  p
    | .anova => (experiment4Tests.find? fun t ↦
        t.construction = c.construction ∧ t.order = c.order).map (·.p)
    | .nonparametric => (experiment4NonparametricTests.find? fun t ↦
        t.construction = c.construction ∧ t.order = c.order).map (·.p)

/-- Whether a record's test by a method is significant at the .05 level. -/
def Record.Significant (r : Record) (m : Method) : Prop :=
  ∃ p ∈ r.p m, p.Significant (1 / 20)

instance (r : Record) (m : Method) : Decidable (r.Significant m) :=
  inferInstanceAs (Decidable (∃ p ∈ r.p m, _))

private theorem rule_eq_pos {r : Record} {m : Method} (h : r.Significant m)
    (hd : 0 < r.difference) : rule m r = {.pos} := by
  obtain ⟨p, hp, hs⟩ := h
  rw [rule, Option.mem_def.1 hp, significance_of_significant hs, _root_.sign_pos hd,
    SignType.pos_eq_one]

private theorem rule_eq_univ {r : Record} {m : Method} (h : ¬ r.Significant m) :
    rule m r = .univ := by
  rw [rule]
  cases hp : r.p m with
  | none => rfl
  | some p => exact significance_of_not_significant fun hs ↦ h ⟨p, hp, hs⟩

private theorem neg_mem_range {m : Method} : {SignType.neg} ∈ Set.range (rule m) :=
  ⟨⟨-1, fun _ ↦ some ⟨.lt, ⟨1, 3⟩⟩⟩, by
    rw [rule, significance_of_significant (by decide +kernel), _root_.sign_neg (by norm_num),
      SignType.neg_eq_neg_one]⟩

/-! ### Experiments and verdicts -/

/-- Experiment 1 of [chemla-schlenker-2012]: the five contrasts of Table 4. -/
noncomputable def experiment1 : Contrasts Theory Cell (Endorsement Inference) Record where
  record := record1
  reading := reading

/-- Experiment 4 of [chemla-schlenker-2012]: the five contrasts of Table 7. -/
noncomputable def experiment4 : Contrasts Theory Cell (Endorsement Inference) Record where
  record := record4
  reading := reading

/-- Experiment 1 with the bare conditional presupposition as the conditional option. -/
noncomputable def experiment1Material : Contrasts Theory Cell (Endorsement Inference) Record where
  record := record1
  reading := readingMaterial

/-- The linking hypotheses that favor the predicted option, in the contrast of the conditional
against the unconditional inference. -/
def favoring : Set (Endorsement Inference → Set SignType) :=
  {ℓ | FavorsPredicted .conditional .unconditional ℓ}

/-- Under a linking hypothesis that favors the predicted option, an account predicts the advantage
of the unconditional inference where it is incremental and the trigger comes first, and of the
conditional one elsewhere. -/
theorem linking_reading {ℓ} (hℓ : ℓ ∈ favoring) (a : Account) (c : Cell) :
    ℓ (reading a.theory c) =
      if a ∈ incremental ∧ c.order = .inverse then {.neg} else {.pos} := by
  have hr := predicted_reading a c
  have hℓ' : FavorsPredicted .conditional .unconditional ℓ := hℓ
  by_cases h : a ∈ incremental ∧ c.order = .inverse
  · rw [ite_eq_left h] at hr ⊢
    exact (hℓ' _).2 (by simp [hr]) (by simp [hr])
  · rw [ite_eq_right h] at hr ⊢
    exact (hℓ' _).1 (by simp [hr]) (by simp [hr])

private theorem verdict_of_pos {X : Contrasts Theory Cell (Endorsement Inference) Record}
    (hX : X.reading = reading) {m : Method} {c : Cell} (hs : (X.record c).Significant m)
    (hd : 0 < (X.record c).difference) {ℓ} (hℓ : ℓ ∈ favoring) (a : Account) :
    X.verdict (rule m) ℓ a.theory c =
      if a ∈ incremental ∧ c.order = .inverse then .wrong else .correct := by
  rw [Contrasts.verdict, hX, linking_reading hℓ, rule_eq_pos hs hd]
  split_ifs
  · exact Verdict.ofRegions_eq_wrong_iff.2 (by simp)
  · exact Verdict.ofRegions_eq_correct (by simp) subset_rfl ⟨_, neg_mem_range, by simp⟩

private theorem verdict_of_not_significant
    {X : Contrasts Theory Cell (Endorsement Inference) Record} (hX : X.reading = reading)
    {m : Method} {c : Cell} (hs : ¬ (X.record c).Significant m) {ℓ} (hℓ : ℓ ∈ favoring)
    (a : Account) : X.verdict (rule m) ℓ a.theory c = .silent := by
  rw [Contrasts.verdict, hX, linking_reading hℓ, rule_eq_univ hs]
  split_ifs <;> exact Verdict.ofRegions_univ_right (by simp) (Set.singleton_ne_univ _)

/-- On Experiment 1, under every linking hypothesis that favors the predicted option and by either
test, every incremental account is wrong on each inverse-order sentence and right on each
canonical one, and every other account is right on all. -/
theorem verdict_experiment1 {ℓ} (hℓ : ℓ ∈ favoring) (m : Method) (a : Account) (c : Cell) :
    experiment1.verdict (rule m) ℓ a.theory c =
      if a ∈ incremental ∧ c.order = .inverse then .wrong else .correct :=
  verdict_of_pos rfl (by cases m <;> cases c <;> decide +kernel) (by cases c <;> decide +kernel)
    hℓ a

/-- On Experiment 4, by the ANOVA, every account is silent on the inverse *if*- and *or*-sentences,
whose differences do not reach significance (§3.3.3); elsewhere the verdicts are Experiment 1's. -/
theorem verdict_experiment4 {ℓ} (hℓ : ℓ ∈ favoring) (a : Account) (c : Cell) :
    experiment4.verdict (rule .anova) ℓ a.theory c =
      if c = .ifInverse ∨ c = .orInverse then .silent
      else if a ∈ incremental ∧ c.order = .inverse then .wrong else .correct := by
  by_cases hc : c = .ifInverse ∨ c = .orInverse
  · rw [ite_eq_left hc]
    exact verdict_of_not_significant rfl (by rcases hc with rfl | rfl <;> decide +kernel) hℓ a
  · rw [ite_eq_right hc]
    exact verdict_of_pos rfl (by cases c <;> simp at hc <;> decide +kernel)
      (by cases c <;> decide +kernel) hℓ a

/-- On Experiment 4, by the non-parametric test, which the paper reports for the inverse *if*- and
*or*-sentences alone (§3.3.3), every incremental account is wrong and every other account right on
the inverse *or*-sentence, and every account is silent elsewhere. -/
theorem verdict_experiment4_nonparametric {ℓ} (hℓ : ℓ ∈ favoring) (a : Account) (c : Cell) :
    experiment4.verdict (rule .nonparametric) ℓ a.theory c =
      if c = .orInverse then (if a ∈ incremental then .wrong else .correct) else .silent := by
  by_cases hc : c = .orInverse
  · subst hc
    rw [verdict_of_pos rfl (by decide +kernel) (by decide +kernel) hℓ a]
    simp [Cell.order]
  · rw [ite_eq_right hc]
    exact verdict_of_not_significant rfl (by cases c <;> simp at hc <;> decide +kernel) hℓ a

/-- The verdicts under the linking hypothesis of Table 1, by test: the instances the evaluation
page shows. -/
theorem verdict_strongest (a : Account) (c : Cell) :
    experiment1.verdict (rule .anova) (strongest .conditional .unconditional) a.theory c =
        (if a ∈ incremental ∧ c.order = .inverse then .wrong else .correct) ∧
      experiment1.verdict (rule .nonparametric) (strongest .conditional .unconditional) a.theory c =
        (if a ∈ incremental ∧ c.order = .inverse then .wrong else .correct) ∧
      experiment4.verdict (rule .anova) (strongest .conditional .unconditional) a.theory c =
        (if c = .ifInverse ∨ c = .orInverse then .silent
          else if a ∈ incremental ∧ c.order = .inverse then .wrong else .correct) ∧
      experiment4.verdict (rule .nonparametric) (strongest .conditional .unconditional) a.theory c =
        if c = .orInverse then (if a ∈ incremental then .wrong else .correct) else .silent :=
  have h := favorsPredicted_strongest Inference.conditional .unconditional
  ⟨verdict_experiment1 h _ a c, verdict_experiment1 h _ a c, verdict_experiment4 h a c,
    verdict_experiment4_nonparametric h a c⟩

/-- In the inverse order the design separates every incremental account from every other account
under every linking hypothesis that favors the predicted option. -/
theorem crucial_inverse {a b : Account} (ha : a ∈ incremental) (hb : b ∉ incremental) {c : Cell}
    (hc : c.order = .inverse) : experiment1.Crucial favoring a.theory b.theory c := fun ℓ hℓ ↦ by
  change Disjoint (ℓ (reading a.theory c)) (ℓ (reading b.theory c))
  rw [linking_reading hℓ, linking_reading hℓ, ite_eq_left ⟨ha, hc⟩, ite_eq_right fun h ↦ hb h.1]
  simp

/-- With the bare conditional presupposition as the conditional option, the design would not
separate the incremental accounts from the symmetric ones: `q` entails `if p, q`, and a preference
for the weaker inference predicts the conditional advantage from both (§3.1.3). -/
theorem not_crucial_material :
    ¬ experiment1Material.Crucial favoring dynamic.theory transparencySymmetric.theory
      .orInverse := by
  intro h
  have hcond (a : Account) :
      Inference.conditional ∈ (readingMaterial a.theory .orInverse).predicted :=
    fun W I C hC w hw ↦ by
      have := (accepts_target_iff I a .orSentence .inverse).1 hC hw.1
      split_ifs at this
      · exact fun _ ↦ this
      · exact this
  have hent (T : Theory) : (readingMaterial T .orInverse).entails .unconditional .conditional :=
    fun W I w hw _ ↦ hw
  have hunc : Inference.unconditional ∈ (readingMaterial dynamic.theory .orInverse).predicted :=
    fun W I C hC w hw ↦ by
      show w ∈ I 1
      simpa [incremental] using (accepts_target_iff I dynamic .orSentence .inverse).1 hC hw.1
  have hw := h _ (favorsPredicted_weaker Inference.conditional .unconditional)
  change Disjoint (weaker .conditional .unconditional (readingMaterial dynamic.theory .orInverse))
    (weaker .conditional .unconditional (readingMaterial transparencySymmetric.theory .orInverse))
    at hw
  rw [weaker, weaker, ite_eq_left ⟨hcond _, fun _ ↦ hent _⟩, ite_eq_left ⟨hcond _, fun _ ↦ hent _⟩]
    at hw
  simp at hw

end Eval.Presupposition.ChemlaSchlenker2012
