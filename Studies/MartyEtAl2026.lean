module

public import Linglib.Data.Statistics.MartyEtAl2026
public import Linglib.Semantics.Presupposition.QuantifiedClause
public import Linglib.Logic.Trivalent.UniversalInference
public import Mathlib.Tactic.NormNum.Ineq
public import Studies.George2008

/-!
# Marty, Elliott, Kalomoiros and Romoli (2026): quantifying presupposition projection

Marty, Elliott, Kalomoiros and Romoli test how the existence presupposition of *the present in
front of him* and the gender presupposition of *her* project from the scope of *each*, *none* and
*exactly one*, against pictures of four children (`Data/Statistics/MartyEtAl2026`). Each of their
interpretive options is a trivalent quantifier, from a quantifier and a three-valued scope to a
three-valued sentence; the options [reproduce Table 2](##MartyEtAl2026.Reading.accepts_iff) but
for one cell, and Strong Kleene [agrees with universal
projection](##MartyEtAl2026.deployQuantifier_eq_true_iff_universalProjection) on these quantifiers.
Only intermediate projection [separates the target pictures of the negated *exactly one* as
observed](##MartyEtAl2026.accepts_nmNeg_iff), and the model that adds it to universal projection
and local accommodation [fits best](##MartyEtAl2026.modelFits_best).

## Implementation notes

* A sentence is accepted at a picture under an option where its value is true, presupposition and
  assertion conjoined as in §2. Local accommodation is ambiguous between the scope and the
  trigger, so its value is the join of the two.
* Intermediate projection is George's 2008 deployment with concern for disappointment, the theory
  note 5 credits with it alone.

## References

* [marty-etal-2026]
* [heim-1983]
* [schlenker-2009]
* [beaver-2001]
* [beaver-krahmer-2001]
* [george-2008]
* [george-2014]
* [fox-2013]
-/

@[expose] public section

namespace MartyEtAl2026

open Quantifier Presupposition
open Trivalent (Designation deployQuantifier ofProp posExt gapExt posExt_subset repairs_eq_Icc
  UniversalEntailment UniversalPresupposition)

/-! ### The interpretive options of §2 -/

section Readings

variable {E : Type*} (Q : Set E → Prop) (A : E → Trivalent)

open Classical in
/-- Universal projection, as Heim's and Schlenker's accounts predict: the quantifier holds of the
individuals of which the scope is true, and the sentence is defined only where the scope is
defined of every individual. -/
noncomputable def universalProjection : Trivalent :=
  if ∀ e, A e ≠ .undefined then ofProp (Q (posExt A)) else .undefined

open Classical in
/-- Local accommodation at a site of standard `d`: the quantifier holds of the individuals of which
the scope is designated at `d`. At the scope, (11) and (12), the standard is K3, Beaver and
Krahmer's assertion operator; at a trigger under negation (13) it is LP, since negation exchanges
the standards (`Trivalent.Designation.dual_threshold_le_compl_iff`). -/
noncomputable def localAccommodation (d : Designation) : Trivalent :=
  ofProp (Q {e | d.threshold ≤ A e})

open Classical in
/-- Existential projection, (5b), (6b) and (7b): the quantifier holds of the scope with its trigger
accommodated where it is, at the trigger's standard `d`, and the sentence is defined only where the
scope is defined of some individual. -/
noncomputable def existentialProjection (d : Designation) : Trivalent :=
  if ∃ e, A e ≠ .undefined then localAccommodation Q A d else .undefined

open Classical in
/-- (14): local accommodation at the scope strengthened by the negation of its alternative whose
scope is the presupposition, *no boy [𝒜 has a present in front of him]*, so that the quantifier
also fails of the individuals of which the scope is defined. -/
noncomputable def enrichedAccommodation : Trivalent :=
  localAccommodation Q A .k3 ⊓ (ofProp (Q (gapExt A)ᶜ))ᶜ

/-- The value of a sentence under an interpretive option, `d` the standard at which accommodating
the trigger where it is reads the scope. -/
noncomputable def Reading.value (d : Designation) : Reading → Trivalent
  | .univ => universalProjection Q A
  | .exist => existentialProjection Q A d
  | .intermediate => George2008.deployWithConcern Q A
  | .locA => localAccommodation Q A .k3 ⊔ localAccommodation Q A d

theorem universalProjection_eq_true_iff :
    universalProjection Q A = .true ↔ (∀ e, A e ≠ .undefined) ∧ Q (posExt A) := by
  unfold universalProjection; split_ifs with h <;> simp [h]

theorem localAccommodation_eq_true_iff {d : Designation} :
    localAccommodation Q A d = .true ↔ Q {e | d.threshold ≤ A e} := by
  simp [localAccommodation]

theorem existentialProjection_eq_true_iff {d : Designation} :
    existentialProjection Q A d = .true ↔
      (∃ e, A e ≠ .undefined) ∧ Q {e | d.threshold ≤ A e} := by
  unfold existentialProjection; split_ifs with h <;> simp [h, localAccommodation_eq_true_iff]

theorem enrichedAccommodation_eq_true_iff :
    enrichedAccommodation Q A = .true ↔
      Q {e | Designation.k3.threshold ≤ A e} ∧ ¬ Q (gapExt A)ᶜ := by
  simp [enrichedAccommodation, localAccommodation_eq_true_iff]

theorem universalPresupposition_universalProjection :
    UniversalPresupposition Set.univ (universalProjection Q) := by
  refine ⟨fun A h e _ he ↦ ?_, fun A h e _ he ↦ ?_⟩ <;>
    simp [universalProjection, show ¬ ∀ e, A e ≠ .undefined from fun h' ↦ h' e he] at h

variable {Q A}

theorem deployQuantifier_eq_true_iff (hQ : UniversalEntailment Set.univ (deployQuantifier Q)) :
    deployQuantifier Q A = .true ↔ universalProjection Q A = .true := by
  have hrep : posExt A ∈ Trivalent.repairs A := repairs_eq_Icc A ▸ ⟨le_rfl, posExt_subset A⟩
  constructor
  · intro h
    have hdef : ∀ e, A e ≠ .undefined := fun e ↦ hQ A h e trivial
    rw [Trivalent.deployQuantifier_eq_supervaluationOn,
      Trivalent.supervaluationOn_eq_true_iff] at h
    simp [universalProjection, hdef, h _ hrep]
  · intro h
    simp only [universalProjection] at h
    split_ifs at h with hdef
    rw [Trivalent.deployQuantifier_eq_supervaluationOn, Trivalent.supervaluationOn_eq_true_iff]
    intro X hX
    rw [repairs_eq_Icc] at hX
    have hX' : X = posExt A := by
      refine le_antisymm (fun u hu ↦ ?_) hX.1
      have := hX.2 hu
      simp only [Set.mem_compl_iff, Trivalent.mem_negExt] at this
      rcases Trivalent.trichotomy (A u) with h' | h' | h'
      · exact absurd h' this
      · exact absurd h' (hdef u)
      · exact h'
    rw [hX']
    simpa using h

end Readings

/-! ### The target sentences -/

/-- The atoms of the target sentences: the restrictor noun, the presupposition of *the present in
front of him* or *her*, and that a child opened the present. -/
inductive Atom where
  | child
  | presupposition
  | opened
  deriving DecidableEq

/-- The quantifier of a target sentence, on the tree of numbers. -/
def Sentence.tree : Sentence → NumberTree
  | .mPos => NumberTree.all
  | .mNeg => NumberTree.no
  | .nmPos | .nmNeg => NumberTree.cardinal {1}

/-- The quantifier of a target sentence over the four children. -/
def Sentence.quantifier (s : Sentence) : Set (Fin children) → Prop := s.tree.toDet Set.univ

theorem Sentence.quantifier_apply (s : Sentence) (X : Set (Fin children)) :
    s.quantifier X ↔ s.tree.toDet Set.univ X :=
  .rfl

/-- The nuclear scope of a target sentence (2), *opened the present in front of him*, a trigger of
the presupposition, negated in nm-neg. -/
def Sentence.scope : Sentence → Formula Atom
  | .nmNeg => .not (.trigger .presupposition .opened)
  | _ => .trigger .presupposition .opened

/-- A target sentence (3) as the quantified clause `(Q child. S)`. -/
def Sentence.clause (s : Sentence) : QuantifiedClause Atom :=
  ⟨s.tree, .atom .child, s.scope⟩

/-- The standard at which accommodating its trigger where it is reads a scope: K3, exchanged for LP
by the negation of nm-neg. -/
def Sentence.triggerStandard : Sentence → Designation
  | .nmNeg => .lp
  | _ => .k3

/-- The atoms at a picture of the four children: every child is in the restrictor, `π` says the
presupposition holds of a child and `o` that the child opened a present. -/
def interp {σ : Type*} (π o : σ → Prop) : Atom → Set ((Fin children → σ) × Fin children)
  | .child => Set.univ
  | .presupposition => {p | π (p.1 p.2)}
  | .opened => {p | o (p.1 p.2)}

/-- The Strong Kleene value of a target sentence's scope at each child of a picture. -/
noncomputable def Sentence.scopeAt {σ : Type*} (s : Sentence) (π o : σ → Prop)
    (w : Fin children → σ) (e : Fin children) : Trivalent :=
  s.scope.strongKleene (interp π o) (w, e)

theorem Sentence.scopeAt_apply {σ : Type*} (s : Sentence) (π o : σ → Prop) [DecidablePred π]
    [DecidablePred o] (w : Fin children → σ) (e : Fin children) :
    s.scopeAt π o w e = match s with
      | .nmNeg => (Trivalent.transplication (ofProp (π (w e))) (ofProp (o (w e))))ᶜ
      | _ => Trivalent.transplication (ofProp (π (w e))) (ofProp (o (w e))) := by
  cases s <;> by_cases hπ : π (w e) <;> by_cases ho : o (w e) <;>
    simp [Sentence.scopeAt, Sentence.scope, Formula.strongKleene, Formula.eval, interp,
      Trivalent.ofProp, hπ, ho]

theorem mem_truth_clause_iff {σ : Type*} (s : Sentence) (π o : σ → Prop) [DecidablePred π]
    [DecidablePred o] (w : Fin children → σ) :
    w ∈ s.clause.truth (interp π o) ↔
      localAccommodation s.quantifier (s.scopeAt π o w) s.triggerStandard = .true := by
  rw [localAccommodation_eq_true_iff]
  simp only [QuantifiedClause.truth, Sentence.clause, scopeTruth, Sentence.quantifier,
    Set.mem_ofPred_eq]
  refine Iff.of_eq (congrArg₂ s.tree.toDet ?_ ?_)
  · rfl
  · ext e
    cases s <;> simp [Formula.truth, interp, Sentence.scope, Sentence.triggerStandard,
      Sentence.scopeAt_apply] <;> exact Iff.rfl

/-- Intermediate projection, (6) and (7c), is George's deployment with concern for
disappointment: *each* and *exactly one* are true where their scope is true of the children they
count, and *none* where its scope is defined of every child and true of none. -/
theorem deployWithConcern_quantifier_eq_true_iff (s : Sentence) (A : Fin children → Trivalent) :
    George2008.deployWithConcern s.quantifier A = .true ↔
      (s = .mNeg → ∀ e, A e ≠ .undefined) ∧ s.quantifier (posExt A) := by
  cases s
  · simp [Sentence.quantifier, Sentence.tree, George2008.deployWithConcern_all_eq_true_iff,
      NumberTree.toDet_all_iff, Set.subset_def]
  · simp only [Sentence.quantifier, Sentence.tree, George2008.deployWithConcern_no_eq_true_iff,
      NumberTree.toDet_no_iff, Set.mem_univ, forall_const, Set.univ_inter, Set.Nonempty,
      Trivalent.mem_posExt, not_exists]
    exact ⟨fun h ↦ ⟨fun e ↦ by simp [h e], fun e ↦ by simp [h e]⟩,
      fun ⟨h₁, h₂⟩ e ↦ by rcases Trivalent.trichotomy (A e) with h | h | h <;> simp_all⟩
  all_goals
    simp only [Sentence.quantifier, Sentence.tree,
      George2008.deployWithConcern_cardinal_eq_true_iff le_rfl, George2008.toDet_cardinal_iff,
      reduceCtorEq, false_implies, true_and]
    have : {x | x ∈ Set.univ ∧ A x = .true} = Set.univ ∩ posExt A := Set.ext fun _ ↦ by simp
    rw [this]

theorem universalEntailment_quantifier (s : Sentence) :
    UniversalEntailment Set.univ (deployQuantifier s.quantifier) := by
  rw [Trivalent.universalEntailment_deployQuantifier_iff]
  rintro B a - ha ⟨h₁, h₂⟩
  cases s <;> simp only [Sentence.quantifier, Sentence.tree, NumberTree.toDet_apply,
    NumberTree.all, NumberTree.no, NumberTree.cardinal_apply, Set.mem_singleton_iff,
    Set.univ_inter] at h₁ h₂
  · rw [Set.ncard_eq_zero, Set.sdiff_eq_empty] at h₁
    exact ha (h₁ trivial)
  · rw [Set.ncard_eq_zero] at h₂
    exact (Set.insert_nonempty a B).ne_empty h₂
  all_goals rw [Set.ncard_insert_of_notMem ha] at h₂; omega

-- Note 2: Strong Kleene, George's deployment, groups with universal projection here.
theorem deployQuantifier_eq_true_iff_universalProjection (s : Sentence)
    (A : Fin children → Trivalent) :
    deployQuantifier s.quantifier A = .true ↔ universalProjection s.quantifier A = .true :=
  deployQuantifier_eq_true_iff (universalEntailment_quantifier s)

/-! ### The pictures -/

/-- A picture: what it shows of each of its children. -/
def picture {σ : Type*} (l : List σ) (h : l.length = children) : Fin children → σ :=
  fun i ↦ l[i]

theorem length_existencePictures (s : Sentence) (p : Picture) :
    (existencePictures s p).children.length = children := by
  cases s <;> cases p <;> rfl

theorem length_genderPictures (s : Sentence) (p : Picture) :
    (genderPictures s p).children.length = children := by
  cases s <;> cases p <;> rfl

/-- In Experiment 1 the presupposition holds of a child with a present. -/
def Gift.HasPresent (g : Gift) : Prop := g ≠ .noPresent

/-- A child of Experiment 1 opened a present. -/
def Gift.Opened (g : Gift) : Prop := g = .openPresent

/-- In Experiment 2 the presupposition holds of a girl. -/
def Recipient.Girl (r : Recipient) : Prop := r = .girlOpen ∨ r = .girlClosed

/-- A child of Experiment 2 opened a present. -/
def Recipient.Opened (r : Recipient) : Prop := r = .girlOpen ∨ r = .boyOpen

instance : DecidablePred Gift.HasPresent := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))
instance : DecidablePred Gift.Opened := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Recipient.Girl := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))
instance : DecidablePred Recipient.Opened := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The value of a target sentence's scope at each child of its picture in an experiment. -/
noncomputable def scopeValue : Experiment → Sentence → Picture → Fin children → Trivalent
  | .existence, s, p => s.scopeAt Gift.HasPresent Gift.Opened
      (picture _ (length_existencePictures s p))
  | .gender, s, p => s.scopeAt Recipient.Girl Recipient.Opened
      (picture _ (length_genderPictures s p))

/-- An interpretive option accepts a target sentence with a picture type of an experiment. -/
def Reading.Accepts (r : Reading) (e : Experiment) (s : Sentence) (p : Picture) : Prop :=
  r.value s.quantifier (scopeValue e s p) s.triggerStandard = .true

/-! ### Table 2 -/

/-- The interpretive options accept a target sentence with a picture as Table 2 predicts, but for
existential projection with nm-neg and the Target-2 picture, which Table 2 prints as accepting in
both experiments. -/
theorem Reading.accepts_iff (r : Reading) (e : Experiment) (s : Sentence) (p : Picture) :
    r.Accepts e s p ↔
      r ∈ (predictions e s p).accepting ∧ ¬ (s = .nmNeg ∧ p = .target2 ∧ r = .exist) := by
  cases e <;> cases s <;> cases p <;> cases r <;>
  simp [Reading.Accepts, Reading.value, universalProjection_eq_true_iff,
    existentialProjection_eq_true_iff, localAccommodation_eq_true_iff,
    deployWithConcern_quantifier_eq_true_iff, scopeValue, Sentence.scopeAt_apply,
    Sentence.triggerStandard, Trivalent.posExt, Sentence.quantifier_apply, Sentence.tree] <;>
  decide

instance (r : Reading) (e : Experiment) (s : Sentence) (p : Picture) :
    Decidable (r.Accepts e s p) :=
  decidable_of_iff _ (r.accepts_iff e s p).symm

-- (7b), Table 2
theorem exist_accepts_nmNeg (e : Experiment) :
    Reading.exist.Accepts e .nmNeg .target1 ∧ ¬ Reading.exist.Accepts e .nmNeg .target2 ∧
      .exist ∈ (predictions e .nmNeg .target2).accepting := by
  cases e <;> decide

-- Table 2
theorem mem_predictions_exist_iff (e : Experiment) (s : Sentence) (p : Picture) :
    .exist ∈ (predictions e s p).accepting ↔
      (∃ i, scopeValue e s p i ≠ .undefined) ∧ Reading.locA.Accepts e s p := by
  cases e <;> cases s <;> cases p <;>
  simp [Reading.Accepts, Reading.value, localAccommodation_eq_true_iff, scopeValue,
    Sentence.scopeAt_apply, Sentence.triggerStandard, Sentence.quantifier_apply, Sentence.tree] <;>
  decide

/-! ### The design and the results -/

/-- The proportion of 'Good' responses. -/
def Responses.rate (r : Responses) : ℚ := r.good / r.trials

theorem univ_accepts_iff (e : Experiment) (s : Sentence) (p : Picture) :
    Reading.univ.Accepts e s p ↔ p = .true := by
  cases e <;> cases s <;> cases p <;> decide

/-- Intermediate projection alone accepts nm-neg with the Target-2 picture and rejects it with the
Target-1 picture, and in both experiments the Target-2 picture is accepted more often. -/
theorem accepts_nmNeg_iff (e : Experiment) (r : Reading) :
    (r.Accepts e .nmNeg .target2 ∧ ¬ r.Accepts e .nmNeg .target1 ↔ r = .intermediate) ∧
      (responses e .nmNeg .target1).rate < (responses e .nmNeg .target2).rate := by
  refine ⟨by cases e <;> cases r <;> decide, ?_⟩
  cases e <;> simp only [Responses.rate, responses] <;> norm_num

/-- Local accommodation alone accepts m-neg with the Target-1 picture, where no child has a present
in Experiment 1 and every child is a boy in Experiment 2; in both experiments that picture is
accepted more often than the False picture and than m-pos with its Target-1 picture. -/
theorem accepts_mNeg_target1_iff (e : Experiment) (r : Reading) :
    (r.Accepts e .mNeg .target1 ↔ r = .locA) ∧
      (responses e .mNeg .false).rate < (responses e .mNeg .target1).rate ∧
      (responses e .mPos .target1).rate < (responses e .mNeg .target1).rate := by
  refine ⟨by cases e <;> cases r <;> decide, ?_⟩
  cases e <;> simp only [Responses.rate, responses] <;> norm_num

theorem accepts_nmPos_target1_iff (e : Experiment) (r : Reading) :
    r.Accepts e .nmPos .target1 ↔ r.Accepts e .nmPos .target2 := by
  cases e <;> cases r <;> decide

/-- The model with universal and intermediate projection and local accommodation has the least AIC
and BIC and the greatest conditional R² of Table 3 in both experiments. -/
theorem modelFits_best (e : Experiment) (m : Model) :
    (modelFits e .univIntermediateLocA).aic ≤ (modelFits e m).aic ∧
      (modelFits e .univIntermediateLocA).bic ≤ (modelFits e m).bic ∧
      (modelFits e m).r2.toRat ≤ (modelFits e .univIntermediateLocA).r2.toRat := by
  cases e <;> cases m <;> norm_num [modelFits, Data.Statistics.Decimal.toRat]

-- §3.6
theorem reportedRates_mismatch :
    reportedRates.filter (fun r ↦ ¬ r.percent.RoundsPercent
        (responses r.experiment r.sentence r.picture).good
        (responses r.experiment r.sentence r.picture).trials) =
      [(⟨.gender, .mNeg, .target1, ⟨20, 0⟩⟩ : ReportedRate),
        ⟨.existence, .mPos, .target1, ⟨13, 0⟩⟩, ⟨.gender, .nmNeg, .target2, ⟨73, 0⟩⟩] := by
  decide

-- (14)
theorem enrichedAccommodation_mNeg :
    enrichedAccommodation Sentence.mNeg.quantifier (scopeValue .existence .mNeg .target2) = .true ∧
      enrichedAccommodation Sentence.mNeg.quantifier (scopeValue .existence .mNeg .target1) ≠
        .true ∧
      Reading.locA.Accepts .existence .mNeg .target1 ∧
      Reading.locA.Accepts .existence .mNeg .target2 := by
  refine ⟨?_, ?_, by decide, by decide⟩ <;>
  simp [enrichedAccommodation_eq_true_iff, scopeValue, Sentence.scopeAt_apply, Trivalent.gapExt,
    Sentence.quantifier_apply, Sentence.tree] <;>
  decide

end MartyEtAl2026
