module

public import Linglib.Pragmatics.RSA.Uniform

/-!
# Champollion, Alsop and Grosu (2019): Free Choice Disjunction as a Rational Speech Act

Free choice, by which *You may take an apple or a pear* conveys that each fruit may be taken by
itself, does not follow from modal logic, and a speaker who prefers informative utterances
never has reason to choose the disjunction over a disjunct. The paper adds semantic
uncertainty: two interpretation functions, the classical (6) and the exhaustified (7), over
which the pragmatic listener reasons jointly with states and utterances (8). Under the
exhaustified function a bare disjunct risks the reading *only that fruit*, so at the
free-choice states Only One and Any Number the disjunction is the speaker's safe choice
(`speaker_or_onlyOne_exh`, `speaker_prefers_a_at_onlyA_exh`), and the listener inverts the
avoidance: hearing *or*, each free-choice state outweighs each other state at the paper's
α = 100 (`fci_derived`, Table 5), and the free-choice states already carry the majority at
α = 2 (`fci_majority_low_alpha`).

Exclusivity, that not both may be taken, tracks the prior instead. Under a prior favouring Any
Number the listener hearing *or* ranks Any Number above every other state, at every rationality
(`anyNumber_of_prior`, Table 6), which is the paper's account of why exclusivity, unlike free
choice, is cancelable. Under negation the negated disjunction is unambiguous and maximally
strong, so the listener assigns no mass to the states at which free choice would survive
(`no_fci_under_negation`, Table 9). The variants without the conjunctive alternative
(Tables 7–8) are not formalized.

## Main results

* `speaker_or_onlyOne_exh`, `speaker_prefers_a_at_onlyA_exh`: under exhaustification the
  disjunction is the safe choice at the free-choice states and a disjunct is not.
* `fci_derived`, `fci_majority_low_alpha`: hearing *or*, the listener favours the free-choice
  states, at the paper's α and at a low one.
* `anyNumber_of_prior`: exclusivity tracks the prior at every rationality.
* `no_fci_under_negation`: the negated disjunction leaves no mass where free choice would arise.

## References

* [champollion-alsop-grosu-2019]
* [franke-2011]
* [fox-2007]
* [bergen-levy-goodman-2016]
* [frank-goodman-2012]
* [kratzer-shimoyama-2002]
* [simons-2005]
-/

@[expose] public section

namespace ChampollionAlsopGrosu2019

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### States, utterances, interpretation functions (Table 2, (5)–(7)) -/

/-- The permission states of Table 2 split Franke's All True into Any Number and Only Both. -/
inductive FCState where
  | onlyA | onlyB | onlyOne | anyNumber | onlyBoth
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace FCState := ⊤
instance : DiscreteMeasurableSpace FCState := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass FCState := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The four utterances (5). -/
inductive Utterance where
  | a | b | or_ | and_
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Utterance := ⊤
instance : DiscreteMeasurableSpace Utterance := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Utterance := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- An interpretation function is classical modal logic or its exhaustification. -/
inductive Interp where
  | literal | exhaustified
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace Interp := ⊤
instance : DiscreteMeasurableSpace Interp := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Interp := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Free choice holds when each fruit may be taken by itself. -/
def HasFCI : FCState → Prop
  | .onlyOne | .anyNumber => True
  | _ => False

instance : DecidablePred HasFCI
  | .onlyA | .onlyB | .onlyBoth => .isFalse id
  | .onlyOne | .anyNumber => .isTrue trivial

/-- Interpretation function 1 (6) is classical modal logic. -/
def I1 : Utterance → FCState → Prop
  | .a, .onlyB => False
  | .a, _ => True
  | .b, .onlyA => False
  | .b, _ => True
  | .or_, _ => True
  | .and_, .anyNumber | .and_, .onlyBoth => True
  | .and_, _ => False

instance : ∀ u, DecidablePred (I1 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- Interpretation function 2 (7) gives the exhaustified meanings. -/
def I2 : Utterance → FCState → Prop
  | .a, .onlyA => True
  | .a, _ => False
  | .b, .onlyB => True
  | .b, _ => False
  | .or_, .onlyBoth => False
  | .or_, _ => True
  | .and_, .onlyBoth => True
  | .and_, _ => False

instance : ∀ u, DecidablePred (I2 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- Meaning indexed by interpretation function. -/
def interpMeaning : Interp → Utterance → FCState → Prop
  | .literal => I1
  | .exhaustified => I2

instance : ∀ i u, DecidablePred (interpMeaning i u)
  | .literal, u => inferInstanceAs (DecidablePred (I1 u))
  | .exhaustified, u => inferInstanceAs (DecidablePred (I2 u))

/-- The extension of each utterance under each interpretation function. -/
def sem (i : Interp) (u : Utterance) : Finset FCState := Finset.univ.filter (interpMeaning i u)

@[simp] theorem mem_sem {i : Interp} {u : Utterance} {w : FCState} :
    w ∈ sem i u ↔ interpMeaning i u w := by simp [sem]

theorem I2_refines_I1 : ∀ u w, I2 u w → I1 u w := by decide

theorem I1_or_everywhere : ∀ w, I1 .or_ w := by decide

theorem I2_or_excludes_onlyBoth : ∀ w, I2 .or_ w ↔ w ≠ .onlyBoth := by decide

theorem I2_a_singleton : ∀ w, I2 .a w ↔ w = .onlyA := by decide

/-! ### The model (8) -/

/-- The literal listener under an interpretation function (8a) conditions the state prior on the
meaning of the utterance. -/
noncomputable abbrev literal (μ : Measure FCState) (i : Interp) : Kernel Utterance FCState :=
  RSA.listener μ (truthful fun u ↦ (sem i u : Set FCState))

/-- The speaker under an interpretation function (8b) knows the state and addresses that
function's literal listener. -/
noncomputable abbrev speaker (μ : Measure FCState) (i : Interp) (α : ℝ) :
    Kernel FCState Utterance :=
  RSA.speaker α 0 (literal μ i) Measure.dirac

/-- The uniform prior over the states. -/
local notation "υ" => uniformOn (Set.univ : Set FCState)

/-- The pragmatic listener (8c) at a uniform prior over states and interpretation functions
inverts the speaker of each function, and her first marginal is her belief about the state. -/
noncomputable abbrev listener (α : ℝ) : Kernel Utterance (FCState × Interp) :=
  RSA.listener (uniformOn Set.univ) fun p : FCState × Interp ↦ speaker υ p.2 α p.1

/-- Under the exhaustified function at Only One, *or* is the only true utterance, so the
speaker produces it with certainty at every rationality (§3.3). -/
theorem speaker_or_onlyOne_exh {α : ℝ} (hα : 0 < α) :
    speaker υ .exhaustified α .onlyOne {.or_} = 1 :=
  speaker_listener_truthful_dirac_eq_one hα _ _ _ (uniformOn_univ_singleton_ne_zero _) (by decide)
    (by decide)

theorem speaker_or_anyNumber_exh {α : ℝ} (hα : 0 < α) :
    speaker υ .exhaustified α .anyNumber {.or_} = 1 :=
  speaker_listener_truthful_dirac_eq_one hα _ _ _ (uniformOn_univ_singleton_ne_zero _) (by decide)
    (by decide)

theorem speaker_or_onlyBoth_exh {α : ℝ} (hα : 0 < α) :
    speaker υ .exhaustified α .onlyBoth {.or_} = 0 :=
  speaker_listener_truthful_dirac_apply_singleton_eq_zero hα _ _ _ (by decide)

/-- Under the exhaustified function at Only A the speaker prefers the bare disjunct to the
disjunction at every rationality, the avoidance mechanism. -/
theorem speaker_prefers_a_at_onlyA_exh {α : ℝ} (hα : 0 < α) :
    (speaker υ .exhaustified α .onlyA).real {.or_} <
      (speaker υ .exhaustified α .onlyA).real {.a} :=
  speaker_uniformOn_dirac_real_singleton_lt_of_card_lt _ hα (by decide) (by decide) (by decide)

/-- Hearing *or* at α = 100, the listener ranks each free-choice state above each of Only A, Only B
and Only Both (Table 5). -/
theorem fci_derived :
    ∀ w ∈ ({.onlyA, .onlyB, .onlyBoth} : Finset FCState),
      ∀ w' ∈ ({.onlyOne, .anyNumber} : Finset FCState),
        (listener 100 .or_).fst.real {w} < (listener 100 .or_).fst.real {w'} := by
  intro w hw w' hw'
  rw [Measure.fst_real_singleton, Measure.fst_real_singleton]
  fin_cases hw <;> fin_cases hw' <;>
    exact listener_uniformOn_family_real_lt_of_divPowSum sem (k := 100) (D := 20)
      (by decide +kernel) (by decide +kernel)

/-- The free-choice pairs of the joint listener. -/
def fciPairs : Finset (FCState × Interp) := Finset.univ.filter fun p => HasFCI p.1

/-- The remaining pairs. -/
def nonFciPairs : Finset (FCState × Interp) := Finset.univ.filter fun p => ¬ HasFCI p.1

/-- At α = 2 the free-choice states still carry the majority of the posterior given *or*
(the paper's "only 70%"). -/
theorem fci_majority_low_alpha :
    (listener 2 .or_).real ↑nonFciPairs < (listener 2 .or_).real ↑fciPairs :=
  listener_uniformOn_family_real_lt_of_divPowSum sem (k := 2) (D := 20) (by decide +kernel)
    (by decide +kernel)

/-! ### Prior sensitivity (Table 6)

The prior enters the literal listener (8a) and the pragmatic listener (8c) alike. -/

/-- These prior weights favour Any Number, 12 against 1 for each other state (75%). -/
def biasedWeight : FCState → ℕ
  | .anyNumber => 12
  | _ => 1

/-- The state prior. -/
noncomputable def priorB : Measure FCState := ∑ w, (biasedWeight w : ℝ≥0∞) • Measure.dirac w

/-- The joint prior, the interpretation function drawn uniformly. -/
noncomputable def jointPriorB : Measure (FCState × Interp) :=
  ∑ p, (biasedWeight p.1 : ℝ≥0∞) • Measure.dirac p

theorem priorB_singleton (w : FCState) : priorB {w} = biasedWeight w :=
  Measure.sum_smul_dirac_apply_singleton (fun w => (biasedWeight w : ℝ≥0∞)) w

theorem jointPriorB_singleton (p : FCState × Interp) : jointPriorB {p} = biasedWeight p.1 :=
  Measure.sum_smul_dirac_apply_singleton (fun p : FCState × Interp => (biasedWeight p.1 : ℝ≥0∞)) p

instance : IsFiniteMeasure priorB :=
  ⟨by
    rw [priorB, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun w _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

instance : IsFiniteMeasure jointPriorB :=
  ⟨by
    rw [jointPriorB, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr fun p _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact ENNReal.natCast_lt_top _⟩

/-- The pragmatic listener at the biased prior. -/
noncomputable def listenerB (α : ℝ) : Kernel Utterance (FCState × Interp) :=
  RSA.listener jointPriorB fun p ↦ speaker priorB p.2 α p.1

theorem jointPriorB_real_singleton (p : FCState × Interp) :
    jointPriorB.real {p} = biasedWeight p.1 := by
  rw [measureReal_def, jointPriorB_singleton, ENNReal.toReal_natCast]

/-- With 75% of the prior on Any Number, the listener hearing *or* ranks Any Number above every
other state at every rationality (Table 6). -/
theorem anyNumber_of_prior {α : ℝ} (hα : 0 < α) {w : FCState} (hw : w ≠ .anyNumber) :
    (listenerB α .or_).fst.real {w} < (listenerB α .or_).fst.real {.anyNumber} := by
  have hμ : priorB {.anyNumber} ≠ 0 := by rw [priorB_singleton]; simp [biasedWeight]
  have hone : speaker priorB .exhaustified α .anyNumber {.or_} = 1 :=
    speaker_listener_truthful_dirac_eq_one hα _ _ _ hμ (by decide) (by decide)
  have hlt : (∑ p ∈ ({w} ×ˢ Finset.univ : Finset (FCState × Interp)), jointPriorB.real {p})
      < jointPriorB.real {(.anyNumber, .exhaustified)} := by
    rw [Finset.sum_product, Finset.sum_singleton]
    simp only [jointPriorB_real_singleton, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      show Fintype.card Interp = 2 from rfl]
    cases w <;> first | exact absurd rfl hw | norm_num [biasedWeight]
  rw [Measure.fst_real_singleton, Measure.fst_real_singleton, listenerB]
  exact listener_real_lt_of_certain _ _ (w₀ := ((.anyNumber, .exhaustified) : FCState × Interp))
    (by simp) (fun p ↦ speaker_real_singleton_le_one α 0 (literal priorB p.2) Measure.dirac p.1 _)
    hone hlt

/-! ### No free choice under negation (§4, Table 9) -/

/-- The states of the negation model. -/
inductive NegState where
  | onlyA | onlyB | onlyOne | neither
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NegState := ⊤
instance : DiscreteMeasurableSpace NegState := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass NegState := DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- The negated utterances (10). -/
inductive NegUtterance where
  | notA | notB | notOr | notAnd
  deriving DecidableEq, Repr, Inhabited, Fintype

instance : MeasurableSpace NegUtterance := ⊤
instance : DiscreteMeasurableSpace NegUtterance := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass NegUtterance :=
  DiscreteMeasurableSpace.toMeasurableSingletonClass

/-- Interpretation function 1 under negation (11). -/
def N1 : NegUtterance → NegState → Prop
  | .notA, .onlyB | .notA, .neither => True
  | .notA, _ => False
  | .notB, .onlyA | .notB, .neither => True
  | .notB, _ => False
  | .notOr, .neither => True
  | .notOr, _ => False
  | .notAnd, _ => True

/-- Under negation, interpretation function 2 (12) weakens rather than strengthens. -/
def N2 : NegUtterance → NegState → Prop
  | .notA, .onlyA => False
  | .notA, _ => True
  | .notB, .onlyB => False
  | .notB, _ => True
  | .notOr, .neither => True
  | .notOr, _ => False
  | .notAnd, _ => True

instance : ∀ u, DecidablePred (N1 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

instance : ∀ u, DecidablePred (N2 u) := fun u w => by
  cases u <;> cases w <;> first | exact .isTrue trivial | exact .isFalse id

/-- The negated meanings indexed by interpretation function. -/
def negMeaning : Interp → NegUtterance → NegState → Prop
  | .literal => N1
  | .exhaustified => N2

instance : ∀ i u, DecidablePred (negMeaning i u)
  | .literal, u => inferInstanceAs (DecidablePred (N1 u))
  | .exhaustified, u => inferInstanceAs (DecidablePred (N2 u))

/-- The extensions of the negation model. -/
def negSem (i : Interp) (u : NegUtterance) : Finset NegState :=
  Finset.univ.filter (negMeaning i u)

@[simp] theorem mem_negSem {i : Interp} {u : NegUtterance} {w : NegState} :
    w ∈ negSem i u ↔ negMeaning i u w := by simp [negSem]

theorem negSem_notOr : ∀ i, negSem i .notOr = {.neither} := by decide

/-- The listener of the negation model. -/
noncomputable abbrev negListener (α : ℝ) : Kernel NegUtterance (NegState × Interp) :=
  RSA.listener (uniformOn Set.univ) fun p : NegState × Interp ↦ RSA.speaker α 0
    (RSA.listener (uniformOn Set.univ) (truthful fun u ↦ (negSem p.2 u : Set NegState)))
    Measure.dirac p.1

/-- Hearing *you may not take an apple or a pear*, the listener assigns no mass to any state but
Neither, so there is no free choice under negation (Table 9). -/
theorem no_fci_under_negation {α : ℝ} (hα : 0 < α) {p : NegState × Interp}
    (hp : p.1 ≠ .neither) : negListener α .notOr {p} = 0 :=
  listener_apply_singleton_eq_zero (speaker_listener_truthful_dirac_apply_singleton_eq_zero hα _ _
    _ (by rw [negSem_notOr]; simpa using hp))

end ChampollionAlsopGrosu2019
