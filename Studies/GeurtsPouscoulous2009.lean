module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.Properties
public import Linglib.Data.Examples.GeurtsPouscoulous2009

/-!
# Geurts and Pouscoulous (2009): Embedded implicatures?!?

This file formalizes the theoretical frame of [geurts-pouscoulous-2009]'s experimental case
against conventionalist theories of scalar implicature ([chierchia-2004], [fox-2007],
[chierchia-fox-spector-2008]), which posit a silent exhaustivity operator adjoinable to any
clause and predict local scalar inferences systematically. The operator `so` negates every
stronger alternative of its prejacent; under a belief verb the parse with `so` below the verb
yields the local reading, that the agent believes *some but not all*, and the parse above it the
global reading, that the agent believes *some* and does not believe *all*
(`local_reading`, `so_pair`). The paper's Gricean reply is that the local reading follows from the
global one whenever the agent is opinionated on the stronger alternative
(`local_of_global_of_opinionated`), while the analogous derivation for a universal quantifier
needs a uniformity assumption across the domain (`all_not_all_of_uniform`) that is far less
plausible, so seemingly local inferences are expected under *believe* and nowhere else.

Mainstream conventionalism predicts the local construal wherever the embedding scope is not
downward entailing (`PredictsLocalSI`, weakly `PredictsLocalSIWeak`). The third experiment's
verification items are reconstructed as situations in which the classical and the local construal
of each sentence conflict (`rows_construals_conflict`); participants answered by the classical
construal throughout (`rows_observed_classical`), against the prediction derived from the scope
monotonicity of the five quantifiers (`rows_predicted_mainstream`).

## Implementation notes

* The experiments' response rates (Tables 2–5) are recorded as features of the rows, with the
  verification and bracketed prediction rates turned into majority responses; the paper's
  statistical tests and its methodological argument that the inference paradigm inflates rates
  stay in prose.
* The verification situations are three squares and three circles; the exact figures of the
  stimuli are not given in the paper, only the conditions they satisfy, which the three situations
  here meet.
* The paper's remark that lexicalist conventionalism reaches only the local reading is not
  formalized; `so` is the syntax-based variant's operator.

## References

* [geurts-pouscoulous-2009]
* [chierchia-2004]
* [fox-2007]
* [chierchia-fox-spector-2008]
* [sauerland-2004]
-/

@[expose] public section

namespace GeurtsPouscoulous2009

open Quantifier Quantifier.GQ Quantifier.NP ModalLogic
open SetRel

variable {W : Type*}

/-! ### The silent exhaustivity operator -/

/-- The silent operator of syntax-based conventionalism conjoins the prejacent with the negation
of every stronger alternative. -/
def so (φ : Set W) (A : Set (Set W)) : Set W := {w | w ∈ φ ∧ ∀ ψ ∈ A, ψ ⊂ φ → w ∉ ψ}

theorem so_pair {φ ψ : Set W} (h : ψ ⊂ φ) : so φ {φ, ψ} = φ \ ψ := by
  ext w
  simp only [so, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨hw, _, hψ⟩ ↦ ⟨hw, hψ h⟩,
    fun ⟨hw, hψ⟩ ↦ ⟨hw, fun hφ ↦ absurd hφ (lt_irrefl φ), fun _ ↦ hψ⟩⟩

theorem local_reading (R : SetRel W W) {some all : Set W} (h : all ⊂ some) :
    R.core (so some {some, all}) = R.core some ∩ R.core allᶜ := by
  rw [so_pair h, Set.sdiff_eq, core_inter]

theorem local_of_global_of_opinionated (R : SetRel W W) {some all : Set W} (h : all ⊂ some)
    {w : W} (h₃₁ : w ∈ R.core some) (h₃₂ : w ∉ R.core all)
    (h₃₃ : w ∈ R.core all ∨ w ∈ R.core allᶜ) : w ∈ R.core (so some {some, all}) := by
  rw [local_reading R h]
  exact ⟨h₃₁, h₃₃.resolve_left h₃₂⟩

theorem all_not_all_of_uniform {C S : Type*} (Shot : C → S → Prop) (h₃₆ : ¬ ∀ c s, Shot c s)
    (h₃₈ : (∀ c s, Shot c s) ∨ ∀ c, ¬ ∀ s, Shot c s) : ∀ c, ¬ ∀ s, Shot c s :=
  h₃₈.resolve_left h₃₆

/-! ### Monotonicity and the mainstream prediction -/

variable {α : Type*}

/-- The stronger mainstream prediction, that a local scalar inference is preferred in every scope
that is not downward entailing. -/
def PredictsLocalSI (Q : GQ α) : Prop := ¬ ScopeAntitone Q

/-- The weaker prediction, that a local scalar inference is preferred in upward-entailing
scopes. -/
def PredictsLocalSIWeak (Q : GQ α) : Prop := ScopeMonotone Q

/-- The quantifiers over squares of the third experiment's sentences. -/
inductive Quant
  | all | moreThanOne | exactlyTwo | notAll | notMoreThanOne
  deriving DecidableEq, Repr

noncomputable def Quant.sem [Fintype α] : Quant → GQ α
  | .all => every
  | .moreThanOne => atLeast 2
  | .exactlyTwo => exactly 2
  | .notAll => everyᶜ
  | .notMoreThanOne => atMost 1

theorem all_predictsLocalSIWeak [Fintype α] : PredictsLocalSIWeak (Quant.all.sem : GQ α) :=
  scopeMonotone_every

theorem moreThanOne_predictsLocalSIWeak [Fintype α] :
    PredictsLocalSIWeak (Quant.moreThanOne.sem : GQ α) :=
  scopeMonotone_atLeast 2

theorem notAll_not_predictsLocalSI [Fintype α] : ¬ PredictsLocalSI (Quant.notAll.sem : GQ α) :=
  not_not.mpr (ScopeMonotone.compl _ scopeMonotone_every)

theorem notMoreThanOne_not_predictsLocalSI [Fintype α] :
    ¬ PredictsLocalSI (Quant.notMoreThanOne.sem : GQ α) :=
  not_not.mpr (scopeAntitone_atMost 1)

/-! ### The verification situations -/

/-- A situation of the third experiment records which squares are connected with which
circles. -/
abbrev Situation := Fin 3 → Fin 3 → Prop

/-- The situation for *all*, *more than one* and the two downward-entailing sentences, in which
every square is connected with some circle and two of them with all. -/
abbrev allSome : Situation := fun s c ↦ s ≠ 0 ∨ c = 0

/-- One square connected with some but not all circles, one with all, one with none. -/
abbrev onePartial : Situation := fun s c ↦ s = 1 ∨ (s = 0 ∧ c = 0)

/-- Two squares connected with some but not all circles, one with all. -/
abbrev twoPartial : Situation := fun s c ↦ s = 2 ∨ c = 0

/-- *Connected with some of the circles*. -/
abbrev someC (R : Situation) (s : Fin 3) : Prop := ∃ c, R s c

/-- The local construal, *connected with some but not all of the circles*. -/
abbrev someNotAllC (R : Situation) (s : Fin 3) : Prop := (∃ c, R s c) ∧ ¬ ∀ c, R s c

/-- The two verification trials of *exactly two*; the other sentences had one. -/
inductive Trial
  | none | a | b
  deriving DecidableEq, Repr

def situation : Quant → Trial → Situation
  | .exactlyTwo, .a => onePartial
  | .exactlyTwo, .b => twoPartial
  | _, _ => allSome

/-- The classical construal of a verification item. -/
def Classical (q : Quant) (t : Trial) : Prop := q.sem (fun _ ↦ True) (someC (situation q t))

/-- The local-implicature construal of a verification item. -/
def Local (q : Quant) (t : Trial) : Prop := q.sem (fun _ ↦ True) (someNotAllC (situation q t))

/-- What mainstream conventionalism predicts of an item, the local construal outside
downward-entailing scopes and the classical one within them. -/
def Mainstream (q : Quant) (t : Trial) : Prop :=
  (PredictsLocalSI (q.sem : GQ (Fin 3)) ∧ Local q t) ∨
    (¬ PredictsLocalSI (q.sem : GQ (Fin 3)) ∧ Classical q t)

theorem all_predictsLocalSI : PredictsLocalSI (Quant.all.sem : GQ (Fin 3)) := fun h ↦
  h (fun _ ↦ True) (show ((fun _ : Fin 3 ↦ False) : Fin 3 → Prop) ≤ fun _ ↦ True from
    fun _ hf ↦ hf.elim) (fun _ _ ↦ trivial) 0 trivial

theorem moreThanOne_predictsLocalSI : PredictsLocalSI (Quant.moreThanOne.sem : GQ (Fin 3)) := by
  intro h
  have key : Quant.moreThanOne.sem (fun _ : Fin 3 ↦ True) (fun _ ↦ True) →
      Quant.moreThanOne.sem (fun _ : Fin 3 ↦ True) (fun _ ↦ False) :=
    h (fun _ ↦ True) (show ((fun _ : Fin 3 ↦ False) : Fin 3 → Prop) ≤ fun _ ↦ True from
      fun _ hf ↦ hf.elim)
  simp only [Quant.sem] at key
  revert key
  decide

theorem exactlyTwo_predictsLocalSI : PredictsLocalSI (Quant.exactlyTwo.sem : GQ (Fin 3)) := by
  intro h
  have key : Quant.exactlyTwo.sem (fun _ : Fin 3 ↦ True) (fun s ↦ s = 0 ∨ s = 1) →
      Quant.exactlyTwo.sem (fun _ : Fin 3 ↦ True) (· = 0) :=
    h (fun _ ↦ True) (show ((· = 0) : Fin 3 → Prop) ≤ fun s ↦ s = 0 ∨ s = 1 from
      fun _ hs ↦ Or.inl hs)
  simp only [Quant.sem] at key
  revert key
  decide

theorem classical_all : Classical .all .none :=
  show ∀ s : Fin 3, True → someC allSome s by decide

theorem not_local_all : ¬ Local .all .none :=
  show ¬ ∀ s : Fin 3, True → someNotAllC allSome s by decide

theorem classical_moreThanOne : Classical .moreThanOne .none := by
  simp only [Classical, Quant.sem, situation]
  decide

theorem not_local_moreThanOne : ¬ Local .moreThanOne .none := by
  simp only [Local, Quant.sem, situation]
  decide

theorem classical_exactlyTwo_a : Classical .exactlyTwo .a := by
  simp only [Classical, Quant.sem, situation]
  decide

theorem not_local_exactlyTwo_a : ¬ Local .exactlyTwo .a := by
  simp only [Local, Quant.sem, situation]
  decide

theorem not_classical_exactlyTwo_b : ¬ Classical .exactlyTwo .b := by
  simp only [Classical, Quant.sem, situation]
  decide

theorem local_exactlyTwo_b : Local .exactlyTwo .b := by
  simp only [Local, Quant.sem, situation]
  decide

theorem not_classical_notAll : ¬ Classical .notAll .none :=
  show ¬ ¬ ∀ s : Fin 3, True → someC allSome s by decide

theorem local_notAll : Local .notAll .none :=
  show ¬ ∀ s : Fin 3, True → someNotAllC allSome s by decide

theorem not_classical_notMoreThanOne : ¬ Classical .notMoreThanOne .none := by
  simp only [Classical, Quant.sem, situation]
  decide

theorem local_notMoreThanOne : Local .notMoreThanOne .none := by
  simp only [Local, Quant.sem, situation]
  decide

/-! ### The verification rows -/

/-- A verification item with the majority response and the majority the stronger mainstream
prediction expects. -/
structure Row where
  quant : Quant
  trial : Trial
  observed : Bool
  predicted : Bool
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let quant ← ex.parse? "quantifier" [("all", Quant.all), ("moreThanOne", .moreThanOne),
    ("exactlyTwo", .exactlyTwo), ("notAll", .notAll), ("notMoreThanOne", .notMoreThanOne)]
  let trial ← ex.parse? "trial" [("none", Trial.none), ("A", .a), ("B", .b)]
  let observed ← ex.nat? "verificationRate"
  let predicted ← ex.nat? "predictedRate"
  pure ⟨quant, trial, decide (50 ≤ observed), decide (50 ≤ predicted)⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_eq : rows = [⟨.all, .none, true, false⟩, ⟨.moreThanOne, .none, true, false⟩,
    ⟨.exactlyTwo, .a, true, false⟩, ⟨.exactlyTwo, .b, false, true⟩, ⟨.notAll, .none, false, false⟩,
    ⟨.notMoreThanOne, .none, false, false⟩] := by
  decide

theorem rows_construals_conflict :
    ∀ r ∈ rows, (Classical r.quant r.trial ↔ ¬ Local r.quant r.trial) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
  exact ⟨iff_of_true classical_all not_local_all,
    iff_of_true classical_moreThanOne not_local_moreThanOne,
    iff_of_true classical_exactlyTwo_a not_local_exactlyTwo_a,
    iff_of_false not_classical_exactlyTwo_b (not_not.mpr local_exactlyTwo_b),
    iff_of_false not_classical_notAll (not_not.mpr local_notAll),
    iff_of_false not_classical_notMoreThanOne (not_not.mpr local_notMoreThanOne)⟩

theorem rows_observed_classical :
    ∀ r ∈ rows, (r.observed = true ↔ Classical r.quant r.trial) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    true_iff, false_iff, Bool.false_eq_true]
  exact ⟨classical_all, classical_moreThanOne, classical_exactlyTwo_a, not_classical_exactlyTwo_b,
    not_classical_notAll, not_classical_notMoreThanOne⟩

/-- The bracketed predictions are the stronger mainstream construal, derived from the scope
monotonicity of each quantifier; outside downward-entailing scopes they invert the responses. -/
theorem rows_predicted_mainstream :
    ∀ r ∈ rows, (r.predicted = true ↔ Mainstream r.quant r.trial) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true,
    true_iff, false_iff, Bool.false_eq_true, Mainstream]
  refine ⟨?_, ?_, ?_, Or.inl ⟨exactlyTwo_predictsLocalSI, local_exactlyTwo_b⟩, ?_, ?_⟩
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact not_local_all h
    · exact h all_predictsLocalSI
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact not_local_moreThanOne h
    · exact h moreThanOne_predictsLocalSI
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact not_local_exactlyTwo_a h
    · exact h exactlyTwo_predictsLocalSI
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h (not_not.mp notAll_not_predictsLocalSI)
    · exact not_classical_notAll h
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h (not_not.mp notMoreThanOne_not_predictsLocalSI)
    · exact not_classical_notMoreThanOne h

end GeurtsPouscoulous2009
