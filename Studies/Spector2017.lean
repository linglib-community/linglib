module

public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Pragmatics.RSA.QUD

/-!
# Spector (2017): The pragmatics of plural predication: Homogeneity and non-maximality within the Rational Speech Act model

Spector reconstructs Križ and Spector's pragmatics of plural predication in the Rational Speech
Act model. A plural definite is ambiguous between an existential and a universal reading, and the
first speaker, unsure which reading the literal listener uses, weighs a message by its expected
utility across the readings (`S1_apply_singleton`). A message false on some reading throughout
the speaker's answer has utility minus infinity there, which derives Križ and Spector's truth on
all interpretations (`S1_apply_singleton_eq_zero_iff`). The utility is the literal listener's
probability of the speaker's answer to the question under discussion together with the question.
When the question is what is the case, *the students came* and *the students didn't come* are
used only where all or where none of the students came (`homogeneity`); when it is whether some
of them came, both are existential (`nonMaximality`), and the listener who hears *the students
came* entertains that only some came only under that question (`L1_the_justSome_ne_zero_iff`).

## Implementation notes

* Priors are arguments, with positive mass on every world, question and interpretation, of which
  the paper's flat priors and its two priors over questions are instances.
* A question maps a world to its answer, yes or no for the polar questions and the world itself
  for *what is the case*; the speaker's answer is that answer together with the question.
* The literal listeners of the two interpretations are one listener on pairs of an interpretation
  and an answer (`RSA.parseListener`), and the speaker's belief is the interpretation prior times
  a point mass at her answer, so `RSA.speaker` takes the expected utility across interpretations.

## TODO

* The higher levels of the recursion and the interpretations of the level-five listener reported
  in the tables of §3.3 to §3.5.

## References

* [spector-2017]
* [kriz-spector-2021]
* [goodman-stuhlmuller-2013]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace Spector2017

/-- No student came, some but not all did, or all did. -/
inductive World
  | none | justSome | all
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace World := ⊤
instance : DiscreteMeasurableSpace World := ⟨fun _ ↦ trivial⟩

/-- The messages of the model. -/
inductive Message
  | no | some | all | notAll | the | notThe
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Message := ⊤
instance : DiscreteMeasurableSpace Message := ⟨fun _ ↦ trivial⟩

/-- The plural definite is read existentially or universally. -/
inductive Interp
  | exist | univ
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Interp := ⊤
instance : DiscreteMeasurableSpace Interp := ⟨fun _ ↦ trivial⟩

/-- Did some of the students come, did all of them, and what is the case. -/
inductive QUD
  | isSome | isAll | whatsTheCase
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace QUD := ⊤
instance : DiscreteMeasurableSpace QUD := ⟨fun _ ↦ trivial⟩

/-- A polar question is answered at a world by yes or no, and *what is the case* by the world
itself. -/
def QUD.answer : QUD → World → Bool ⊕ World
  | .isSome, w => .inl (decide (w ≠ .none))
  | .isAll, w => .inl (decide (w = .all))
  | .whatsTheCase, w => .inr w

/-- The meaning of a message under an interpretation of the plural definite. -/
def meaning : Interp → Message → Set World
  | _, .no => {w | w = .none}
  | _, .some => {w | w ≠ .none}
  | _, .all => {w | w = .all}
  | _, .notAll => {w | w ≠ .all}
  | .exist, .the => {w | w ≠ .none}
  | .univ, .the => {w | w = .all}
  | .exist, .notThe => {w | w = .none}
  | .univ, .notThe => {w | w ≠ .all}

instance (i : Interp) (u : Message) : DecidablePred (· ∈ meaning i u) := fun w ↦ by
  cases i <;> cases u <;> unfold meaning <;> infer_instance

/-- The costs of the messages. -/
noncomputable def cost : Message → ℝ
  | .the => 0
  | .notThe | .some | .all => 1
  | .no => 3 / 2
  | .notAll => 2

/-- The answer at a world and a question, together with the question. -/
def answer (p : World × QUD) : (Bool ⊕ World) × QUD := (p.2.answer p.1, p.2)

variable (μ : Measure World) (ρ : Measure QUD) (ν : Measure Interp) (α : ℝ)

/-- The literal listener of an interpretation conditions the prior over worlds and questions on
the message. -/
noncomputable def L0 (i : Interp) : Kernel Message (World × QUD) :=
  listener (μ.prod ρ) (truthful fun u ↦ Prod.fst ⁻¹' meaning i u)

instance (i : Interp) : IsFiniteKernel (L0 μ ρ i) :=
  inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

/-- The first speaker is uncertain about the interpretation of the literal listener and weighs a
message by its expected utility across interpretations, the utility of each being the literal
listener's probability of her answer. -/
noncomputable def S1 : Kernel (World × QUD) Message :=
  speaker α cost (parseListener fun i ↦ (L0 μ ρ i).map answer)
    fun p ↦ ν.prod (Measure.dirac (answer p))

instance : IsFiniteKernel (S1 μ ρ ν α) := inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

/-- The pragmatic listener inverts the first speaker against the prior over worlds and
questions. -/
noncomputable def L1 : Kernel Message (World × QUD) :=
  listener (μ.prod ρ) (S1 μ ρ ν α)

theorem S1_apply_singleton (p : World × QUD) (u : Message) :
    S1 μ ρ ν α p {u} =
      ν.geomMean (fun i ↦ (L0 μ ρ i).map answer u {answer p}) ^ α *
          ENNReal.ofReal (Real.exp (-(α * cost u))) /
        ∑ u', ν.geomMean (fun i ↦ (L0 μ ρ i).map answer u' {answer p}) ^ α *
          ENNReal.ofReal (Real.exp (-(α * cost u'))) := by
  simp only [S1, speaker_apply_singleton, geomMean_prod_dirac_parseListener]

variable {μ ρ ν α}

section Support

variable [IsFiniteMeasure μ] [IsFiniteMeasure ρ] (hμ : ∀ w, μ {w} ≠ 0) (hρ : ∀ Q, ρ {Q} ≠ 0)
include hμ hρ

theorem L0_map_answer_eq_zero_iff (u : Message) (i : Interp) (w : World) (Q : QUD) :
    (L0 μ ρ i).map answer u {answer (w, Q)} = 0 ↔
      ∀ v, Q.answer v = Q.answer w → v ∉ meaning i u := by
  rw [L0, listener_truthful_map_apply_singleton,
    ENNReal.div_eq_zero_iff, or_iff_left (measure_ne_top _ _),
    measure_null_iff_singleton (Set.to_countable _)]
  have hprod (p : World × QUD) : (μ.prod ρ) {p} ≠ 0 := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
    exact mul_ne_zero (hμ p.1) (hρ p.2)
  simp only [hprod, imp_false]
  refine ⟨fun h v hv hvu ↦ h (v, Q) ⟨hvu, by simp [answer, hv]⟩, ?_⟩
  rintro h ⟨v, Q'⟩ ⟨hvu, hx⟩
  simp only [answer, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hx
  obtain ⟨hv, rfl⟩ := hx
  exact h v hv hvu

variable [IsFiniteMeasure ν] (hα : 0 < α)
include hα

theorem S1_apply_singleton_eq_zero_iff (w : World) (Q : QUD) (u : Message) :
    S1 μ ρ ν α (w, Q) {u} = 0 ↔
      ∃ i, ν {i} ≠ 0 ∧ ∀ v, Q.answer v = Q.answer w → v ∉ meaning i u := by
  rw [S1, speaker_parseListener_apply_singleton_eq_zero_iff _ hα]
  exact exists_congr fun i ↦ and_congr_right fun _ ↦ L0_map_answer_eq_zero_iff hμ hρ u i w Q

variable (hν : ∀ i, ν {i} ≠ 0)
include hν

theorem S1_apply_singleton_ne_zero_iff (w : World) (Q : QUD) (u : Message) :
    S1 μ ρ ν α (w, Q) {u} ≠ 0 ↔ ∀ i, ∃ v, Q.answer v = Q.answer w ∧ v ∈ meaning i u := by
  rw [ne_eq, S1_apply_singleton_eq_zero_iff hμ hρ hα]
  simp [hν]

/-- When the question is what is the case, the first speaker uses *the* only where all of the
students came and *not the* only where none did, so neither where only some did. -/
theorem homogeneity (w : World) :
    (S1 μ ρ ν α (w, .whatsTheCase) {.the} ≠ 0 ↔ w = .all) ∧
      (S1 μ ρ ν α (w, .whatsTheCase) {.notThe} ≠ 0 ↔ w = .none) := by
  simp only [S1_apply_singleton_ne_zero_iff hμ hρ hα hν]
  revert w; decide

theorem nonMaximality (w : World) :
    (S1 μ ρ ν α (w, .isSome) {.the} ≠ 0 ↔ w ≠ .none) ∧
      (S1 μ ρ ν α (w, .isSome) {.notThe} ≠ 0 ↔ w = .none) := by
  simp only [S1_apply_singleton_ne_zero_iff hμ hρ hα hν]
  revert w; decide

theorem L1_the_justSome_ne_zero_iff (Q : QUD) :
    L1 μ ρ ν α .the {(.justSome, Q)} ≠ 0 ↔ Q = .isSome := by
  rw [L1, listener_apply_singleton_ne_zero_iff, ← Set.singleton_prod_singleton,
    Measure.prod_prod, S1_apply_singleton_ne_zero_iff hμ hρ hα hν]
  simp only [ne_eq, mul_eq_zero, hμ, hρ, or_self, not_false_eq_true, true_and]
  revert Q; decide

end Support

end Spector2017
