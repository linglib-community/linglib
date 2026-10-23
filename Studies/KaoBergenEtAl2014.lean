module

public import Linglib.Pragmatics.RSA.QUD

/-!
# Kao, Bergen and Goodman (2014): Formalizing the Pragmatics of Metaphor Understanding

Kao, Bergen and Goodman model metaphor on the RSA kernel pipeline. A meaning pairs a category,
the animal named or a person, with a vector of three features. The literal listener conditions
the prior on the category named, a speaker whose goal is to communicate one feature is
informative about that feature's value (eqs. 1 and 2), and the pragmatic listener marginalizes
the goal. *John is a shark* can then convey scariness to a listener who does not believe John a
shark.

## Main results

* `KaoBergenEtAl2014.nonliteral`: a person with some value of the goal's feature is a possible
  meaning of the animal's name whenever some animal of positive prior shares the value.
* `KaoBergenEtAl2014.category_odds`: a goal ignores the category, so the listener's posterior
  odds between the animal and the person at a feature vector are their prior odds.
* `KaoBergenEtAl2014.speaker_odds`, `KaoBergenEtAl2014.names_animal_iff`: the speaker names the
  animal rather than the person exactly when the feature's value is likelier under the animal.

## Implementation notes

* Priors are arguments. The category prior and the feature priors of Experiment 1b enter as one
  probability measure on meanings, and the goal prior as a probability measure on goals, uniform
  under a vague question and weighted toward the asked feature under a specific one.
* The model's numerical fits rest on the elicited priors of thirty-two animals, which the paper
  does not print, and are not stated.

## References

* [kao-etal-2014-metaphor]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace KaoBergenEtAl2014

/-- A referent is either the animal named or a person. -/
inductive Cat
  | animal | person
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Cat := ⊤
instance : DiscreteMeasurableSpace Cat := ⟨fun _ ↦ trivial⟩
instance : Nonempty Cat := ⟨.person⟩

/-- The three features of the paper's example, each present or absent. -/
abbrev Features := Bool × Bool × Bool

/-- A meaning pairs the category with the feature vector. -/
abbrev Meaning := Cat × Features

/-- A goal names the feature to communicate, `g_i(f) = f_i`. -/
inductive Goal
  | f₁ | f₂ | f₃
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Goal := ⊤
instance : DiscreteMeasurableSpace Goal := ⟨fun _ ↦ trivial⟩
instance : Nonempty Goal := ⟨.f₁⟩

/-- The value of the goal's feature. -/
def Goal.feature : Goal → Features → Bool
  | .f₁, (a, _, _) => a
  | .f₂, (_, b, _) => b
  | .f₃, (_, _, c) => c

/-- The projection of a goal (eq. 1) reads the goal's feature and ignores the category. -/
def project (g : Goal) (m : Meaning) : Bool := g.feature m.2

/-- An utterance is true of the meanings whose category it names. -/
def sem (u : Cat) : Set Meaning := {m | m.1 = u}

/-- The literal listener conditions the prior on the category named. -/
noncomputable def L0 (μ : Measure Meaning) : Kernel Cat Meaning :=
  listener μ (truthful sem)

instance (μ : Measure Meaning) : IsFiniteKernel (L0 μ) :=
  inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

/-- The goal-indexed speaker (eq. 2) knows the value of her goal's feature and is informative
about the literal listener's belief about it (eq. 1), at rationality `α` and no utterance cost. -/
noncomputable def S1 (μ : Measure Meaning) (α : ℝ) (p : Meaning × Goal) : Measure Cat :=
  speaker α 0 ((L0 μ).map (project p.2)) Measure.dirac (project p.2 p.1)

instance (μ : Measure Meaning) (α : ℝ) (p : Meaning × Goal) : IsFiniteMeasure (S1 μ α p) :=
  inferInstanceAs (IsFiniteMeasure (speaker _ _ _ _ _))

/-- The pragmatic listener over meaning and goal inverts the speaker against the product of
the meaning prior and the goal prior; its first marginal is the meaning listener. -/
noncomputable def L1 (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
    [IsProbabilityMeasure ν] (α : ℝ) : Kernel Cat (Meaning × Goal) :=
  listener (μ.prod ν) (S1 μ α)

section Speaker

variable (μ : Measure Meaning) (α : ℝ) (g : Goal) (m : Meaning)

theorem speaker_odds :
    S1 μ α (m, g) {.animal} * (L0 μ).map (project g) .person {project g m} ^ α
      = S1 μ α (m, g) {.person} * (L0 μ).map (project g) .animal {project g m} ^ α := by
  simp only [S1, speaker_dirac_zero_apply_singleton, ENNReal.div_eq_inv_mul]
  ring

theorem names_animal_iff (hα : 0 < α)
    (h0 : ∃ u, (L0 μ).map (project g) u {project g m} ≠ 0) :
    (S1 μ α (m, g)).real {.person} < (S1 μ α (m, g)).real {.animal}
      ↔ (L0 μ).map (project g) .person {project g m} <
        (L0 μ).map (project g) .animal {project g m} := by
  rw [S1, speaker_dirac_real_singleton_lt_iff hα.le h0]
  simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one,
    ENNReal.rpow_lt_rpow_iff hα]

end Speaker

section Listener

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure Goal)
  [IsProbabilityMeasure ν] (α : ℝ)

theorem listener_ne_zero_iff (hα : 0 < α) (u : Cat) (m : Meaning) :
    (L1 μ ν α u).fst {m} ≠ 0 ↔ μ {m} ≠ 0 ∧
      ∃ g, ν {g} ≠ 0 ∧ ∃ m', g.feature m'.2 = g.feature m.2 ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [L1]
  refine (listener_prod_speaker_map_dirac_fst_apply_singleton_ne_zero_iff hα 0 (L0 μ) project μ ν
    u m).trans ?_
  simp only [L0, listener_truthful_apply_singleton_ne_zero_iff]
  rfl

theorem nonliteral (hα : 0 < α) {g : Goal} (hν : ν {g} ≠ 0) {f f' : Features}
    (hp : μ {(.person, f)} ≠ 0) (ha : μ {(.animal, f')} ≠ 0)
    (hf : g.feature f' = g.feature f) : (L1 μ ν α .animal).fst {(.person, f)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα]
  exact ⟨hp, g, hν, (.animal, f'), hf, rfl, ha⟩

theorem category_odds (u : Cat) (c c' : Cat) (f : Features) :
    (L1 μ ν α u).fst {(c, f)} * μ {(c', f)} = (L1 μ ν α u).fst {(c', f)} * μ {(c, f)} := by
  have key : ∀ c, (L1 μ ν α u).fst {(c, f)}
      = μ {(c, f)} * ∑ g, ν {g} *
          (S1 μ α ((.person, f), g) {u} / ∑ p, S1 μ α p {u} * (μ.prod ν) {p}) :=
    fun c ↦ by
      rw [L1, Measure.fst_apply_singleton, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      rw [listener_apply_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
        show S1 μ α ((c, f), g) = S1 μ α ((.person, f), g) from rfl, mul_comm, mul_div_assoc,
        mul_assoc]
  rw [key c, key c']
  ring

end Listener

end KaoBergenEtAl2014
