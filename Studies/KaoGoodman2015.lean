module

public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Pragmatics.RSA.QUD

/-!
# Kao and Goodman (2015): Let's Talk (Ironically) About the Weather

Kao and Goodman model irony on the RSA kernel pipeline. The model is that of Kao and colleagues
for hyperbole, over meanings that pair a weather state with the speaker's affect toward it, the
question being the state or a dimension of affect (eq. 1). The paper's contribution is the affect
space, valence together with the arousal dimension it finds in its elicited emotion ratings.

## Main results

* `KaoGoodman2015.irony`: under the arousal question, *the weather is terrible* can mean amazing
  weather with positive valence and high arousal, whenever the prior admits high arousal at
  terrible weather.
* `KaoGoodman2015.valence_flip_needs_arousal`: under the questions of state and valence alone, a
  positive-valence reading of *terrible* needs positive valence to be possible at terrible
  weather itself.
* `KaoGoodman2015.hyperbole`: the reading as merely bad weather is available under the valence
  question.

## Implementation notes

* Priors are arguments. The state prior of a weather context and the affect prior of
  Experiment 1, the probabilities of positive valence and high arousal at each state, enter as
  one probability measure on meanings, and the question prior as a probability measure on
  questions.
* The model's fits to Experiment 2 are not stated.

## References

* [kao-goodman-2015]
* [kao-etal-2014-hyperbole]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

namespace KaoGoodman2015

/-- The weather states, which are also the utterances. -/
inductive Weather
  | terrible | bad | neutral | good | amazing
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace Weather := ⊤
instance : DiscreteMeasurableSpace Weather := ⟨fun _ ↦ trivial⟩
instance : Nonempty Weather := ⟨.neutral⟩

/-- The speaker's affect records positive valence and high arousal. -/
abbrev Affect := Bool × Bool

/-- A meaning pairs the weather state with the speaker's affect toward it. -/
abbrev Meaning := Weather × Affect

/-- The question under discussion asks for the state or for a dimension of affect. -/
inductive QUD
  | state | valence | arousal
  deriving DecidableEq, Repr, Fintype

instance : MeasurableSpace QUD := ⊤
instance : DiscreteMeasurableSpace QUD := ⟨fun _ ↦ trivial⟩
instance : Nonempty QUD := ⟨.state⟩

/-- The projection of a question (eq. 1) reads off the state, the valence, or the arousal. -/
def project : QUD → Meaning → Weather ⊕ Bool
  | .state, m => .inl m.1
  | .valence, m => .inr m.2.1
  | .arousal, m => .inr m.2.2

/-- An utterance is true of the meanings whose state it names. -/
def sem (u : Weather) : Set Meaning := {m | m.1 = u}

/-- The literal listener conditions the prior on the state named. -/
noncomputable def L0 (μ : Measure Meaning) : Kernel Weather Meaning :=
  listener μ (truthful sem)

instance (μ : Measure Meaning) : IsFiniteKernel (L0 μ) :=
  inferInstanceAs (IsFiniteKernel (listener _ (truthful _)))

/-- The question-indexed speaker knows the answer to her question and is informative about the
literal listener's belief about it (eq. 1), at rationality `α` and no utterance cost. -/
noncomputable def S1 (μ : Measure Meaning) (α : ℝ) (p : Meaning × QUD) : Measure Weather :=
  speaker α 0 ((L0 μ).map (project p.2)) Measure.dirac (project p.2 p.1)

instance (μ : Measure Meaning) (α : ℝ) (p : Meaning × QUD) : IsFiniteMeasure (S1 μ α p) :=
  inferInstanceAs (IsFiniteMeasure (speaker _ _ _ _ _))

/-- The pragmatic listener over meaning and question inverts the speaker against the product of
the meaning prior and the question prior; its first marginal is the meaning listener. -/
noncomputable def L1 (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure QUD)
    [IsProbabilityMeasure ν] (α : ℝ) : Kernel Weather (Meaning × QUD) :=
  listener (μ.prod ν) (S1 μ α)

variable (μ : Measure Meaning) [IsProbabilityMeasure μ] (ν : Measure QUD)
  [IsProbabilityMeasure ν] (α : ℝ)

theorem listener_ne_zero_iff (hα : 0 < α) (u : Weather) (m : Meaning) :
    (L1 μ ν α u).fst {m} ≠ 0 ↔ μ {m} ≠ 0 ∧
      ∃ q, ν {q} ≠ 0 ∧ ∃ m', project q m' = project q m ∧ m'.1 = u ∧ μ {m'} ≠ 0 := by
  rw [L1]
  refine (listener_prod_speaker_map_dirac_fst_apply_singleton_ne_zero_iff hα 0 (L0 μ) project μ ν
    u m).trans ?_
  simp only [L0, listener_truthful_apply_singleton_ne_zero_iff]
  rfl

/-- Under the valence question, "terrible" can hyperbolically mean bad weather with negative
valence, through the negative valence of terrible weather. -/
theorem hyperbole (hα : 0 < α) (hν : ν {.valence} ≠ 0) {a a' : Bool}
    (hbad : μ {(.bad, false, a)} ≠ 0) (hterrible : μ {(.terrible, false, a')} ≠ 0) :
    (L1 μ ν α .terrible).fst {(.bad, false, a)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα]
  exact ⟨hbad, .valence, hν, (.terrible, false, a'), rfl, rfl, hterrible⟩

/-- Under the arousal question, "terrible" can ironically mean amazing weather with positive
valence and high arousal, through the high arousal of terrible weather. -/
theorem irony (hα : 0 < α) (hν : ν {.arousal} ≠ 0) {v : Bool}
    (hamazing : μ {(.amazing, true, true)} ≠ 0) (hterrible : μ {(.terrible, v, true)} ≠ 0) :
    (L1 μ ν α .terrible).fst {(.amazing, true, true)} ≠ 0 := by
  rw [listener_ne_zero_iff μ ν α hα]
  exact ⟨hamazing, .arousal, hν, (.terrible, v, true), rfl, rfl, hterrible⟩

/-- Without the arousal question, a positive-valence reading of "terrible" needs positive
valence to be possible at terrible weather itself, since a negative utterance carries no true
information about positive affect. -/
theorem valence_flip_needs_arousal (hα : 0 < α) (hν : ∀ q, ν {q} ≠ 0 → q ≠ .arousal)
    {s : Weather} {a : Bool} (h : (L1 μ ν α .terrible).fst {(s, true, a)} ≠ 0) :
    ∃ a', μ {(.terrible, true, a')} ≠ 0 := by
  obtain ⟨hm, q, hq, ⟨s', v', a'⟩, hm', hs', hμ⟩ := (listener_ne_zero_iff μ ν α hα _ _).mp h
  simp only at hs'
  subst hs'
  rcases q with _ | _ | _
  · obtain rfl : Weather.terrible = s := Sum.inl.inj hm'
    exact ⟨a, hm⟩
  · obtain rfl : v' = true := Sum.inr.inj hm'
    exact ⟨a', hμ⟩
  · exact absurd rfl (hν _ hq)

end KaoGoodman2015
