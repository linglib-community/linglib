module

public import Linglib.Pragmatics.RSA.Uniform
public import Linglib.Pragmatics.RSA.Decision
public import Linglib.Core.Probability.Kernel.Posterior
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Causation.CausalModel.Basic
public import Linglib.Core.Relation.ReflTransGen
public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Harding, Gerstenberg, and Icard (2025): A Communication-First Account of Explanation

On the model of Harding, Gerstenberg and Icard an answer to "why FACT?" is a message in a
Rational Speech Act game, after Frank and Goodman, whose literal meaning is actual causation and
whose speaker is useful rather than informative, after Sumers and colleagues. The literal
listener conditions a prior over causal situations on the message (2); the listener acts in a
decision problem by the softmax of expected reward (3), `RSA.policy`; the speaker maximizes the
reward of the listener's action, `RSA.actionUtility` (4), less the message's cost (6),
`speaker`; the
pragmatic listener is the posterior of the speaker at the prior (7); and the goodness of an
explanation is the gain in expected reward over acting on the prior alone (8), `goodness`.
When the listener's interests are unknown the decision problem is the manipulation game
(Definition 2), whose reward for a variable is the probability over contexts that intervening
on it changes FACT, `manipulationReward`. In the roof example (Example 2) citing the thatched
roof and citing the drought are equally informative but not equally useful, since only the
former bears on replacing a roof (Table 1), so at any rationality the listener replaces the roof
more readily after the former, `RoofReplacement.policy_replace_lt`. In the late-meeting example
(Example 3) citing the tardiness is worth giving although the listener already knows it: the
speaker cites the birthday exactly in the conjunctive world, so the pragmatic listener infers
from her not doing so that tardiness alone is the cause, and the goodness of the message is
positive, `LateMeeting.goodness_pos`. In the milk example (Example 4) citing both culprits is
worth more than citing one, but a sufficient cost difference makes the speaker prefer the
shorter message, `MilkTheft.speaker_prefers_short`. The interpretation sets are the paper's,
and for the late meeting they are derived from actual causation in the worlds' causal models.

## Implementation notes

The agents are kept at finite rationality, where the paper takes the limit, and each claim is
stated for the rationalities it needs. Actual causation is the witness form of the
Halpern–Pearl definition, `actualCause`, which the paper leaves open to any extant account: some
contingency, an intervention on other variables, under which the cause is but-for the effect in
the actual context. A negative membership follows from the graph when no path runs from the
cited variable to the fact. Priors are uniform, as in the examples.

## TODO

* Table 4, the manipulation-game rewards of Example 2, from the four structural models and a
  product prior over the contexts; the roof and milk interpretation sets from actual causation.

## References

* [harding-gerstenberg-icard-2025]
* [halpern-pearl-2005]
* [sumers-etal-2024]
* [frank-goodman-2012]
-/

@[expose] public section

namespace HardingGerstenbergIcard2025

open MeasureTheory ProbabilityTheory RSA
open scoped ENNReal

/-! ### The communication game, section 3 -/

section Framework

variable {W M A : Type*} [Fintype W] [MeasurableSpace W] [DiscreteMeasurableSpace W]
  [Fintype M] [MeasurableSpace M] [DiscreteMeasurableSpace M] [Fintype A] [MeasurableSpace A]

/-- The speaker scores a message by rationality times utility, less cost. -/
noncomputable def speakerScore (β : ℝ) (cost : M → ℝ) (π : Kernel M A) (R : A → W → ℝ)
    (w : W) (m : M) : EReal :=
  ((β * actionUtility π R m w - cost m : ℝ) : EReal)

/-- The speaker (6) is the softmax of utility less cost at rationality `β`. -/
noncomputable def speaker (β : ℝ) (cost : M → ℝ) (π : Kernel M A) (R : A → W → ℝ) :
    Kernel W M :=
  Kernel.softmax (speakerScore β cost π R)

/-- The goodness (8) of a message at a world is the listener's expected reward after the
message less what acting on the prior alone would have earned. -/
noncomputable def goodness (πL πPrior : Kernel M A) (R : A → W → ℝ) (m : M) (w : W) : ℝ :=
  actionUtility πL R m w - actionUtility πPrior R m w

variable (β : ℝ) (R : A → W → ℝ) (cost : M → ℝ) (π : Kernel M A)

instance : IsFiniteKernel (speaker β cost π R) :=
  inferInstanceAs (IsFiniteKernel (Kernel.softmax _))

instance [Nonempty M] : IsMarkovKernel (speaker β cost π R) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary M, EReal.coe_ne_bot _⟩)
    (fun _ _ => EReal.coe_ne_top _)

variable {β} {m m' : M} {a a' : A} {w : W}

/-- Row preference of the speaker is comparison of utility less cost. -/
theorem speaker_real_lt_iff :
    (speaker β cost π R w).real {m} < (speaker β cost π R w).real {m'} ↔
      β * actionUtility π R m w - cost m < β * actionUtility π R m' w - cost m' := by
  rw [speaker, Kernel.softmax_real_singleton_lt_iff (score := speakerScore β cost π R) (w := w)
    (fun _ ↦ EReal.coe_ne_top _) ⟨m, EReal.coe_ne_bot _⟩, speakerScore, speakerScore,
    EReal.coe_lt_coe_iff]

theorem speaker_real_of_pair (hmm' : m ≠ m') (hall : ∀ c, c = m ∨ c = m') :
    (speaker β cost π R w).real {m} =
      Real.sigmoid (β * (actionUtility π R m w - actionUtility π R m' w) - (cost m - cost m')) := by
  rw [speaker, Kernel.softmax_real_singleton_of_pair (score := speakerScore β cost π R) (w := w)
    hmm' (EReal.coe_ne_bot _) (EReal.coe_ne_bot _) (fun _ ↦ EReal.coe_ne_top _) (fun c _ => hall c),
    speakerScore, speakerScore, EReal.toReal_coe, EReal.toReal_coe]
  ring_nf

end Framework

/-! ### The manipulation game, Definition 2 -/

section ManipulationGame

variable {U V : Type*} [DecidableEq V] [Fintype U]

open Classical CausalModel in
/-- The reward of intervening on `X` in a model (Definition 2) is the probability, over contexts
drawn with weights `P`, that intervening on `X` changes FACT. -/
noncomputable def manipulationReward (P : U → ℝ) (M : CausalModel U V fun _ ↦ Bool)
    [M.IsAcyclic] (X fact : V) : ℝ :=
  ∑ u, P u * if M.solve [X ← true] u fact ≠ M.solve [X ← false] u fact then 1 else 0

end ManipulationGame

/-! ### Actual causation, the literal meaning of "because" -/

/-- In the context `u`, `cause` is an actual cause of `effect` in witness form when both hold
and, under some contingency `I` intervening on other variables, the cause is but-for the effect.
This is [halpern-pearl-2005]'s definition without the restriction on contingencies that the paper
leaves to any extant account. -/
def actualCause {U V : Type*} [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
    (u : U) (cause effect : V) : Prop :=
  M.solve ⊥ u cause = true ∧ M.solve ⊥ u effect = true ∧
    ∃ I : V → Flat Bool, M.solve (Function.update I cause ↑true) u effect = true ∧
      M.solve (Function.update I cause ↑false) u effect ≠ true

/-! ### Example 3: the late meeting -/

namespace LateMeeting

/-- The endogenous variables are Bob's tardiness, his forgetting the birthday, and Charlie's
crossness. -/
inductive V | T | B | C
  deriving DecidableEq, Fintype, Repr

/-- Tardiness alone bears on crossness. -/
def edgesT : Finset (V × V) := {(.T, .C)}

/-- Tardiness and the forgotten birthday both bear on crossness. -/
def edgesConj : Finset (V × V) := {(.T, .C), (.B, .C)}

/-- The context settles whether Bob was late and whether he forgot the birthday. -/
structure Context where
  T : Bool
  B : Bool

/-- The model in which tardiness alone causes crossness. -/
def semT : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edgesT⟩
  eqn | .T => fun u _ ↦ u.T | .B => fun u _ ↦ u.B | .C => fun _ x ↦ x .T

/-- The conjunctive model, in which both are needed. -/
def semConj : CausalModel Context V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edgesConj⟩
  eqn | .T => fun u _ ↦ u.T | .B => fun u _ ↦ u.B | .C => fun _ x ↦ x .T && x .B

instance : DecidableRel semT.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edgesT))

instance : DecidableRel semConj.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edgesConj))

instance : semT.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

instance : semConj.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- In the context Bob knows, he was late and forgot the birthday. -/
def context : Context := ⟨true, true⟩

/-- "Because T" is true in both worlds and "because B" in the conjunctive world. These are the
interpretation sets of Example 3, derived from actual causation with the empty contingency. -/
theorem actualCause_T_semT : actualCause semT context .T .C :=
  ⟨by decide, by decide, ⊥, by decide, by decide⟩

theorem actualCause_T_semConj : actualCause semConj context .T .C :=
  ⟨by decide, by decide, ⊥, by decide, by decide⟩

theorem actualCause_B_semConj : actualCause semConj context .B .C :=
  ⟨by decide, by decide, ⊥, by decide, by decide⟩

/-- "Because B" is false in the tardiness-only world, the negative membership of Example 3, since
no path runs from the birthday to crossness, so under no contingency is it but-for crossness. -/
theorem not_actualCause_B_semT : ¬ actualCause semT context .B .C := by
  rintro ⟨-, -, I, h1, h2⟩
  have hB : ¬ Relation.ReflTransGen semT.graph.Adj .B .C := by decide
  rw [CausalModel.solve_update_of_not_reflTransGen hB] at h1 h2
  exact h2 h1

/-- The worlds are the tardiness-only model `0` and the conjunctive model `1`. -/
abbrev World := Fin 2

/-- The messages are "because T", `0`, and "because B", `1`. -/
abbrev Msg := Fin 2

/-- The actions of Table 3 are to apologize for the tardiness alone, `0`, or for both, `1`. -/
abbrev Act := Fin 2

/-- The interpretation sets (Example 3). -/
def sem : Msg → Finset World := ![{0, 1}, {1}]

/-- In Table 3, apologizing for what is the cause earns 1, and otherwise −1. -/
def reward : Act → World → ℝ := fun a w => if a = w then 1 else -1

/-- The uniform prior over the worlds. -/
noncomputable abbrev μ : Measure World := uniformOn Set.univ

/-- The literal listener (2) conditions the uniform prior on the interpretation set. -/
noncomputable abbrev L0 : Kernel Msg World :=
  RSA.listener μ (truthful fun m ↦ (sem m : Set World))

/-- The prior as a listener who has heard nothing. -/
noncomputable abbrev prior : Kernel Msg World := Kernel.const Msg μ

theorem expectedReward_L0 (a : Act) :
    expectedReward L0 reward 0 a = 0 ∧
      expectedReward L0 reward 1 a = if a = 1 then 1 else -1 := by
  fin_cases a <;> simp [expectedReward, Fin.sum_univ_two,
    listener_uniformOn_truthful_apply_singleton, measureReal_def, sem, reward]

theorem expectedReward_prior (m : Msg) (a : Act) : expectedReward prior reward m a = 0 := by
  fin_cases a <;> simp [expectedReward, Fin.sum_univ_two, uniformOn_univ_real_singleton, reward]

variable {βL βS : ℝ}

theorem policy_L0_both :
    (policy βL L0 reward 1).real {1} = Real.sigmoid (2 * βL) ∧
      (policy βL L0 reward 0).real {1} = 1 / 2 := by
  constructor
  · rw [policy_real_of_pair L0 reward (u := 1) (a := 1) (a' := 0) (by decide) (by decide),
      (expectedReward_L0 1).2, (expectedReward_L0 0).2]
    norm_num
    ring
  · rw [policy_real_of_pair L0 reward (u := 0) (a := 1) (a' := 0) (by decide) (by decide),
      (expectedReward_L0 1).1, (expectedReward_L0 0).1]
    simp [Real.sigmoid_zero]

theorem policy_prior_half (m : Msg) : (policy βL prior reward m).real {1} = 1 / 2 := by
  rw [policy_real_of_pair prior reward (u := m) (a := 1) (a' := 0) (by decide) (by decide),
    expectedReward_prior, expectedReward_prior]
  simp [Real.sigmoid_zero]

/-- By the speaker's utilities (4), "because T" is worth nothing in either world, and "because
B" less than nothing in the tardiness-only world and more in the conjunctive one. -/
theorem utility_L0 :
    actionUtility (policy βL L0 reward) reward 0 0 = 0 ∧
      actionUtility (policy βL L0 reward) reward 0 1 = 0 ∧
      actionUtility (policy βL L0 reward) reward 1 0 = 1 - 2 * Real.sigmoid (2 * βL) ∧
      actionUtility (policy βL L0 reward) reward 1 1 = 2 * Real.sigmoid (2 * βL) - 1 := by
  have h := policy_L0_both (βL := βL)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [actionUtility_of_pair reward (policy βL L0 reward) (a := 1) (a' := 0) (by decide)
      (by decide)]
  · rw [h.2]; simp [reward]; norm_num
  · rw [h.2]; simp [reward]; norm_num
  · rw [h.1]; simp [reward]; ring
  · rw [h.1]; simp [reward]; ring

theorem half_lt_sigmoid (hβ : 0 < βL) : 1 / 2 < Real.sigmoid (2 * βL) := by
  have := Real.sigmoid_lt (show (0 : ℝ) < 2 * βL by linarith)
  rwa [Real.sigmoid_zero, inv_eq_one_div] at this

theorem speaker_cites_B_iff (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    (speaker βS (fun _ ↦ c) (policy βL L0 reward) reward 0).real {1} <
        (speaker βS (fun _ ↦ c) (policy βL L0 reward) reward 0).real {0} ∧
      (speaker βS (fun _ ↦ c) (policy βL L0 reward) reward 1).real {0} <
        (speaker βS (fun _ ↦ c) (policy βL L0 reward) reward 1).real {1} := by
  obtain ⟨h00, h01, h10, h11⟩ := utility_L0 (βL := βL)
  have hs := half_lt_sigmoid hβL
  constructor
  · rw [speaker_real_lt_iff reward (fun _ ↦ c) (policy βL L0 reward) (w := 0) (m := 1) (m' := 0),
      h00, h10]
    nlinarith
  · rw [speaker_real_lt_iff reward (fun _ ↦ c) (policy βL L0 reward) (w := 1) (m := 0) (m' := 1),
      h01, h11]
    nlinarith

theorem μ_singleton (w : World) : μ {w} ≠ 0 ∧ μ.real {w} = 1 / 2 :=
  ⟨uniformOn_univ_singleton_ne_zero w, by rw [uniformOn_univ_real_singleton]; simp⟩

/-- The speaker of Example 3 at equal costs `c`. -/
noncomputable def S (βL βS c : ℝ) : Kernel World Msg :=
  speaker βS (fun _ ↦ c) (policy βL L0 reward) reward

instance (βL βS c : ℝ) : IsFiniteKernel (S βL βS c) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _ _))

instance (βL βS c : ℝ) : IsMarkovKernel (S βL βS c) :=
  inferInstanceAs (IsMarkovKernel (speaker _ _ _ _))

theorem S_apply_ne_zero (βL βS c : ℝ) (w : World) (m : Msg) : S βL βS c w {m} ≠ 0 :=
  Kernel.softmax_apply_singleton_ne_zero
    (score := speakerScore βS (fun _ ↦ c) (policy βL L0 reward) reward) (EReal.coe_ne_bot _)
    (fun _ ↦ EReal.coe_ne_top _)

theorem comp_S_ne_zero (βL βS c : ℝ) : (S βL βS c ∘ₘ μ) {0} ≠ 0 := by
  rw [Measure.comp_apply_singleton]
  intro h
  exact mul_ne_zero (μ_singleton 0).1 (S_apply_ne_zero βL βS c 0 0)
    (Finset.sum_eq_zero_iff.mp h 0 (Finset.mem_univ _))

theorem S_real_lt (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    (S βL βS c 1).real {0} < (S βL βS c 0).real {0} := by
  obtain ⟨h00, h01, h10, h11⟩ := utility_L0 (βL := βL)
  have hs := half_lt_sigmoid hβL
  unfold S
  rw [speaker_real_of_pair reward (fun _ ↦ c) (policy βL L0 reward) (w := 1) (m := 0) (m' := 1)
    (by decide) (by decide), speaker_real_of_pair reward (fun _ ↦ c) (policy βL L0 reward)
    (w := 0) (m := 0) (m' := 1) (by decide) (by decide), h00, h01, h10, h11]
  exact Real.sigmoid_lt (by nlinarith)

/-- The pragmatic listener (7). -/
noncomputable def PL (βL βS c : ℝ) : Kernel Msg World := RSA.listener μ (S βL βS c)

instance (βL βS c : ℝ) : IsMarkovKernel (PL βL βS c) :=
  ⟨fun m ↦ RSA.isProbabilityMeasure_listener_of_ne_zero _ _ (μ_singleton 0).1
    (S_apply_ne_zero βL βS c 0 m)⟩

theorem pragmatic_T (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    μ.real {0} < (PL βL βS c 0).real {0} := by
  rw [PL, RSA.listener_apply_eq_posterior _ _ (comp_S_ne_zero βL βS c),
    real_lt_posterior_real_singleton_iff_of_pair (S βL βS c) μ (ω := 0) (ω' := 1)
    (by decide) (fun w _ => by fin_cases w <;> simp) (comp_S_ne_zero βL βS c) (μ_singleton 0).1
    (μ_singleton 1).1]
  exact S_real_lt hβL hβS c

/-- By goodness (8), citing the tardiness is worth giving, although Bob already knew it. -/
theorem goodness_pos (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    0 < goodness (policy βL (PL βL βS c) reward) (policy βL prior reward) reward 0 0 := by
  have hpost : μ.real {0} < (PL βL βS c 0).real {0} := pragmatic_T hβL hβS c
  have hsum : (PL βL βS c 0).real {0} + (PL βL βS c 0).real {1} = 1 :=
    measureReal_singleton_add_singleton_of_pair (PL βL βS c 0) (ω := 0) (ω' := 1) (by decide)
      (fun w _ => by fin_cases w <;> simp)
  have hE : expectedReward (PL βL βS c) reward 0 0 - expectedReward (PL βL βS c) reward 0 1 =
      2 * ((PL βL βS c 0).real {0} - (PL βL βS c 0).real {1}) := by
    simp [expectedReward, Fin.sum_univ_two, reward]
    ring
  have hpos : 0 < βL * (expectedReward (PL βL βS c) reward 0 0 -
      expectedReward (PL βL βS c) reward 0 1) := by
    rw [hE]
    have := (μ_singleton 0).2
    nlinarith
  rw [goodness, actionUtility_of_pair reward (policy βL (PL βL βS c) reward) (a := 0) (a' := 1)
    (by decide) (by decide),
    actionUtility_of_pair reward (policy βL prior reward) (a := 0) (a' := 1)
    (by decide) (by decide), policy_real_of_pair (PL βL βS c) reward (u := 0) (a := 0) (a' := 1)
    (by decide) (by decide), policy_real_of_pair prior reward (u := 0) (a := 0) (a' := 1)
    (by decide) (by decide), expectedReward_prior, expectedReward_prior]
  have hσ := Real.sigmoid_lt hpos
  rw [Real.sigmoid_zero] at hσ
  simp only [reward, Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, mul_one, sub_zero,
    mul_zero, Real.sigmoid_zero]
  norm_num at hσ ⊢
  linarith

end LateMeeting

/-! ### Example 2: the roof replacement -/

namespace RoofReplacement

/-- The worlds are the roof-only model `0`, the drought-only model `1`, the conjunctive `2` and
the disjunctive `3`, all at the context where the roof is thatched and there was a drought. -/
abbrev World := Fin 4

/-- The messages are "because R", `0`, and "because D", `1`. -/
abbrev Msg := Fin 2

/-- The actions of Table 1 are to replace the roof, `0`, or not, `1`. -/
abbrev Act := Fin 2

/-- The interpretation sets of Example 2. -/
def sem : Msg → Finset World := ![{0, 2, 3}, {1, 2, 3}]

/-- In Table 1, replacing earns 0 everywhere, and not replacing earns 1 in the drought-only
world and −1 elsewhere. -/
def reward : Act → World → ℝ := fun a w => if a = 0 then 0 else if w = 1 then 1 else -1

noncomputable abbrev L0 : Kernel Msg World :=
  RSA.listener (uniformOn Set.univ) (truthful fun m ↦ (sem m : Set World))

theorem L0_conj_eq : (L0 0).real {2} = (L0 1).real {2} := by
  simp [listener_uniformOn_truthful_apply_singleton, measureReal_def, sem]

theorem expectedReward_L0 :
    expectedReward L0 reward 0 0 = 0 ∧ expectedReward L0 reward 0 1 = -1 ∧
      expectedReward L0 reward 1 0 = 0 ∧ expectedReward L0 reward 1 1 = -1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [expectedReward, Fin.sum_univ_four, listener_uniformOn_truthful_apply_singleton,
      measureReal_def, sem, reward] <;> norm_num

/-- The two messages are not equally useful, since at any rationality the listener replaces the
roof more readily after "because R" than after "because D". -/
theorem policy_replace_lt {βL : ℝ} (hβ : 0 < βL) :
    (policy βL L0 reward 1).real {0} < (policy βL L0 reward 0).real {0} := by
  obtain ⟨h00, h01, h10, h11⟩ := expectedReward_L0
  rw [policy_real_of_pair L0 reward (u := 1) (a := 0) (a' := 1) (by decide) (by decide),
    policy_real_of_pair L0 reward (u := 0) (a := 0) (a' := 1) (by decide) (by decide), h00, h01,
    h10, h11]
  exact Real.sigmoid_lt (by nlinarith)

end RoofReplacement

/-! ### Example 4: the milk theft -/

namespace MilkTheft

/-- The worlds are the contexts in which Charlie alone (`0`), Dana alone (`1`), or both (`2`)
drank the milk, in the disjunctive model. -/
abbrev World := Fin 3

/-- The messages are "because C", `0`, "because D", `1`, and "because C and D", `2`. -/
abbrev Msg := Fin 3

/-- The actions of Table 5 are to confront Charlie (`0`), Dana (`1`), or both (`2`). -/
abbrev Act := Fin 3

/-- The interpretation sets of Example 4. -/
def sem : Msg → Finset World := ![{0, 2}, {1, 2}, {2}]

/-- Table 5. -/
def reward : Act → World → ℝ :=
  ![![1, -1, 0], ![-1, 1, 0], ![0, 0, 1]]

noncomputable abbrev L0 : Kernel Msg World :=
  RSA.listener (uniformOn Set.univ) (truthful fun m ↦ (sem m : Set World))

theorem expectedReward_L0_conj (a : Act) :
    expectedReward L0 reward 2 a = if a = 2 then 1 else 0 := by
  fin_cases a <;> simp [expectedReward, Fin.sum_univ_three,
    listener_uniformOn_truthful_apply_singleton, measureReal_def, sem, reward]

theorem expectedReward_L0_C :
    expectedReward L0 reward 0 0 = 1 / 2 ∧ expectedReward L0 reward 0 1 = -1 / 2 ∧
      expectedReward L0 reward 0 2 = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [expectedReward, Fin.sum_univ_three, listener_uniformOn_truthful_apply_singleton,
      measureReal_def, sem, reward]
  norm_num

/-- After "because C and D" confronting both is the strictly preferred action; after
"because C" it is tied with confronting Charlie. -/
theorem policy_L0 {βL : ℝ} (hβ : 0 < βL) :
    (policy βL L0 reward 2).real {0} < (policy βL L0 reward 2).real {2} ∧
      ¬ (policy βL L0 reward 0).real {0} < (policy βL L0 reward 0).real {2} := by
  constructor
  · rw [policy_real_lt_iff L0 reward (u := 2) hβ, expectedReward_L0_conj, expectedReward_L0_conj]
    simp
  · rw [policy_real_lt_iff L0 reward (u := 0) hβ, expectedReward_L0_C.1, expectedReward_L0_C.2.2]
    simp

/-- With a sufficient cost difference the speaker prefers the shorter message although it is
less useful, the redundancy trade-off of section 4.4.1. -/
theorem speaker_prefers_short {βL βS : ℝ} (cost : Msg → ℝ)
    (h : βS * (actionUtility (policy βL L0 reward) reward 2 2 -
        actionUtility (policy βL L0 reward) reward 0 2)
      < cost 2 - cost 0) :
    (speaker βS cost (policy βL L0 reward) reward 2).real {2} <
      (speaker βS cost (policy βL L0 reward) reward 2).real {0} := by
  rw [speaker_real_lt_iff reward cost (policy βL L0 reward) (w := 2) (m := 2) (m' := 0)]
  linarith

end MilkTheft

end HardingGerstenbergIcard2025
