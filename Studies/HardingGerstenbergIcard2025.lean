module

public import Linglib.Pragmatics.Probabilistic.Uniform
public import Linglib.Pragmatics.Probabilistic.Decision
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
reward of the listener's action, in expectation (4), less the message's cost (6),
`RSA.actionSpeaker`; the pragmatic listener is the posterior of the speaker at the prior (7); and
the goodness of an explanation is the gain in expected reward over acting on the prior alone (8),
`goodness`. When the listener's interests are unknown the decision problem is the manipulation
game (Definition 2), whose reward for a variable is the probability over contexts that intervening
on it changes FACT, `manipulationReward`; with the roof less probable than the drought it favours
the roof in the conjunctive structure, `RoofReplacement.manipulationReward_semConj_lt`, and the
drought in the disjunctive one. In the roof example (Example 2) citing the thatched
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

* The roof and milk interpretation sets from actual causation, and the speaker's preference
  between the roof and the drought from the manipulation-game rewards.

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

/-- The goodness (8) of a message at a world is the listener's expected reward after the
message less what acting on the prior alone would have earned. -/
noncomputable def goodness (πL πPrior : Kernel M A) (R : A → W → ℝ) (m : M) (w : W) : ℝ :=
  ∫ a, R a w ∂(πL m) - ∫ a, R a w ∂(πPrior m)

end Framework

/-! ### The manipulation game, Definition 2 -/

section ManipulationGame

variable {U V : Type*} {α : V → Type*} [DecidableEq V] (M : CausalModel U V α) [M.IsAcyclic]
  [∀ v, Nonempty (α v)]

open CausalModel in
/-- The contexts in which some intervention on `X` changes whether FACT holds (Definition 2). -/
def manipulates (X : V) (fact : Set (∀ v, α v)) : Set U :=
  {u | ∃ x, ¬(M[X ← x].solve u ∈ fact ↔ M.solve u ∈ fact)}

/-- The reward of intervening on `X` in a model (Definition 2) is the probability, over contexts
drawn from `ν`, that some intervention on `X` changes whether FACT holds. -/
noncomputable def manipulationReward [MeasurableSpace U] (ν : Measure U) (X : V)
    (fact : Set (∀ v, α v)) : ℝ :=
  ν.real (manipulates M X fact)

end ManipulationGame

/-! ### Actual causation, the literal meaning of "because" -/

open CausalModel in
/-- In the context `u`, `cause` is an actual cause of `effect` in witness form when both hold
and, under some contingency holding a set `W` of variables at values `w`, the cause is but-for the
effect. This is [halpern-pearl-2005]'s definition without the restriction on contingencies that
the paper leaves to any extant account. -/
def actualCause {U V : Type*} [DecidableEq V] (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
    (u : U) (cause effect : V) : Prop :=
  M.solve u cause = true ∧ M.solve u effect = true ∧
    ∃ (W : Finset V) (w : ∀ v : W, Bool),
      (M.intervene W w)[cause ← true].solve u effect = true ∧
        (M.intervene W w)[cause ← false].solve u effect ≠ true

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

-- Example 3
theorem actualCause_T_semT : actualCause semT context .T .C :=
  ⟨by decide, by decide, ∅, isEmptyElim, by decide, by decide⟩

theorem actualCause_T_semConj : actualCause semConj context .T .C :=
  ⟨by decide, by decide, ∅, isEmptyElim, by decide, by decide⟩

theorem actualCause_B_semConj : actualCause semConj context .B .C :=
  ⟨by decide, by decide, ∅, isEmptyElim, by decide, by decide⟩

-- Example 3
theorem not_actualCause_B_semT : ¬ actualCause semT context .B .C := by
  rintro ⟨-, -, W, w, h1, h2⟩
  have hB : ¬ Relation.ReflTransGen semT.graph.Adj .B .C := by decide
  rw [CausalModel.solve_intervene_singleton_of_not_reflTransGen (M := semT.intervene W w) hB]
    at h1 h2
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
  RSA.literalListener μ (fun m ↦ (sem m : Set World))

/-- The prior as a listener who has heard nothing. -/
noncomputable abbrev prior : Kernel Msg World := Kernel.const Msg μ

theorem expectedReward_L0 (a : Act) :
    ∫ w, reward a w ∂(L0 0) = 0 ∧
      ∫ w, reward a w ∂(L0 1) = if a = 1 then 1 else -1 := by
  fin_cases a <;> simp [integral_fintype .of_finite, smul_eq_mul, Fin.sum_univ_two,
    literalListener_uniformOn_apply_singleton, measureReal_def, sem, reward]

theorem expectedReward_prior (m : Msg) (a : Act) : ∫ w, reward a w ∂(prior m) = 0 := by
  fin_cases a <;> simp [integral_fintype .of_finite, smul_eq_mul, Fin.sum_univ_two,
      uniformOn_univ_real_singleton, reward]

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

-- (4)
theorem utility_L0 :
    ∫ a, reward a 0 ∂(policy βL L0 reward 0) = 0 ∧
      ∫ a, reward a 1 ∂(policy βL L0 reward 0) = 0 ∧
      ∫ a, reward a 0 ∂(policy βL L0 reward 1) = 1 - 2 * Real.sigmoid (2 * βL) ∧
      ∫ a, reward a 1 ∂(policy βL L0 reward 1) = 2 * Real.sigmoid (2 * βL) - 1 := by
  have h := policy_L0_both (βL := βL)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [integral_of_pair (a := 1) (a' := 0) (by decide) (by decide)]
  · rw [h.2]; simp [reward]; norm_num
  · rw [h.2]; simp [reward]; norm_num
  · rw [h.1]; simp [reward]; ring
  · rw [h.1]; simp [reward]; ring

theorem half_lt_sigmoid (hβ : 0 < βL) : 1 / 2 < Real.sigmoid (2 * βL) := by
  have := Real.sigmoid_lt (show (0 : ℝ) < 2 * βL by linarith)
  rwa [Real.sigmoid_zero, inv_eq_one_div] at this

theorem speaker_cites_B_iff (hβL : 0 < βL) (hβS : 0 < βS) (c : ℝ) :
    (actionSpeaker βS (fun _ ↦ c) (policy βL L0 reward) reward 0).real {1} <
        (actionSpeaker βS (fun _ ↦ c) (policy βL L0 reward) reward 0).real {0} ∧
      (actionSpeaker βS (fun _ ↦ c) (policy βL L0 reward) reward 1).real {0} <
        (actionSpeaker βS (fun _ ↦ c) (policy βL L0 reward) reward 1).real {1} := by
  obtain ⟨h00, h01, h10, h11⟩ := utility_L0 (βL := βL)
  have hs := half_lt_sigmoid hβL
  constructor
  · rw [actionSpeaker_real_lt_iff reward (fun _ ↦ c) (policy βL L0 reward) (w := 0) (m := 1)
      (m' := 0), h00, h10]
    nlinarith
  · rw [actionSpeaker_real_lt_iff reward (fun _ ↦ c) (policy βL L0 reward) (w := 1) (m := 0)
      (m' := 1), h01, h11]
    nlinarith

theorem μ_singleton (w : World) : μ {w} ≠ 0 ∧ μ.real {w} = 1 / 2 :=
  ⟨uniformOn_univ_singleton_ne_zero w, by rw [uniformOn_univ_real_singleton]; simp⟩

/-- The speaker of Example 3 at equal costs `c`. -/
noncomputable def S (βL βS c : ℝ) : Kernel World Msg :=
  actionSpeaker βS (fun _ ↦ c) (policy βL L0 reward) reward

instance (βL βS c : ℝ) : IsFiniteKernel (S βL βS c) :=
  inferInstanceAs (IsFiniteKernel (actionSpeaker _ _ _ _))

instance (βL βS c : ℝ) : IsMarkovKernel (S βL βS c) :=
  inferInstanceAs (IsMarkovKernel (actionSpeaker _ _ _ _))

theorem S_apply_ne_zero (βL βS c : ℝ) (w : World) (m : Msg) : S βL βS c w {m} ≠ 0 :=
  actionSpeaker_apply_singleton_ne_zero reward (fun _ ↦ c) (policy βL L0 reward)

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
  rw [actionSpeaker_real_of_pair reward (fun _ ↦ c) (policy βL L0 reward) (w := 1) (m := 0)
    (m' := 1) (by decide) (by decide),
    actionSpeaker_real_of_pair reward (fun _ ↦ c) (policy βL L0 reward) (w := 0) (m := 0)
    (m' := 1) (by decide) (by decide), h00, h01, h10, h11]
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
  have hE : ∫ w, reward 0 w ∂(PL βL βS c 0) - ∫ w, reward 1 w ∂(PL βL βS c 0) =
      2 * ((PL βL βS c 0).real {0} - (PL βL βS c 0).real {1}) := by
    simp [integral_fintype .of_finite, smul_eq_mul, Fin.sum_univ_two, reward]
    ring
  have hpos : 0 < βL * (∫ w, reward 0 w ∂(PL βL βS c 0) -
      ∫ w, reward 1 w ∂(PL βL βS c 0)) := by
    rw [hE]
    have := (μ_singleton 0).2
    nlinarith
  rw [goodness, integral_of_pair (a := 0) (a' := 1) (by decide) (by decide),
    integral_of_pair (a := 0) (a' := 1) (by decide) (by decide),
        policy_real_of_pair (PL βL βS c) reward (u := 0) (a := 0) (a' := 1)
    (by decide) (by decide), policy_real_of_pair prior reward (u := 0) (a := 0) (a' := 1)
    (by decide) (by decide), expectedReward_prior, expectedReward_prior]
  have hσ := Real.sigmoid_lt hpos
  rw [Real.sigmoid_zero] at hσ
  simp only [reward, Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, mul_one, sub_zero,
    mul_zero, Real.sigmoid_zero] at hσ ⊢
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
  RSA.literalListener (uniformOn Set.univ) (fun m ↦ (sem m : Set World))

theorem L0_conj_eq : (L0 0).real {2} = (L0 1).real {2} := by
  simp [literalListener_uniformOn_apply_singleton, measureReal_def, sem]

theorem expectedReward_L0 :
    ∫ w, reward 0 w ∂(L0 0) = 0 ∧ ∫ w, reward 1 w ∂(L0 0) = -1 ∧
      ∫ w, reward 0 w ∂(L0 1) = 0 ∧ ∫ w, reward 1 w ∂(L0 1) = -1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [integral_fintype .of_finite, smul_eq_mul, Fin.sum_univ_four,
        literalListener_uniformOn_apply_singleton,
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

/-! #### The manipulation game of the four structures -/

/-- The endogenous variables are the thatched roof, the drought and the fire. -/
inductive Var | R | D | F
  deriving DecidableEq, Fintype, Repr

/-- The context settles whether the roof is thatched and whether there was a drought. -/
structure Context where
  R : Bool
  D : Bool
  deriving DecidableEq, Fintype, Inhabited, Repr

instance : MeasurableSpace Context := ⊤

/-- Only the roof bears on the fire. -/
def edgesR : Finset (Var × Var) := {(.R, .F)}

/-- Only the drought bears on the fire. -/
def edgesD : Finset (Var × Var) := {(.D, .F)}

/-- The roof and the drought both bear on the fire. -/
def edges : Finset (Var × Var) := {(.R, .F), (.D, .F)}

/-- The structure in which the house catches fire just in case its roof is thatched. -/
def semR : CausalModel Context Var fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edgesR⟩
  eqn | .R => fun u _ ↦ u.R | .D => fun u _ ↦ u.D | .F => fun _ x ↦ x .R

/-- The structure in which the house catches fire just in case there was a drought. -/
def semD : CausalModel Context Var fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edgesD⟩
  eqn | .R => fun u _ ↦ u.R | .D => fun u _ ↦ u.D | .F => fun _ x ↦ x .D

/-- The conjunctive structure, in which the fire needs both. -/
def semConj : CausalModel Context Var fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .R => fun u _ ↦ u.R | .D => fun u _ ↦ u.D | .F => fun _ x ↦ x .R && x .D

/-- The disjunctive structure, in which either suffices for the fire. -/
def semDisj : CausalModel Context Var fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn | .R => fun u _ ↦ u.R | .D => fun u _ ↦ u.D | .F => fun _ x ↦ x .R || x .D

instance : DecidableRel semR.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edgesR))

instance : DecidableRel semD.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edgesD))

instance : DecidableRel semConj.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : DecidableRel semDisj.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w, v) ∈ edges))

instance : semR.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

instance : semD.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

instance : semConj.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

instance : semDisj.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- The explanandum: the house catches fire. -/
def fire : Set (Var → Bool) := {w | w .F = true}

-- Table 4: the contexts in which intervening on a variable changes whether the house catches
-- fire; a reward of the table is the probability of the set
theorem manipulates_semR_R : manipulates semR .R fire = Set.univ :=
  Set.eq_univ_of_forall fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

theorem manipulates_semR_D : manipulates semR .D fire = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

theorem manipulates_semD_R : manipulates semD .R fire = ∅ :=
  Set.eq_empty_of_forall_notMem fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

theorem manipulates_semD_D : manipulates semD .D fire = Set.univ :=
  Set.eq_univ_of_forall fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

theorem manipulates_semConj_R : manipulates semConj .R fire = {u | u.D = true} :=
  Set.ext fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

theorem manipulates_semConj_D : manipulates semConj .D fire = {u | u.R = true} :=
  Set.ext fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

theorem manipulates_semDisj_R : manipulates semDisj .R fire = {u | u.D = false} :=
  Set.ext fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

theorem manipulates_semDisj_D : manipulates semDisj .D fire = {u | u.R = false} :=
  Set.ext fun ⟨r, d⟩ ↦ by
    cases r <;> cases d <;> simp only [manipulates, fire, Set.mem_ofPred_eq] <;> decide

variable (ν : Measure Context)

-- §4.3.1: with the roof less probable than the drought, intervening on the roof earns more in
-- the conjunctive structure
theorem manipulationReward_semConj_lt (h : ν.real {u | u.R = true} < ν.real {u | u.D = true}) :
    manipulationReward semConj ν .D fire < manipulationReward semConj ν .R fire := by
  rw [manipulationReward, manipulationReward, manipulates_semConj_R, manipulates_semConj_D]
  exact h

-- §4.3.1: and less in the disjunctive structure
theorem manipulationReward_semDisj_lt [IsProbabilityMeasure ν]
    (h : ν.real {u | u.R = true} < ν.real {u | u.D = true}) :
    manipulationReward semDisj ν .R fire < manipulationReward semDisj ν .D fire := by
  have hc (p : Context → Bool) : ν.real {u | p u = false} = 1 - ν.real {u | p u = true} := by
    rw [← probReal_compl_eq_one_sub MeasurableSpace.measurableSet_top]
    congr 1
    ext u
    simp
  rw [manipulationReward, manipulationReward, manipulates_semDisj_R, manipulates_semDisj_D,
    hc (·.D), hc (·.R)]
  linarith

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
  RSA.literalListener (uniformOn Set.univ) (fun m ↦ (sem m : Set World))

theorem expectedReward_L0_conj (a : Act) :
    ∫ w, reward a w ∂(L0 2) = if a = 2 then 1 else 0 := by
  fin_cases a <;> simp [integral_fintype .of_finite, smul_eq_mul, Fin.sum_univ_three,
    literalListener_uniformOn_apply_singleton, measureReal_def, sem, reward]

theorem expectedReward_L0_C :
    ∫ w, reward 0 w ∂(L0 0) = 1 / 2 ∧ ∫ w, reward 1 w ∂(L0 0) = -1 / 2 ∧
      ∫ w, reward 2 w ∂(L0 0) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [integral_fintype .of_finite, smul_eq_mul, Fin.sum_univ_three,
        literalListener_uniformOn_apply_singleton,
      measureReal_def, sem, reward]
  norm_num

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
    (h : βS * (∫ a, reward a 2 ∂(policy βL L0 reward 2) -
        ∫ a, reward a 2 ∂(policy βL L0 reward 0))
      < cost 2 - cost 0) :
    (actionSpeaker βS cost (policy βL L0 reward) reward 2).real {2} <
      (actionSpeaker βS cost (policy βL L0 reward) reward 2).real {0} := by
  rw [actionSpeaker_real_lt_iff reward cost (policy βL L0 reward) (w := 2) (m := 2) (m' := 0)]
  linarith

end MilkTheft

end HardingGerstenbergIcard2025
