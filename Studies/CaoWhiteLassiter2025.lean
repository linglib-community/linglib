module

public import Mathlib.Probability.Independence.Basic
public import Linglib.Core.MeasureTheory.Measure.Tilted
public import Linglib.Core.Probability.UniformOn
public import Linglib.Data.Examples.CaoWhiteLassiter2025
public import Studies.NadathurLauer2020

/-!
# Cao, White and Lassiter (2025): Cause, make, and force as graded causatives

Cao, White and Lassiter grade English *cause*, *make* and *force* by three measures on a causal
model of tic-tac-toe whose players follow a soft-optimal policy: Pearl's probability of
sufficiency `suf`, the number `alt` of alternatives open to the causee, and a degree of intention,
[an exponential tilting](##intention_real_singleton) of the law of the action on the goal that
[is 1 for an action without alternatives](##intention_eq_one_of_alt). When the causee replies to
each move independently, the sufficiency of a move for a reply is
[the policy's probability of that reply](##suf_exchange_pi), for the best players
[1 over the number of best replies](##suf_exchange_professional). Nadathur and Lauer's categorical
*make* [entails sufficiency 1](##suf_eq_one_of_make).

## Implementation notes

`softOptimalPolicy` takes the set of highest-utility moves and divides `ρ` among them, as the
paper's comparison of two boards does for a board with two best replies; with one best move it is
the displayed `ρ + (1 - ρ) / n`. The edge labels of the paper's game-tree figure give the best
move `ρ` and divide `1 - ρ` among the other moves.

`exchange` is one causer move and the causee's reply, the two timesteps the comparison of two
boards reads from the game. Its context is the causee's reply to each move the causer could make.

## TODO

* The tic-tac-toe model itself: boards, the minimax utility, and the measures of the 30 stimuli.

## References

* [cao-white-lassiter-2025]
* [pearl-2019]
* [halpern-kleiman-weiner-2018]
* [nadathur-lauer-2020]
* [cao-geiger-kreiss-icard-gerstenberg-2023]
-/

@[expose] public section

namespace CaoWhiteLassiter2025

open CausalModel MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Soft-optimal policy -/

section Policy

variable {A : Type*} [MeasurableSpace A] (best : Set A) (ρ : ℝ≥0∞) {a b : A}

/-- A player of skill `ρ` plays a uniformly random highest-utility move with probability `ρ` and
otherwise a uniformly random move. -/
noncomputable def softOptimalPolicy : Measure A :=
  ρ • uniformOn best + (1 - ρ) • uniformOn Set.univ

@[simp] theorem softOptimalPolicy_zero : softOptimalPolicy best 0 = uniformOn Set.univ := by
  simp [softOptimalPolicy]

@[simp] theorem softOptimalPolicy_one : softOptimalPolicy best 1 = uniformOn best := by
  simp [softOptimalPolicy]

variable [MeasurableSingletonClass A]

theorem isProbabilityMeasure_softOptimalPolicy [Finite A] {best : Set A} (hbest : best.Nonempty)
    (hρ : ρ ≤ 1) : IsProbabilityMeasure (softOptimalPolicy best ρ) := by
  have := isProbabilityMeasure_uniformOn best.toFinite hbest
  have := hbest.to_type
  exact ⟨by simp [softOptimalPolicy, add_tsub_cancel_of_le hρ]⟩

variable [Fintype A] {best}

theorem softOptimalPolicy_apply_singleton_of_mem (h : a ∈ best) :
    softOptimalPolicy best ρ {a} = ρ / best.ncard + (1 - ρ) / Fintype.card A := by
  simp [softOptimalPolicy, uniformOn_apply_singleton_of_mem best.toFinite h,
    uniformOn_univ_apply_singleton, div_eq_mul_inv]

theorem softOptimalPolicy_apply_singleton_of_notMem (h : a ∉ best) :
    softOptimalPolicy best ρ {a} = (1 - ρ) / Fintype.card A := by
  simp [softOptimalPolicy, uniformOn_apply_singleton_of_notMem h,
    uniformOn_univ_apply_singleton, div_eq_mul_inv]

-- §2.1.1
theorem softOptimalPolicy_singleton_self :
    softOptimalPolicy {a} ρ {a} = ρ + (1 - ρ) / Fintype.card A := by
  simp [softOptimalPolicy_apply_singleton_of_mem]

-- §2.4: the only best reply against one of two best replies; at `ρ = 0` they do not differ
theorem softOptimalPolicy_pair_lt_singleton (hab : a ≠ b) (hρ₀ : ρ ≠ 0) (hρ : ρ ≠ ∞) :
    softOptimalPolicy {a, b} ρ {a} < softOptimalPolicy {a} ρ {a} := by
  have : Nonempty A := ⟨a⟩
  rw [softOptimalPolicy_singleton_self, softOptimalPolicy_apply_singleton_of_mem _ (.inl rfl),
    Set.ncard_pair hab]
  refine ENNReal.add_lt_add_right (ENNReal.div_ne_top ?_ (by simp)) (ENNReal.half_lt_self hρ₀ hρ)
  exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

end Policy

/-! ### Alternatives and intention -/

section Intention

/-- ALT is the number of actions available to the causee other than the one taken (§2.2). -/
noncomputable def alt {A : Type*} (available : Set A) (taken : A) : ℕ :=
  (available \ {taken}).ncard

theorem alt_eq_zero_iff {A : Type*} {available : Set A} {a : A} (h : available.Finite) :
    alt available a = 0 ↔ available ⊆ {a} := by
  rw [alt, Set.ncard_eq_zero (h.subset Set.sdiff_subset), Set.sdiff_eq_empty]

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] (ν : Measure Ω) (act : Ω → A)
  (goal : Set Ω) (util : A → ℝ) {available : Set A} {a : A}

/-- INT gives each action its degree of intention (§2.3): the probability, over the worlds `ν`,
that the agent takes the action and the goal results, reweighted by the exponential of the
action's utility and normalized over the actions. It is the exponential tilting by utility of the
law of the action on the goal. -/
noncomputable def intention : Measure A :=
  ((ν.restrict goal).map act).tilted util

variable {ν act goal util}

theorem intention_const [IsFiniteMeasure ν] (hact : Measurable act) (c : ℝ) :
    intention ν act goal (fun _ ↦ c) = (ν[|goal]).map act := by
  rw [intention, tilted_const', Measure.map_apply hact .univ, Set.preimage_univ,
    Measure.restrict_apply_univ, ProbabilityTheory.cond, Measure.map_smul _ hact.aemeasurable]

variable [Fintype A] [MeasurableSingletonClass A] [IsFiniteMeasure ν]

/-- The degree of intention of an action is the paper's displayed quotient (§2.3). -/
theorem intention_real_singleton (hact : Measurable act) (a : A) :
    (intention ν act goal util).real {a} =
      ν.real (act ⁻¹' {a} ∩ goal) * Real.exp (util a) /
        ∑ a', ν.real (act ⁻¹' {a'} ∩ goal) * Real.exp (util a') := by
  have h (b : A) : ((ν.restrict goal).map act).real {b} = ν.real (act ⁻¹' {b} ∩ goal) := by
    rw [measureReal_def, Measure.map_apply hact (measurableSet_singleton b),
      Measure.restrict_apply (hact (measurableSet_singleton b)), measureReal_def]
  rw [intention, tilted_real_singleton]
  simp_rw [h]

theorem intention_apply_singleton_eq_one (hact : Measurable act)
    (h : ∀ᵐ ω ∂ν.restrict goal, act ω = a) (h₀ : ν goal ≠ 0) :
    intention ν act goal util {a} = 1 := by
  have : NeZero ((ν.restrict goal).map act) :=
    ⟨fun h0 ↦ h₀ <| by simpa [Measure.map_apply hact .univ] using congr($h0 Set.univ)⟩
  have : IsProbabilityMeasure (intention ν act goal util) := isProbabilityMeasure_tilted .of_finite
  rw [← prob_compl_eq_zero_iff (measurableSet_singleton a)]
  refine tilted_absolutelyContinuous _ _ ?_
  rw [Measure.map_apply hact (measurableSet_singleton a).compl]
  exact h

/-- An action without alternatives has degree of intention 1: when the causee could not have done
otherwise, ALT is 0 and INT is maximal. -/
theorem intention_eq_one_of_alt (hact : Measurable act) (hfin : available.Finite)
    (hav : ∀ᵐ ω ∂ν.restrict goal, act ω ∈ available) (h : alt available a = 0) (h₀ : ν goal ≠ 0) :
    intention ν act goal util {a} = 1 :=
  intention_apply_singleton_eq_one hact (hav.mono fun _ hω ↦ (alt_eq_zero_iff hfin).1 h hω) h₀

end Intention

/-! ### Sufficiency -/

section Model

variable {U V : Type*} {α : V → Type*} [DecidableEq V] [MeasurableSpace U]
  (M : CausalModel U V α) [M.IsAcyclic] [∀ v, Nonempty (α v)]

/-- SUF, Pearl's probability of sufficiency ([pearl-2019]), is the probability, among the
contexts drawn from `ν` in which the observation `obs` holds, that setting `c := x` makes
`e = y` (§2.4). -/
noncomputable def suf (ν : Measure U) (obs : ∀ v, Part (α v)) (c : V) (x : α c) (e : V)
    (y : α e) : ℝ≥0∞ :=
  ν[{u | M[c ← x].solve u e = y} | M.contexts obs]

variable {M} (ν : Measure U) (c : V) (x : α c) (e : V) (y : α e)

theorem suf_bot [IsProbabilityMeasure ν] :
    suf M ν ⊥ c x e y = ν {u | M[c ← x].solve u e = y} := by
  rw [suf, contexts_bot, cond_univ]

open Classical in
theorem suf_dirac [MeasurableSingletonClass U] (u₀ : U) :
    suf M (Measure.dirac u₀) ⊥ c x e y = if M[c ← x].solve u₀ e = y then 1 else 0 := by
  rw [suf_bot, Measure.dirac_apply, Set.indicator_apply]
  simp only [Set.mem_ofPred_eq, Pi.one_apply]

variable {c x e y}

/-- Nadathur and Lauer's *make* entails maximal SUF. Whenever *make* holds of the empty
background, SUF is 1 under every distribution over contexts. -/
theorem suf_eq_one_of_make [IsProbabilityMeasure ν] {u₀ : U}
    (h : NadathurLauer2020.Make M ⊥ u₀ c x e y) : suf M ν ⊥ c x e y = 1 := by
  have h' := h.1.2
  rw [Function.update_idem] at h'
  have hall : {u | M[c ← x].solve u e = y} = Set.univ :=
    Set.eq_univ_of_forall h'.solve_intervene_singleton_eq
  rw [suf_bot, hall, measure_univ]

end Model

/-- A time index for a causal model (the paper's definition 1) places each parent exactly one
timestep before its child. -/
structure TimeIndex {U V : Type*} {α : V → Type*} (M : CausalModel U V α) where
  /-- The timestep of each variable. -/
  time : V → ℕ
  /-- Parents immediately precede their children. -/
  parent_succ : ∀ {w v : V}, M.graph.Adj w v → time w + 1 = time v

theorem TimeIndex.isAcyclic {U V : Type*} {α : V → Type*} {M : CausalModel U V α}
    (ti : TimeIndex M) : M.IsAcyclic :=
  .of_depth _ ti.time fun h ↦ by have := ti.parent_succ h; omega

/-! ### One exchange

The paper compares the SUF of two moves of player X for the same reply of player O. The
comparison reads two timesteps of the game, a move and the reply to it. -/

/-- The variables of one exchange are the causer's move and the causee's reply. -/
inductive Turn | causer | causee
  deriving DecidableEq, Fintype, Repr

section Exchange

universe u

variable {X Y : Type u}

/-- The causer's variable takes moves in `X` and the causee's takes replies in `Y`. -/
abbrev Turn.Val (X Y : Type u) : Turn → Type u
  | .causer => X
  | .causee => Y

instance [Nonempty X] [Nonempty Y] : ∀ v, Nonempty (Turn.Val X Y v)
  | .causer => ‹_›
  | .causee => ‹_›

/-- The reply reads the move. -/
def Turn.edges : Finset (Turn × Turn) := {(.causer, .causee)}

/-- In one exchange the causer actually moves `x₀`, and the context settles what the causee
replies to each move the causer could make. -/
def exchange (x₀ : X) : CausalModel (X → Y) Turn (Turn.Val X Y) where
  graph := ⟨fun w v ↦ (w, v) ∈ Turn.edges⟩
  eqn
    | .causer => fun _ _ ↦ x₀
    | .causee => fun u s ↦ u (s .causer)

instance (x₀ : X) : DecidableRel (exchange (Y := Y) x₀).graph.Adj :=
  fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ Turn.edges))

/-- An exchange is time-indexed, the move at step 0 and the reply at step 1. -/
def exchange.timeIndex (x₀ : X) : TimeIndex (exchange (Y := Y) x₀) where
  time
    | .causer => 0
    | .causee => 1
  parent_succ {w v} (h : (w, v) ∈ Turn.edges) := by revert w v; decide

instance (x₀ : X) : (exchange (Y := Y) x₀).IsAcyclic := (exchange.timeIndex x₀).isAcyclic

variable [Nonempty X] [Nonempty Y] {x₀ x : X} {y₀ y : Y} {u : X → Y}

@[simp] theorem solve_exchange_causer : (exchange x₀).solve u Turn.causer = x₀ :=
  solve_apply u Turn.causer

@[simp] theorem solve_exchange_causee : (exchange x₀).solve u Turn.causee = u x₀ := by
  rw [solve_apply]
  exact congrArg u solve_exchange_causer

@[simp] theorem solve_exchange_intervene_causee :
    (exchange x₀)[Turn.causer ← x].solve u Turn.causee = u x := by
  rw [solve_intervene_of_notMem (by decide)]
  exact congrArg u (solve_intervene_singleton_self (M := exchange x₀) .causer x)

theorem contexts_exchange :
    (exchange x₀).contexts [.causer ← x₀, .causee ← y₀] = {u : X → Y | u x₀ = y₀} := by
  ext u
  simp only [contexts, Set.mem_ofPred_eq, Part.pi_le_iff]
  refine ⟨fun h ↦ ?_, fun h v ↦ ?_⟩
  · simpa [eq_comm] using h .causee
  · cases v <;> simp [h]

variable [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem suf_exchange (ν : Measure (X → Y)) [IsFiniteMeasure ν]
    (h : IndepFun (fun u ↦ u x₀) (fun u ↦ u x) ν) (hc : ν {u | u x₀ = y₀} ≠ 0) :
    suf (exchange x₀) ν [.causer ← x₀, .causee ← y₀] .causer x .causee y = ν {u | u x = y} := by
  have hs : MeasurableSet {u : X → Y | u x₀ = y₀} :=
    show MeasurableSet ((fun u : X → Y ↦ u x₀) ⁻¹' {y₀}) from
      measurable_pi_apply x₀ (measurableSet_singleton y₀)
  have hmul : ν ({u | u x₀ = y₀} ∩ {u | u x = y}) = ν {u | u x₀ = y₀} * ν {u | u x = y} :=
    h.measure_inter_preimage_eq_mul {y₀} {y} (measurableSet_singleton y₀)
      (measurableSet_singleton y)
  rw [suf, contexts_exchange]
  simp only [solve_exchange_intervene_causee]
  rw [cond_apply hs, hmul, ← mul_assoc, ENNReal.inv_mul_cancel hc (measure_ne_top _ _), one_mul]

/-- When the causee replies to each move by an independent draw from a policy, the SUF of a move
other than the actual one for a reply is the policy's probability of that reply after the move
(§2.4). -/
theorem suf_exchange_pi [Fintype X] (π : X → Measure Y) [∀ x, IsProbabilityMeasure (π x)]
    (hx : x ≠ x₀) (hc : π x₀ {y₀} ≠ 0) :
    suf (exchange x₀) (Measure.pi π) [.causer ← x₀, .causee ← y₀] .causer x .causee y =
      π x {y} := by
  have hpi (x : X) (y : Y) : Measure.pi π {u | u x = y} = π x {y} :=
    (measurePreserving_eval π x).measure_preimage (measurableSet_singleton y).nullMeasurableSet
  have hind : iIndepFun (fun (i : X) (u : X → Y) ↦ u i) (Measure.pi π) :=
    iIndepFun_pi (μ := π) (X := fun _ ↦ id) fun _ ↦ aemeasurable_id
  rw [suf_exchange _ (hind.indepFun hx.symm) (by rwa [hpi]), hpi]

/-- Between players who always pick a best move, the SUF of a move for a best reply to it is 1
over the number of best replies: 1 when the reply is forced and 1/2 when there are two (§2.4). -/
theorem suf_exchange_professional [Fintype X] [Finite Y] (best : X → Set Y)
    (hbest : ∀ x, (best x).Nonempty) (hx : x ≠ x₀) (hy₀ : y₀ ∈ best x₀) (hy : y ∈ best x) :
    suf (exchange x₀) (Measure.pi fun x ↦ softOptimalPolicy (best x) 1)
      [.causer ← x₀, .causee ← y₀] .causer x .causee y = ((best x).ncard : ℝ≥0∞)⁻¹ := by
  have (x : X) := isProbabilityMeasure_uniformOn (best x).toFinite (hbest x)
  simp_rw [softOptimalPolicy_one]
  rw [suf_exchange_pi _ hx, uniformOn_apply_singleton_of_mem (best x).toFinite hy]
  simp [uniformOn_apply_singleton_of_mem (best x₀).toFinite hy₀]

end Exchange

end CaoWhiteLassiter2025
