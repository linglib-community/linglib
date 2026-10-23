module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Data.Set.Card
public import Linglib.Core.Probability.UniformOn
public import Linglib.Data.Examples.CaoWhiteLassiter2025
public import Mathlib.Probability.ConditionalProbability
public import Studies.NadathurLauer2020

/-!
# Cao, White and Lassiter (2025): Cause, make, and force as graded causatives

Cao, White and Lassiter treat English *cause*, *make* and *force* as graded causatives. Where
Nadathur and Lauer give *make* a categorical truth condition, causal sufficiency, they measure
three quantities in a structural causal model of tic-tac-toe: Pearl's probability of sufficiency
(`suf`), a simplified version of Halpern and Kleiman-Weiner's degree of intention, and the number
of alternative actions open to the causee. No one quantity determines which verb speakers accept;
each verb has its own set of reliable interactions. As in the model of Cao, Geiger, Kreiss, Icard
and Gerstenberg, the models are time-indexed (`TimeIndex`) and their agents play a
soft-optimality policy.

The paper's in-text judgments, its examples (3)–(11), are rows in
`Data/Examples/CaoWhiteLassiter2025.json`; the regression estimates stay in prose.

## Main statements

* `intentionDegree_eq_one_of_altCount_eq_zero`: an action with no alternative comes out maximally
  intentional, so the simplified INT drops Frankfurt's alternative-possibilities condition and
  ALT carries it instead
* `suf_eq_one_of_make`: where Nadathur and Lauer's *make* holds, SUF is 1 under every
  distribution over contexts
* `judgment_differs_make_force`: the paper's (8) separates *make* from *force*
* `ProbabilisticExample.suf_eq`: with an uncertain background, SUF is the background's
  probability rather than 0 or 1

## References

* [cao-white-lassiter-2025]
* [pearl-2019]
* [halpern-kleiman-weiner-2018]
* [frankfurt-1969]
* [nadathur-lauer-2020]
* [cao-geiger-kreiss-icard-gerstenberg-2023]
-/

@[expose] public section

namespace CaoWhiteLassiter2025

open CausalModel
open scoped ENNReal NNReal

/-! ### Soft-optimality policy

The paper's mechanism for agent moves (§2.1.1). The highest-utility move — minimax over the game
tree, with terminal utility `Winner × (EmptySpace + 1)` — is taken with probability `ρ + (1−ρ)/n`
and every other available move with `(1−ρ)/n`, for `n` the number of empty spaces. The skill
parameter interpolates between a uniformly random player ("assume that the players are infants"),
under which the paper's worked SUF contrast between two board states collapses, and a
deterministic professional. -/

section
variable {A : Type*} [MeasurableSpace A] (best : A) (ρ : ℝ≥0∞)

open MeasureTheory ProbabilityTheory

/-- A player of skill `ρ` plays the highest-utility move `best` with probability `ρ` and otherwise a
uniform random move. -/
noncomputable def softOptimalPolicy : Measure A :=
  (1 - ρ) • uniformOn Set.univ + ρ • Measure.dirac best

theorem isProbabilityMeasure_softOptimalPolicy [Finite A] [Nonempty A] (hρ : ρ ≤ 1) :
    IsProbabilityMeasure (softOptimalPolicy best ρ) :=
  ⟨by simp [softOptimalPolicy, tsub_add_cancel_of_le hρ]⟩

theorem softOptimalPolicy_zero : softOptimalPolicy best 0 = uniformOn Set.univ := by
  simp [softOptimalPolicy]

theorem softOptimalPolicy_one : softOptimalPolicy best 1 = Measure.dirac best := by
  simp [softOptimalPolicy]

variable [Fintype A] [MeasurableSingletonClass A]

@[simp] theorem softOptimalPolicy_singleton_best :
    softOptimalPolicy best ρ {best} = ρ + (1 - ρ) / Fintype.card A := by
  simp [softOptimalPolicy, uniformOn_univ_apply_singleton, div_eq_mul_inv, add_comm]

@[simp] theorem softOptimalPolicy_singleton_of_ne {a : A} (h : a ≠ best) :
    softOptimalPolicy best ρ {a} = (1 - ρ) / Fintype.card A := by
  simp [softOptimalPolicy, uniformOn_univ_apply_singleton, h.symm, div_eq_mul_inv]

end

/-! ### The ALT measure

ALT (§2.2) counts the alternative actions available to the causee, excluding the one actually
taken — `ALT(Y₁) = 5` at the paper's fig. 2a board state. `ALT = 0` is the Frankfurt-style
could-not-have-done-otherwise configuration. -/

section
variable {A : Type*} [Fintype A] (taken : A)

/-- The number of alternative actions available to the causee is the number of actions of
positive probability other than the one taken. -/
noncomputable def altCount [MeasurableSpace A] (μ : MeasureTheory.Measure A) : ℕ :=
  ({a | μ {a} ≠ 0} \ {taken}).ncard

theorem altCount_eq_zero_iff [MeasurableSpace A] (μ : MeasureTheory.Measure A) :
    altCount taken μ = 0 ↔ ∀ a ≠ taken, μ {a} = 0 := by
  rw [altCount, Set.ncard_eq_zero (Set.toFinite _), Set.sdiff_eq_empty,
    Set.subset_singleton_iff]
  exact forall_congr' fun b => not_imp_comm

/-! ### The INT measure

The paper's §2.3 displayed equation, a simplified [halpern-kleiman-weiner-2018] degree of
intention:

`INT(a) = Pr(A = a ∧ G) · u′(a) / Σ_{a′} Pr(A = a′ ∧ G) · u′(a′)`

"the probability that an action performed in a state will result in the desired outcome,
normalized by the probability of all alternative actions that would have resulted in the same
outcome", each term weighted by exponentiated utility `u′ = eᵘ`, the exponential serving only to
make the weights strictly positive. Here `pr a′` is the joint probability that the agent takes
`a′` and the goal results, and the weight is abstracted to any `w : A → ℝ≥0`; `modelIntention`
instantiates `pr` over a `SEM`.

The simplification costs the principle it is motivated by: [halpern-kleiman-weiner-2018] hold,
after [frankfurt-1969], that an action an agent could not have avoided is never intentional,
while under this measure such an action is maximally intentional, its sole goal-conducive
alternative being itself. It is ALT rather than INT that registers the paper's *made*/*forced*
contrast in (8). -/

variable (pr : A → ℝ≥0∞) (w : A → ℝ≥0) (a : A)

/-- The goal-weighted share of action `a` among all goal-conducive
    alternatives. -/
noncomputable def intentionDegree : ℝ≥0∞ :=
  (pr a * w a) / ∑ a', pr a' * w a'

theorem intentionDegree_le_one : intentionDegree pr w a ≤ 1 :=
  ENNReal.div_le_of_le_mul <| by
    simpa using Finset.single_le_sum (f := fun a' => pr a' * w a') (fun _ _ => zero_le)
      (Finset.mem_univ a)

theorem intentionDegree_eq_one_of_no_alternatives
    (h : ∀ a ≠ taken, pr a = 0) (h0 : pr taken ≠ 0) (hw : w taken ≠ 0)
    (htop : pr taken ≠ ∞) :
    intentionDegree pr w taken = 1 := by
  rw [intentionDegree, Finset.sum_eq_single_of_mem taken (Finset.mem_univ taken)
    fun a _ ha => by rw [h a ha, zero_mul]]
  exact ENNReal.div_self (mul_ne_zero h0 (ENNReal.coe_ne_zero.mpr hw))
    (ENNReal.mul_ne_top htop ENNReal.coe_ne_top)

/-- An agent who could not have done otherwise comes out maximally intentional, since the
simplified INT does not carry the alternative-possibilities condition; ALT is what separates
*made* from *forced*. -/
theorem intentionDegree_eq_one_of_altCount_eq_zero [MeasurableSpace A]
    (μ : MeasureTheory.Measure A) [MeasureTheory.IsFiniteMeasure μ]
    (hle : ∀ a, pr a ≤ μ {a}) (h : altCount taken μ = 0) (h0 : pr taken ≠ 0)
    (hw : w taken ≠ 0) : intentionDegree pr w taken = 1 :=
  intentionDegree_eq_one_of_no_alternatives taken pr w
    (fun a ha => le_zero_iff.mp ((altCount_eq_zero_iff taken μ).mp h a ha ▸ hle a))
    h0 hw (ne_top_of_le_ne_top (MeasureTheory.measure_ne_top μ _) (hle taken))

end

section Model

variable {U V : Type*} {α : V → Type*} [DecidableEq V] [MeasurableSpace U]
  (M : CausalModel U V α) [M.IsAcyclic] [∀ v, Nonempty (α v)]

/-- The paper's INT over a causal model instantiates `intentionDegree` with `pr a′` the
    probability, over contexts drawn from `ν`, that under the intervention `I` the action variable
    takes the value `a′` and the outcome satisfies the goal: the paper's
    `Pr((M,u⃗) ⊨ A = a⃗′ ∧ G = g⃗)`. -/
noncomputable def modelIntention (ν : MeasureTheory.Measure U) (I : ∀ v, Flat (α v))
    (act : V) [Fintype (α act)] (goal : Set (∀ v, α v)) (w : α act → ℝ≥0) (a : α act) : ℝ≥0∞ :=
  intentionDegree (fun a' ↦ ν {u | M.solve I u act = a' ∧ M.solve I u ∈ goal}) w a

/-- SUF, Pearl's probability of sufficiency ([pearl-2019]), is the probability, among the
    contexts drawn from `ν` in which the observation `obs` holds, that setting `c := x` makes
    `e = y`. -/
noncomputable def suf (ν : MeasureTheory.Measure U) (obs : ∀ v, Flat (α v)) (c : V) (x : α c)
    (e : V) (y : α e) : ℝ≥0∞ :=
  ProbabilityTheory.cond ν (M.contexts obs) {u | M.solve [c ← x] u e = y}

variable {M}

theorem suf_bot (ν : MeasureTheory.Measure U) [MeasureTheory.IsProbabilityMeasure ν] (c : V)
    (x : α c) (e : V) (y : α e) :
    suf M ν ⊥ c x e y = ν {u | M.solve [c ← x] u e = y} := by
  rw [suf, contexts_bot, ProbabilityTheory.cond_univ]

/-! ### Deterministic limit

With a certain context SUF collapses to a {0,1} indicator, and wherever Nadathur and Lauer's
categorical *make* holds of the empty background, SUF is 1 whatever the distribution over
contexts. The converse fails: a single context can make the intervention yield the effect without
the effect being settled by the strict development, so the categorical *make* semantics is
strictly stronger than maximal graded SUF. -/

open Classical in
theorem suf_dirac [MeasurableSingletonClass U] (u₀ : U) (c : V) (x : α c) (e : V) (y : α e) :
    suf M (MeasureTheory.Measure.dirac u₀) ⊥ c x e y =
      if M.solve [c ← x] u₀ e = y then 1 else 0 := by
  rw [suf_bot, MeasureTheory.Measure.dirac_apply, Set.indicator_apply]
  simp only [Set.mem_ofPred_eq, Pi.one_apply]

/-- Nadathur and Lauer's *make* entails maximal SUF. Whenever *make* holds of the empty
background, SUF is 1 under every distribution over contexts. -/
theorem suf_eq_one_of_make (ν : MeasureTheory.Measure U) [MeasureTheory.IsProbabilityMeasure ν]
    {u₀ : U} {c e : V} {x : α c} {y : α e} (h : NadathurLauer2020.Make M ⊥ u₀ c x e y) :
    suf M ν ⊥ c x e y = 1 := by
  have h' := h.1.2
  rw [Function.update_idem] at h'
  have hall : {u | M.solve [c ← x] u e = y} = Set.univ :=
    Set.eq_univ_of_forall h'.solve_eq_of_intervene
  rw [suf_bot, hall, MeasureTheory.measure_univ]

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

/-! ### The paper's judgment data

The in-text contrasts are rows in `Data.Examples.CaoWhiteLassiter2025`: the
non-interchangeability triplets (3)–(4), the gym gradability triplets (5)–(7), the
could-have-done-otherwise pair (8), the intent-denial continuations (9)–(10), and the
*make*/*let* sufficiency pair (11). -/

/-- The paper's (8) separates *make* from *force*. In one frame with a could-have-done-otherwise
continuation, *made* tolerates the continuation and *forced* resists it, a difference in the
causee's alternatives, which ALT measures. -/
theorem judgment_differs_make_force :
    Examples.cwl2025_ex8a.judgment ≠ Examples.cwl2025_ex8b.judgment := by decide

/-- The gym triplets (5)–(7) grade the stronger verbs against a constant *cause*. The same three
causing events leave *caused* acceptable throughout while *forced* switches, which is why the
account measures the causal relation rather than classifying it. -/
theorem gym_grades_stronger_verbs :
    Examples.cwl2025_ex5a.judgment = Examples.cwl2025_ex6a.judgment ∧
      Examples.cwl2025_ex6a.judgment = Examples.cwl2025_ex7a.judgment ∧
      Examples.cwl2025_ex5c.judgment ≠ Examples.cwl2025_ex7c.judgment := by decide

/-! ### A probabilistic model

SUF is a probability when the background is uncertain. In a model whose `effect` holds when the
`cause` and a background `noise` both do, and whose noise is true with probability `p`, setting
the cause makes the effect true with probability `p`, strictly between the 0 and 1 of the
categorical semantics. -/

namespace ProbabilisticExample

/-- The vertices are the cause, the background noise, and the effect. -/
inductive V | cause | noise | effect
  deriving DecidableEq, Fintype, Repr

/-- The effect reads the cause and the noise. -/
def edges : Finset (V × V) := {(.cause, .effect), (.noise, .effect)}

/-- The effect holds when the cause and the noise both do; the context settles the noise, and the
cause is off unless set. -/
def model : CausalModel Bool V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w, v) ∈ edges⟩
  eqn
    | .cause => fun _ _ ↦ false
    | .noise => fun u _ ↦ u
    | .effect => fun _ x ↦ x .cause && x .noise

instance : DecidableRel model.graph.Adj := fun w v ↦ inferInstanceAs (Decidable ((w, v) ∈ edges))

/-- The model is time-indexed in the sense of the paper's definition 1, with `cause` and `noise`
at step 0 and `effect` at step 1. -/
def timeIndex : TimeIndex model where
  time := fun | .effect => 1 | _ => 0
  parent_succ := by decide

instance : model.IsAcyclic := timeIndex.isAcyclic

/-- In the background the noise is true with probability `p`. -/
noncomputable def background (p : ℝ≥0∞) : MeasureTheory.Measure Bool :=
  p • MeasureTheory.Measure.dirac true + (1 - p) • MeasureTheory.Measure.dirac false

theorem effect_iff (b : Bool) :
    model.solve [.cause ← true] b .effect = true ↔ b = true := by
  cases b <;> decide

/-- SUF is the probability of the noise, graded as the paper's measure requires. -/
theorem suf_eq {p : ℝ≥0∞} (hp : p ≤ 1) :
    suf model (background p) ⊥ .cause true .effect true = p := by
  have : MeasureTheory.IsProbabilityMeasure (background p) :=
    ⟨by simp [background, add_tsub_cancel_of_le hp]⟩
  have h : {b : Bool | model.solve [.cause ← true] b .effect = true} = {true} :=
    Set.ext fun b ↦ effect_iff b
  rw [suf_bot, h]
  simp [background]

end ProbabilisticExample

end CaoWhiteLassiter2025
