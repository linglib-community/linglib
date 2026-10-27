module

public import Linglib.Logic.Trivalent.Probability
public import Linglib.Logic.Trivalent.Propositional
public import Studies.Adams1975

/-!
# Égré, Rossi and Sprenger (2026): Probability for Trivalent Conditionals

Égré, Rossi and Sprenger give a unified truth-conditional and probabilistic theory of indicative
conditionals on Cooper's trivalent tables: the conditional asserts its consequent where its
antecedent is non-false, conjunction and disjunction skip the void value, and the probability of a
sentence is the weight of its truth against that of its truth and falsity together. The semantics
validates a Reduction Theorem, every compound of conditionals is equivalent to a simple
conditional, and the probability function validates Adams's Thesis and, through Import-Export,
Stalnaker's Thesis in full generality, escaping the triviality results by giving up classical
conjunction and the Product Rule.

## Implementation notes

* The language is the shared `Trivalent.Formula` and a Cooper valuation is its evaluation by
  `Trivalent.Connectives.cooper` on a Boolean model, so the paper's `⊤` and `⊥` are the formulas
  `p ∨ ¬p` and `p ∧ ¬p` of an atom.
* Worlds carry a classical valuation of the atoms through a map `t : W → ι → Bool`, after the
  paper's identification of worlds with atom-classical valuations; a formula's value at a world
  is a `SignType`, and its probability is `Trivalent.prob`, which builds in the paper's All Void
  convention. With that convention axiom 3′ holds unconditionally. The second principle carries
  its own all-void exception, but the third principle and axioms 2′ and 5′ also need the
  relevant sentence to be non-void with positive credence, which the printed versions omit;
  `additivity_all_void`, `axiom2'_all_void` and `additivity_cond_all_void` are the
  counterexamples.
* The logic C is defined by its trivalent characterization, preservation of LP-designated values,
  which [egre-rossi-sprenger-2025] prove equivalent to preservation of probability 1; the
  equivalence is `cEntails_iff_forall_prob`, proved over the valuation space itself.
* The die and coin examples are stated against `uniformOn Set.univ` and computed by counting
  worlds through `Trivalent.prob_uniformOn_univ`.

## TODO

* Theorem 2, the representation of the uncertain logic U in Adams's p-validity through the
  Reduction Theorem, and Propositions 3 and 4, its trivalent characterization and conservativity.
  With `pEntails_iff_prob` both sides are conditions on trivalent probability; what remains is
  Adams's equivalence of p-entailment with the uncertainty-sum criterion, open in `Adams1975`.
* Theorem 4, trivalent conditionalization as f-divergence minimization.
* McGee's adequacy conditions C2–C8 for the conditional probability `p(A → B)`.

## References

* [egre-rossi-sprenger-2026a]
* [egre-rossi-sprenger-2025]
* [cooper-1968]
* [de-finetti-1936]
* [adams-1965]
* [adams-1975]
* [lewis-1976]
* [mcgee-1989]
* [goldstein-santorio-2021]
* [santorio-wellwood-2023]
* [edgington-1991]
-/

@[expose] public section

namespace EgreRossiSprenger2026a

open SignType Trivalent MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### Cooper's laws at the value level

The laws of Proposition 1 are pointwise facts about `SignType.condAssert` at the LP standard and
the Belnap connectives, each with the classicality hypotheses the paper gives it. -/

section ValueLaws

variable {a b c d : SignType}

theorem condAssert_lp_meetBelnap_left :
    condAssert .lp (meetBelnap a b) c = condAssert .lp (a ⊓ b) c :=
  condAssert_congr_left (by simp) c

-- Proposition 1
theorem meetBelnap_condAssert_condAssert (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    meetBelnap (condAssert .lp a b) (condAssert .lp c d) =
      condAssert .lp (joinBelnap a c)
        (meetBelnap (joinBelnap (-a) b) (joinBelnap (-c) d)) := by
  revert ha hb hc hd; cases a <;> cases b <;> cases c <;> cases d <;> decide

-- Proposition 1
theorem joinBelnap_condAssert_condAssert (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    joinBelnap (condAssert .lp a b) (condAssert .lp c d) =
      condAssert .lp (joinBelnap a c) (joinBelnap (meetBelnap a b) (meetBelnap c d)) := by
  revert ha hb hc hd; cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Conjunction does not extend to trivalent conjuncts. -/
theorem conjunction_needs_boolean :
    ¬ ∀ a b c d : SignType,
      meetBelnap (condAssert .lp a b) (condAssert .lp c d) =
        condAssert .lp (joinBelnap a c)
          (meetBelnap (joinBelnap (-a) b) (joinBelnap (-c) d)) := by
  decide

/-- With Strong Kleene conjunction in place of Cooper's, Conjunction fails already for classical
values (footnote 6). -/
theorem sk_fails_conjunction :
    ¬ ∀ a b c d : SignType, a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
      condAssert .lp a b ⊓ condAssert .lp c d =
        condAssert .lp (joinBelnap a c)
          (meetBelnap (joinBelnap (-a) b) (joinBelnap (-c) d)) := by
  decide

-- Proposition 1
theorem condAssert_condAssert_material (hb : b ≠ 0) :
    condAssert .lp (condAssert .lp a b) c = condAssert .lp (joinBelnap (-a) b) c := by
  revert hb; cases a <;> cases b <;> cases c <;> decide

theorem left_nesting_needs_boolean :
    ¬ ∀ a b c : SignType,
      condAssert .lp (condAssert .lp a b) c = condAssert .lp (joinBelnap (-a) b) c := by
  decide

-- footnote 6
theorem condAssert_k3_left_eq_nested (ha : a ≠ 0) (hb : b ≠ 0) :
    condAssert .k3 (condAssert .k3 a b) c = condAssert .k3 a (condAssert .k3 b c) := by
  revert ha hb; cases a <;> cases b <;> cases c <;> decide

theorem condAssert_k3_fails_left_nesting :
    ¬ ∀ a b c : SignType, b ≠ 0 →
      condAssert .k3 (condAssert .k3 a b) c = condAssert .k3 (joinBelnap (-a) b) c := by
  decide

theorem condAssert_condAssert_condAssert (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    condAssert .lp (condAssert .lp a b) (condAssert .lp c d) =
      condAssert .lp (meetBelnap (joinBelnap (-a) b) c) d := by
  revert ha hb hc hd; cases a <;> cases b <;> cases c <;> cases d <;> decide

-- footnote 3
theorem zero_le_sup_condAssert (d : Trivalent.Designation) (a b : SignType) :
    0 ≤ condAssert d a b ⊔ condAssert d b a := by
  cases d <;> cases a <;> cases b <;> decide

-- footnote 11
theorem meetBelnap_condAssert_of_false (b : SignType) :
    meetBelnap (condAssert .lp (-1) b) 1 = 1 :=
  rfl

end ValueLaws

/-! ### Cooper valuations

The language `L→` is `Trivalent.Formula`, atoms closed under `¬`, `∧`, `∨` and `→`, and a Cooper
valuation (Definition 1) evaluates it by `Connectives.cooper` on the Boolean model of a classical
valuation of the atoms. The paper's `⊤` and `⊥` abbreviate a classical tautology and
contradiction. -/

variable {ι : Type*}

/-- The Cooper valuation induced by a classical valuation of the atoms (Definition 1), in which
negation is Kleene's, conjunction and disjunction skip the void value, and the conditional asserts
its consequent where its antecedent is non-false. -/
def cooperEval (v : ι → Bool) (φ : Formula ι) : SignType := φ.eval .cooper (Model.ofBool v)

/-- `⊤`, the classical tautology `p ∨ ¬p`. -/
def top (i : ι) : Formula ι := .disj (.atom i) (.neg (.atom i))

/-- `⊥`, the classical contradiction `p ∧ ¬p`. -/
def bot (i : ι) : Formula ι := .conj (.atom i) (.neg (.atom i))

/-- The material conditional `¬φ ∨ ψ`, with Cooper's disjunction. -/
def material (φ ψ : Formula ι) : Formula ι := .disj (.neg φ) ψ

section CooperEval

variable {v : ι → Bool}

@[simp] theorem cooperEval_atom (i : ι) : cooperEval v (.atom i) = ofProp (v i) := rfl

@[simp] theorem cooperEval_neg (φ : Formula ι) : cooperEval v (.neg φ) = -cooperEval v φ := rfl

@[simp] theorem cooperEval_conj (φ ψ : Formula ι) :
    cooperEval v (.conj φ ψ) = meetBelnap (cooperEval v φ) (cooperEval v ψ) := rfl

@[simp] theorem cooperEval_disj (φ ψ : Formula ι) :
    cooperEval v (.disj φ ψ) = joinBelnap (cooperEval v φ) (cooperEval v ψ) := rfl

@[simp] theorem cooperEval_cond (φ ψ : Formula ι) :
    cooperEval v (.cond φ ψ) = condAssert .lp (cooperEval v φ) (cooperEval v ψ) := rfl

@[simp] theorem cooperEval_material (φ ψ : Formula ι) :
    cooperEval v (material φ ψ) = joinBelnap (-cooperEval v φ) (cooperEval v ψ) := rfl

@[simp] theorem cooperEval_top (i : ι) : cooperEval v (top i) = 1 := by
  simp only [top, cooperEval_disj, cooperEval_neg, cooperEval_atom]
  cases v i <;> rfl

@[simp] theorem cooperEval_bot (i : ι) : cooperEval v (bot i) = -1 := by
  simp only [bot, cooperEval_conj, cooperEval_neg, cooperEval_atom]
  cases v i <;> rfl

end CooperEval

/-- Two formulas are semantically equivalent when every Cooper valuation gives them the same value
(Definition 2). -/
def CooperEquiv (φ ψ : Formula ι) : Prop := ∀ v : ι → Bool, cooperEval v φ = cooperEval v ψ

/-- The conditional-free fragment `L`. -/
def NoCond : Formula ι → Prop
  | .atom _ => True
  | .neg φ => NoCond φ
  | .conj φ ψ | .disj φ ψ => NoCond φ ∧ NoCond ψ
  | .cond _ _ => False

theorem NoCond.cooperEval_ne_zero {φ : Formula ι} (h : NoCond φ) (v : ι → Bool) :
    cooperEval v φ ≠ 0 := by
  induction φ with
  | atom i => simp
  | neg φ ih => simpa using ih h
  | conj φ ψ ihφ ihψ =>
      rw [cooperEval_conj, Ne, meetBelnap_eq_zero_iff]
      exact fun hc ↦ ihφ h.1 hc.1
  | disj φ ψ ihφ ihψ =>
      rw [cooperEval_disj, Ne, joinBelnap_eq_zero_iff]
      exact fun hc ↦ ihφ h.1 hc.1
  | cond φ ψ _ _ => exact h.elim

/-! ### Proposition 1: the five equivalences -/

/-- Negating a conditional negates its consequent, for arbitrary formulas (**Negation
Commutation**). -/
theorem equiv_neg_cond (φ ψ : Formula ι) : CooperEquiv (.neg (.cond φ ψ)) (.cond φ (.neg ψ)) :=
  fun _ ↦ neg_condAssert

/-- **Import-Export**, for arbitrary formulas. -/
theorem equiv_cond_cond (φ ψ χ : Formula ι) :
    CooperEquiv (.cond φ (.cond ψ χ)) (.cond (.conj φ ψ) χ) := fun v ↦ by
  rw [cooperEval_cond, cooperEval_cond, cooperEval_cond, condAssert_condAssert, cooperEval_conj,
    condAssert_lp_meetBelnap_left]

/-- **Conjunction**, for conditional-free components. -/
theorem equiv_conj_cond {φ ψ χ ξ : Formula ι} (hφ : NoCond φ) (hψ : NoCond ψ) (hχ : NoCond χ)
    (hξ : NoCond ξ) :
    CooperEquiv (.conj (.cond φ ψ) (.cond χ ξ))
      (.cond (.disj φ χ) (.conj (material φ ψ) (material χ ξ))) := fun v ↦ by
  simpa using meetBelnap_condAssert_condAssert (hφ.cooperEval_ne_zero v)
    (hψ.cooperEval_ne_zero v) (hχ.cooperEval_ne_zero v) (hξ.cooperEval_ne_zero v)

/-- **Disjunction**, for conditional-free components. -/
theorem equiv_disj_cond {φ ψ χ ξ : Formula ι} (hφ : NoCond φ) (hψ : NoCond ψ) (hχ : NoCond χ)
    (hξ : NoCond ξ) :
    CooperEquiv (.disj (.cond φ ψ) (.cond χ ξ))
      (.cond (.disj φ χ) (.disj (.conj φ ψ) (.conj χ ξ))) := fun v ↦ by
  simpa using joinBelnap_condAssert_condAssert (hφ.cooperEval_ne_zero v)
    (hψ.cooperEval_ne_zero v) (hχ.cooperEval_ne_zero v) (hξ.cooperEval_ne_zero v)

/-- **Left-Nesting**, for a conditional-free inner consequent: in antecedent position an
indicative and its material conditional express the same supposition. -/
theorem equiv_cond_left {ψ : Formula ι} (hψ : NoCond ψ) (φ χ : Formula ι) :
    CooperEquiv (.cond (.cond φ ψ) χ) (.cond (material φ ψ) χ) := fun v ↦ by
  simpa using condAssert_condAssert_material (b := cooperEval v ψ) (hψ.cooperEval_ne_zero v)

/-! ### The Reduction Theorem -/

/-- The conditional-free antecedent and consequent of the simple conditional equivalent to a
formula, by the appendix's recursion; an atom `p` is `⊤ → p`. -/
def flat : Formula ι → Formula ι × Formula ι
  | .atom i => (top i, .atom i)
  | .neg φ => ((flat φ).1, .neg (flat φ).2)
  | .conj φ ψ =>
      (.disj (flat φ).1 (flat ψ).1,
        .conj (material (flat φ).1 (flat φ).2) (material (flat ψ).1 (flat ψ).2))
  | .disj φ ψ =>
      (.disj (flat φ).1 (flat ψ).1,
        .disj (.conj (flat φ).1 (flat φ).2) (.conj (flat ψ).1 (flat ψ).2))
  | .cond φ ψ => (.conj (material (flat φ).1 (flat φ).2) (flat ψ).1, (flat ψ).2)

theorem noCond_flat (φ : Formula ι) : NoCond (flat φ).1 ∧ NoCond (flat φ).2 := by
  induction φ with
  | atom i => exact ⟨⟨trivial, trivial⟩, trivial⟩
  | neg φ ih => exact ih
  | conj φ ψ ihφ ihψ => exact ⟨⟨ihφ.1, ihψ.1⟩, ⟨ihφ.1, ihφ.2⟩, ihψ.1, ihψ.2⟩
  | disj φ ψ ihφ ihψ => exact ⟨⟨ihφ.1, ihψ.1⟩, ⟨ihφ.1, ihφ.2⟩, ihψ.1, ihψ.2⟩
  | cond φ ψ ihφ ihψ => exact ⟨⟨⟨ihφ.1, ihφ.2⟩, ihψ.1⟩, ihψ.2⟩

/-- Every formula is semantically equivalent to the simple conditional `flat` computes (**the
Reduction Theorem**, Theorem 1). -/
theorem cooperEval_flat (φ : Formula ι) (v : ι → Bool) :
    cooperEval v φ = cooperEval v (.cond (flat φ).1 (flat φ).2) := by
  induction φ with
  | atom i => simp [flat]
  | neg φ ih => rw [cooperEval_neg, ih, flat]; exact neg_condAssert
  | conj φ ψ ihφ ihψ =>
      have hφ := noCond_flat φ
      have hψ := noCond_flat ψ
      rw [cooperEval_conj, ihφ, ihψ, flat]
      simpa using meetBelnap_condAssert_condAssert (hφ.1.cooperEval_ne_zero v)
        (hφ.2.cooperEval_ne_zero v) (hψ.1.cooperEval_ne_zero v) (hψ.2.cooperEval_ne_zero v)
  | disj φ ψ ihφ ihψ =>
      have hφ := noCond_flat φ
      have hψ := noCond_flat ψ
      rw [cooperEval_disj, ihφ, ihψ, flat]
      simpa using joinBelnap_condAssert_condAssert (hφ.1.cooperEval_ne_zero v)
        (hφ.2.cooperEval_ne_zero v) (hψ.1.cooperEval_ne_zero v) (hψ.2.cooperEval_ne_zero v)
  | cond φ ψ ihφ ihψ =>
      have hφ := noCond_flat φ
      have hψ := noCond_flat ψ
      rw [cooperEval_cond, ihφ, ihψ, flat]
      simpa using condAssert_condAssert_condAssert (hφ.1.cooperEval_ne_zero v)
        (hφ.2.cooperEval_ne_zero v) (hψ.1.cooperEval_ne_zero v) (hψ.2.cooperEval_ne_zero v)

-- Theorem 1
theorem reduction (φ : Formula ι) :
    ∃ A B : Formula ι, NoCond A ∧ NoCond B ∧ CooperEquiv φ (.cond A B) :=
  ⟨_, _, (noCond_flat φ).1, (noCond_flat φ).2, cooperEval_flat φ⟩

/-! ### The logic C of certain inference

The paper takes from [egre-rossi-sprenger-2025] the logic C, preservation of probability 1, and
its trivalent characterization as preservation of the LP-designated values. Here the
characterization is the definition and the probabilistic description is the theorem. -/

/-- An inference is certain when every Cooper valuation designating the premises designates the
conclusion. -/
def CEntails (Γ : List (Formula ι)) (B : Formula ι) : Prop :=
  ∀ v : ι → Bool, (∀ A ∈ Γ, 0 ≤ cooperEval v A) → 0 ≤ cooperEval v B

instance [Fintype ι] [DecidableEq ι] (Γ : List (Formula ι)) (B : Formula ι) :
    Decidable (CEntails Γ B) :=
  inferInstanceAs (Decidable (∀ v : ι → Bool, (∀ A ∈ Γ, 0 ≤ cooperEval v A) → 0 ≤ cooperEval v B))

/-- Certain inference preserves probability 1 under every credence over the valuations, and
conversely (Definition 4 and [egre-rossi-sprenger-2025]'s characterization). -/
theorem cEntails_iff_forall_prob [MeasurableSpace (ι → Bool)]
    [DiscreteMeasurableSpace (ι → Bool)] {Γ : List (Formula ι)} {B : Formula ι} :
    CEntails Γ B ↔ ∀ μ : Measure (ι → Bool), IsProbabilityMeasure μ →
      (∀ A ∈ Γ, Trivalent.prob μ (cooperEval · A) = 1) → Trivalent.prob μ (cooperEval · B) = 1 := by
  constructor
  · intro h μ hμ hΓ
    rw [Trivalent.prob_eq_one_iff]
    refine measure_mono_null (fun v hv ↦ ?_) <|
      (measure_biUnion_null_iff Γ.finite_toSet.countable).2 fun A hA ↦
        Trivalent.prob_eq_one_iff.1 (hΓ A hA)
    rw [mem_negSupport] at hv
    by_contra hnot
    simp only [Set.mem_iUnion, mem_negSupport, not_exists] at hnot
    have h0 := h v fun A hA ↦ SignType.nonneg_iff_ne_neg_one.2 (hnot A hA)
    rw [hv] at h0
    exact absurd h0 (by decide)
  · intro h v hΓ
    have := h (Measure.dirac v) inferInstance fun A hA ↦
      (Trivalent.prob_dirac_eq_one_iff (p := (cooperEval · A))).2 (hΓ A hA)
    exact (Trivalent.prob_dirac_eq_one_iff (p := (cooperEval · B))).1 this

/-! ### Trivalent probability over a world space -/

section Probability

variable {W : Type*} [MeasurableSpace W]

/-- The trivalent proposition a formula expresses over a world space whose worlds `t` maps to
classical valuations of the atoms. -/
abbrev value (t : W → ι → Bool) (φ : Formula ι) : W → SignType := fun w ↦ cooperEval (t w) φ

variable {μ : Measure W} {t : W → ι → Bool}

theorem prob_value_top [IsProbabilityMeasure μ] (i : ι) :
    Trivalent.prob μ (value t (top i)) = 1 := by
  have : value t (top i) = fun w ↦ ofProp True := funext fun w ↦ cooperEval_top i
  rw [this, Trivalent.prob_ofProp]
  simp

theorem prob_value_bot [IsProbabilityMeasure μ] (i : ι) :
    Trivalent.prob μ (value t (bot i)) = 0 := by
  have : value t (bot i) = fun w ↦ ofProp False := funext fun w ↦ cooperEval_bot i
  rw [this, Trivalent.prob_ofProp]
  simp

/-- The third principle (`prob_value_disj` below) fails without its properness clause, which the
printed axiom omits: a
certainly void disjunction of certainly void disjuncts has probability 1 by the All Void
convention, while the disjuncts' probabilities sum to 2. -/
theorem additivity_all_void (μ : Measure W) (t : W → ι → Bool) (i : ι) :
    posSupport (value t (.cond (bot i) (top i))) = ∅ ∧
      Trivalent.prob μ (value t (.disj (.cond (bot i) (top i)) (.cond (bot i) (top i)))) = 1 ∧
        Trivalent.prob μ (value t (.cond (bot i) (top i))) +
          Trivalent.prob μ (value t (.cond (bot i) (top i))) = 2 := by
  have hA : value t (.cond (bot i) (top i)) = fun _ ↦ 0 := funext fun w ↦ by simp
  have hD : value t (.disj (.cond (bot i) (top i)) (.cond (bot i) (top i))) = fun _ ↦ 0 :=
    funext fun w ↦ by simp
  refine ⟨by rw [hA]; ext w; simp, ?_, ?_⟩
  · rw [hD, Trivalent.prob_of_measure_support_eq_zero (by simp)]
  · rw [hA, Trivalent.prob_of_measure_support_eq_zero (by simp), one_add_one_eq_two]

/-! ### Conditional probability and Stalnaker's Thesis -/

/-- Axiom 2′ fails as printed. C refutes `⊥ → ⊤` and makes `⊤` certain, yet the conditional
probability of `⊥ → ⊤` given `⊤` is 1 by the All Void convention, not 0. -/
theorem axiom2'_all_void (μ : Measure W) (t : W → ι → Bool) (i : ι) :
    CEntails [] (.neg (.cond (bot i) (top i))) ∧ CEntails [] (top i) ∧
      Trivalent.prob μ (value t (.cond (top i) (.cond (bot i) (top i)))) = 1 := by
  refine ⟨fun v _ ↦ by simp, fun v _ ↦ by simp, ?_⟩
  have : value t (.cond (top i) (.cond (bot i) (top i))) = fun _ ↦ 0 := funext fun w ↦ by simp
  rw [this, Trivalent.prob_of_measure_support_eq_zero (by simp)]

/-- Antecedents equivalent in C give the same conditional probabilities (Left Logical Equivalence,
axiom 4′), which is also Proposition 5 on updating. -/
theorem prob_cond_congr_left {A A' : Formula ι} (h₁ : CEntails [A] A') (h₂ : CEntails [A'] A)
    (C : Formula ι) :
    Trivalent.prob μ (value t (.cond A C)) = Trivalent.prob μ (value t (.cond A' C)) := by
  have : value t (.cond A C) = value t (.cond A' C) := by
    funext w
    simp only [cooperEval_cond]
    exact condAssert_congr_left
      ⟨fun h ↦ h₁ (t w) (by simpa using h), fun h ↦ h₂ (t w) (by simpa using h)⟩ _
  rw [this]

/-- The conditional probability of `B → C` given `A` is that of `C` given `A ∧ B` (Stalnaker's
Thesis, Theorem 3). -/
theorem stalnaker_thesis (A B C : Formula ι) :
    Trivalent.prob μ (value t (.cond A (.cond B C))) =
      Trivalent.prob μ (value t (.cond (.conj A B) C)) := by
  rw [show value t (.cond A (.cond B C)) = value t (.cond (.conj A B) C) from
    funext fun w ↦ equiv_cond_cond A B C (t w)]

theorem designated_cond_iff_material {A B : Formula ι} (hA : NoCond A) (hB : NoCond B)
    (v : ι → Bool) : 0 ≤ cooperEval v (.cond A B) ↔ 0 ≤ cooperEval v (material A B) := by
  have ha := hA.cooperEval_ne_zero v
  have hb := hB.cooperEval_ne_zero v
  rw [cooperEval_cond, cooperEval_material]
  revert ha hb
  cases cooperEval v A <;> cases cooperEval v B <;> decide

/-- Learning `A → B` is learning the material conditional `A ⊃ B`, for conditional-free `A` and `B`
(**Updating on Simple Conditionals**, Proposition 6). -/
theorem prob_cond_material_eq {A B : Formula ι} (hA : NoCond A) (hB : NoCond B) (H : Formula ι) :
    Trivalent.prob μ (value t (.cond (.cond A B) H)) =
      Trivalent.prob μ (value t (.cond (material A B) H)) :=
  prob_cond_congr_left
    (fun v h ↦ (designated_cond_iff_material hA hB v).1 (by simpa using h))
    (fun v h ↦ (designated_cond_iff_material hA hB v).2 (by simpa using h)) H

namespace AllVoid

/-! The model refuting the printed 5′: three atomic conditionals, pairwise constrained so that
conditions (ii) and (iii) hold at every valuation, read at the single all-false world. -/

/-- `p → q`. -/
def A : Formula (Fin 4) := .cond (.atom 0) (.atom 1)

/-- `p → ¬q`, so that `A ∧ B` is never true and condition (ii) holds globally. -/
def B : Formula (Fin 4) := .cond (.atom 0) (.neg (.atom 1))

/-- `r → s`, designated but void at the all-false world. -/
def C : Formula (Fin 4) := .cond (.atom 2) (.atom 3)

/-- The single world, carrying the all-false valuation. -/
def assign : Unit → Fin 4 → Bool := fun _ _ ↦ false

end AllVoid

/-- With credence concentrated where both disjuncts are void, All Void makes all three conditional
probabilities 1, so Axiom 5′ fails as printed. -/
theorem additivity_cond_all_void :
    CEntails [AllVoid.C] (.neg (.conj AllVoid.A AllVoid.B)) ∧
      ¬ CEntails [AllVoid.C] (.conj AllVoid.A AllVoid.B) ∧
      (∀ v, 0 ≤ cooperEval v AllVoid.C →
        (cooperEval v AllVoid.A = 0 ↔ cooperEval v AllVoid.B = 0)) ∧
      Measure.dirac () {w : Unit | 0 ≤ value AllVoid.assign AllVoid.C w} ≠ 0 ∧
      Trivalent.prob (Measure.dirac ())
        (value AllVoid.assign (.cond AllVoid.C (.disj AllVoid.A AllVoid.B))) = 1 ∧
      Trivalent.prob (Measure.dirac ()) (value AllVoid.assign (.cond AllVoid.C AllVoid.A)) +
        Trivalent.prob (Measure.dirac ())
          (value AllVoid.assign (.cond AllVoid.C AllVoid.B)) = 2 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [show {w : Unit | 0 ≤ value AllVoid.assign AllVoid.C w} = Set.univ from
      Set.eq_univ_of_forall fun w ↦ by cases w; decide]
    simp
  · rw [show value AllVoid.assign (.cond AllVoid.C (.disj AllVoid.A AllVoid.B)) = fun _ ↦ 0
        from rfl,
      Trivalent.prob_of_measure_support_eq_zero (by simp)]
  · rw [show value AllVoid.assign (.cond AllVoid.C AllVoid.A) = fun _ ↦ 0 from rfl,
      show value AllVoid.assign (.cond AllVoid.C AllVoid.B) = fun _ ↦ 0 from rfl,
      Trivalent.prob_of_measure_support_eq_zero (by simp), one_add_one_eq_two]

variable [DiscreteMeasurableSpace W]

/-! ### The principles under a live defined region

The remaining principles divide credence by the weight of the defined region, so they read the
measure of explicit sets and hold under the discrete σ-algebra of the paper's finite models. -/

/-- Negation complements probability unless the sentence is void almost surely, the second
principle with its printed exception. -/
theorem prob_value_neg [IsFiniteMeasure μ] {φ : Formula ι}
    (h : μ (Function.support (value t φ)) ≠ 0) :
    Trivalent.prob μ (value t (.neg φ)) = 1 - Trivalent.prob μ (value t φ) :=
  Trivalent.prob_neg h

/-- Disjuncts that are never true together and take classical values in the same worlds add, when
the common defined region has positive credence (the third principle). -/
theorem prob_value_disj {φ ψ : Formula ι}
    (hsupp : Function.support (value t φ) = Function.support (value t ψ))
    (hdisj : Disjoint (posSupport (value t φ)) (posSupport (value t ψ)))
    (h : μ (Function.support (value t φ)) ≠ 0) :
    Trivalent.prob μ (value t (.disj φ ψ)) =
      Trivalent.prob μ (value t φ) + Trivalent.prob μ (value t ψ) :=
  Trivalent.prob_joinBelnap hsupp hdisj h

/-- A conditional certain in C has conditional probability 1 (axiom 3′), with no properness
needed, since the All Void convention points the right way here. -/
theorem prob_cond_eq_one_of_cEntails [IsFiniteMeasure μ] {A B : Formula ι}
    (h : CEntails [A] B) :
    Trivalent.prob μ (value t (.cond A B)) = 1 := by
  rw [Trivalent.prob_eq_one_iff]
  convert measure_empty (μ := μ)
  ext w
  simp only [mem_negSupport, value, cooperEval_cond, condAssert_eq_neg_one_iff,
    Trivalent.Designation.threshold_lp, Set.mem_empty_iff_false, iff_false, not_and]
  intro hw hB
  have h0 := h (t w) fun X hX ↦ by rw [List.mem_singleton] at hX; exact hX ▸ hw
  rw [hB] at h0
  exact absurd h0 (by decide)

theorem prob_cond_eq_zero_of_cEntails_neg {A B : Formula ι} (h : CEntails [] (.neg B))
    (hproper : μ (Function.support (value t (.cond A B))) ≠ 0) :
    Trivalent.prob μ (value t (.cond A B)) = 0 := by
  rw [Trivalent.prob_eq_div_measure_support hproper]
  convert ENNReal.zero_div
  convert measure_empty (μ := μ)
  ext w
  rw [mem_posSupport]
  simp only [value, cooperEval_cond, condAssert_eq_one_iff, Set.mem_empty_iff_false, iff_false,
    not_and]
  intro _ hB
  have := h (t w) (by simp)
  rw [cooperEval_neg, hB] at this
  exact absurd this (by decide)

/-- Trivalent Additivity (axiom 5′) holds under conditions (ii) and (iii) in their
designated-value form together with a live defined region for `C → A`, the properness the
printed version lacks. -/
theorem prob_cond_disj {A B C : Formula ι} (hii : CEntails [C] (.neg (.conj A B)))
    (hiii : ∀ v, 0 ≤ cooperEval v C → (cooperEval v A = 0 ↔ cooperEval v B = 0))
    (hproper : μ (Function.support (value t (.cond C A))) ≠ 0) :
    Trivalent.prob μ (value t (.cond C (.disj A B))) =
      Trivalent.prob μ (value t (.cond C A)) + Trivalent.prob μ (value t (.cond C B)) := by
  have hval : value t (.cond C (.disj A B)) =
      fun w ↦ joinBelnap (value t (.cond C A) w) (value t (.cond C B) w) := by
    funext w
    exact condAssert_joinBelnap
  have hsupp : Function.support (value t (.cond C A)) =
      Function.support (value t (.cond C B)) := by
    ext w
    simp only [Function.mem_support, Ne, value, cooperEval_cond, condAssert_eq_zero_iff,
      Trivalent.Designation.threshold_lp]
    by_cases hC : 0 ≤ cooperEval (t w) C
    · simp [hC, hiii (t w) hC]
    · simp [hC]
  have hdisj : Disjoint (posSupport (value t (.cond C A))) (posSupport (value t (.cond C B))) := by
    rw [Set.disjoint_left]
    intro w hwA hwB
    rw [mem_posSupport] at hwA hwB
    simp only [value, cooperEval_cond, condAssert_eq_one_iff, Trivalent.Designation.threshold_lp]
      at hwA hwB
    have := hii (t w) (by simpa using hwA.1)
    rw [cooperEval_neg, cooperEval_conj, hwA.2, hwB.2] at this
    exact absurd this (by decide)
  rw [hval, Trivalent.prob_joinBelnap hsupp hdisj hproper]

end Probability

/-! ### Adams's conditionals are conditional events

[adams-1975] gives *if `A` then `B`* the conditional probability of `B` given `A` and no truth
conditions. On the trivalent semantics his formula denotes Cooper's simple conditional, the
conditional event of its consequent on its antecedent, whose trivalent probability is his
conditional probability; his proper assignments are those under which no formula is void almost
surely; and his simple conditionals exhaust the trivalent propositions, the semantic content of
the Reduction Theorem. -/

section Adams

open Classical

variable {W : Type*}

/-- The trivalent proposition an [adams-1975] formula denotes, Cooper's conditional of its
consequent on its antecedent. -/
noncomputable def ofAdams (φ : Adams1975.Formula W) : W → SignType :=
  fun w ↦ condAssert .lp (ofProp (w ∈ φ.ante)) (ofProp (w ∈ φ.cons))

theorem ofAdams_eq_indicator (φ : Adams1975.Formula W) :
    ofAdams φ = φ.ante.indicator fun w ↦ ofProp (w ∈ φ.cons) := by
  funext w
  by_cases h : w ∈ φ.ante <;> simp [ofAdams, h]

@[simp] theorem support_ofAdams (φ : Adams1975.Formula W) :
    Function.support (ofAdams φ) = φ.ante := by
  rw [ofAdams_eq_indicator]
  simp [Set.support_indicator]

/-- Adams's simple conditionals exhaust the trivalent propositions, each being the conditional
event of its truth on its definedness. -/
theorem exists_ofAdams_eq (p : W → SignType) : ∃ φ : Adams1975.Formula W, ofAdams φ = p := by
  refine ⟨⟨Function.support p, posSupport p⟩, ?_⟩
  rw [ofAdams_eq_indicator]
  conv_rhs => rw [← indicator_support_ofProp_eq_one p]
  congr 1
  funext w
  congr 1

/-- Two Adams formulas denote the same proposition exactly when they have the same antecedent and
agree on it, de Finetti's identity of conditional events. -/
theorem ofAdams_eq_ofAdams_iff {φ ψ : Adams1975.Formula W} :
    ofAdams φ = ofAdams ψ ↔ φ.ante = ψ.ante ∧ φ.ante ∩ φ.cons = ψ.ante ∩ ψ.cons := by
  rw [ofAdams_eq_indicator, ofAdams_eq_indicator, indicator_ofProp_eq_indicator_ofProp_iff]
  rfl

theorem value_cond_eq_ofAdams {A B : Formula ι} (hA : NoCond A) (hB : NoCond B)
    (t : W → ι → Bool) :
    value t (.cond A B) = ofAdams ⟨{w | cooperEval (t w) A = 1}, {w | cooperEval (t w) B = 1}⟩ := by
  funext w
  simp only [value, cooperEval_cond, ofAdams, Set.mem_ofPred_eq]
  congr 1
  · convert (ofProp_eq_one_of_ne_zero (hA.cooperEval_ne_zero (t w))).symm
  · convert (ofProp_eq_one_of_ne_zero (hB.cooperEval_ne_zero (t w))).symm

variable [MeasurableSpace W] [DiscreteMeasurableSpace W] {μ : Measure W}

/-- The trivalent probability of an Adams formula with a live antecedent is his conditional
probability. -/
theorem prob_ofAdams {φ : Adams1975.Formula W} (h : μ φ.ante ≠ 0) :
    Trivalent.prob μ (ofAdams φ) = μ[φ.cons | φ.ante] := by
  rw [ofAdams_eq_indicator, Trivalent.prob_indicator_ofProp _ _ h]
  rfl

/-- For conditional-free `A` and `B` with a live antecedent, the probability of `A → B` is the
conditional probability of `B` given `A` (**Adams's Thesis**). -/
theorem adams_thesis {A B : Formula ι} (hA : NoCond A) (hB : NoCond B) {t : W → ι → Bool}
    (h : μ {w | cooperEval (t w) A = 1} ≠ 0) :
    Trivalent.prob μ (value t (.cond A B)) =
      μ[{w | cooperEval (t w) B = 1} | {w | cooperEval (t w) A = 1}] := by
  rw [value_cond_eq_ofAdams hA hB t, prob_ofAdams h]

/-- [adams-1975]'s p-entailment is a condition on trivalent probabilities, with his proper
assignments the credences under which no premise or conclusion is void almost surely. -/
theorem pEntails_iff_prob {κ : Type*} {s : Finset κ} {X : κ → Adams1975.Formula W}
    {d : Adams1975.Formula W} :
    Adams1975.PEntails s X d ↔ ∀ ε > 0, ∃ δ > 0, ∀ μ : Measure W, IsProbabilityMeasure μ →
      μ (Function.support (ofAdams d)) ≠ 0 →
      (∀ i ∈ s, μ (Function.support (ofAdams (X i))) ≠ 0) →
      (∀ i ∈ s, 1 - δ ≤ Trivalent.prob μ (ofAdams (X i))) →
      1 - ε ≤ Trivalent.prob μ (ofAdams d) := by
  simp only [support_ofAdams, Adams1975.PEntails]
  refine forall₂_congr fun ε _ ↦ exists_congr fun δ ↦ and_congr_right fun _ ↦
    forall₂_congr fun μ _ ↦ imp_congr_right fun hd ↦ imp_congr_right fun hX ↦ ?_
  rw [prob_ofAdams hd]
  exact imp_congr_left (forall₂_congr fun i hi ↦ by rw [prob_ofAdams (hX i hi)])

end Adams

/-! ### The die and coin models

The fair models the paper computes in: Goldstein and Santorio's die, Santorio and Wellwood's
partition die, Edgington's coin, and the two-world model where `p(X ∧ Y) ≤ p(X)` fails. -/

section Examples

private theorem ennreal_div_eq {a b c d : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ⊤) (hd0 : d ≠ 0)
    (hd : d ≠ ⊤) (h : a * d = c * b) : a / b = c / d :=
  (ENNReal.div_eq_div_iff hd0 hd hb0 hb).2 (by rw [mul_comm d a, h, mul_comm c b])

/-- Outcome `n + 1` of a fair die as a valuation of the atoms *even*, *two-or-four*, *six*. -/
def dieVal : Fin 6 → Fin 3 → Bool :=
  ![![false, false, false], ![true, true, false], ![false, false, false],
    ![true, true, false], ![false, false, false], ![true, false, true]]

/-- In Goldstein and Santorio's die (§5), `p(A) = 1`, `p(B) = 1/4` and `p(C) = 1/2`, yet `p(B ∧ C) =
1/2 ≠ p(B)`. -/
theorem goldstein_santorio_die :
    Trivalent.prob (uniformOn Set.univ)
        (value dieVal (.cond (.atom 0) (.cond (.neg (.atom 1)) (.atom 2)))) = 1 ∧
      Trivalent.prob (uniformOn Set.univ)
        (value dieVal (.cond (.neg (.atom 1)) (.atom 2))) = 1 / 4 ∧
      Trivalent.prob (uniformOn Set.univ) (value dieVal (.atom 0)) = 1 / 2 ∧
      Trivalent.prob (uniformOn Set.univ)
        (value dieVal (.conj (.cond (.neg (.atom 1)) (.atom 2)) (.atom 0))) = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Trivalent.prob_uniformOn_univ]
  · rw [Trivalent.prob_count_eq (P := {5}) (S := {5}) (by decide) (by decide) ⟨5, by decide⟩]
    simp
  · rw [Trivalent.prob_count_eq (P := {5}) (S := {0, 2, 4, 5}) (by decide) (by decide)
        ⟨5, by decide⟩,
      show ({5} : Finset (Fin 6)).card = 1 from by decide,
      show ({0, 2, 4, 5} : Finset (Fin 6)).card = 4 from by decide]
    exact ennreal_div_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [Trivalent.prob_count_eq (P := {1, 3, 5}) (S := Finset.univ) (by decide) (by decide)
      Finset.univ_nonempty,
      show ({1, 3, 5} : Finset (Fin 6)).card = 3 from by decide,
      show (Finset.univ : Finset (Fin 6)).card = 6 from by decide]
    exact ennreal_div_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [Trivalent.prob_count_eq (P := {1, 3, 5}) (S := Finset.univ) (by decide) (by decide)
      Finset.univ_nonempty,
      show ({1, 3, 5} : Finset (Fin 6)).card = 3 from by decide,
      show (Finset.univ : Finset (Fin 6)).card = 6 from by decide]
    exact ennreal_div_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Outcome `n + 1` of a fair die as a valuation of the atoms *even*, *two*, *one*. -/
def dieVal' : Fin 6 → Fin 3 → Bool :=
  ![![false, false, true], ![true, true, false], ![false, false, false],
    ![true, false, false], ![false, false, false], ![true, false, false]]

/-- In Santorio and Wellwood's die (§4, example 3), *if the outcome was even, it was two; and if it
was odd, it was one* has probability `1/3`. -/
theorem santorio_wellwood_die :
    Trivalent.prob (uniformOn Set.univ)
      (value dieVal' (.conj (.cond (.atom 0) (.atom 1))
        (.cond (.neg (.atom 0)) (.atom 2)))) = 1 / 3 := by
  rw [Trivalent.prob_uniformOn_univ,
    Trivalent.prob_count_eq (P := {0, 1}) (S := Finset.univ) (by decide) (by decide)
      Finset.univ_nonempty,
    show ({0, 1} : Finset (Fin 6)).card = 2 from by decide,
    show (Finset.univ : Finset (Fin 6)).card = 6 from by decide]
  exact ennreal_div_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The four equiprobable worlds of **Edgington's coin** (§6) as valuations of *double-headed*,
*flipped*, *heads*. -/
def coinVal : Fin 4 → Fin 3 → Bool :=
  ![![true, true, true], ![true, false, false], ![false, true, false], ![false, false, false]]

/-- In Edgington's coin, `p((F → H) → D) = 2/3`, not the `1` Edgington's intuition demands (§6). -/
theorem edgington_coin :
    Trivalent.prob (uniformOn Set.univ)
      (value coinVal (.cond (.cond (.atom 1) (.atom 2)) (.atom 0))) = 2 / 3 := by
  rw [Trivalent.prob_uniformOn_univ,
    Trivalent.prob_count_eq (P := {0, 1}) (S := {0, 1, 3}) (by decide) (by decide) ⟨0, by decide⟩,
    show ({0, 1} : Finset (Fin 4)).card = 2 from by decide,
    show ({0, 1, 3} : Finset (Fin 4)).card = 3 from by decide]
  exact ennreal_div_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The two-world valuation behind the failure of `p(X ∧ Y) ≤ p(X)`: the first atom tracks the
world, the second is true everywhere. -/
def lawVal : Bool → Fin 2 → Bool := fun w i ↦ if i = 0 then w else true

/-- The law `p(X ∧ Y) ≤ p(X)` fails, as `A → ⊥` has probability 0 while its conjunction with a truth
has positive probability (§2, §4). -/
theorem prob_conj_gt :
    Trivalent.prob (uniformOn Set.univ) (value lawVal (.cond (.atom 0) (bot 1))) = 0 ∧
      Trivalent.prob (uniformOn Set.univ)
        (value lawVal (.conj (.cond (.atom 0) (bot 1)) (.atom 1))) = 1 / 2 := by
  constructor <;> rw [Trivalent.prob_uniformOn_univ]
  · rw [Trivalent.prob_count_eq (P := ∅) (S := {true}) (by decide) (by decide) ⟨true, by decide⟩]
    simp
  · rw [Trivalent.prob_count_eq (P := {false}) (S := Finset.univ) (by decide) (by decide)
      Finset.univ_nonempty,
      show ({false} : Finset Bool).card = 1 from by decide,
      show (Finset.univ : Finset Bool).card = 2 from by decide]
    exact ennreal_div_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Examples

end EgreRossiSprenger2026a
