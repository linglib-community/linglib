module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Order
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Data.Examples.YingEtAl2025

/-!
# Ying, Zhi-Xuan, Wong, Mansinghka & Tenenbaum (2025): Understanding Epistemic Language

This file formalizes the epistemic language of thought of
Ying and colleagues, a degree-based semantics for attitude verbs,
modal verbs and modal adjectives grounded in the probability an agent assigns to a formula,
following the scalar semantics of Lassiter. Each expression is the positive form of the
probability scale at a lexical threshold (`Thresholds`), the preimage of `Set.Ici`:
*believes*, *certain*, the modal verbs from *could* to *must*, and *likely* hold when the
probability clears their threshold; *uncertain* and *unlikely* when it falls below
(the preimage of `Set.Iio`); *knows that* is belief plus truth, *knows if* knowledge of the
question, and the *about* operators quantify over a contextually restricted domain
(`knowsAbout`, `certainAbout`, `uncertainAbout`). A modal under *believes* is lowered to a
comparison with the modal's own threshold rather than the belief threshold
(`believesModal_might`). Comparatives and superlatives compare probabilities, and the
strengthened superlative scales the threshold by a multiplier (`mostStr`). The entailments among
the expressions follow from the ordering of the thresholds alone (`Thresholds.Ordered`,
`must_entails_might`, `certainAbout_believes`, `uncertainAbout_certainAbout`), and the fitted
values of the paper's lexicon respect that ordering (`fitted`, `fitted_ordered`). The modal
verbs' forces in the English fragment agree with the ordering: no possibility modal carries a
higher threshold than a necessity modal (`force_threshold_le`).

## Implementation notes

An agent's credences are a Markov kernel from agents to worlds, `Pr a φ` the probability agent
`a` assigns to `φ`; the Bayesian theory-of-mind inference that produces it from observed
actions is not modelled. Thresholds live on the probability scale `ℝ≥0∞`. The fitted thresholds
and the literature-derived initial values of the paper's second appendix are recorded as
instances of `Thresholds`, and the theorems are stated for any thresholds satisfying the
ordering. The paper states no ordering; `Thresholds.Ordered` is this file's, and its modal part
agrees with Lassiter's θ_might < θ_likely < θ_must < θ_certain (p. 152), weakened to
`≤` since the fitted values tie.

## References

* [ying-zhi-xuan-wong-mansinghka-tenenbaum-2025]
* [lassiter-2017]
* [hintikka-1962]
-/

@[expose] public section

namespace YingEtAl2025

open MeasureTheory ProbabilityTheory Degree English.Auxiliaries Modality
open scoped ENNReal

variable {E W X : Type*} [MeasurableSpace E] [MeasurableSpace W]

/-! ### Thresholds -/

/-- The probability thresholds of the epistemic lexicon and the multiplier of the
strengthened superlative. -/
structure Thresholds where
  believes : ℝ≥0∞
  certain : ℝ≥0∞
  uncertain : ℝ≥0∞
  likely : ℝ≥0∞
  unlikely : ℝ≥0∞
  could : ℝ≥0∞
  might : ℝ≥0∞
  may : ℝ≥0∞
  should : ℝ≥0∞
  must : ℝ≥0∞
  most : ℝ≥0∞

/-- The thresholds are ordered as the entailments need when the modal verbs form a scale from
*could* to *must*, *likely* sits between *may* and *should*, belief lies above *likely* and
below *certain*, and the reversed-polarity thresholds lie below *certain*. -/
structure Thresholds.Ordered (Θ : Thresholds) : Prop where
  could_might : Θ.could ≤ Θ.might
  might_may : Θ.might ≤ Θ.may
  may_likely : Θ.may ≤ Θ.likely
  likely_believes : Θ.likely ≤ Θ.believes
  believes_should : Θ.believes ≤ Θ.should
  should_must : Θ.should ≤ Θ.must
  must_certain : Θ.must ≤ Θ.certain
  unlikely_uncertain : Θ.unlikely ≤ Θ.uncertain
  uncertain_certain : Θ.uncertain ≤ Θ.certain
  one_le_most : 1 ≤ Θ.most

/-- The thresholds fitted against human plausibility ratings. -/
noncomputable def fitted : Thresholds :=
  ⟨.ofReal (3/4), .ofReal (19/20), .ofReal (7/10), .ofReal (7/10), .ofReal (2/5), .ofReal (1/5),
    .ofReal (1/5), .ofReal (3/10), .ofReal (4/5), .ofReal (19/20), .ofReal (3/2)⟩

/-- The initial thresholds derived from the literature, before fitting. -/
noncomputable def initial : Thresholds :=
  ⟨.ofReal (3/4), .ofReal (19/20), .ofReal (1/2), .ofReal (3/5), .ofReal (2/5), .ofReal (1/5),
    .ofReal (1/5), .ofReal (3/10), .ofReal (4/5), .ofReal (19/20), .ofReal (3/2)⟩

theorem fitted_ordered : fitted.Ordered := by
  constructor <;> simp only [fitted] <;>
    first
      | exact ENNReal.ofReal_le_ofReal (by norm_num)
      | exact ENNReal.one_le_ofReal.2 (by norm_num)

theorem initial_ordered : initial.Ordered := by
  constructor <;> simp only [initial] <;>
    first
      | exact ENNReal.ofReal_le_ofReal (by norm_num)
      | exact ENNReal.one_le_ofReal.2 (by norm_num)

/-! ### The epistemic expressions -/

variable (Θ : Thresholds) (Pr : Kernel E W)

/-- *A believes that φ*. -/
def believes (a : E) (φ : Set W) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.believes

/-- *A believes M*, for a modal claim `M`, applies the modal to the agent. -/
def believesModal (a : E) (M : E → Prop) : Prop := M a

/-- *A knows that φ* holds when A believes φ and φ is true. -/
def knowsThat (a : E) (φ : Set W) (w : W) : Prop := believes Θ Pr a φ ∧ w ∈ φ

/-- *A knows if φ* holds when A knows the answer. -/
def knowsIf (a : E) (φ : Set W) (w : W) : Prop :=
  knowsThat Θ Pr a φ w ∨ knowsThat Θ Pr a φᶜ w

/-- *A knows about φ* holds when the agent knows φ of some relevant entity. -/
def knowsAbout (a : E) (C : X → Prop) (φ : X → Set W) (w : W) : Prop :=
  ∃ x, C x ∧ knowsThat Θ Pr a (φ x) w

/-- *A does not know that φ* holds when φ is true but not believed. -/
def notKnowsThat (a : E) (φ : Set W) (w : W) : Prop := ¬ believes Θ Pr a φ ∧ w ∈ φ

/-- *A is certain that φ*. -/
def certainThat (a : E) (φ : Set W) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.certain

/-- *A is certain about φ* holds when the agent is certain of φ for some relevant entity. -/
def certainAbout (a : E) (C : X → Prop) (φ : X → Set W) : Prop :=
  ∃ x, C x ∧ certainThat Θ Pr a (φ x)

/-- *A is uncertain if φ or ψ* holds when neither alternative reaches the threshold. -/
def uncertainIf (a : E) (φ ψ : Set W) : Prop :=
  φ ∈ (Pr a) ⁻¹' Set.Iio Θ.uncertain ∧ ψ ∈ (Pr a) ⁻¹' Set.Iio Θ.uncertain

/-- *A is uncertain about φ* holds when no relevant entity reaches the threshold. -/
def uncertainAbout (a : E) (C : X → Prop) (φ : X → Set W) : Prop :=
  ∀ x, C x → φ x ∈ (Pr a) ⁻¹' Set.Iio Θ.uncertain

/-- The modal verbs and adjective, each a property of agents. -/
def could (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.could
def might (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.might
def may (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.may
def should (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.should
def must (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.must
def likely (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici Θ.likely
def unlikely (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Iio Θ.unlikely

/-- *φ is more likely than ψ*. -/
def more (φ ψ : Set W) (a : E) : Prop := Pr a ψ < Pr a φ

/-- *φ of o is most likely* among the relevant alternatives. -/
def mostSup (o : X) (C : X → Prop) (φ : X → Set W) (a : E) : Prop :=
  ∀ x, C x → Pr a (φ x) ≤ Pr a (φ o)

/-- The strengthened superlative holds when the probability reaches the multiplied threshold. -/
def mostStr (θ : ℝ≥0∞) (φ : Set W) (a : E) : Prop := φ ∈ (Pr a) ⁻¹' Set.Ici (Θ.most * θ)

/-! ### Entailments from the ordering -/

variable {Θ Pr}

/-- Knowledge entails belief. -/
theorem knowsThat_believes {a : E} {φ : Set W} {w : W} (h : knowsThat Θ Pr a φ w) :
    believes Θ Pr a φ := h.1

/-- Knowledge is veridical. -/
theorem knowsThat_mem {a : E} {φ : Set W} {w : W} (h : knowsThat Θ Pr a φ w) : w ∈ φ := h.2

/-- Knowing that answers the question. -/
theorem knowsIf_of_knowsThat {a : E} {φ : Set W} {w : W} (h : knowsThat Θ Pr a φ w) :
    knowsIf Θ Pr a φ w := Or.inl h

/-- Belief and not knowing exclude one another. -/
theorem not_notKnowsThat_of_believes {a : E} {φ : Set W} {w : W} (h : believes Θ Pr a φ) :
    ¬ notKnowsThat Θ Pr a φ w := fun hn ↦ hn.1 h

/-- A modal under *believes* is lowered to the modal's own threshold. -/
theorem believesModal_might (a : E) (φ : Set W) :
    believesModal (E := E) a (might Θ Pr φ) ↔ φ ∈ (Pr a) ⁻¹' Set.Ici Θ.might := Iff.rfl

/-- *must* entails *should*, *likely*, *may*, *might* and *could* under the ordering. -/
theorem must_entails_might (h : Θ.Ordered) {φ : Set W} {a : E} (hm : must Θ Pr φ a) :
    might Θ Pr φ a := by
  have := h.might_may; have := h.may_likely; have := h.likely_believes
  have := h.believes_should; have := h.should_must
  exact le_trans (show Θ.might ≤ Θ.must by order) hm

theorem must_entails_should (h : Θ.Ordered) {φ : Set W} {a : E} (hm : must Θ Pr φ a) :
    should Θ Pr φ a :=
  le_trans h.should_must hm

theorem should_entails_likely (h : Θ.Ordered) {φ : Set W} {a : E} (hm : should Θ Pr φ a) :
    likely Θ Pr φ a :=
  le_trans (h.likely_believes.trans h.believes_should) hm

theorem might_entails_could (h : Θ.Ordered) {φ : Set W} {a : E} (hm : might Θ Pr φ a) :
    could Θ Pr φ a :=
  le_trans h.could_might hm

/-- Certainty entails belief. -/
theorem certainThat_believes (h : Θ.Ordered) {a : E} {φ : Set W} (hc : certainThat Θ Pr a φ) :
    believes Θ Pr a φ :=
  le_trans (h.believes_should.trans (h.should_must.trans h.must_certain)) hc

/-- Certainty about supplies a believed witness. -/
theorem certainAbout_believes (h : Θ.Ordered) {a : E} {C : X → Prop} {φ : X → Set W}
    (hc : certainAbout Θ Pr a C φ) : ∃ x, C x ∧ believes Θ Pr a (φ x) :=
  let ⟨x, hC, hx⟩ := hc
  ⟨x, hC, certainThat_believes h hx⟩

/-- Uncertainty about and certainty about are incompatible. -/
theorem uncertainAbout_certainAbout (h : Θ.Ordered) {a : E} {C : X → Prop} {φ : X → Set W}
    (hu : uncertainAbout Θ Pr a C φ) (hc : certainAbout Θ Pr a C φ) : False :=
  let ⟨x, hC, hx⟩ := hc
  (h.uncertain_certain.trans hx).not_gt (hu x hC)

/-- The strengthened superlative entails the plain threshold reading. -/
theorem mostStr_meets (h : Θ.Ordered) {θ : ℝ≥0∞} {φ : Set W} {a : E}
    (hm : mostStr Θ Pr θ φ a) : φ ∈ (Pr a) ⁻¹' Set.Ici θ :=
  le_trans (le_mul_of_one_le_left zero_le h.one_le_most) hm

/-! ### The English modal verbs -/

/-- The modal verbs of the lexicon. -/
inductive ModalVerb where
  | could
  | might
  | may
  | should
  | must
  deriving DecidableEq, Repr, Fintype

/-- The threshold of each modal verb. -/
def ModalVerb.threshold (Θ : Thresholds) : ModalVerb → ℝ≥0∞
  | .could => Θ.could
  | .might => Θ.might
  | .may => Θ.may
  | .should => Θ.should
  | .must => Θ.must

/-- The English auxiliary of each modal verb. -/
def ModalVerb.aux : ModalVerb → ModalAuxiliary
  | .could => English.Auxiliaries.could
  | .might => English.Auxiliaries.might
  | .may => English.Auxiliaries.may
  | .should => English.Auxiliaries.should
  | .must => English.Auxiliaries.must

/-- The epistemic forces of each modal verb, read off the fragment. -/
def ModalVerb.forces (v : ModalVerb) : Finset ModalForce := v.aux.forcesOf .epistemic

theorem forces_might : ModalVerb.might.forces = {.possibility} := by decide

theorem forces_must : ModalVerb.must.forces = {.necessity} := by decide

theorem forces_should : ModalVerb.should.forces = {.weakNecessity} := by decide

/-- Under the ordering, a possibility modal never carries a higher threshold than a modal of
necessity or weak necessity. -/
theorem force_threshold_le (h : Θ.Ordered) {v v' : ModalVerb}
    (hv : v.forces = {.possibility}) (hv' : v'.forces ≠ {.possibility}) :
    v.threshold Θ ≤ v'.threshold Θ := by
  have hc := h.could_might; have hm := h.might_may; have hl := h.may_likely
  have hb := h.likely_believes; have hs := h.believes_should; have hu := h.should_must
  cases v <;> cases v' <;>
    first
      | exact absurd hv (by decide)
      | exact absurd (by decide) hv'
      | (simp only [ModalVerb.threshold]; order)

end YingEtAl2025
