module

public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Core.Probability.Kernel.Softmax
public import Linglib.Core.Order.Pareto
public import Linglib.Pragmatics.RSA.AlternatingMaximization
public import Mathlib.Data.Set.Finite.Lemmas
public import Linglib.Data.Examples.XuEtAl2024

/-!
# Xu, Kemp, Frermann & Xu (2024): Word Reuse and Combination Support Efficient Communication

This file formalizes the efficient-communication account of lexicalization in [xu-etal-2024].
A novel concept enters the lexicon by reusing an existing form or by combining existing forms
into a compound, and both strategies are shaped by a tradeoff between speaker effort, the
expected length of the form, and information loss, the expected surprisal of the intended
concept under the listener's distribution. The speaker produces from the expanded lexicon while
the listener, who has not yet acquired the new pairs, interprets each form as the label of a
category with a prototype, assigning concepts probability by a similarity choice rule
(`listener`), the softmax of the negative distances to the prototype (`real_listener`), so that
under a form a concept closer to the prototype is less surprising and incurs less information
loss (`surprisal_listener_le`).

An encoding of the emerging concepts is a speaker who names each concept by one form
(`encoder`). Its two costs (eq. 4, `costs`) are the information loss and the expected cost of
`RSA` with the form length as cost (`informationLoss_encoder`, `expectedCost_encoder`), so that the
objective is the negative expected utility at cost `β • l` (`objective_eq_neg_expectedUtility`).
With need held fixed the objective decomposes into an item-level objective (eq. 5,
`objective_eq_sum`), so an encoding that is optimal concept by concept is optimal overall
(`objective_le_of_forall`) and, for a positive parameter, on the Pareto frontier
(`minimalFor_costs`).
Along the frontier the expected length of the optimal encodings falls and their information loss
rises as the parameter grows (`antitone_expectedLength`, `monotoneOn_expectedSurprisal`), and the
efficiency loss of an encoding (eq. 8, `efficiencyLoss`) vanishes exactly when the encoding is
optimal at one of the sampled parameters (`efficiencyLoss_eq_zero_iff`).
A compound is longer than the constituent it reuses (`length_compound`), the length half of the
tradeoff the paper reports between the two strategies. An item is literal when the intended
concept is a hyponym of an existing sense of the reused form or of the compound's head
(`Literal`).

## Implementation notes

The speaker's distribution is a point mass on the intended concept, so the expected
Kullback–Leibler divergence of the paper is the expected surprisal. Need is a measure on the
concepts and the production policy a deterministic encoding, the case under which the paper
computes its frontier. The paper takes optima for every `β ≥ 0` to lie on the Pareto frontier; at
`β = 0` an optimum may be dominated by an encoding of equal information loss and shorter forms, so
`minimalFor_costs` takes `β > 0`. The corpus results, the fitted sensitivity parameter, the
sentence-encoder prototypes, and the baseline encodings are not restated; the attested items of
the paper's first table and the near-synonyms of its second are recorded as examples. Surprisal
is measured in nats; bits differ by the factor `log 2`, which rescales the tradeoff parameter.

## Errata

* Eq. 8 is said to follow [zaslavsky-kemp-regier-tishby-2018], but it is a different measure.
  There the deviation from the optimal objective is taken at the parameter that minimizes it and
  divided by that parameter (`ZaslavskyKempRegierTishby2018.efficiencyLoss`); eq. 8 takes the
  least deviation itself, undivided (`efficiencyLoss`).

## References

* [xu-etal-2024]
* [kemp-regier-2012]
* [zaslavsky-kemp-regier-tishby-2018]
* [regier-kemp-kay-2015]
-/

@[expose] public section

namespace XuEtAl2024

open InformationTheory MeasureTheory ProbabilityTheory Finset

/-! ### The listener -/

section Listener

variable {C W Q : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Countable W] [MeasurableSpace W] [MeasurableSingletonClass W]

/-- On hearing a form, the similarity choice listener weighs each concept by an exponential that
falls off, at rate `γ`, with the concept's distance from the form's prototype. -/
noncomputable def listener (γ : ℝ) (d : C → Q → ℝ) (q : W → Q) : Kernel W C :=
  Kernel.softmax fun w c ↦ ((-γ * d c (q w) : ℝ) : EReal)

variable (γ : ℝ) (d : C → Q → ℝ) (q : W → Q)

instance [Nonempty C] : IsMarkovKernel (listener γ d q) :=
  Kernel.isMarkovKernel_softmax (fun _ ↦ ⟨Classical.arbitrary C, EReal.coe_ne_bot _⟩)
    fun _ _ ↦ EReal.coe_ne_top _

theorem real_listener (w : W) (c : C) :
    (listener γ d q w).real {c} = Real.softmax (fun c ↦ -γ * d c (q w)) c :=
  Kernel.softmax_coe_real_singleton _ w c

theorem surprisal_listener_le [Nonempty C] (hγ : 0 ≤ γ) {w : W} {c c' : C}
    (h : d c (q w) ≤ d c' (q w)) :
    surprisal (listener γ d q w) c ≤ surprisal (listener γ d q w) c' := by
  rw [surprisal, surprisal, real_listener, real_listener, neg_le_neg_iff]
  exact Real.log_le_log (Real.softmax_pos _ _) (Real.softmax_le_softmax_iff.2 (by nlinarith))

theorem real_listener_zero (w : W) (c : C) :
    (listener 0 d q w).real {c} = 1 / Fintype.card C := by
  simp [real_listener, Real.softmax_apply]

end Listener

/-! ### Communicative costs -/

section Costs

variable {C W : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [MeasurableSpace W] [MeasurableSingletonClass W]

/-- The speaker who encodes each concept by its form under `f`. -/
noncomputable def encoder (f : C → W) : Kernel C W := Kernel.deterministic f .of_discrete

instance (f : C → W) : IsMarkovKernel (encoder f) := by unfold encoder; infer_instance

variable (need : Measure C) (l : W → ℝ) (m : Kernel W C)

/-- The costs of an encoding `f` under need `need`, form length `l` and listener `m` (eq. 4): the
information the listener loses about the intended concept and the expected length of the form. -/
noncomputable def costs (f : C → W) : ℝ × ℝ :=
  (RSA.informationLoss need Kernel.id (encoder f) m, RSA.expectedCost need Kernel.id l (encoder f))

/-- The objective `L_β` of an encoding (eq. 4), its information loss plus `β` times its expected
length. -/
noncomputable def objective (β : ℝ) (f : C → W) : ℝ :=
  (costs need l m f).1 + β * (costs need l m f).2

/-- The item-level objective (eq. 7): the surprisal of the concept under the form, plus the
weighted length of the form. -/
noncomputable def itemObjective (β : ℝ) (c : C) (w : W) : ℝ :=
  surprisal (m w) c + β * l w

@[simp] theorem informationLoss_encoder (f : C → W) :
    RSA.informationLoss need Kernel.id (encoder f) m =
      ∑ c, need.real {c} * surprisal (m (f c)) c := by
  simp [RSA.informationLoss, encoder, Kernel.deterministic_apply, integral_dirac]

@[simp] theorem expectedCost_encoder (f : C → W) :
    RSA.expectedCost need Kernel.id l (encoder f) = ∑ c, need.real {c} * l (f c) := by
  simp [RSA.expectedCost, encoder, Kernel.deterministic_apply, integral_dirac]

/-- The objective is the negative expected utility of `RSA` at cost `β • l`. -/
theorem objective_eq_neg_expectedUtility [Finite W] (β : ℝ) (f : C → W) :
    objective need l m β f = -RSA.expectedUtility need Kernel.id (β • l) (encoder f) m := by
  rw [RSA.expectedUtility_eq_neg_add, RSA.expectedCost_smul, neg_neg]
  rfl

/-- Eq. 5: with need held fixed, the objective is the need-weighted item-level objective. -/
theorem objective_eq_sum (β : ℝ) (f : C → W) :
    objective need l m β f = ∑ c, need.real {c} * itemObjective l m β c (f c) := by
  simp only [objective, costs, informationLoss_encoder, expectedCost_encoder, itemObjective,
    mul_add, sum_add_distrib, mul_sum, mul_left_comm β]

theorem objective_le_of_forall {f g : C → W} (β : ℝ)
    (h : ∀ c, itemObjective l m β c (f c) ≤ itemObjective l m β c (g c)) :
    objective need l m β f ≤ objective need l m β g := by
  rw [objective_eq_sum, objective_eq_sum]
  exact sum_le_sum fun c _ ↦ mul_le_mul_of_nonneg_left (h c) measureReal_nonneg

/-- Optimizing eq. 5 at a positive tradeoff parameter yields a point of the Pareto frontier. -/
theorem minimalFor_costs {f : C → W} {β : ℝ} (hβ : 0 < β)
    (hf : ∀ c w, itemObjective l m β c (f c) ≤ itemObjective l m β c w) :
    MinimalFor (fun _ ↦ True) (costs need l m) f :=
  .of_fst_add_mul_snd_le hβ trivial fun g _ ↦ objective_le_of_forall need l m β fun c ↦ hf c (g c)

/-- The efficiency loss of an encoding against the frontier `E` (eq. 8), its least excess
objective over the optimal encoding across the tradeoff parameters in `B`. -/
noncomputable def efficiencyLoss (B : Set ℝ) (E : ℝ → C → W) (f : C → W) : ℝ :=
  ⨅ β : B, (objective need l m β f - objective need l m β (E β))

/-! ### The frontier -/

variable {need l m} {E : ℝ → C → W}
  (hE : ∀ β c w, itemObjective l m β c (E β c) ≤ itemObjective l m β c w)
include hE

theorem antitone_expectedLength : Antitone fun β ↦ ∑ c, need.real {c} * l (E β c) := by
  simpa [costs] using antitone_snd_of_fst_add_mul_snd_le (c := fun β ↦ costs need l m (E β))
    fun β β' ↦ objective_le_of_forall need l m β fun c ↦ hE β c (E β' c)

theorem monotoneOn_expectedSurprisal :
    MonotoneOn (fun β ↦ ∑ c, need.real {c} * surprisal (m (E β c)) c) (Set.Ici 0) := by
  simpa [costs] using monotoneOn_fst_of_fst_add_mul_snd_le (c := fun β ↦ costs need l m (E β))
    fun β β' ↦ objective_le_of_forall need l m β fun c ↦ hE β c (E β' c)

/-- An encoding has zero efficiency loss exactly when it is optimal at one of the sampled
tradeoff parameters. -/
theorem efficiencyLoss_eq_zero_iff {B : Set ℝ} (hB : B.Finite) (hne : B.Nonempty) (f : C → W) :
    efficiencyLoss need l m B E f = 0 ↔
      ∃ β ∈ B, ∀ g, objective need l m β f ≤ objective need l m β g := by
  have hopt (β : ℝ) (g : C → W) : objective need l m β (E β) ≤ objective need l m β g :=
    objective_le_of_forall need l m β fun c ↦ hE β c (g c)
  have hnn (β : B) : 0 ≤ objective need l m β f - objective need l m β (E β) :=
    sub_nonneg.2 (hopt β f)
  have : Nonempty B := hne.to_subtype
  refine ⟨fun h0 ↦ ?_, fun ⟨β, hβ, h⟩ ↦ le_antisymm ?_ (Real.iInf_nonneg hnn)⟩
  · obtain ⟨β, hβ, hmin⟩ := Set.exists_min_image B
      (fun β ↦ objective need l m β f - objective need l m β (E β)) hB hne
    have := (le_ciInf fun β : B ↦ hmin β β.2).trans_eq h0
    exact ⟨β, hβ, fun g ↦ (sub_nonpos.1 this).trans (hopt β g)⟩
  · exact (ciInf_le ⟨0, Set.forall_mem_range.2 hnn⟩ ⟨β, hβ⟩).trans (sub_nonpos.2 (h (E β)))

end Costs

/-! ### Reuse and combination -/

section Forms

variable {A C Q : Type*}

/-- A compound concatenates two existing forms. -/
def compound (w₁ w₂ : List A) : List A := w₁ ++ w₂

theorem length_compound (w₁ : List A) {w₂ : List A} (h : w₂ ≠ []) :
    w₁.length < (compound w₁ w₂).length := by
  simp [compound, List.length_pos_iff_ne_nil.2 h]

/-- The prototype of a compound is the sum of its constituents' prototypes. -/
def compoundPrototype [Add Q] (q : List A → Q) (w₁ w₂ : List A) : Q := q w₁ + q w₂

/-- An item is literal when its concept is a hyponym of an existing sense of the form that
carries it: the reused form, or the head of a compound. -/
def Literal (Hypo : C → C → Prop) (senses : List A → Set C) (carrier : List A) (c : C) :
    Prop :=
  ∃ c' ∈ senses carrier, Hypo c c'

end Forms

end XuEtAl2024
