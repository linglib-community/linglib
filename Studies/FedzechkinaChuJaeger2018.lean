module

public import Linglib.Core.Probability.Independence.Basic
public import Linglib.Syntax.DependencyGrammar.Length
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.UniformOn

/-!
# Fedzechkina, Chu and Jaeger (2018): Human information processing shapes language change

Fedzechkina, Chu and Jaeger taught English speakers two miniature languages with free order of
subject and object, one verb-final and one verb-initial, from input in which both orders were
equally frequent and the two arguments always equally long. Describing scenes with one long
argument, verb-final learners put it first and verb-initial learners put it last, the orders
that shorten the verb's dependencies, although English prefers short before long (Arnold,
Wasow, Losongco and Ginstrom); their productions had shorter dependencies than the input.

The paper measures the verb's dependency length as the summed distance in words from the verb to
the closest boundary of each argument: on its sentences, the yield distance of dependency graphs
(`Graph.yieldDist`), and on arrangements of subject, object and verb, the boundary distance of
constituents of given lengths (`Arrangement.boundaryDist`), which agree on Fig. 1 as the
substrate's bridge theorem predicts. The measure is invariant under mirroring, and with the verb
at an edge it is two plus the length of the argument next to the verb. A learner's productions
are a probability measure on pairs of the scene's long argument and the order used. Their mean
dependency length is affine in the probability of the symmetric difference of "the subject is
long" and "the subject comes first", which places every learner in the diamond of Fig. 5 and ties
Fig. 5 to the order proportions of Fig. 4.

## Main statements

* `verbDependencyLength_eq`: the measure on a clause with the verb at an edge.
* `integral_dependencyLength_eq_cond`: the mean dependency length of a verb-final learner is an
  affine function of the difference of the subject-first proportions on the two kinds of scene.
* `abs_integral_dependencyLength_sub_le`: the diamond of Fig. 5.
* `integral_dependencyLength_eq_lower_iff`: who reaches its lower lines.

## Implementation notes

* A short argument is a bare noun, a long one a noun with an adpositional phrase of `L - 1`
  words; `L = 4` in Figs. 1 and 2 and in every number of Fig. 5.
* The measure of Fig. 5 is over the test productions with one long argument, the long subject
  and the long object equally often (`P.fst = uniformOn {.subject, .object}`); the short-short
  baseline is excluded, as in the paper.
* Verb-final learners also used object-first order more often overall, which the paper ascribes
  to the bias to place the case-marked argument first seen in the authors' earlier experiments;
  the overall frequency is a free parameter here.

## References

* [fedzechkina-chu-jaeger-2018]
* [arnold-losongco-wasow-ginstrom-2000]
* [fedzechkina-newport-2012]
* [fedzechkina-newport-2017]
-/

@[expose] public section

namespace FedzechkinaChuJaeger2018

open WordOrder DependencyGrammar Morphology MeasureTheory ProbabilityTheory
open scoped symmDiff ENNReal

/-! ### The paper's measure -/

/-- The verb's dependency length sums the distances from the verb to the closest boundary of
each argument (Fig. 1). -/
def verbDependencyLength (a : Arrangement Constituent 3) (ℓ : Constituent → ℕ) : ℕ :=
  a.boundaryDist ℓ .verb .subject + a.boundaryDist ℓ .verb .object

theorem verbDependencyLength_mirror (a : Arrangement Constituent 3) (ℓ : Constituent → ℕ) :
    verbDependencyLength a.mirror ℓ = verbDependencyLength a ℓ := by
  simp only [verbDependencyLength, Arrangement.boundaryDist_mirror]

/-- `language d` holds the orders of the miniature language whose verb has direction `d`
towards both arguments. -/
def language (d : HeadDirection) : Finset (Arrangement Constituent 3) := {a | a.IsEnd .verb d}

theorem language_headFinal : language .headFinal = {.sov, .osv} := by decide

theorem language_headInitial :
    language .headInitial = (language .headFinal).image Arrangement.mirror := by
  decide

/-- With the verb at an edge, the measure is two plus the length of the argument in the middle,
next to the verb. -/
theorem verbDependencyLength_eq {d : HeadDirection} {a : Arrangement Constituent 3}
    (ha : a ∈ language d) (ℓ : Constituent → ℕ) :
    verbDependencyLength a ℓ = ℓ (a.symm 1) + 2 := by
  have key : ∀ b ∈ language .headFinal, verbDependencyLength b ℓ = ℓ (b.symm 1) + 2 := by
    have hu : (Finset.univ : Finset Constituent) = {.subject, .object, .verb} := by decide
    simp only [language_headFinal, Finset.mem_insert, Finset.mem_singleton]
    rintro b (rfl | rfl) <;>
    · simp [verbDependencyLength, Arrangement.boundaryDist, hu, Finset.sum_filter,
        Arrangement.Precedes, Arrangement.sov, Arrangement.osv]
      omega
  cases d with
  | headFinal => exact key a ha
  | headInitial =>
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (language_headInitial ▸ ha)
    rw [verbDependencyLength_mirror, key b hb]
    simp only [language_headFinal, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl <;> rfl

-- Fig. 1
theorem long_before_short_head_final (ℓ : Constituent → ℕ) :
    verbDependencyLength .sov ℓ < verbDependencyLength .osv ℓ ↔ ℓ .object < ℓ .subject := by
  rw [verbDependencyLength_eq (d := .headFinal) (by decide),
    verbDependencyLength_eq (d := .headFinal) (by decide)]
  simp [Arrangement.sov, Arrangement.osv]

-- Fig. 1
theorem short_before_long_head_initial (ℓ : Constituent → ℕ) :
    verbDependencyLength .vso ℓ < verbDependencyLength .vos ℓ ↔ ℓ .subject < ℓ .object := by
  rw [verbDependencyLength_eq (d := .headInitial) (by decide),
    verbDependencyLength_eq (d := .headInitial) (by decide)]
  simp [Arrangement.vso, Arrangement.vos]

-- Fig. 4
theorem verbDependencyLength_eq_of_subject_eq_object {d : HeadDirection}
    {a b : Arrangement Constituent 3} (ha : a ∈ language d) (hb : b ∈ language d)
    {ℓ : Constituent → ℕ}
    (h : ℓ .subject = ℓ .object) : verbDependencyLength a ℓ = verbDependencyLength b ℓ := by
  have hm : ∀ c ∈ language d, c.symm 1 = .subject ∨ c.symm 1 = .object := by
    cases d <;> decide
  rw [verbDependencyLength_eq ha, verbDependencyLength_eq hb]
  grind

/-! ### Fig. 1 -/

/-- Fig. 1's verb-final sentence with subject first, MOUNTIE [[RED STOOL ON] HUNTER-OBJ] PUNCH,
with the arcs of its bracketing. -/
def fig1Sov : Graph 6 :=
  .ofArcs [Word.mk' "rizba" .NOUN, Word.mk' "redal" .ADJ, Word.mk' "lanferda" .NOUN,
      Word.mk' "sool" .ADP, Word.mk' "barsadi" .NOUN, Word.mk' "kyse" .VERB]
    5 [(5, 0, .nsubj), (5, 4, .obj), (4, 2, .nmod), (2, 1, .amod), (2, 3, .case)]

/-- Object first, [[RED STOOL ON] HUNTER-OBJ] MOUNTIE PUNCH. -/
def fig1Osv : Graph 6 := fig1Sov.linearize [1, 2, 3, 4, 0, 5] (by decide)

/-- The verb-initial sentence with subject first, PUNCH MOUNTIE [HUNTER-OBJ [ON RED STOOL]]. -/
def fig1Vso : Graph 6 := fig1Sov.linearize [5, 0, 4, 3, 1, 2] (by decide)

/-- Object first, PUNCH [HUNTER-OBJ [ON RED STOOL]] MOUNTIE. -/
def fig1Vos : Graph 6 := fig1Sov.linearize [5, 4, 3, 1, 2, 0] (by decide)

theorem fig1_isTree_isProjective : ∀ g ∈ [fig1Sov, fig1Osv, fig1Vso, fig1Vos],
    g.IsTree ∧ g.IsProjective := by
  decide +kernel

-- Fig. 1
theorem fig1_yieldDist :
    let ℓ := Function.update (1 : Constituent → ℕ) .object 4
    fig1Sov.yieldDist 5 0 = Arrangement.sov.boundaryDist ℓ .verb .subject ∧
    fig1Sov.yieldDist 5 4 = Arrangement.sov.boundaryDist ℓ .verb .object ∧
    fig1Osv.yieldDist 5 4 = Arrangement.osv.boundaryDist ℓ .verb .subject ∧
    fig1Osv.yieldDist 5 3 = Arrangement.osv.boundaryDist ℓ .verb .object ∧
    fig1Vso.yieldDist 0 1 = Arrangement.vso.boundaryDist ℓ .verb .subject ∧
    fig1Vso.yieldDist 0 2 = Arrangement.vso.boundaryDist ℓ .verb .object ∧
    fig1Vos.yieldDist 0 5 = Arrangement.vos.boundaryDist ℓ .verb .subject ∧
    fig1Vos.yieldDist 0 1 = Arrangement.vos.boundaryDist ℓ .verb .object := by
  decide +kernel

theorem fig1_yieldDist_eq :
    fig1Sov.yieldDist 5 0 = 5 ∧ fig1Sov.yieldDist 5 4 = 1 ∧ fig1Osv.yieldDist 5 4 = 1 ∧
    fig1Osv.yieldDist 5 3 = 2 ∧ fig1Vso.yieldDist 0 1 = 1 ∧ fig1Vso.yieldDist 0 2 = 2 ∧
    fig1Vos.yieldDist 0 5 = 5 ∧ fig1Vos.yieldDist 0 1 = 1 := by
  decide +kernel

theorem fig1_projection_length :
    (fig1Sov.projection 4).length = 4 ∧ (fig1Sov.projection 0).length = 1 := by
  decide +kernel

/-! ### Two events and their symmetric difference -/

section Events

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {A B : Set Ω}

theorem abs_measureReal_symmDiff_sub_half_le (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA₂ : P.real A = 1 / 2) : |P.real (A ∆ B) - 1 / 2| ≤ min (P.real B) (1 - P.real B) := by
  have h₁ := abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet
    hB.nullMeasurableSet (μ := P)
  have h₂ : P.real (A ∆ B) ≤ P.real A + P.real B :=
    (measureReal_mono symmDiff_le_sup).trans (measureReal_union_le A B)
  have h₃ : P.real (Aᶜ ∆ Bᶜ) ≤ P.real Aᶜ + P.real Bᶜ :=
    (measureReal_mono symmDiff_le_sup).trans (measureReal_union_le _ _)
  rw [compl_symmDiff_compl, measureReal_compl hA, measureReal_compl hB, probReal_univ] at h₃
  grind

theorem measureReal_symmDiff_of_indepSet (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : IndepSet A B P) :
    P.real (A ∆ B) = P.real A + P.real B - 2 * (P.real A * P.real B) := by
  have hi := hAB.measureReal_inter_eq_mul
  have h₁ := measureReal_sdiff_add_inter (μ := P) (s := A) hB
  have h₂ := measureReal_sdiff_add_inter (μ := P) (s := B) hA
  rw [Set.inter_comm] at h₂
  rw [measureReal_symmDiff_eq hA hB]
  linarith

end Events

/-! ### Learners' productions -/

section Learner

local instance : MeasurableSpace Constituent := ⊤
local instance : MeasurableSpace (Arrangement Constituent 3) := ⊤

/-- A test production pairs the long argument of the scene with the order used. -/
abbrev Production := Constituent × Arrangement Constituent 3

/-- A production is subject-first when the subject precedes the object. -/
def subjectFirst : Set Production := {x | x.2.Precedes .subject .object}

/-- A production is in `long c` when `c` is the long argument of its scene. -/
def long (c : Constituent) : Set Production := Prod.fst ⁻¹' {c}

/-- A production is in `longAdjacent` when its long argument is next to the verb. -/
def longAdjacent : Set Production := {x | x.2.Adjacent .verb x.1}

theorem symm_one_eq_iff_adjacent {d : HeadDirection} {a : Arrangement Constituent 3}
    (ha : a ∈ language d) (c : Constituent) : a.symm 1 = c ↔ a.Adjacent .verb c := by
  revert c ha a
  cases d <;> decide

/-- `dependencyLength L x` is the verb's dependency length in the production `x` when its long
argument has `L` words and its other argument is a bare noun. -/
def dependencyLength (L : ℕ) (x : Production) : ℝ :=
  verbDependencyLength x.2 (Function.update 1 x.1 L)

variable {P : Measure Production} {d : HeadDirection} {L : ℕ}

section Marginal

variable (hscene : P.fst = uniformOn {.subject, .object})
include hscene

theorem measureReal_long {c : Constituent} (hc : c ≠ .verb) : P.real (long c) = 1 / 2 := by
  rw [long, measureReal_def, ← Measure.fst_apply (measurableSet_singleton _), hscene,
    ← Finset.coe_pair, ← Finset.coe_singleton, uniformOn_apply_finset]
  cases c <;> simp +decide at hc ⊢

theorem ae_fst_ne_verb : ∀ᵐ x ∂P, x.1 ≠ .verb := by
  have : P (long .verb) = 0 := by
    rw [long, ← Measure.fst_apply (measurableSet_singleton _), hscene,
      uniformOn_eq_zero_iff (Set.toFinite _)]
    ext c; simp +decide
  exact measure_mono_null (fun x hx ↦ by simpa [long] using hx) this

theorem longAdjacent_ae_eq_headFinal (hlang : ∀ᵐ x ∂P, x.2 ∈ language .headFinal) :
    longAdjacent =ᵐ[P] (long .subject ∆ subjectFirst : Set Production) := by
  filter_upwards [hlang, ae_fst_ne_verb hscene] with ⟨c, a⟩ hx hv
  simp only [language_headFinal, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> cases c <;>
    simp_all +decide [longAdjacent, long, subjectFirst, Set.mem_symmDiff]

theorem longAdjacent_ae_eq_headInitial (hlang : ∀ᵐ x ∂P, x.2 ∈ language .headInitial) :
    longAdjacent =ᵐ[P] ((long .subject ∆ subjectFirst)ᶜ : Set Production) := by
  filter_upwards [hlang, ae_fst_ne_verb hscene] with ⟨c, a⟩ hx hv
  rw [language_headInitial, language_headFinal] at hx
  simp only [Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> cases c <;>
    simp_all +decide [longAdjacent, long, subjectFirst]

theorem measureReal_cond_long {c : Constituent} (hc : c ≠ .verb) (s : Set Production) :
    (P[|long c]).real s = 2 * P.real (long c ∩ s) := by
  rw [measureReal_def, cond_apply (.of_discrete), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, measureReal_long hscene hc]
  norm_num

end Marginal

variable [IsProbabilityMeasure P]

theorem integral_dependencyLength (hlang : ∀ᵐ x ∂P, x.2 ∈ language d) :
    ∫ x, dependencyLength L x ∂P = 3 + ((L : ℝ) - 1) * P.real longAdjacent := by
  have h : dependencyLength L =ᵐ[P] fun x ↦ 3 + ((L : ℝ) - 1) * longAdjacent.indicator 1 x := by
    filter_upwards [hlang] with x hx
    rw [dependencyLength, verbDependencyLength_eq hx, Function.update_apply]
    by_cases h : x.2.Adjacent .verb x.1 <;> simp [longAdjacent, h, symm_one_eq_iff_adjacent hx]
    ring
  rw [integral_congr_ae h, integral_add (integrable_const _) .of_finite, integral_const,
    integral_const_mul, integral_indicator_one (.of_discrete)]
  simp

section Prediction

variable (hscene : P.fst = uniformOn {.subject, .object})
include hscene

private theorem abs_integral_sub (hlang : ∀ᵐ x ∂P, x.2 ∈ language d) :
    |∫ x, dependencyLength L x ∂P - ((L : ℝ) + 5) / 2| =
      |(L : ℝ) - 1| * |P.real (long .subject ∆ subjectFirst) - 1 / 2| := by
  rw [integral_dependencyLength hlang, ← abs_mul]
  cases d with
  | headFinal => rw [measureReal_congr (longAdjacent_ae_eq_headFinal hscene hlang)]; ring_nf
  | headInitial =>
    rw [measureReal_congr (longAdjacent_ae_eq_headInitial hscene hlang),
      measureReal_compl (.of_discrete), probReal_univ, ← abs_neg]
    ring_nf

-- Fig. 5
theorem integral_dependencyLength_of_indepFun (hlang : ∀ᵐ x ∂P, x.2 ∈ language d)
    (h : IndepFun Prod.fst Prod.snd P) : ∫ x, dependencyLength L x ∂P = ((L : ℝ) + 5) / 2 := by
  have hAB : IndepSet (long .subject) subjectFirst P := by
    rw [indepSet_iff_measure_inter_eq_mul (.of_discrete)
      (.of_discrete) P]
    exact indepFun_iff_measure_inter_preimage_eq_mul.1 h {Constituent.subject}
      {a : Arrangement Constituent 3 | a.Precedes .subject .object} (measurableSet_singleton _)
      (Set.to_countable _).measurableSet
  have := abs_integral_sub hscene (L := L) hlang
  rw [measureReal_symmDiff_of_indepSet (.of_discrete)
    (.of_discrete) hAB, measureReal_long hscene (by decide)] at this
  simpa [sub_eq_zero] using this

/-- The mean dependency length lies within `L - 1` times the rarer order's frequency of `(L + 5) /
2`, the diamond of Fig. 5. -/
theorem abs_integral_dependencyLength_sub_le (hL : 1 ≤ L) (hlang : ∀ᵐ x ∂P, x.2 ∈ language d) :
    |∫ x, dependencyLength L x ∂P - ((L : ℝ) + 5) / 2| ≤
      ((L : ℝ) - 1) * min (P.real subjectFirst) (1 - P.real subjectFirst) := by
  have hL' : (0 : ℝ) ≤ (L : ℝ) - 1 := by rw [sub_nonneg]; exact_mod_cast hL
  rw [abs_integral_sub hscene hlang, abs_of_nonneg hL']
  exact mul_le_mul_of_nonneg_left (abs_measureReal_symmDiff_sub_half_le
    (.of_discrete) (.of_discrete)
    (measureReal_long hscene (by decide))) hL'

theorem measureReal_subjectFirst_eq_half_of_integral_eq_three (hL : 1 < L)
    (hlang : ∀ᵐ x ∂P, x.2 ∈ language d) (h : ∫ x, dependencyLength L x ∂P = 3) :
    P.real subjectFirst = 1 / 2 := by
  have := abs_integral_dependencyLength_sub_le hscene hL.le hlang
  have hL' : (0 : ℝ) < L - 1 := by rw [sub_pos]; exact_mod_cast hL
  rw [h, abs_of_neg (by linarith), show -(3 - ((L : ℝ) + 5) / 2) = ((L : ℝ) - 1) * (1 / 2) by
    ring] at this
  have := le_of_mul_le_mul_left this hL'
  grind

theorem integral_dependencyLength_of_fixed (hL : 1 ≤ L) (hlang : ∀ᵐ x ∂P, x.2 ∈ language d)
    (h : P.real subjectFirst = 0 ∨ P.real subjectFirst = 1) :
    ∫ x, dependencyLength L x ∂P = ((L : ℝ) + 5) / 2 := by
  have := abs_integral_dependencyLength_sub_le hscene hL hlang
  rcases h with h | h <;> rw [h] at this <;> norm_num at this <;> linarith

theorem measureReal_subjectFirst : P.real subjectFirst =
    ((P[|long .subject]).real subjectFirst + (P[|long .object]).real subjectFirst) / 2 := by
  have h : subjectFirst =ᵐ[P] (long .subject ∩ subjectFirst ∪ long .object ∩ subjectFirst :) := by
    filter_upwards [ae_fst_ne_verb hscene] with ⟨c, a⟩ hv
    cases c <;> simp_all [long]
  rw [measureReal_congr h, measureReal_union (Set.disjoint_left.2 fun x h₁ h₂ ↦ by
      simp_all [long]) (.of_discrete),
    measureReal_cond_long hscene (by decide), measureReal_cond_long hscene (by decide)]
  ring

theorem measureReal_long_symmDiff_subjectFirst : P.real (long .subject ∆ subjectFirst) =
    ((1 - (P[|long .subject]).real subjectFirst) + (P[|long .object]).real subjectFirst) / 2 := by
  have h : (long .subject ∆ subjectFirst : Set Production) =ᵐ[P]
      (long .subject \ subjectFirst ∪ long .object ∩ subjectFirst :) := by
    filter_upwards [ae_fst_ne_verb hscene] with ⟨c, a⟩ hv
    cases c <;> simp_all [long, Set.mem_symmDiff]
  have hs := measureReal_sdiff_add_inter (μ := P) (s := long .subject)
    (MeasurableSet.of_discrete (s := subjectFirst))
  rw [measureReal_long hscene (by decide)] at hs
  rw [measureReal_congr h, measureReal_union (Set.disjoint_left.2 fun x h₁ h₂ ↦ by
      simp_all [long]) (.of_discrete),
    measureReal_cond_long hscene (by decide), measureReal_cond_long hscene (by decide)]
  linarith

/-- A verb-final learner's mean dependency length is the input's minus `(L - 1) / 2` times their
length-conditioned subject-first difference (Fig. 4). -/
theorem integral_dependencyLength_eq_cond (hlang : ∀ᵐ x ∂P, x.2 ∈ language .headFinal) :
    ∫ x, dependencyLength L x ∂P = ((L : ℝ) + 5) / 2 - ((L : ℝ) - 1) / 2 *
      ((P[|long .subject]).real subjectFirst - (P[|long .object]).real subjectFirst) := by
  rw [integral_dependencyLength hlang,
    measureReal_congr (longAdjacent_ae_eq_headFinal hscene hlang),
    measureReal_long_symmDiff_subjectFirst hscene]
  ring

/-- A verb-final learner reaches the lower lines of Fig. 5 iff they never put the subject first with
a long object or always do with a long subject. -/
theorem integral_dependencyLength_eq_lower_iff (hL : 1 < L)
    (hlang : ∀ᵐ x ∂P, x.2 ∈ language .headFinal) :
    ∫ x, dependencyLength L x ∂P =
        ((L : ℝ) + 5) / 2 - ((L : ℝ) - 1) * min (P.real subjectFirst) (1 - P.real subjectFirst) ↔
      (P[|long .object]).real subjectFirst = 0 ∨ (P[|long .subject]).real subjectFirst = 1 := by
  have hk : (L : ℝ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hL.ne'
  rw [integral_dependencyLength_eq_cond hscene hlang, measureReal_subjectFirst hscene,
    sub_right_inj, show ∀ D : ℝ, ((L : ℝ) - 1) / 2 * D = ((L : ℝ) - 1) * (D / 2) from
      fun D ↦ by ring, mul_right_inj' hk]
  have hle : ∀ c ≠ Constituent.verb, (P[|long c]).real subjectFirst ≤ 1 := fun c hc ↦ by
    have := measureReal_mono (μ := P) (Set.inter_subset_left (s := long c) (t := subjectFirst))
    rw [measureReal_cond_long hscene hc, measureReal_long hscene hc] at *
    linarith
  have h₁ := hle .subject (by decide)
  have h₂ := hle .object (by decide)
  have h₃ : 0 ≤ (P[|long .subject]).real subjectFirst := measureReal_nonneg
  have h₄ : 0 ≤ (P[|long .object]).real subjectFirst := measureReal_nonneg
  grind

end Prediction

-- Fig. 5
theorem exists_integral_dependencyLength_eq_lower (p : unitInterval) :
    ∃ P : Measure Production, IsProbabilityMeasure P ∧ P.fst = uniformOn {.subject, .object} ∧
      (∀ᵐ x ∂P, x.2 ∈ language .headFinal) ∧ P.real subjectFirst = p ∧
      ∫ x, dependencyLength L x ∂P = ((L : ℝ) + 5) / 2 - ((L : ℝ) - 1) * min (p : ℝ) (1 - p) := by
  let h : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let f : unitInterval → Production := fun ω ↦
    (if ω < h then .subject else .object, if ω < p then .sov else .osv)
  have hf : Measurable f :=
    (Measurable.ite measurableSet_Iio measurable_const measurable_const).prodMk
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have hpre : ∀ s, (volume.map f).real s = volume.real (f ⁻¹' s) := fun s ↦ by
    rw [measureReal_def, Measure.map_apply hf (.of_discrete), measureReal_def]
  have hA : f ⁻¹' long .subject = Set.Iio h := by
    ext ω; by_cases hω : ω < h <;> simp [f, long, hω]
  have hB : f ⁻¹' subjectFirst = Set.Iio p := by
    ext ω; by_cases hω : ω < p <;> simp [f, subjectFirst, hω] <;> decide
  have hscene : (volume.map f).fst = uniformOn {.subject, .object} := by
    refine Measure.ext_of_singleton fun c ↦ ?_
    have hu : uniformOn ({.subject, .object} : Set Constituent) {c} =
        (({.subject, .object} ∩ {c} : Finset Constituent).card : ℝ≥0∞) / 2 := by
      rw [← Finset.coe_pair, ← Finset.coe_singleton, uniformOn_apply_finset]; simp +decide
    rw [Measure.fst_apply (measurableSet_singleton c), Measure.map_apply hf
      (.of_discrete), hu]
    cases c
    · rw [show f ⁻¹' (Prod.fst ⁻¹' {.subject}) = Set.Iio h from hA, unitInterval.volume_Iio]
      simp +decide [h]
    · rw [show f ⁻¹' (Prod.fst ⁻¹' {.object}) = Set.Ici h by
        ext ω; by_cases hω : ω < h <;> simp [f, hω, not_lt.1], unitInterval.volume_Ici]
      simp +decide [h]
      rw [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos two_pos]; simp
    · rw [show f ⁻¹' (Prod.fst ⁻¹' {.verb}) = ∅ by ext ω; simp [f]; split_ifs <;> decide]
      simp +decide
  have hlang : ∀ᵐ x ∂volume.map f, x.2 ∈ language .headFinal := by
    rw [ae_map_iff hf.aemeasurable (.of_discrete)]
    exact ae_of_all _ fun ω ↦ by simp only [f]; split_ifs <;> decide
  have hdiff : ∀ x y : unitInterval, Set.Iio x \ Set.Iio y = Set.Ico y x := fun x y ↦ by
    ext; simp
  refine ⟨volume.map f, inferInstance, hscene, hlang, ?_, ?_⟩
  · rw [hpre, hB, measureReal_def, unitInterval.volume_Iio, ENNReal.toReal_ofReal p.2.1]
  · rw [integral_dependencyLength hlang,
      measureReal_congr (longAdjacent_ae_eq_headFinal hscene hlang), hpre, Set.preimage_symmDiff,
      hA, hB,
      measureReal_symmDiff_eq measurableSet_Iio measurableSet_Iio, hdiff, hdiff, measureReal_def,
      measureReal_def, unitInterval.volume_Ico, unitInterval.volume_Ico, ENNReal.toReal_ofReal',
      ENNReal.toReal_ofReal']
    simp only [h]
    rcases le_total (p : ℝ) (1 / 2) with hp | hp
    · rw [min_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · rw [min_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
      ring

end Learner

end FedzechkinaChuJaeger2018
