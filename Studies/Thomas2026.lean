module

public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Data.Examples.Thomas2026
public import Mathlib.Probability.ConditionalProbability

/-!
# Thomas (2026): A Probabilistic, Question-Based Approach to Additivity

This file formalizes [thomas-2026]'s felicity conditions for additive *too*, which unify its
canonical use, a second answer to a salient question, (2), with the argument-building use in
which the antecedent and the prejacent together argue for a conclusion, (1) and (18). The
account is stated in an inquisitive question semantics with a listener's probability measure
over worlds. A proposition is relevant to a question if it shifts the probability of one of the
question's alternatives, (61); it answers the question if it raises the probability of some
resolution, a nonempty set of alternatives, by a factor exceeding that of every resolution not
entailed by it, (62); and one proposition evidences a resolution more strongly than another if
it gives it the higher conditional probability, (63). *Too* requires an antecedent proposition
and a question relevant to the discourse such that the antecedent answers the question, the
conjunction of antecedent and prejacent answers it and evidences its resolution more strongly
than the antecedent alone, and the prejacent neither entails that resolution nor could be
weakened without weakening the evidence, (64).

The definitions are `Relevant`, `IsResolutionOf`, `Answers`, `EvidencesMore` and
`TooFelicitous`. Answering needs a positive prior on the evidence, `IsResolutionOf.ne_zero`,
and trivial evidence answers nothing, `not_answers_univ`; the resolutions a proposition
evidences are nested, `IsResolutionOf.subset_or_subset`, and a singleton resolution makes the
proposition relevant to the question, `IsResolutionOf.relevant`. The paper's arguments for
its examples reduce to three patterns: an antecedent entailing a resolution gives it
probability one, `cond_eq_one_of_subset`, so a conjunction entailing what the antecedent
leaves uncertain evidences it more strongly, `evidencesMore_of_subset`, as in (68); a
prejacent that leaves every resolution's conditional probability unchanged fails the
conjunction condition, `not_tooFelicitous_of_cond_eq`, as in (25) and (72); a prejacent
entailing the evidenced resolution fails the first prejacent condition,
`not_tooFelicitous_of_subset`, as in (11) and (29); and evidence raising every candidate
resolution by the same factor answers no question, `not_answers_of_impact_eq`, as in (71).

## Implementation notes

The listener's belief state is a probability measure, and conditioning is mathlib's
`ProbabilityTheory.cond`, so the paper's statements hold at every prior. The resolution
evidenced by a proposition, which the paper calls unique, is only unique up to nesting: the
dominance clause of (62) waives resolutions containing the candidate, so the felicity
condition quantifies existentially over the resolution that the conjunction evidences and
the prejacent conditions constrain. Bayesian belief revision through a speaker model, (57)–(59),
is not formalized: the antecedent is the proposition the listener learns. The examples are the
rows of `Data.Examples.Thomas2026`, with the paper's diagnosis of each *too* recorded as a
feature.

## References

* [thomas-2026]
* [beaver-clark-2008]
* [buring-2003]
* [kripke-2009]
* [roberts-1996]
* [rullmann-2003]
-/

@[expose] public section

namespace Thomas2026

open MeasureTheory ProbabilityTheory Question
open scoped ENNReal

variable {W : Type*} [MeasurableSpace W] (μ : Measure W)

/-! ### Relevance and answerhood (section 5.1.3) -/

/-- Relevance (61a): a question is relevant to a question if some alternative of the first
shifts the probability of some alternative of the second. -/
def Relevant (R S : Question W) : Prop :=
  ∃ A ∈ alt R, ∃ A' ∈ alt S, μ[A' | A] ≠ μ A'

/-- The impact of a proposition on a proposition: the factor by which learning the first
raises the probability of the second. -/
noncomputable def impact (R A : Set W) : ℝ≥0∞ := μ[A | R] / μ A

/-- Answerhood (62): a nonempty set of alternatives is the resolution of a question evidenced
by a proposition when the proposition raises the probability of its conjunction and impacts
it more than the conjunction of any set of alternatives not entailed by it. -/
structure IsResolutionOf (Q : Question W) (𝒜 : Set (Set W)) (R : Set W) : Prop where
  subset_alt : 𝒜 ⊆ alt Q
  nonempty : 𝒜.Nonempty
  raises : μ (⋂₀ 𝒜) < μ[⋂₀ 𝒜 | R]
  dominates : ∀ 𝒜' ⊆ alt Q, 𝒜'.Nonempty → ¬ ⋂₀ 𝒜 ⊆ ⋂₀ 𝒜' →
    impact μ R (⋂₀ 𝒜') < impact μ R (⋂₀ 𝒜)

/-- A proposition answers a question when it evidences some resolution of it. -/
def Answers (R : Set W) (Q : Question W) : Prop := ∃ 𝒜, IsResolutionOf μ Q 𝒜 R

/-- (63): a proposition evidences a resolution more strongly than another proposition. -/
def EvidencesMore (A R R' : Set W) : Prop := μ[A | R'] < μ[A | R]

/-! ### The felicity conditions of *too* (section 5.2) -/

/-- (64a)–(64c): the antecedent answers the question; the conjunction of antecedent and
prejacent answers it and evidences its resolution more strongly than the antecedent; the
prejacent does not entail that resolution, and any weaker prejacent would evidence it less
strongly. -/
def TooFelicitous (π ant : Set W) (rq : Question W) : Prop :=
  Answers μ ant rq ∧ ∃ 𝒜, IsResolutionOf μ rq 𝒜 (ant ∩ π) ∧
    EvidencesMore μ (⋂₀ 𝒜) (ant ∩ π) ant ∧ ¬ π ⊆ ⋂₀ 𝒜 ∧
    ∀ S, π ⊂ S → EvidencesMore μ (⋂₀ 𝒜) (ant ∩ π) (ant ∩ S)

/-- (64): *too* is licensed by an antecedent and a question relevant to a question in the
discourse tree. -/
def Too (π ant : Set W) (rq dq : Question W) : Prop :=
  TooFelicitous μ π ant rq ∧ Relevant μ rq dq

variable {μ} {Q rq : Question W} {𝒜 : Set (Set W)} {A R R' π ant : Set W}

/-! ### Consequences -/

theorem IsResolutionOf.ne_zero (h : IsResolutionOf μ Q 𝒜 R) : μ R ≠ 0 := by
  intro h0
  have := h.raises
  rw [cond_eq_zero_of_meas_eq_zero h0] at this
  simp at this

theorem Answers.ne_zero (h : Answers μ R Q) : μ R ≠ 0 :=
  let ⟨_, h⟩ := h
  h.ne_zero

theorem IsResolutionOf.subset_or_subset {𝒜' : Set (Set W)} (h : IsResolutionOf μ Q 𝒜 R)
    (h' : IsResolutionOf μ Q 𝒜' R) : ⋂₀ 𝒜 ⊆ ⋂₀ 𝒜' ∨ ⋂₀ 𝒜' ⊆ ⋂₀ 𝒜 := by
  by_contra hcon
  rw [not_or] at hcon
  exact lt_asymm (h.dominates 𝒜' h'.subset_alt h'.nonempty hcon.1)
    (h'.dominates 𝒜 h.subset_alt h.nonempty hcon.2)

/-- An answer through a single alternative is relevant to the question (section 5.1.3). -/
theorem IsResolutionOf.relevant (h : IsResolutionOf μ Q {A} R) : Relevant μ (ofSet R) Q := by
  refine ⟨R, by simp, A, h.subset_alt rfl, ?_⟩
  have := h.raises
  rw [Set.sInter_singleton] at this
  exact this.ne'

/-- A prejacent leaving every resolution's conditional probability unchanged fails the conjunction
condition ((72), (25)). -/
theorem not_tooFelicitous_of_cond_eq
    (h : ∀ 𝒜 ⊆ alt rq, μ[⋂₀ 𝒜 | ant ∩ π] = μ[⋂₀ 𝒜 | ant]) : ¬ TooFelicitous μ π ant rq := by
  rintro ⟨-, 𝒜, hres, hmore, -, -⟩
  rw [EvidencesMore, h 𝒜 hres.subset_alt] at hmore
  exact lt_irrefl _ hmore

/-- A prejacent entailing every resolution the conjunction evidences fails the first prejacent
condition: *he's ecstatic*, (11), and *he stole the cookies*, (29b). -/
theorem not_tooFelicitous_of_subset (h : ∀ 𝒜, IsResolutionOf μ rq 𝒜 (ant ∩ π) → π ⊆ ⋂₀ 𝒜) :
    ¬ TooFelicitous μ π ant rq := by
  rintro ⟨-, 𝒜, hres, -, hnot, -⟩
  exact hnot (h 𝒜 hres)

/-- Evidence raising every candidate resolution equally answers no question whose candidates are not
all nested (71). -/
theorem not_answers_of_impact_eq {c : ℝ≥0∞}
    (hc : ∀ 𝒜 ⊆ alt Q, 𝒜.Nonempty → impact μ R (⋂₀ 𝒜) = c)
    (hcomp : ∀ 𝒜 ⊆ alt Q, 𝒜.Nonempty → ∃ 𝒜' ⊆ alt Q, 𝒜'.Nonempty ∧ ¬ ⋂₀ 𝒜 ⊆ ⋂₀ 𝒜') :
    ¬ Answers μ R Q := by
  rintro ⟨𝒜, h⟩
  obtain ⟨𝒜', hsub, hne, hnot⟩ := hcomp 𝒜 h.subset_alt h.nonempty
  have := h.dominates 𝒜' hsub hne hnot
  rw [hc 𝒜 h.subset_alt h.nonempty, hc 𝒜' hsub hne] at this
  exact lt_irrefl _ this

theorem TooFelicitous.answers_inter (h : TooFelicitous μ π ant rq) :
    Answers μ (ant ∩ π) rq ∧ μ (ant ∩ π) ≠ 0 :=
  let ⟨_, 𝒜, hres, _⟩ := h
  ⟨⟨𝒜, hres⟩, hres.ne_zero⟩

variable [IsProbabilityMeasure μ]

theorem cond_univ_apply : μ[A | Set.univ] = μ A := by
  rw [cond_apply MeasurableSet.univ, measure_univ, inv_one, one_mul, Set.univ_inter]

theorem not_answers_univ : ¬ Answers μ Set.univ Q := by
  rintro ⟨𝒜, h⟩
  have := h.raises
  rw [cond_univ_apply] at this
  exact lt_irrefl _ this

variable [DiscreteMeasurableSpace W]

theorem cond_eq_one_of_subset (h : R ⊆ A) (h0 : μ R ≠ 0) : μ[A | R] = 1 := by
  rw [cond_apply .of_discrete, Set.inter_eq_left.2 h,
    ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)]

/-- A conjunction entailing a resolution that the antecedent leaves uncertain evidences it
more strongly, the conjunction condition in (68). -/
theorem evidencesMore_of_subset (hR : R ⊆ A) (h0 : μ R ≠ 0) (h : μ[A | R'] < 1) :
    EvidencesMore μ A R R' := by
  rw [EvidencesMore, cond_eq_one_of_subset hR h0]
  exact h

end Thomas2026
