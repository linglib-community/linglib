module

public import Mathlib.Order.LatticeIntervals
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.Attitudes.Preference.ExpectedValue
public import Linglib.Core.Probability.UniformOn
public import Linglib.Fragments.English.Adjectives
public import Studies.Lassiter2015
public import Linglib.Core.MeasureTheory.Measure.Dirac

/-!
# Lassiter (2017): Graded Modality

This file formalizes chapters 4 to 8 of Lassiter.

Chapters 4 to 6 place the epistemic adjectives and auxiliaries on one scale. *Likely* and
*probable* measure a proposition by its probability, on a scale bounded below by the likelihood
of a contradiction and above by that of a tautology (`likelihood_univ`, `ofOrder_probability`),
and they are relative adjectives on it. *Certain* takes the scale's maximum as its standard and
*possible* its minimum, so the three are Kennedy's three positive forms on one closed
scale (`mem_likely_iff_relativePos`, `mem_certain_iff_maxStandardPos`,
`mem_possible_iff_minStandardPos`). A relative adjective on a closed scale is what Kennedy's
Interpretive Economy excludes, `Degree.Boundedness.Admits`, and what the book's own typology
(4.58) allows: *likely* is the counter-example of p. 82
(`coherent_and_not_admits_contextual_probability`). The distribution of *completely* and
*slightly*, which Kennedy reads off the scale, the book reads off the positive form (§4.2.9);
Kennedy's licensing is the book's quantified over the standards Interpretive Economy admits
(`licenses_iff_exists_admits`), so the two disagree exactly on adjectives like *likely*, which
license neither (`not_licensesPos_contextual`).

The auxiliaries are thresholds on the same scale (6.29), Lassiter 2015's `probMust` and
`probMight`, and at threshold one they are the adjectives *certain* and *possible*
(`mem_possible_iff_not_mem_certain_compl`). The ordering of the five thresholds of p. 152 makes
every item entail every weaker one (`antitone_pos`), and the strong theory, a *must* at
probability one, conflicts with that ordering (`not_strictMono_of_strong`), as does a *might* at
probability zero (`not_strictMono_of_might_zero`); with a positive threshold *might* is strictly
stronger than *possible* (`exists_mem_possible_not_mem_might`).

Chapters 7 and 8 give the scalar semantics of *good* and *ought*. Goodness is expected value, the
probability-weighted average of world values over a proposition
(`Desire.ExpectedValue.expectedValue`); it is an interval scale and intermediate on disjoint
unions. *Ought* is constrained rather than defined (`Constraints`): Sloman's Principle relates it
to goodness (an obligatory proposition is strictly better than each of its alternatives, after
Sloman), the Smith Principle restricts agglomeration to exhaustive pairs, and Weakening
closes obligation under disjunction. Sloman's Principle alone excludes conflicting oughts,
`ought φ` together with `ought ¬φ` (`Constraints.not_compl`), and the Smith Principle carries the
Smith argument from `ought (M ∨ S)` and `ought ¬M` to `ought S` (`Smith.ought_S`), on a sample
model that meets the Sloman requirements of all three. On Cariani's four-world
counter-model to Weakening, where `A` and `B` each beat their negations in expected value but
`A ∨ B` ties with its negation, Sloman's Principle and Weakening together make `ought A` and
`ought B` incompatible (`Cariani.not_ought_and`). The scalar reading of *ought* as a threshold on
an intermediate scale derives Weakening and, given ought-exclusivity, the Smith Principle; both
derivations live with the expected-value substrate.

## Implementation notes

Probabilities are probability measures read on their real values, as in Lassiter 2015, and
the probability scale is the closed real unit interval. The p. 82 claim that the likelihood
scale, if connected, is isomorphic to a finitely additive probability holds of these measures by
construction; its measurement-theoretic direction, from the axioms listed on p. 97 to a measure,
is not formalized, and the tower's own representation theorem uses Scott's cancellation
condition rather than those axioms. The book states the threshold ordering twice: strictly on
p. 152, θ_possible < θ_might < θ_likely < θ_must < θ_certain, which `StrictMono` records, and on
p. 156 with θ_possible = θ_might. That the Disjunctive Inference fails on the probability scale,
and that *more likely than* does not entail *might*, are Lassiter 2015's
`Lassiter2015.prob_refutes_rightUnion` and `Lassiter2015.weak_refutes_moreLikely_might`.

For chapters 7 and 8, the goodness scale and the alternative sets of the constraint set are
parameters; the consequences take the needed alternative memberships as hypotheses, the polar
sets `{φ, ¬φ}` being the book's weakest choice. The counter-model instantiates the scale by
expected value over an equiprobable domain of four worlds indexed by the truth values of `A` and
`B`.

## TODO

* The measurement-theoretic representation of p. 82 and p. 97, and its generalization to sets of
  measures when connectedness fails.
* The certainty scales of Analyses 2 and 3 (§5.1.6, §5.1.7), the first a half-open interval
  (`Degree.Boundedness.ofOrder_Ioc`) or a log transform.
* The experiment of §6.5 as `Data/Experiments`, and the modifier judgments of §4.2 as examples.

## References

* [lassiter-2017]
* [kennedy-2007]
* [lassiter-2015]
* [scott-1964]
* [cariani-2016]
* [sloman-1970]
-/

@[expose] public section

namespace Lassiter2017

open MeasureTheory

/-! ### Chapter 4: the likelihood scale -/

/-- The probability scale, the closed unit interval, on which *likely* and *probable* measure
propositions (§4.1). -/
abbrev Probability : Type := Set.Icc (0 : ℝ) 1

section Scale

open ComparativeProbability

variable {W : Type*} [MeasurableSpace W] (P : Measure W) [IsProbabilityMeasure P]

/-- A proposition's degree of likelihood is its probability. -/
noncomputable def likelihood (A : Set W) : Probability :=
  ⟨P.real A, measureReal_nonneg, measureReal_le_one⟩

@[simp] theorem coe_likelihood (A : Set W) : (likelihood P A : ℝ) = P.real A := rfl

/-- Nothing is likelier than a tautology (p. 84). -/
@[simp] theorem likelihood_univ : likelihood P Set.univ = ⊤ := Subtype.ext (by simp)

/-- Nothing is less likely than a contradiction (p. 84). -/
@[simp] theorem likelihood_empty : likelihood P ∅ = ⊥ := Subtype.ext (by simp)

end Scale

/-- The probability scale is totally closed (p. 82, p. 97). -/
theorem ofOrder_probability : Degree.Boundedness.ofOrder Probability = .closed :=
  Degree.Boundedness.ofOrder_Icc zero_le_one

/-! ### Two typologies of standards (§4.2.4–§4.2.6) -/

section Typology

open Degree

/-- A positive standard admits a scale as in (4.58), where a minimum or maximum standard needs its
endpoint and a contextual standard fits any scale. Interpretive Economy, `Boundedness.Admits`,
is (4.59), which confines the contextual standard to open scales. -/
def Coherent (b : Boundedness) (s : PositiveStandard) : Prop := s = .contextual ∨ b.Admits s

theorem coherent_of_admits {b : Boundedness} {s : PositiveStandard} (h : b.Admits s) :
    Coherent b s :=
  .inr h

theorem coherent_and_not_admits_contextual {b : Boundedness} (hb : b ≠ .open_) :
    Coherent b .contextual ∧ ¬ b.Admits .contextual :=
  ⟨.inl rfl, Boundedness.not_admits_contextual_of_ne_open hb⟩

/-- On the probability scale a contextual standard is coherent and Interpretive Economy excludes
it, so a relative *likely* is the counter-example of p. 82. -/
theorem coherent_and_not_admits_contextual_probability :
    Coherent (Boundedness.ofOrder Probability) .contextual ∧
      ¬ (Boundedness.ofOrder Probability).Admits .contextual :=
  coherent_and_not_admits_contextual (by rw [ofOrder_probability]; decide)

/-- The open-interval alternative of §4.2.6 keeps Interpretive Economy by making the scale
`(0, 1)`, which is open, at the cost of a degree for the tautology. -/
theorem ofOrder_Ioo_zero_one :
    Boundedness.ofOrder (Set.Ioo (0 : ℝ) 1) = .open_ ∧ (1 : ℝ) ∉ Set.Ioo (0 : ℝ) 1 :=
  ⟨Boundedness.ofOrder_Ioo, fun h ↦ lt_irrefl _ h.2⟩

/-- As the book licenses maximizers and minimizers (§4.2.9), *completely* takes the positive
form of a maximum adjective and *slightly* that of a minimum adjective, whatever the scale. -/
def LicensesPos : EndpointModifier → PositiveStandard → Prop
  | .maximizer, s => s = .maxEndpoint
  | .minimizer, s => s = .minEndpoint

instance : ∀ m s, Decidable (LicensesPos m s)
  | .maximizer, s => inferInstanceAs (Decidable (s = .maxEndpoint))
  | .minimizer, s => inferInstanceAs (Decidable (s = .minEndpoint))

theorem licenses_iff_exists_admits (m : EndpointModifier) (b : Boundedness) :
    b.Licenses m ↔ ∃ s, b.Admits s ∧ LicensesPos m s := by
  cases m <;> cases b <;> simp [Boundedness.Licenses, LicensesPos, Boundedness.Admits,
    Boundedness.HasMin, Boundedness.HasMax]

/-- A relative adjective licenses neither modifier, whatever its scale, which is why
*completely likely* and *slightly likely* lack a degree reading on a closed scale
((4.62), (4.63)), where Kennedy's licensing predicts one. -/
theorem not_licensesPos_contextual (m : EndpointModifier) :
    ¬ LicensesPos m .contextual := by
  cases m <;> simp [LicensesPos]

end Typology

/-! ### The epistemic adjectives on one scale (§4.2.2, §5.1.5, §5.2.5) -/

section Adjectives

open ComparativeProbability Degree

variable {W : Type*} [MeasurableSpace W] (P : Measure W) {A : Set W} {θ : ℝ}

/-- *Likely* and *probable* are relative adjectives, true above a contextual threshold. -/
def likely (θ : ℝ) : Set (Set W) := P.real ⁻¹' Set.Ioi θ

/-- *Certain* and *sure* take the maximum standard of the probability scale (§5.1.5). -/
def certain : Set (Set W) := P.real ⁻¹' Set.Ici 1

/-- *Possible* takes the minimum standard of the probability scale (§5.2.5). -/
def possible : Set (Set W) := P.real ⁻¹' Set.Ioi 0

theorem mem_possible_iff : A ∈ possible P ↔ 0 < P.real A := Iff.rfl

/-- Certainty entails likelihood (§5.1.4). -/
theorem certain_subset_likely (hθ : θ < 1) : certain P ⊆ likely P θ :=
  fun _ h ↦ lt_of_lt_of_le hθ h

/-- Likelihood entails possibility (§5.2.3). -/
theorem likely_subset_possible (hθ : 0 ≤ θ) : likely P θ ⊆ possible P :=
  fun _ h ↦ lt_of_le_of_lt hθ h

variable [IsProbabilityMeasure P]

theorem mem_certain_iff : A ∈ certain P ↔ P.real A = 1 :=
  ⟨fun h ↦ le_antisymm measureReal_le_one h, fun h ↦ h.ge⟩

theorem mem_likely_iff_relativePos (θ : Probability) :
    A ∈ likely P θ ↔ RelativePos (likelihood P) θ A :=
  Iff.rfl

theorem mem_certain_iff_maxStandardPos :
    A ∈ certain P ↔ MaxStandardPos (likelihood P) A := by
  rw [mem_certain_iff, MaxStandardPos, Subtype.ext_iff, coe_likelihood,
    Set.Icc.coe_top]

theorem mem_possible_iff_minStandardPos :
    A ∈ possible P ↔ MinStandardPos (likelihood P) A := by
  rw [mem_possible_iff, MinStandardPos, ← Subtype.coe_lt_coe, coe_likelihood,
    Set.Icc.coe_bot]

/-- The English fragment agrees, since its *possible* takes the minimum standard and its
*impossible* the maximum of the dual (§5.2.5). The fragment's possibility scale is only lower
closed; the maximum of the probability scale is the book's claim that *possible* shares the scale
of *likely*. -/
example : English.Adjectives.possible.standard = .minEndpoint ∧
    English.Adjectives.impossible.standard = .maxEndpoint := by
  decide

/-- *Certain* and *possible* are [lassiter-2015]'s *must* and *might* at threshold one, the
strong auxiliaries (p. 156), and so duals, `A` being possible iff its negation is not certain. -/
theorem mem_possible_iff_not_mem_certain_compl [DiscreteMeasurableSpace W] :
    A ∈ possible P ↔ Aᶜ ∉ certain P := by
  have h := Lassiter2015.probMight_iff_not_probMust_compl P 1 A
  rwa [Lassiter2015.probMight, sub_self] at h

/-- *n percent A* compares the degree with the scale's maximum (4.51b). -/
def percent (n : ℝ) : Set (Set W) := {A | P.real A / P.real Set.univ = n / 100}

/-- *n percent likely* is interpretable because the maximum is a degree of the scale
(p. 121–122). -/
theorem mem_percent_iff (n : ℝ) : A ∈ percent P n ↔ P.real A = n / 100 := by
  simp [percent]

/-- *Fifty percent likely* is "exactly as likely as not" (p. 103). -/
theorem mem_percent_fifty_iff [DiscreteMeasurableSpace W] :
    A ∈ percent P 50 ↔ P.real A = P.real Aᶜ := by
  rw [mem_percent_iff]
  have := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  constructor <;> intro h <;> linarith

end Adjectives

/-! ### Chapter 6: the thresholds -/

/-- The five epistemic items of the ordering on p. 152, weakest first. -/
inductive EpistemicItem
  | possible | might | likely | must | certain
  deriving DecidableEq

namespace EpistemicItem

/-- The rank of an item in the strength ordering. -/
def rank : EpistemicItem → Fin 5
  | .possible => 0 | .might => 1 | .likely => 2 | .must => 3 | .certain => 4

theorem rank_injective : Function.Injective rank := fun a b h ↦ by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

instance : LinearOrder EpistemicItem := LinearOrder.lift' rank rank_injective

/-- *Must* and *certain* compare the probability weakly with their thresholds, *might*, *likely*
and *possible* strictly (6.29). -/
def comparison : EpistemicItem → Degree.Comparison
  | .must | .certain => .ge
  | .possible | .might | .likely => .gt

end EpistemicItem

section Thresholds

open ComparativeProbability Degree

variable {W : Type*} [MeasurableSpace W] (P : Measure W) (θ : EpistemicItem → ℝ) {A : Set W}

/-- The positive form of an item under a profile of thresholds. -/
def pos (i : EpistemicItem) : Set (Set W) := P.real ⁻¹' i.comparison.interval (θ i)

theorem mem_pos_iff (i : EpistemicItem) : A ∈ pos P θ i ↔ i.comparison.Rel (P.real A) (θ i) :=
  Comparison.mem_interval _ _ _

/-- (6.29a) is [lassiter-2015]'s *must*. -/
theorem mem_pos_must_iff : A ∈ pos P θ .must ↔ Lassiter2015.probMust P (θ .must) A := Iff.rfl

/-- (6.29b) with the duality `θ_might = 1 − θ_must` of p. 156 is [lassiter-2015]'s *might*, so
*might* `A` holds iff *must* `¬A` fails. -/
theorem mem_pos_might_iff [DiscreteMeasurableSpace W] [IsProbabilityMeasure P]
    (hdual : θ .might = 1 - θ .must) :
    A ∈ pos P θ .might ↔ Aᶜ ∉ pos P θ .must := by
  have h := Lassiter2015.probMight_iff_not_probMust_compl P (θ .must) A
  rw [Lassiter2015.probMight, ← hdual] at h
  exact h

theorem pos_certain (h : θ .certain = 1) : pos P θ .certain = certain P := by
  simp [pos, EpistemicItem.comparison, certain, h]

theorem pos_possible (h : θ .possible = 0) : pos P θ .possible = possible P := by
  simp [pos, EpistemicItem.comparison, possible, h]

/-- The ordering of p. 152 makes the positive forms antitone in strength, so *certain* entails
*must* (§6.1), *must* entails *likely* (6.14), *likely* entails *might* (6.18), and *might*
entails *possible* (§6.5). -/
theorem antitone_pos (hθ : StrictMono θ) : Antitone (pos P θ) := by
  intro i j hij A hA
  rw [mem_pos_iff] at hA ⊢
  rcases hij.lt_or_eq with h | rfl
  · have hlt : θ i < θ j := hθ h
    cases i <;> cases j <;>
      simp only [EpistemicItem.comparison, Comparison.rel_ge, Comparison.rel_gt] at hA ⊢ <;>
      first | exact absurd h (by decide) | linarith
  · exact hA

/-- *Must* `A` leaves `¬A` at most `1 − θ_must` likely, so above one half `A` is more likely
than its negation (6.16). -/
theorem compl_lt_of_mem_must [DiscreteMeasurableSpace W] [IsProbabilityMeasure P] {θ' : ℝ}
    (hθ : 1 / 2 < θ') (h : A ∈ P.real ⁻¹' Set.Ici θ') : P.real Aᶜ < P.real A := by
  have := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  change θ' ≤ P.real A at h
  linarith

/-- What is more likely than not is a *might*, given `θ_might ≤ 1/2` (6.19). -/
theorem mem_might_of_compl_lt [DiscreteMeasurableSpace W] [IsProbabilityMeasure P] {θ' : ℝ}
    (hθ : θ' ≤ 1 / 2) (h : P.real Aᶜ < P.real A) : A ∈ P.real ⁻¹' Set.Ioi θ' := by
  have := probReal_add_probReal_compl (μ := P) (.of_discrete : MeasurableSet A)
  change θ' < P.real A
  linarith

/-- Under the dualities of *must* and *might* and of *certain* and *possible*, *certain* is
stronger than *must* iff *might* is stronger than *possible* (p. 164). -/
theorem must_lt_certain_iff_possible_lt_might (hmm : θ .might = 1 - θ .must)
    (hcp : θ .possible = 1 - θ .certain) : θ .must < θ .certain ↔ θ .possible < θ .might := by
  constructor <;> intro h <;> linarith

/-- The strong theory, a *must* at probability one, conflicts with the ordering of p. 152 when
no threshold exceeds the tautology's degree, since *must* cannot then be weaker than *certain*
(§6.1). -/
theorem not_strictMono_of_strong (h : θ .must = 1) (hc : θ .certain ≤ 1) : ¬ StrictMono θ :=
  fun hθ ↦ (hθ (show EpistemicItem.must < .certain by decide)).not_ge (h ▸ hc)

/-- Likewise a *might* at probability zero cannot be stronger than *possible* (p. 152). -/
theorem not_strictMono_of_might_zero (h : θ .might = 0) (hp : 0 ≤ θ .possible) :
    ¬ StrictMono θ :=
  fun hθ ↦ (hθ (show EpistemicItem.possible < .might by decide)).not_ge (h ▸ hp)

end Thresholds

/-- With a positive threshold, *might* is strictly stronger than *possible* (§6.5), since a
proposition of probability exactly `θ` is possible and not a *might*. -/
theorem exists_mem_possible_not_mem_might {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) :
    ∃ P : Measure (Fin 2), IsProbabilityMeasure P ∧ ∃ A : Set (Fin 2),
      A ∈ possible P ∧ A ∉ P.real ⁻¹' Set.Ioi θ := by
  have hw (i : Fin 2) : 0 ≤ (![θ, 1 - θ] : Fin 2 → ℝ) i := by
    fin_cases i <;> simp <;> linarith
  set P : Measure (Fin 2) := ∑ i, ENNReal.ofReal (![θ, 1 - θ] i) • Measure.dirac i with hP
  have hP0 : P.real {0} = θ := by rw [hP, Measure.sum_ofReal_smul_dirac_real_apply hw]; simp
  refine ⟨P, Measure.isProbabilityMeasure_sum_ofReal_smul_dirac hw (by simp [Fin.sum_univ_two]),
    {0}, ?_, ?_⟩
  · rwa [mem_possible_iff, hP0]
  · simp only [Set.mem_preimage, Set.mem_Ioi, hP0, lt_irrefl, not_false_eq_true]

open Desire.ExpectedValue

section Constraints

variable {W : Type*} {μ : Set W → ℝ} {ought : Set W → Prop} {alt : Set W → Set (Set W)}

/-- The constraints on *ought* relative to a goodness scale `μ` and alternative sets `alt` are
Sloman's Principle, the Smith Principle, and Weakening. -/
structure Constraints (μ : Set W → ℝ) (ought : Set W → Prop) (alt : Set W → Set (Set W)) :
    Prop where
  sloman : ∀ ⦃φ⦄, ought φ → ∀ ψ ∈ alt φ, ψ ≠ φ → μ ψ < μ φ
  smith : ∀ ⦃φ ψ⦄, φ ∪ ψ = Set.univ → ought φ → ought ψ → ought (φ ∩ ψ)
  weakening : ∀ ⦃φ ψ⦄, ought φ → ought ψ → ought (φ ∪ ψ)

variable [Nonempty W] (h : Constraints μ ought alt) {φ ψ : Set W}
include h

theorem Constraints.not_compl (hφ : φᶜ ∈ alt φ) (hφ' : φ ∈ alt φᶜ) (h₁ : ought φ) :
    ¬ ought φᶜ := fun h₂ ↦
  lt_asymm (h.sloman h₁ _ hφ ne_compl_self.symm) (h.sloman h₂ _ hφ' ne_compl_self)

theorem Constraints.not_and_of_le (hne : (φ ∪ ψ)ᶜ ∈ alt (φ ∪ ψ))
    (hle : μ (φ ∪ ψ) ≤ μ (φ ∪ ψ)ᶜ) : ¬ (ought φ ∧ ought ψ) := fun ⟨h₁, h₂⟩ ↦
  (h.sloman (h.weakening h₁ h₂) _ hne ne_compl_self.symm).not_ge hle

end Constraints

section Goodness

variable {W : Type*} [MeasurableSpace W]

/-- Goodness as expected value over the whole domain, the book's default `prob(D) = 1`. -/
noncomputable def goodness (pr : MeasureTheory.Measure W) (V : W → ℝ) (φ : Set W) : ℝ :=
  expectedValue pr V Set.univ φ

end Goodness

attribute [local simp] goodness expectedValue_eq_sum Finset.sum_filter Fintype.sum_prod_type
  Fintype.sum_bool MeasureTheory.uniformOn_univ_real_singleton

/-! ### The Smith scenario -/

/-- Smith can do military service, alternative service, or neither. -/
inductive Smith
  | military
  | service
  | neither
  deriving DecidableEq

namespace Smith

instance : Fintype Smith := ⟨{military, service, neither}, fun w ↦ by cases w <;> simp⟩

instance : MeasurableSpace Smith := ⊤

instance : MeasurableSingletonClass Smith := ⟨fun _ ↦ trivial⟩

/-- Smith serves in the military. -/
def M : Set Smith := {military}

/-- Smith performs alternative service. -/
def S : Set Smith := {service}

/-- The sample model's prior makes the three options equiprobable. -/
noncomputable abbrev prior : MeasureTheory.Measure Smith :=
  ProbabilityTheory.uniformOn Set.univ

/-- In the sample model only alternative service is worth anything. -/
def value : Smith → ℝ := fun w ↦ if w = service then 1 else 0

private theorem card_eq : Fintype.card Smith = 3 := rfl

attribute [local simp] M S value card_eq Finset.univ Fintype.elems Finset.sum_insert

theorem sloman :
    goodness prior value (M ∪ S)ᶜ < goodness prior value (M ∪ S) ∧
      goodness prior value M < goodness prior value Mᶜ ∧
      goodness prior value Sᶜ < goodness prior value S := by
  classical norm_num [-Finset.sum_const]

theorem ought_S {μ : Set Smith → ℝ} {ought : Set Smith → Prop} {alt : Set Smith → Set (Set Smith)}
    (h : Constraints μ ought alt) (h₁ : ought (M ∪ S)) (h₂ : ought Mᶜ) : ought S :=
  have : (M ∪ S) ∩ Mᶜ = S := by ext w; cases w <;> simp
  this ▸ h.smith (by ext w; cases w <;> simp) h₁ h₂

end Smith

/-! ### Cariani's counter-model to Weakening -/

namespace Cariani

/-- Four equiprobable worlds, indexed by the truth values of `A` and `B`. -/
abbrev World := Bool × Bool

/-- The uniform prior. -/
noncomputable abbrev prior : MeasureTheory.Measure World := ProbabilityTheory.uniformOn Set.univ

/-- A world is worth `100` at `A ∧ B`, `-50` at `A ∧ ¬B` and `¬A ∧ B`, and `0` at `¬A ∧ ¬B`. -/
def value : World → ℝ
  | (true, true) => 100
  | (true, false) => -50
  | (false, true) => -50
  | (false, false) => 0

/-- The proposition `A`. -/
def A : Set World := {w | w.1 = true}

/-- The proposition `B`. -/
def B : Set World := {w | w.2 = true}

attribute [local simp] A B value

theorem goodness_A : goodness prior value A = 25 := by
  classical norm_num [-Finset.sum_const]

theorem goodness_compl_A : goodness prior value Aᶜ = -25 := by
  classical norm_num [-Finset.sum_const]

theorem goodness_B : goodness prior value B = 25 := by
  classical norm_num [-Finset.sum_const]

theorem goodness_compl_B : goodness prior value Bᶜ = -25 := by
  classical norm_num [-Finset.sum_const]

theorem goodness_union : goodness prior value (A ∪ B) = 0 := by
  classical norm_num [-Finset.sum_const]

theorem goodness_compl_union : goodness prior value (A ∪ B)ᶜ = 0 := by
  classical norm_num [-Finset.sum_const]

theorem sloman :
    goodness prior value Aᶜ < goodness prior value A ∧
      goodness prior value Bᶜ < goodness prior value B := by
  rw [goodness_A, goodness_compl_A, goodness_B, goodness_compl_B]; norm_num

theorem not_ought_and {ought : Set World → Prop} {alt : Set World → Set (Set World)}
    (h : Constraints (goodness prior value) ought alt) (halt : (A ∪ B)ᶜ ∈ alt (A ∪ B)) :
    ¬ (ought A ∧ ought B) :=
  h.not_and_of_le halt (goodness_compl_union ▸ goodness_union ▸ le_rfl)

end Cariani

end Lassiter2017
