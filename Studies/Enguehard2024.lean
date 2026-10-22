module

public import Linglib.Data.Examples.Enguehard2024
public import Studies.TieuEtAl2020
public import Linglib.Fragments.English.Nouns
public import Linglib.Fragments.English.Pronouns
public import Linglib.Syntax.Number.Resolve
public import Linglib.Logic.Trivalent.Pointwise
public import Linglib.Pragmatics.Competition
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Core.MeasureTheory.MeasurableSpace.Constructions
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.Order.Filter.Extr

/-!
# Enguehard (2024): What number marking on indefinites means: conceivability presuppositions and sensitivity to probabilities

Singular and plural indefinites infer exactly one witness and at least two, (1), but under
negation both mean that there is none, (2)–(3). Following Spector and Zweig these inferences are
scalar enrichments of a weak existential meaning, the exhaustifications of `TieuEtAl2020`, and
the cardinalities a number fits are those English gives a referent of that many individuals.
Enguehard shows that what survives negation is a conceivability presupposition (7): each number
presupposes that a witness set it fits is conceivable, so a book has no *table of contents* and
no *chapters*, (5)–(6).

In a production experiment the share of plural among negated indefinites rises gradiently with
the probability that symbols come in multiples, and both numbers are produced at parity,
(10)–(11). Productions form a kernel from conditions, and the categorical rule that Maximize
Presupposition derives from Farkas and de Swart's prototypicality generalization (8) is a
zero-one law, which the experiment refutes (§4.1). Enguehard's account has speakers prefer
referents that later continuations can resume: a negated indefinite sets one up, as in the
bilateral dynamic semantics of Krahmer and Muskens and of Elliott, and a pronoun resuming it bears
its number, as Sudo assumes, and must fit the witness set, (14)–(23). The preference yields the
conceivability presupposition, which fails exactly where the chance of ineffability is certain
(§6).

## Main statements

* `useful_iff_negated_ne_zero`: preferring useful referents yields the conceivability
  presupposition.
* `negated_ne_zero_iff_ineffability_ne_one`: the presupposition holds exactly when ineffability
  is not certain.
* `unblocked_mpPresup_isCompl`, `not_H2_of_isZeroOneMeasure`: Maximize Presupposition puts the
  two numbers in complementary distribution, and a speaker in complementary distribution is not
  gradient.
* `not_H2_of_follows_bestGuess`: a speaker producing only best guesses is not gradient either.

## Implementation notes

* Worlds are witness cardinalities, as in `TieuEtAl2020`, and the conceivable cardinalities are a
  parameter, so the presupposition is constant across worlds. A negated indefinite is a trivalent
  proposition `ℕ → SignType`, undefined where its presupposition fails.
* A production is a negated indefinite of some number or another strategy (`none`), the three
  categories of Figure 2, and the hypotheses concern the productions conditioned on the
  indefinites, the second analysis of footnote 8. Figure 2 is a plot, so no share is typed.
* The limiting case takes the conceivable cardinalities to be those of positive probability, and
  a condition enters as the probability of multiples given a witness.
* The negated indefinites of (2) and the negative ones of (3) are both `Polarity.negative`.

## TODO

* Exact minimization makes the best guess a majority rule (`bestGuess_plural_iff`), so a speaker
  producing only best guesses is categorical off parity, while Figure 2 shows both numbers in
  every intermediate condition. The gradience needs a probabilistic choice rule over
  `ineffability`, or variation in the distribution each participant saw (footnote 5), which the
  paper leaves open.
* Projection out of questions (§2) awaits a question semantics over trivalent propositions.

## References

* [enguehard-2024]
* [spector-2007b]
* [zweig-2009]
* [tieu-etal-2020]
* [farkas-de-swart-2010]
* [sauerland-2003]
* [krahmer-muskens-1995]
* [elliott-2020]
* [sudo-2012]
-/

@[expose] public section

namespace Enguehard2024

open MeasureTheory ProbabilityTheory Exhaustification
open scoped ENNReal NNReal
open TieuEtAl2020 (weak strong singular)
open English.Nouns (numberSystem)

/-! ### The number inference -/

/-- The number inference of a positive indefinite, (1), holds of the witness cardinalities that
English gives the number. -/
def inference (n : Number) : Set ℕ := {k | 1 ≤ k ∧ numberSystem.ofCard k = n}

@[simp] theorem inference_singular : inference .singular = singular := by
  ext k
  rcases k with _ | _ | _ | _ | k <;>
    simp [inference, Number.System.ofCard, Number.fromCard, numberSystem, singular]

@[simp] theorem inference_plural : inference .plural = strong := by
  ext k
  rcases k with _ | _ | _ | _ | k <;>
    simp [inference, Number.System.ofCard, Number.fromCard, numberSystem, strong]

theorem inference_subset_weak (n : Number) : inference n ⊆ weak := fun _ hk ↦ hk.1

theorem compl_weak : weakᶜ = {0} := by
  ext k; simp [weak]

/-- The singular's inference is its weak meaning exhaustified against (4), *two*, whose meaning
is the plural's inference. -/
theorem exhIE_weak_inference_plural :
    exhIE {weak, inference .plural} weak = inference .singular := by
  rw [inference_plural, inference_singular,
    exhIE_pair_sdiff (φ := weak) (d := strong) ⟨1, by simp [weak, strong]⟩]
  ext k
  simp only [weak, strong, singular, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  omega

/-- The plural's inference is its weak meaning exhaustified against the enriched singular. -/
theorem exhIE_weak_inference_singular :
    exhIE {weak, inference .singular} weak = inference .plural := by
  simpa using TieuEtAl2020.exhIE_weak

/-- Under negation every competitor is entailed, so nothing is excluded and either number
conveys that there is no witness, (2)–(3). -/
theorem exhIE_compl (m : Number) : exhIE {weakᶜ, (inference m)ᶜ} weakᶜ = {0} := by
  rw [← compl_weak]
  ext k
  rw [mem_exhIE_iff]
  refine ⟨And.left, fun h ↦ ⟨h, fun a ha ↦ ?_⟩⟩
  have hsub : weakᶜ ⊆ a := by
    rcases Set.mem_insert_iff.1 ha.1 with rfl | h
    · exact subset_rfl
    · exact (Set.mem_singleton_iff.1 h) ▸ Set.compl_subset_compl.2 (inference_subset_weak m)
  exact absurd ha (not_isInnocentlyExcludable_of_phi_subset (Set.toFinite _)
    ⟨0, by simp [weak]⟩ hsub)

/-! ### The rows of (1)–(3) -/

/-- The rows name the numbers by these strings. -/
def numberTable : List (String × Number) := [("sg", .singular), ("pl", .plural)]

/-- The rows name the polarities by these strings, negated (2) and negative (3) indefinites
both being negative. -/
def polarityTable : List (String × Polarity) :=
  [("positive", .positive), ("negated", .negative), ("negative", .negative)]

/-- The rows print the inferences as these sets of witness cardinalities. -/
def inferenceTable : List (String × Set ℕ) :=
  [("one", {1}), ("atLeastTwo", {k | 2 ≤ k}), ("zero", {0})]

/-- An indefinite of (1)–(3) records its number, its polarity and the inference it carries. -/
structure IndefiniteRow where
  number : Number
  polarity : Polarity
  inference : Set ℕ

/-- An example yields a row when it records each feature. -/
def IndefiniteRow.ofDatum (ex : Datum) : Option IndefiniteRow := do
  pure ⟨← ex.parse? "number" numberTable, ← ex.parse? "polarity" polarityTable,
    ← ex.parse? "inference" inferenceTable⟩

/-- The examples (1)–(3) give the indefinite rows. -/
def indefiniteRows : List IndefiniteRow := Examples.all.filterMap IndefiniteRow.ofDatum

private theorem indefiniteRows_eq :
    indefiniteRows = [⟨.singular, .positive, {1}⟩, ⟨.plural, .positive, {k | 2 ≤ k}⟩,
      ⟨.singular, .negative, {0}⟩, ⟨.plural, .negative, {0}⟩,
      ⟨.singular, .negative, {0}⟩, ⟨.plural, .negative, {0}⟩] := rfl

/-- A positive indefinite carries the inference of its number and a negated one the empty
witness set, whatever its number, (1)–(3). -/
theorem indefiniteRows_inference : ∀ r ∈ indefiniteRows,
    r.inference = if r.polarity = .positive then inference r.number else {0} := by
  rw [indefiniteRows_eq]
  simp [singular, strong]

/-! ### The conceivability presupposition -/

open Classical in
/-- The negated indefinite of number `n`, where the conceivable witness cardinalities are `K`,
asserts that there is no witness and presupposes that a cardinality its number fits is
conceivable, (7). -/
noncomputable def negated (K : Set ℕ) (n : Number) : ℕ → SignType :=
  {_k | (K ∩ inference n).Nonempty}.indicator fun k ↦ SignType.ofProp (k ∈ weakᶜ)

theorem negated_ne_zero_iff {K : Set ℕ} {n : Number} {k : ℕ} :
    negated K n k ≠ 0 ↔ (K ∩ inference n).Nonempty := by
  simp [negated]

/-- Both numbers assert the same thing under negation, so they agree wherever both are
defined. -/
theorem negated_eq_negated {K : Set ℕ} {n n' : Number} {k : ℕ} (h : negated K n k ≠ 0)
    (h' : negated K n' k ≠ 0) : negated K n k = negated K n' k := by
  simp_all [negated]

/-- The presupposition projects through negation and out of a conditional antecedent (§2). -/
theorem support_negated_projects (K : Set ℕ) (n : Number) (q : ℕ → SignType) :
    Function.support (-negated K n) = Function.support (negated K n) ∧
      Function.support (fun k ↦ (-negated K n k).joinMiddle (q k)) ⊆
        Function.support (negated K n) :=
  ⟨by ext; simp, fun k hk ha ↦ hk (by simp [ha])⟩

/-- A book has at most one table of contents. -/
def tableOfContents : Set ℕ := Set.Iic 1

/-- A book never has a single chapter. -/
def chapters : Set ℕ := {1}ᶜ

/-- The singular presupposition of *table of contents* is met and the plural one fails, (5). -/
theorem negated_tableOfContents :
    negated tableOfContents .singular 0 ≠ 0 ∧ negated tableOfContents .plural 0 = 0 := by
  refine ⟨negated_ne_zero_iff.2 ⟨1, Set.mem_Iic.2 le_rfl, by simp [singular]⟩,
    not_not.1 fun h ↦ ?_⟩
  obtain ⟨k, hk, h⟩ := negated_ne_zero_iff.1 h
  simp only [tableOfContents, inference_plural, strong, Set.mem_Iic, Set.mem_ofPred_eq] at hk h
  omega

/-- The plural presupposition of *chapters* is met and the singular one fails, (6). -/
theorem negated_chapters :
    negated chapters .plural 0 ≠ 0 ∧ negated chapters .singular 0 = 0 := by
  refine ⟨negated_ne_zero_iff.2 ⟨2, by simp [chapters], by simp [strong]⟩, not_not.1 fun h ↦ ?_⟩
  obtain ⟨_, hk, h⟩ := negated_ne_zero_iff.1 h
  exact hk (by simpa [singular] using h)

/-- The rows name the nouns, each standing for its conceivable cardinalities. -/
def nounTable : List (String × Set ℕ) :=
  [("tableOfContents", tableOfContents), ("chapters", chapters)]

/-- A negated indefinite of (5)–(6) records its noun's conceivable cardinalities, its number and
its judgment. -/
structure BookRow where
  noun : Set ℕ
  number : Number
  judgment : Judgment

/-- An example yields a row when it records each feature. -/
def BookRow.ofDatum (ex : Datum) : Option BookRow := do
  pure ⟨← ex.parse? "noun" nounTable, ← ex.parse? "number" numberTable, ex.judgment⟩

/-- The examples (5)–(6) give the book rows. -/
def bookRows : List BookRow := Examples.all.filterMap BookRow.ofDatum

private theorem bookRows_eq :
    bookRows = [⟨tableOfContents, .singular, .acceptable⟩,
      ⟨tableOfContents, .plural, .unacceptable⟩, ⟨chapters, .singular, .unacceptable⟩,
      ⟨chapters, .plural, .acceptable⟩] := rfl

/-- The judgments of (5)–(6) are the conceivability presupposition. -/
theorem bookRows_judgment :
    ∀ r ∈ bookRows, r.judgment = .acceptable ↔ negated r.noun r.number 0 ≠ 0 := by
  rw [bookRows_eq]
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨by simpa using negated_tableOfContents.1, by simpa using negated_tableOfContents.2,
    by simpa using negated_chapters.2, by simpa using negated_chapters.1⟩

/-! ### Referents and their continuations -/

open English.Pronouns (it they pronouns)

/-- The rows name the pronouns by their forms. -/
def pronounTable : List (String × PersonalPronoun) := [("it", it), ("they", they)]

/-- A continuation of (18)–(19) records the number of the negated indefinite, the pronoun resuming
it and the judgment. -/
structure ContinuationRow where
  antecedent : Number
  pronoun : PersonalPronoun
  judgment : Judgment
  deriving DecidableEq

/-- An example yields a row when it records each feature. -/
def ContinuationRow.ofDatum (ex : Datum) : Option ContinuationRow := do
  pure ⟨← ex.parse? "antecedent" numberTable, ← ex.parse? "pronoun" pronounTable, ex.judgment⟩

/-- The examples (18)–(19) give the continuation rows. -/
def continuationRows : List ContinuationRow := Examples.all.filterMap ContinuationRow.ofDatum

/-- A pronoun resuming a negated indefinite bears its number, (18)–(19). -/
theorem continuationRows_match :
    ∀ r ∈ continuationRows, r.judgment = .acceptable ↔ r.pronoun.number = some r.antecedent := by
  decide

/-- The referent of an indefinite of number `n` can be resumed when the witness set has `k`
members, that is, when a third person pronoun bears `n` and, read maximally, its number fits `k`. -/
def Usable (n : Number) (k : ℕ) : Prop :=
  ∃ p ∈ pronouns, p.person = some .third ∧ p.number = some n ∧ k ∈ inference n

theorem usable_iff {n : Number} (hn : n ∈ numberSystem.values) {k : ℕ} :
    Usable n k ↔ k ∈ inference n := by
  refine ⟨fun ⟨_, _, _, _, hk⟩ ↦ hk, fun hk ↦ ?_⟩
  rcases (by simpa [numberSystem] using hn : n = .singular ∨ n = .plural) with rfl | rfl
  exacts [⟨it, by decide, rfl, rfl, hk⟩, ⟨they, by decide, rfl, rfl, hk⟩]

/-- The denier of (22) has a witness and no licit pronoun, since the referent of a negated singular
indefinite cannot be resumed when there are several circles. -/
theorem not_usable_singular_of_two_le {k : ℕ} (hk : 2 ≤ k) : ¬ Usable .singular k := by
  rw [usable_iff (by decide)]
  grind [inference_singular, singular]

/-- A referent of number `n` is useful when some conceivable witness set lets a continuation
resume it, (23). -/
def Useful (K : Set ℕ) (n : Number) : Prop := ∃ k ∈ K, Usable n k

/-- Preferring useful referents, (23), yields the conceivability presupposition (7). -/
theorem useful_iff_negated_ne_zero {n : Number} (hn : n ∈ numberSystem.values) (K : Set ℕ)
    (k : ℕ) : Useful K n ↔ negated K n k ≠ 0 := by
  simp only [negated_ne_zero_iff, Useful, Set.Nonempty, Set.mem_inter_iff, usable_iff hn]

/-- Where both numbers are conceivable, (23) cannot be obeyed, since each number's referent cannot
be resumed in some conceivable situation with a witness. -/
theorem exists_not_usable {K : Set ℕ} (hsg : (K ∩ inference .singular).Nonempty)
    (hpl : (K ∩ inference .plural).Nonempty) {n : Number} (hn : n ∈ numberSystem.values) :
    ∃ k ∈ K, 1 ≤ k ∧ ¬ Usable n k := by
  rw [inference_singular] at hsg
  rw [inference_plural] at hpl
  rcases (by simpa [numberSystem] using hn : n = .singular ∨ n = .plural) with rfl | rfl
  · obtain ⟨k, hk, h⟩ := hpl
    exact ⟨k, hk, le_trans one_le_two h, not_usable_singular_of_two_le h⟩
  · obtain ⟨k, hk, h⟩ := hsg
    obtain rfl : k = 1 := h
    exact ⟨1, hk, le_rfl, by rw [usable_iff hn]; simp [strong]⟩

/-! ### The production experiment -/

/-- The five conditions (11) differ in how often symbols come in multiples. -/
inductive Condition
  | sg
  | sgPl
  | mix
  | plSg
  | pl
  deriving DecidableEq, Repr, Fintype

/-- `c.pMultiple` is the probability in condition `c` that symbols of a kind come in multiples
when there are any, (11). -/
def Condition.pMultiple : Condition → ℚ≥0
  | .sg => 0
  | .sgPl => 1 / 10
  | .mix => 1 / 2
  | .plSg => 9 / 10
  | .pl => 1

theorem Condition.pMultiple_injective : Function.Injective Condition.pMultiple := by
  decide +kernel

/-- The conditions are ordered by the frequency of multiples, the order of Figure 2. -/
instance : LinearOrder Condition := LinearOrder.lift' _ Condition.pMultiple_injective

instance : MeasurableSpace Condition := ⊤
instance : MeasurableSpace Number := ⊤
instance : DiscreteMeasurableSpace Number := ⟨fun _ ↦ trivial⟩

/-- A production is a negated indefinite of some number, or another strategy. -/
abbrev Production := Option Number

/-- `indefinite` is the set of productions that are negated indefinites. -/
def indefinite : Set Production := Set.range some

/-- Under H0, (10a), productions do not depend on the distribution. -/
def H0 (κ : Kernel Condition Production) : Prop := ∀ c c', κ c = κ c'

/-- Under H1, (10b), the singular is produced where uniqueness dominates and the plural
otherwise, including at parity. -/
def H1 (κ : Kernel Condition Production) : Prop :=
  ∀ c, (κ c)[|indefinite] = Measure.dirac (some (if c < .mix then .singular else .plural))

/-- Under H2, (10c), the more multiples there are the more plural is produced, and both numbers
are produced at parity. -/
def H2 (κ : Kernel Condition Production) : Prop :=
  StrictMono (fun c ↦ (κ c)[{some .plural} | indefinite]) ∧
    (κ .mix)[{some .singular} | indefinite] ≠ 0 ∧ (κ .mix)[{some .plural} | indefinite] ≠ 0

variable {κ : Kernel Condition Production}

theorem H1.not_H0 (h : H1 κ) : ¬ H0 κ := fun h0 ↦ by
  have := (h .sg).symm.trans ((congrArg (·[|indefinite]) (h0 .sg .pl)).trans (h .pl))
  simp only [show Condition.sg < .mix by decide +kernel, show ¬ Condition.pl < .mix by
    decide +kernel, ↓reduceIte] at this
  simpa using congrArg (· {some Number.singular}) this

/-- A speaker in complementary distribution at parity is not gradient (§4.1). -/
theorem not_H2_of_isZeroOneMeasure [IsZeroOneMeasure (κ .mix)[|indefinite]] : ¬ H2 κ := by
  rintro ⟨-, hs, hp⟩
  have h1 : (κ .mix)[{some .singular} | indefinite] = 1 := (Measure.zero_one _ _).resolve_left hs
  have : IsProbabilityMeasure (κ .mix)[|indefinite] := ⟨IsZeroOneMeasure.measure_univ h1⟩
  have hle := measure_mono (μ := (κ .mix)[|indefinite])
    (show ({some Number.plural} : Set Production) ⊆ {some Number.singular}ᶜ by simp)
  rw [prob_compl_eq_one_sub .of_discrete, h1, tsub_self] at hle
  exact hp (le_zero_iff.1 hle)

theorem H1.not_H2 (h : H1 κ) : ¬ H2 κ :=
  haveI : IsZeroOneMeasure (κ .mix)[|indefinite] := h .mix ▸ inferInstance
  not_H2_of_isZeroOneMeasure

/-! ### Maximize Presupposition over the conditions -/

open Competition (unblocked)

/-- The English numbers are each other's alternatives. -/
def englishAlts : Number → Set Number := fun _ ↦ {n | n ∈ numberSystem.values}

/-- In the Maximize Presupposition account of §4.1 the singular presupposes `S` of the condition,
the plural presupposes nothing, and the values outside English presuppose the impossible. -/
def mpPresup (S : Set Condition) : Number → Set Condition
  | .singular => S
  | .plural => Set.univ
  | _ => ∅

theorem unblocked_mpPresup_singular (S : Set Condition) :
    unblocked englishAlts (mpPresup S) .singular = S := by
  refine Competition.unblocked_eq_self ?_
  rintro ⟨m, hm, hss⟩
  rcases (by simpa [englishAlts, numberSystem] using hm : m = .singular ∨ m = .plural)
    with rfl | rfl
  · exact hss.ne rfl
  · exact hss.not_subset (Set.subset_univ _)

/-- The plural is used exactly where the singular's presupposition fails. -/
theorem unblocked_mpPresup_plural {S : Set Condition} (hS : S ≠ Set.univ) :
    unblocked englishAlts (mpPresup S) .plural = Sᶜ := by
  rw [Competition.unblocked_eq_sdiff (ψ := .singular) (by simp [englishAlts, numberSystem])
    hS.lt_top, Set.compl_eq_univ_sdiff]
  · rfl
  rintro χ hχ hss
  rcases (by simpa [englishAlts, numberSystem] using hχ : χ = .singular ∨ χ = .plural)
    with rfl | rfl
  · exact le_rfl
  · exact absurd rfl hss.ne

/-- Maximize Presupposition puts the two numbers in complementary distribution over the
conditions, as §4.1 says competition must. -/
theorem unblocked_mpPresup_isCompl {S : Set Condition} (hS : S ≠ Set.univ) :
    IsCompl (unblocked englishAlts (mpPresup S) .singular)
      (unblocked englishAlts (mpPresup S) .plural) := by
  rw [unblocked_mpPresup_singular, unblocked_mpPresup_plural hS]
  exact isCompl_compl

/-- A production kernel follows the use conditions `U` when in every condition it almost surely
produces a negated indefinite usable there. -/
def Follows (U : Number → Set Condition) (κ : Kernel Condition Production) : Prop :=
  ∀ c, ∀ᵐ p ∂(κ c)[|indefinite], ∀ n, p = some n → c ∈ U n

/-- A speaker following use conditions that allow one number in a condition produces it there
with certainty. -/
theorem Follows.eq_dirac {U : Number → Set Condition} (h : Follows U κ) {c : Condition}
    [IsProbabilityMeasure (κ c)[|indefinite]] {n : Number} (hn : ∀ m, c ∈ U m ↔ m = n) :
    (κ c)[|indefinite] = Measure.dirac (some n) :=
  Measure.eq_dirac_of_ae_eq <| by
    filter_upwards [h c, ae_cond_mem .of_discrete] with p hp ⟨m, hm⟩
    rw [← hm, (hn m).1 (hp m hm.symm)]

/-- Maximize Presupposition with the singular presupposing that uniqueness dominates, (8) read
as uniqueness in most situations, yields H1 (§4.1). -/
theorem Follows.H1_of_mpPresup [∀ c, IsProbabilityMeasure (κ c)[|indefinite]]
    (h : Follows (unblocked englishAlts (mpPresup (Set.Iio .mix))) κ) : H1 κ := fun c ↦
  h.eq_dirac fun m ↦ by
    have hS : Set.Iio Condition.mix ≠ Set.univ := fun h ↦
      lt_irrefl Condition.mix (Set.mem_Iio.1 (h ▸ Set.mem_univ _))
    cases m
    case singular => rw [unblocked_mpPresup_singular]; split_ifs <;> simp_all
    case plural => rw [unblocked_mpPresup_plural hS]; split_ifs <;> simp_all
    all_goals
      refine ⟨fun hc ↦ absurd (Competition.unblocked_subset _ _ _ hc) (Set.notMem_empty c),
        fun h ↦ ?_⟩
      split_ifs at h

/-! ### The chance of ineffability -/

/-- The chance of ineffability of number `n` under the witness distribution `μ` is the probability,
given a witness, that its cardinality does not fit `n`, so that the referent of a negated
indefinite of number `n` cannot be resumed. -/
noncomputable def ineffability (μ : Measure ℕ) (n : Number) : ℝ≥0∞ := μ[(inference n)ᶜ | weak]

theorem ineffability_singular (μ : Measure ℕ) : ineffability μ .singular = μ[strong | weak] := by
  rw [ineffability, cond_apply .of_discrete, cond_apply .of_discrete]
  congr 2
  ext k
  simp only [weak, strong, singular, inference_singular, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_compl_iff, Set.mem_singleton_iff]
  omega

/-- Given a witness exactly one number fits it, so the two chances of ineffability sum to one. -/
theorem ineffability_singular_add_plural (μ : Measure ℕ) [IsFiniteMeasure μ] (hμ : μ weak ≠ 0) :
    ineffability μ .singular + ineffability μ .plural = 1 := by
  have := cond_isProbabilityMeasure hμ
  rw [ineffability_singular, ineffability, inference_plural,
    prob_compl_eq_one_sub .of_discrete, add_tsub_cancel_of_le prob_le_one]

/-- The conceivability presupposition is the limiting case of the chance of ineffability (§6).
With the conceivable cardinalities those of positive probability, a number's presupposition
holds exactly when the chance that its referent cannot be resumed is not certain. -/
theorem negated_ne_zero_iff_ineffability_ne_one (μ : Measure ℕ) [IsFiniteMeasure μ]
    (hμ : μ weak ≠ 0) (n : Number) (w : ℕ) :
    negated {k | μ {k} ≠ 0} n w ≠ 0 ↔ ineffability μ n ≠ 1 := by
  have := cond_isProbabilityMeasure hμ
  rw [ineffability, ← (prob_le_one (μ := μ[|weak])).lt_iff_ne, prob_compl_eq_one_sub .of_discrete,
    ENNReal.sub_lt_self_iff ENNReal.one_ne_top, cond_apply .of_discrete,
    Set.inter_eq_right.2 (inference_subset_weak n)]
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, measure_ne_top, false_or]
  rw [← Set.biUnion_of_singleton (inference n), measure_biUnion_null_iff (Set.to_countable _)]
  simp [negated_ne_zero_iff, Set.Nonempty, and_comm]

/-- A best guess under the witness distribution `μ` is an English number minimizing the chance of
ineffability (§5.3). -/
def BestGuess (μ : Measure ℕ) (n : Number) : Prop :=
  IsMinOn (ineffability μ) {m | m ∈ numberSystem.values} n

/-- The plural is a best guess exactly when multiples are at least as likely as not. -/
theorem bestGuess_plural_iff (μ : Measure ℕ) [IsFiniteMeasure μ] (hμ : μ weak ≠ 0) :
    BestGuess μ .plural ↔ 1 / 2 ≤ μ[strong | weak] := by
  have hsum := ineffability_singular_add_plural μ hμ
  rw [ineffability_singular] at hsum
  have hle : μ[strong | weak] ≤ 1 := by
    have := cond_isProbabilityMeasure hμ; exact prob_le_one
  have hpl : ineffability μ .plural = 1 - μ[strong | weak] := by
    rw [← hsum, ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ENNReal.one_ne_top hle)]
  simp only [BestGuess, IsMinOn, IsMinFilter, Filter.eventually_principal, numberSystem,
    Finset.mem_insert, Finset.mem_singleton, Set.mem_ofPred_eq, forall_eq_or_imp, forall_eq,
    le_refl, and_true, hpl, ineffability_singular]
  rw [tsub_le_iff_right, ENNReal.div_le_iff two_ne_zero ENNReal.ofNat_ne_top, mul_two]

/-- A speaker who produces only best guesses is not gradient, since when the conditions teach
their probabilities of multiples only the singular is a best guess in the Sg and SgPl
conditions. -/
theorem not_H2_of_follows_bestGuess (μ : Condition → Measure ℕ) [∀ c, IsFiniteMeasure (μ c)]
    (hμ : ∀ c, μ c weak ≠ 0)
    (hp : ∀ c, (μ c)[strong | weak] = ((c.pMultiple : ℝ≥0) : ℝ≥0∞))
    (h : Follows (fun n ↦ {c | BestGuess (μ c) n}) κ) : ¬ H2 κ := by
  rintro ⟨hmono, -, -⟩
  have hzero : ∀ c, ((c.pMultiple : ℝ≥0) : ℝ≥0∞) < 1 / 2 →
      (κ c)[{some .plural} | indefinite] = 0 := fun c hc ↦ by
    refine measure_mono_null (fun p (hp' : p = some .plural) ↦ ?_) (ae_iff.1 (h c))
    simp only [Set.mem_ofPred_eq, not_forall]
    exact ⟨.plural, hp', fun hb ↦ absurd ((bestGuess_plural_iff (μ c) (hμ c)).1 hb)
      (not_le.2 (hp c ▸ hc))⟩
  have hlt := hmono (show Condition.sg < Condition.sgPl by decide +kernel)
  dsimp only at hlt
  rw [hzero .sg (by simp [Condition.pMultiple]), hzero .sgPl ?_] at hlt
  · exact lt_irrefl _ hlt
  · rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) by simp, ENNReal.coe_lt_coe]
    norm_num [Condition.pMultiple]

end Enguehard2024
