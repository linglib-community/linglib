module

public import Linglib.Data.Examples.Feinmann2026
public import Linglib.Pragmatics.DecisionTheoretic.Basic
public import Linglib.Semantics.Questions.Inquisitive.OfPartition
public import Linglib.Semantics.Questions.Inquisitive.Answerhood
public import Linglib.Semantics.Questions.Partition.Answer

/-!
# Feinmann (2026): A Note on Relevance

[feinmann-2026] argues that relevance to a question under discussion is not informativity about
it. Standard QUD relevance, (D-I), is the partial answerhood of [groenendijk-stokhof-1984]: a
sentence rules out a cell that the context set leaves open (`standardRelevant_iff`).
Probabilistic QUD relevance, (D-II), after [buring-2003], asks only that the sentence shift the
probability of a cell, which is to say that it is not independent of the cells
(`probabilisticRelevant_iff_not_indepSets`), and it is the weaker notion
(`StandardRelevant.probabilisticRelevant`). A report and a contrary report of equal strength
cancel, so a conjunction of two relevant sentences can leave every cell's probability where it
was (`not_probabilisticRelevant_inter`), as [keynes-1921] held against the relevance that
[carnap-1950] later adopted; the conjunction is then exactly as irrelevant as a sentence about
something else, though only the latter is judged irrelevant, (3) and (4). The accommodation
constraint (D-III) does not repair this: it is met by the common refinement of the sentence's
polar question with that of any relevant sentence (`accommodable_polar_inf_polar`), the pattern
of the paper's (11). Subject matters, (D-IV), give topical congruence, (D-V) and (D-VI).

## Implementation notes

A QUD is a `Setoid` on all worlds and the context set a set of worlds, so the cells of the QUD of
(D-I), a partition of the context set, are the traces on the context set of the cells compatible
with it. The prior of (D-II) is a measure, and the positive probability that (D-II) requires of
the sentence is what separates failure of independence from a shifted conditional probability,
mathlib's conditional on a null event being zero. The worked model of (3) and (4) gives each
parent's report a reliability of two thirds through an independent three-valued coordinate, and
its opposite and conflicting reports are irrelevant by the cancellation theorem, whose hypotheses
the model satisfies. Constituent clauses in (D-VI) are those of the Boolean language of (D-IV);
the clauses embedded under *told me* and *on the assumption that* in (19) and (23), which the
paper leaves to a broader conception of subject matter, are not represented. The examples are the
rows of `Data.Examples.Feinmann2026`.

## TODO

* The strategy-of-inquiry and ignorance-inference responses of sections 3.2 and 3.3.
* Subject matters of embedded clauses, which (D-VI) needs for (19), (22) and (23).

## References

* [feinmann-2026]
* [groenendijk-stokhof-1984]
* [roberts-2012]
* [buring-2003]
* [carnap-1950]
* [keynes-1921]
* [merin-1999-relevance]
* [beddor-goldstein-2023]
-/

@[expose] public section

open Inquisitive

open MeasureTheory ProbabilityTheory Setoid
open scoped ENNReal

namespace Feinmann2026

variable {W : Type*}

/-! ### Standard QUD relevance (D-I) -/

section Standard

variable {Q : Setoid W} {c φ : Set W}

/-- Standard QUD relevance (D-I): the sentence is consistent with the context set and its truth
conditions are disjoint from some cell of the partition that the QUD makes on the context set. -/
def StandardRelevant (Q : Setoid W) (c φ : Set W) : Prop :=
  (φ ∩ c).Nonempty ∧ ∃ q ∈ Q.compatible c, Disjoint (q ∩ c) φ

-- Standard QUD relevance is giving a partial answer in the sense of Groenendijk and Stokhof:
-- the context set updated with the sentence is consistent and closer to an answer.
theorem standardRelevant_iff :
    StandardRelevant Q c φ ↔ (c ∩ φ).Nonempty ∧ Q.CloserToAnswer (c ∩ φ) c := by
  rw [StandardRelevant, Set.inter_comm φ c, closerToAnswer_iff, and_iff_right Set.inter_subset_left]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨_, ⟨⟨w, rfl⟩, hc⟩, h⟩
    exact ⟨w, hc, fun ⟨v, hv, hvc, hvφ⟩ ↦ Set.disjoint_left.1 h ⟨hv, hvc⟩ hvφ⟩
  · rintro ⟨w, hc, h⟩
    exact ⟨_, ⟨Q.mem_classes w, hc⟩,
      Set.disjoint_left.2 fun v ⟨hv, hvc⟩ hvφ ↦ h ⟨v, hv, hvc, hvφ⟩⟩

-- A standardly relevant sentence gives a partial answer in the sense of Roberts: on the
-- context set it rules out an alternative of the question.
theorem StandardRelevant.partiallyAnsweredBy (h : StandardRelevant Q c φ) :
    (Inquisitive.Proposition.fromSetoid Q).PartiallyAnsweredBy (c ∩ φ) :=
  let ⟨_, q, ⟨hq, _⟩, h⟩ := h
  ⟨q, Inquisitive.Proposition.mem_alt_fromSetoid_of_mem_classes Q hq,
    .inr fun _ hv hvq ↦ Set.disjoint_left.1 h ⟨hvq, hv.1⟩ hv.2⟩

-- The two partial answers agree on a consistent sentence when the context set leaves every
-- cell possible and lies inside none. In a context set that lies inside one cell every sentence
-- evaluates that alternative, and none rules out a cell.
theorem standardRelevant_iff_partiallyAnsweredBy [Nonempty W] (hne : (c ∩ φ).Nonempty)
    (hlive : ∀ w, (Q.cell w ∩ c).Nonempty) (hopen : ∀ w, ¬ c ⊆ Q.cell w) :
    StandardRelevant Q c φ ↔ (Proposition.fromSetoid Q).PartiallyAnsweredBy (c ∩ φ) := by
  refine ⟨StandardRelevant.partiallyAnsweredBy, fun ⟨p, hp, h⟩ ↦ ?_⟩
  rw [Inquisitive.Proposition.alt_fromSetoid] at hp
  obtain ⟨u, rfl⟩ := hp
  refine standardRelevant_iff.2 ⟨hne, closerToAnswer_iff.2 ⟨Set.inter_subset_left, ?_⟩⟩
  rcases h with h | h
  · obtain ⟨z, hzc, hzu⟩ := Set.not_subset.1 (hopen u)
    exact ⟨z, ⟨z, Q.refl' z, hzc⟩, fun ⟨v, hvz, hv⟩ ↦ hzu (Q.trans' (Q.symm' hvz) (h hv))⟩
  · exact ⟨u, hlive u, fun ⟨v, hvu, hv⟩ ↦ h hv hvu⟩

end Standard

/-! ### Probabilistic QUD relevance (D-II) -/

section Probabilistic

variable [MeasurableSpace W] (μ : Measure W) {Q : Setoid W} {c φ ψ h : Set W}

/-- Probabilistic QUD relevance (D-II): the prior does not rule the sentence out, and
conditioning on it shifts the probability of some cell of the QUD. -/
def ProbabilisticRelevant (Q : Setoid W) (φ : Set W) : Prop :=
  μ φ ≠ 0 ∧ ∃ q ∈ Q.classes, μ q ≠ μ[q | φ]

variable {μ}

theorem probabilisticRelevant_iff_exists_ne [IsFiniteMeasure μ] (hφ : MeasurableSet φ) :
    ProbabilisticRelevant μ Q φ ↔ ∃ q ∈ Q.classes, μ (φ ∩ q) ≠ μ φ * μ q := by
  rcases eq_or_ne (μ φ) 0 with h0 | h0
  · simp [ProbabilisticRelevant, h0, measure_mono_null Set.inter_subset_left h0]
  · rw [ProbabilisticRelevant, and_iff_right h0]
    exact exists_congr fun q ↦ and_congr_right fun _ ↦ not_congr
      (eq_comm.trans (cond_apply_eq_iff_measure_inter_eq_mul hφ h0 (measure_ne_top _ _)))

/-- A sentence is probabilistically relevant exactly when it is not independent of the cells. -/
theorem probabilisticRelevant_iff_not_indepSets [IsFiniteMeasure μ] (hφ : MeasurableSet φ) :
    ProbabilisticRelevant μ Q φ ↔ ¬ IndepSets {φ} Q.classes μ := by
  rw [probabilisticRelevant_iff_exists_ne hφ, indepSets_singleton_left]
  simp only [not_forall, exists_prop]

-- A sentence that the prior does not rule out is relevant when it excludes a cell that the
-- prior does not rule out.
theorem probabilisticRelevant_of_measure_inter_eq_zero [IsFiniteMeasure μ] (hφ : MeasurableSet φ)
    {q : Set W} (hq : q ∈ Q.classes) (h0 : μ φ ≠ 0) (hq0 : μ q ≠ 0) (h : μ (φ ∩ q) = 0) :
    ProbabilisticRelevant μ Q φ :=
  (probabilisticRelevant_iff_exists_ne hφ).2 ⟨q, hq, h ▸ (mul_ne_zero h0 hq0).symm⟩

/-- Probabilistic QUD relevance is weaker than standard QUD relevance: a sentence that rules out
a cell on the context set shifts that cell's probability under every prior that rules out
exactly the propositions incompatible with the context set. -/
theorem StandardRelevant.probabilisticRelevant [IsFiniteMeasure μ] (hφ : MeasurableSet φ)
    (hc : ∀ s, μ s = 0 ↔ Disjoint s c) (h : StandardRelevant Q c φ) :
    ProbabilisticRelevant μ Q φ := by
  obtain ⟨hne, q, ⟨hq, hqc⟩, h⟩ := h
  refine probabilisticRelevant_of_measure_inter_eq_zero hφ hq
    (fun h0 ↦ Set.not_disjoint_iff_nonempty_inter.2 hne ((hc _).1 h0))
    (fun h0 ↦ Set.not_disjoint_iff_nonempty_inter.2 hqc ((hc _).1 h0)) ((hc _).2 ?_)
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm φ q, Set.inter_right_comm]
  exact h.inter_eq

-- Relevance to a polar question is Carnap's relevance of a sentence to a hypothesis: the
-- sentence is not independent of the hypothesis.
theorem probabilisticRelevant_polar_iff [IsProbabilityMeasure μ] (hφ : MeasurableSet φ)
    (hh : MeasurableSet h) : ProbabilisticRelevant μ (polar h) φ ↔ ¬ IndepSet φ h μ := by
  rw [probabilisticRelevant_iff_exists_ne hφ]
  refine ⟨fun ⟨q, hq, hne⟩ hind ↦ hne ?_, fun hind ↦ ⟨h, mem_classes_polar_iff.2 ⟨?_, .inl rfl⟩,
    mt (indepSet_iff_measure_inter_eq_mul hφ hh μ).2 hind⟩⟩
  · rcases (mem_classes_polar_iff.1 hq).2 with rfl | rfl
    · exact hind.measure_inter_eq_mul
    · exact hind.symm.compl_left.symm.measure_inter_eq_mul
  · by_contra hne
    exact hind (Set.not_nonempty_iff_eq_empty.1 hne ▸ indepSet_empty_right φ)

end Probabilistic

/-! ### Uninformative sentences: (3) and (4) -/

section Cancellation

open DTS

variable [MeasurableSpace W]

-- Relevance to the polar question of a live issue is relevance to the issue in Merin's sense.
theorem probabilisticRelevant_polar_topic_iff {ctx : Context W} [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] {e : Set W} (he : MeasurableSet e) :
    ProbabilisticRelevant ctx.prior (polar ctx.topic) e ↔ ¬ irrelevant ctx e := by
  rw [probabilisticRelevant_polar_iff he ctx.topicMeasurable, irrelevant_iff_indepSet he]
  exact not_congr ⟨IndepSet.symm, IndepSet.symm⟩

/-- Two sentences that are independent given each answer and shift the odds in opposite
directions with the same strength, so that their Bayes factors multiply to one, have a
conjunction that is not relevant: the configuration of (3)B₁. -/
theorem not_probabilisticRelevant_inter {ctx : Context W} [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] {a b : Set W} (ha : MeasurableSet a) (hb : MeasurableSet b)
    (hind : CondIndepIssue ctx a b)
    (h : ctx.prior[|ctx.topic] a * ctx.prior[|ctx.topic] b =
      ctx.prior[|ctx.topicᶜ] a * ctx.prior[|ctx.topicᶜ] b) :
    ¬ ProbabilisticRelevant ctx.prior (polar ctx.topic) (a ∩ b) := by
  have hi := (condIndepIssue_iff ctx ha hb).1 hind
  rw [probabilisticRelevant_polar_topic_iff (ha.inter hb), not_not, irrelevant, hi.1, hi.2, h]

end Cancellation

/-! ### A model of (3) and (4)

A world settles whether Mary is coming, a three-valued coordinate for each parent, and whether
Bezos hates Gates. A parent reports the truth unless their coordinate is `2`, so each report
has reliability two thirds, and all worlds are equally probable. -/

section Model

open DTS

/-- The worlds of the model. -/
structure World where
  /-- Mary is coming to the party. -/
  coming : Bool
  /-- The father reports the truth unless this is `2`. -/
  father : Fin 3
  /-- The mother reports the truth unless this is `2`. -/
  mother : Fin 3
  /-- Jeff Bezos hates Bill Gates. -/
  bezos : Bool
deriving DecidableEq, Fintype

instance : Nonempty World := ⟨⟨true, 0, 0, true⟩⟩

instance : MeasurableSpace World := ⊤

/-- Mary is coming to the party. -/
abbrev maryComing : Set World := {w | w.coming}

/-- Mary's father says that she is coming. -/
abbrev fatherSaysComing : Set World := {w | w.coming ↔ w.father ≠ 2}

/-- Mary's mother says that she is coming. -/
abbrev motherSaysComing : Set World := {w | w.coming ↔ w.mother ≠ 2}

/-- Jeff Bezos hates Bill Gates. -/
abbrev bezosHatesGates : Set World := {w | w.bezos}

/-- (3)B₁: the father says that she is coming and the mother says the opposite. -/
abbrev oppositeReports : Set World := fatherSaysComing ∩ motherSaysComingᶜ

/-- (4)B₁: the parents' reports conflict. -/
abbrev conflictingReports : Set World :=
  fatherSaysComing ∩ motherSaysComingᶜ ∪ fatherSaysComingᶜ ∩ motherSaysComing

/-- The issue whether Mary is coming, all worlds being equally probable. -/
noncomputable def issue : Context World := ⟨maryComing, .of_discrete, uniformOn Set.univ⟩

instance : IsProbabilityMeasure issue.prior :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn Set.univ))

instance : issue.Nondegenerate :=
  ⟨(uniformOn_ne_zero_iff Set.finite_univ).2 ⟨⟨true, 0, 0, true⟩, trivial, rfl⟩,
    (uniformOn_ne_zero_iff Set.finite_univ).2 ⟨⟨false, 0, 0, true⟩, trivial, by simp [issue]⟩⟩

private theorem relevant_iff {φ : Set World} :
    ProbabilisticRelevant issue.prior (polar maryComing) φ ↔
      ¬ IndepSet φ maryComing (uniformOn Set.univ) :=
  probabilisticRelevant_polar_iff .of_discrete .of_discrete

-- The reports of two parents are independent given each answer and equally reliable.
private theorem condIndepIssue_reports :
    CondIndepIssue issue fatherSaysComing motherSaysComingᶜ ∧
      CondIndepIssue issue fatherSaysComingᶜ motherSaysComing := by
  refine ⟨fun θ ↦ ?_, fun θ ↦ ?_⟩ <;> cases θ <;>
    simp only [Context.conditional, issue, uniformOn_univ_cond, indepSet_uniformOn_iff,
      Set.ncard_eq_toFinset_card'] <;> decide

private theorem ncard_reports :
    (maryComing ∩ fatherSaysComing).ncard = (maryComingᶜ ∩ motherSaysComingᶜ).ncard ∧
      (maryComing ∩ motherSaysComingᶜ).ncard = (maryComingᶜ ∩ fatherSaysComing).ncard ∧
      (maryComing ∩ fatherSaysComingᶜ).ncard = (maryComingᶜ ∩ motherSaysComing).ncard ∧
      (maryComing ∩ motherSaysComing).ncard = (maryComingᶜ ∩ fatherSaysComingᶜ).ncard ∧
      maryComing.ncard = maryComingᶜ.ncard := by
  simp only [Set.ncard_eq_toFinset_card']
  decide

-- Each parent's report is relevant to whether Mary is coming.
theorem relevant_reports :
    ProbabilisticRelevant issue.prior (polar maryComing) fatherSaysComing ∧
      ProbabilisticRelevant issue.prior (polar maryComing) motherSaysComingᶜ := by
  simp only [relevant_iff, indepSet_uniformOn_iff, Set.univ_inter, Set.ncard_eq_toFinset_card']
  decide

/-- Informativity does not separate the sentences of (3) and (4): the opposite reports of
(3)B₁ and the conflicting reports of (4)B₁ cancel, and the sentence about Bezos is about
something else, so all three leave the probability that Mary is coming where it was. -/
theorem not_relevant :
    ¬ ProbabilisticRelevant issue.prior (polar maryComing) oppositeReports ∧
      ¬ ProbabilisticRelevant issue.prior (polar maryComing) conflictingReports ∧
      ¬ ProbabilisticRelevant issue.prior (polar maryComing) bezosHatesGates := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := ncard_reports
  have hfin (s : Set World) : s.Finite := s.toFinite
  have opp : ¬ ProbabilisticRelevant issue.prior (polar maryComing) oppositeReports :=
    not_probabilisticRelevant_inter .of_discrete .of_discrete condIndepIssue_reports.1 <| by
      simp only [issue, uniformOn_univ_cond, uniformOn_apply_of_finite (hfin _), h₁, h₂, h₅]
      exact mul_comm _ _
  have opp' : ¬ ProbabilisticRelevant issue.prior (polar maryComing)
      (fatherSaysComingᶜ ∩ motherSaysComing) :=
    not_probabilisticRelevant_inter .of_discrete .of_discrete condIndepIssue_reports.2 <| by
      simp only [issue, uniformOn_univ_cond, uniformOn_apply_of_finite (hfin _), h₃, h₄, h₅]
      exact mul_comm _ _
  refine ⟨opp, ?_, ?_⟩
  · rw [relevant_iff, not_not] at opp opp' ⊢
    exact (opp.symm.union_right opp'.symm
      (Set.disjoint_left.2 fun _ hx hx' ↦ hx'.1 hx.1) .of_discrete .of_discrete .of_discrete).symm
  · simp only [relevant_iff, not_not, indepSet_uniformOn_iff, Set.univ_inter,
      Set.ncard_eq_toFinset_card']
    decide

end Model

/-! ### QUD accommodation (D-III) -/

section Accommodation

variable [MeasurableSpace W] (μ : Measure W) {Q : Setoid W} {φ ψ : Set W}

/-- The accommodation constraint (D-III): a QUD `Q'` may replace `Q` only if the sentence is
relevant to `Q'` and some cell of `Q'` is relevant to `Q`. -/
def Accommodable (φ : Set W) (Q Q' : Setoid W) : Prop :=
  ProbabilisticRelevant μ Q' φ ∧ ∃ q ∈ Q'.classes, ProbabilisticRelevant μ Q q

variable {μ}

-- The product rule for the two parts of an event cut by a measurable event gives it for the
-- whole.
private theorem measure_inter_eq_mul_of_inter_of_compl_inter {r s t : Set W} (hr : MeasurableSet r)
    (h₁ : μ (r ∩ t ∩ s) = μ (r ∩ t) * μ s) (h₂ : μ (rᶜ ∩ t ∩ s) = μ (rᶜ ∩ t) * μ s) :
    μ (t ∩ s) = μ t * μ s := by
  rw [← measure_inter_add_sdiff (t ∩ s) hr, ← measure_inter_add_sdiff t hr, add_mul,
    Set.inter_right_comm, Set.inter_comm t r, h₁, Set.sdiff_eq, Set.inter_right_comm,
    Set.inter_comm t rᶜ, h₂, Set.sdiff_eq, Set.inter_comm t rᶜ]

variable [IsProbabilityMeasure μ]

-- The product rule passes to the complement of a measurable event.
private theorem measure_compl_inter_eq_mul {s t : Set W} (hs : MeasurableSet s)
    (h : μ (s ∩ t) = μ s * μ t) : μ (sᶜ ∩ t) = μ sᶜ * μ t := by
  have e₁ : μ (s ∩ t) + μ (sᶜ ∩ t) = μ t := by
    rw [Set.inter_comm s, Set.inter_comm sᶜ, ← Set.sdiff_eq]
    exact measure_inter_add_sdiff t hs
  have e₂ : μ s * μ t + μ sᶜ * μ t = μ t := by
    rw [← add_mul, measure_add_measure_compl hs, measure_univ, one_mul]
  rw [h] at e₁
  exact (ENNReal.add_right_inj (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1
    (e₁.trans e₂.symm)

-- The constraint blocks the polar question of an irrelevant sentence, as it blocks (10).
theorem not_accommodable_polar_self (hφ : MeasurableSet φ)
    (h : ¬ ProbabilisticRelevant μ Q φ) : ¬ Accommodable μ φ Q (polar φ) := by
  rintro ⟨-, q, hq, hrel⟩
  rcases (mem_classes_polar_iff.1 hq).2 with rfl | rfl
  · exact h hrel
  · obtain ⟨q, hq, hne⟩ := (probabilisticRelevant_iff_exists_ne hφ.compl).1 hrel
    refine hne (measure_compl_inter_eq_mul hφ (not_not.1 fun hn ↦ h ?_))
    exact (probabilisticRelevant_iff_exists_ne hφ).2 ⟨q, hq, hn⟩

/-- The constraint is met by the common refinement of the sentence's polar question with the
polar question of any sentence relevant to the QUD, as it is met by (11): whenever some sentence
is relevant to the QUD, every sentence that is neither certain nor excluded can be accommodated. -/
theorem accommodable_polar_inf_polar (hφ : MeasurableSet φ) (hψ : MeasurableSet ψ)
    (h0 : μ φ ≠ 0) (h1 : μ φᶜ ≠ 0) (h : ProbabilisticRelevant μ Q ψ) :
    Accommodable μ φ Q (polar φ ⊓ polar ψ) := by
  -- a nonempty intersection of `φ` or its complement with `ψ` or its complement is a cell
  have cell {a b : Set W} (ha : a = φ ∨ a = φᶜ) (hb : b = ψ ∨ b = ψᶜ) (hne : (a ∩ b).Nonempty) :
      a ∩ b ∈ (polar φ ⊓ polar ψ).classes :=
    inter_mem_classes_inf (mem_classes_polar_iff.2 ⟨hne.mono Set.inter_subset_left, ha⟩)
      (mem_classes_polar_iff.2 ⟨hne.mono Set.inter_subset_right, hb⟩) hne
  refine ⟨?_, ?_⟩
  · -- a cell outside `φ` that the prior does not rule out
    obtain ⟨b, hb, hb0⟩ : ∃ b, (b = ψ ∨ b = ψᶜ) ∧ μ (φᶜ ∩ b) ≠ 0 := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      refine h1 ?_
      rw [← Set.inter_univ φᶜ, ← Set.union_compl_self ψ, Set.inter_union_distrib_left]
      exact measure_union_null (hc ψ (.inl rfl)) (hc ψᶜ (.inr rfl))
    refine probabilisticRelevant_of_measure_inter_eq_zero hφ
      (cell (.inr rfl) hb (nonempty_of_measure_ne_zero hb0)) h0 hb0 ?_
    rw [← Set.inter_assoc, Set.inter_compl_self, Set.empty_inter, measure_empty]
  · -- one of the two parts of `ψ` cut by `φ` is relevant to the QUD
    obtain ⟨q, hq, hne⟩ := (probabilisticRelevant_iff_exists_ne hψ).1 h
    obtain ⟨a, ha, hne⟩ : ∃ a, (a = φ ∨ a = φᶜ) ∧ μ (a ∩ ψ ∩ q) ≠ μ (a ∩ ψ) * μ q := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      exact hne (measure_inter_eq_mul_of_inter_of_compl_inter hφ (hc φ (.inl rfl))
        (hc φᶜ (.inr rfl)))
    have hmeas : MeasurableSet (a ∩ ψ) := by
      rcases ha with rfl | rfl <;> [exact hφ.inter hψ; exact hφ.compl.inter hψ]
    refine ⟨a ∩ ψ, cell ha (.inl rfl) ?_, (probabilisticRelevant_iff_exists_ne hmeas).2
      ⟨q, hq, hne⟩⟩
    by_contra hemp
    simp [Set.not_nonempty_iff_eq_empty.1 hemp] at hne

-- In the model the constraint lets the sentence about Bezos through: the common refinement
-- of its polar question with that of the father's report can be accommodated, though its own
-- polar question cannot.
theorem accommodable_bezos :
    Accommodable issue.prior bezosHatesGates (polar maryComing)
        (polar bezosHatesGates ⊓ polar fatherSaysComing) ∧
      ¬ Accommodable issue.prior bezosHatesGates (polar maryComing) (polar bezosHatesGates) := by
  refine ⟨accommodable_polar_inf_polar .of_discrete .of_discrete ?_ ?_ relevant_reports.1,
    not_accommodable_polar_self .of_discrete not_relevant.2.2⟩
  · exact (uniformOn_ne_zero_iff Set.finite_univ).2 ⟨⟨true, 0, 0, true⟩, trivial, rfl⟩
  · exact (uniformOn_ne_zero_iff Set.finite_univ).2 ⟨⟨true, 0, 0, false⟩, trivial, by simp⟩

end Accommodation

/-! ### Subject matters (D-IV) and topical congruence (D-V), (D-VI) -/

section SubjectMatter

/-- The sentences of (D-IV), built from atoms by negation, conjunction and disjunction. -/
inductive Sentence (α : Type*) where
  | atom (a : α)
  | neg (φ : Sentence α)
  | conj (φ ψ : Sentence α)
  | disj (φ ψ : Sentence α)

namespace Sentence

variable {α : Type*} (v : α → Set W)

/-- The truth conditions of a sentence under a valuation of the atoms. -/
def truth : Sentence α → Set W
  | atom a => v a
  | neg φ => (φ.truth)ᶜ
  | conj φ ψ => φ.truth ∩ ψ.truth
  | disj φ ψ => φ.truth ∪ ψ.truth

/-- The subject matter of a sentence (D-IV): the polar question of an atom, preserved by
negation, and the common refinement of the subject matters of conjuncts and of disjuncts. -/
def subjectMatter : Sentence α → Setoid W
  | atom a => polar (v a)
  | neg φ => φ.subjectMatter
  | conj φ ψ => φ.subjectMatter ⊓ ψ.subjectMatter
  | disj φ ψ => φ.subjectMatter ⊓ ψ.subjectMatter

-- The cells of the subject matter of a conjunction are the nonempty intersections of a cell
-- of each conjunct's subject matter, clause (ii) of (D-IV).
theorem classes_subjectMatter_conj (φ ψ : Sentence α) :
    ((conj φ ψ).subjectMatter v).classes = {c | ∃ i ∈ (φ.subjectMatter v).classes,
      ∃ j ∈ (ψ.subjectMatter v).classes, c = i ∩ j ∧ c.Nonempty} :=
  Setoid.classes_inf _ _

-- A sentence is entirely about its subject matter: its truth conditions are a union of
-- cells.
theorem determines_truth : ∀ φ : Sentence α, (φ.subjectMatter v).Determines (φ.truth v)
  | atom _ => polar_determines
  | neg φ => (determines_truth φ).compl
  | conj φ ψ => ((determines_truth φ).mono inf_le_left).inter
      ((determines_truth ψ).mono inf_le_right)
  | disj φ ψ => ((determines_truth φ).mono inf_le_left).union
      ((determines_truth ψ).mono inf_le_right)

/-- The constituent clauses of a sentence, the sentence itself among them. -/
inductive Constituent : Sentence α → Sentence α → Prop
  | refl (φ : Sentence α) : Constituent φ φ
  | neg {k φ : Sentence α} : Constituent k φ → Constituent k (neg φ)
  | conj_left {k φ : Sentence α} (ψ : Sentence α) : Constituent k φ → Constituent k (conj φ ψ)
  | conj_right {k ψ : Sentence α} (φ : Sentence α) : Constituent k ψ → Constituent k (conj φ ψ)
  | disj_left {k φ : Sentence α} (ψ : Sentence α) : Constituent k φ → Constituent k (disj φ ψ)
  | disj_right {k ψ : Sentence α} (φ : Sentence α) : Constituent k ψ → Constituent k (disj φ ψ)

end Sentence

variable {α : Type*} (v : α → Set W)

/-- Topical congruence (D-V): the subject matter of the sentence is the QUD. -/
def TopicallyCongruent (φ : Sentence α) (Q : Setoid W) : Prop :=
  φ.subjectMatter v = Q

/-- The weaker topical congruence of (D-VI): the subject matter of some constituent clause is
the QUD. -/
def WeaklyTopicallyCongruent (φ : Sentence α) (Q : Setoid W) : Prop :=
  ∃ k, k.Constituent φ ∧ TopicallyCongruent v k Q

variable {v} {φ : Sentence α} {Q : Setoid W}

theorem TopicallyCongruent.weakly (h : TopicallyCongruent v φ Q) :
    WeaklyTopicallyCongruent v φ Q :=
  ⟨φ, .refl φ, h⟩

-- A QUD that is topically congruent with a sentence determines its truth conditions.
theorem TopicallyCongruent.determines (h : TopicallyCongruent v φ Q) :
    Q.Determines (φ.truth v) :=
  h ▸ φ.determines_truth v

-- An atomic sentence is topically congruent with a polar QUD only when it expresses the
-- proposition asked about or its negation, so the answers of (20) and (21), relevant as they are,
-- are not topically congruent.
theorem topicallyCongruent_atom_polar_iff {a : α} {h : Set W} :
    TopicallyCongruent v (.atom a) (polar h) ↔ v a = h ∨ v a = hᶜ :=
  polar_eq_polar_iff

end SubjectMatter

end Feinmann2026
