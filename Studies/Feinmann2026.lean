module

public import Linglib.Data.Examples.Feinmann2026
public import Linglib.Pragmatics.DecisionTheoretic.Basic
public import Linglib.Semantics.Questions.Partition.Inquisitive
public import Linglib.Semantics.Questions.Resolution

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

A QUD is a `Setoid` on all worlds and the context set a set of worlds, so the cells of the
QUD of (D-I), a partition of the context set, are the traces on the context set of the cells
compatible with it. The prior of (D-II) is a measure, and the positive probability that (D-II)
requires of the sentence is what separates failure of independence from a shifted conditional
probability, mathlib's conditional on a null event being zero. The worked model of (3) and (4)
gives each parent's report a reliability of two thirds through an independent three-valued
coordinate. Constituent clauses in (D-VI) are those of the Boolean language of (D-IV); the
clauses embedded under *told me* and *on the assumption that* in (19) and (23), which the paper
leaves to a broader conception of subject matter, are not represented. The examples are the rows
of `Data.Examples.Feinmann2026`.

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
  (φ ∩ c).Nonempty ∧ ∃ q ∈ Q.compatible c, q ∩ c ∩ φ = ∅

-- Standard QUD relevance is giving a partial answer in the sense of
-- [groenendijk-stokhof-1984]: the context set updated with the sentence is consistent and closer
-- to an answer than the context set.
theorem standardRelevant_iff :
    StandardRelevant Q c φ ↔ (c ∩ φ).Nonempty ∧ Q.CloserToAnswer (c ∩ φ) c := by
  rw [StandardRelevant, Set.inter_comm φ c, closerToAnswer_iff, and_iff_right Set.inter_subset_left]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨_, ⟨⟨w, rfl⟩, hc⟩, h⟩
    exact ⟨w, hc, fun ⟨v, hv, hvc, hvφ⟩ ↦
      (h ▸ (⟨⟨hv, hvc⟩, hvφ⟩ : v ∈ _ ∩ c ∩ φ) : v ∈ (∅ : Set W))⟩
  · rintro ⟨w, hc, h⟩
    exact ⟨_, ⟨Q.mem_classes w, hc⟩, Set.not_nonempty_iff_eq_empty.1
      fun ⟨v, ⟨hv, hvc⟩, hvφ⟩ ↦ h ⟨v, hv, hvc, hvφ⟩⟩

-- A standardly relevant sentence gives a partial answer in the sense of [roberts-2012]: on the
-- context set it rules out an alternative of the question.
theorem StandardRelevant.partiallyAnsweredBy (h : StandardRelevant Q c φ) :
    (Question.fromSetoid Q).PartiallyAnsweredBy (c ∩ φ) := by
  obtain ⟨-, q, ⟨hq, -⟩, h⟩ := h
  refine ⟨q, Question.mem_alt_fromSetoid_of_mem_classes Q hq, Or.inr fun v hv hvq ↦ ?_⟩
  exact (h ▸ (⟨⟨hvq, hv.1⟩, hv.2⟩ : v ∈ q ∩ c ∩ φ) : v ∈ (∅ : Set W))

-- The two partial answers agree on a consistent sentence when the context set leaves every
-- cell possible and lies inside none. In a context set that lies inside one cell every sentence
-- evaluates that alternative, and none rules out a cell.
theorem standardRelevant_iff_partiallyAnsweredBy [Nonempty W] (hne : (c ∩ φ).Nonempty)
    (hlive : ∀ w, (Q.cell w ∩ c).Nonempty) (hopen : ∀ w, ¬ c ⊆ Q.cell w) :
    StandardRelevant Q c φ ↔ (Question.fromSetoid Q).PartiallyAnsweredBy (c ∩ φ) := by
  refine ⟨StandardRelevant.partiallyAnsweredBy, fun ⟨p, hp, h⟩ ↦ ?_⟩
  rw [Question.alt_fromSetoid] at hp
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

private theorem indepSets_singleton_left {S : Set (Set W)} :
    IndepSets {φ} S μ ↔ ∀ q ∈ S, μ (φ ∩ q) = μ φ * μ q := by
  rw [IndepSets_iff]
  exact ⟨fun h q hq ↦ h φ q rfl hq, fun h _ q hφ hq ↦ Set.mem_singleton_iff.1 hφ ▸ h q hq⟩

/-- A sentence is probabilistically relevant exactly when it is not independent of the cells. -/
theorem probabilisticRelevant_iff_not_indepSets [IsFiniteMeasure μ] (hφ : MeasurableSet φ) :
    ProbabilisticRelevant μ Q φ ↔ ¬ IndepSets {φ} Q.classes μ := by
  rw [indepSets_singleton_left, ProbabilisticRelevant]
  simp only [not_forall, exists_prop]
  rcases eq_or_ne (μ φ) 0 with h0 | h0
  · simp [h0, measure_mono_null Set.inter_subset_left h0]
  · rw [and_iff_right h0]
    exact exists_congr fun q ↦ and_congr_right fun _ ↦ not_congr
      (eq_comm.trans (cond_apply_eq_iff_measure_inter_eq_mul hφ h0 (measure_ne_top _ _)))

theorem probabilisticRelevant_iff_exists_not_indepSet [IsProbabilityMeasure μ]
    (hφ : MeasurableSet φ) (hQ : ∀ q ∈ Q.classes, MeasurableSet q) :
    ProbabilisticRelevant μ Q φ ↔ ∃ q ∈ Q.classes, ¬ IndepSet φ q μ := by
  rw [probabilisticRelevant_iff_not_indepSets hφ, indepSets_singleton_left]
  simp only [not_forall, exists_prop]
  exact exists_congr fun q ↦ and_congr_right fun hq ↦
    not_congr (indepSet_iff_measure_inter_eq_mul hφ (hQ q hq) μ).symm

-- Relevance to a polar question is the relevance of a sentence to a hypothesis of
-- [carnap-1950]: the sentence is not independent of the hypothesis.
theorem probabilisticRelevant_polar_iff [IsProbabilityMeasure μ] (hφ : MeasurableSet φ)
    (hh : MeasurableSet h) : ProbabilisticRelevant μ (polar h) φ ↔ ¬ IndepSet φ h μ := by
  have hcl : ∀ q ∈ (polar h).classes, q = h ∨ q = hᶜ := by
    rintro _ ⟨w, rfl⟩
    by_cases hw : w ∈ h
    · exact .inl (polar_cell_of_mem hw)
    · exact .inr (polar_cell_of_notMem hw)
  rw [probabilisticRelevant_iff_exists_not_indepSet hφ fun q hq ↦ by
    rcases hcl q hq with rfl | rfl <;> [exact hh; exact hh.compl]]
  refine ⟨fun ⟨q, hq, hind⟩ hφh ↦ hind ?_, fun hind ↦ ?_⟩
  · rcases hcl q hq with rfl | rfl
    · exact hφh
    · exact hφh.symm.compl_left.symm
  · obtain ⟨w, hw⟩ : h.Nonempty := by
      by_contra hne
      exact hind (Set.not_nonempty_iff_eq_empty.1 hne ▸ indepSet_empty_right φ)
    exact ⟨h, ⟨w, (polar_cell_of_mem hw).symm⟩, hind⟩

/-- Probabilistic QUD relevance is weaker than standard QUD relevance: a sentence that rules out
a cell on the context set shifts that cell's probability under every prior whose possibilities
are those of the context set. -/
theorem StandardRelevant.probabilisticRelevant [IsFiniteMeasure μ] (hφ : MeasurableSet φ)
    (hc : μ cᶜ = 0) (hpos : ∀ w ∈ c, μ {w} ≠ 0) (h : StandardRelevant Q c φ) :
    ProbabilisticRelevant μ Q φ := by
  obtain ⟨⟨y, hyφ, hyc⟩, q, ⟨hq, x, hxq, hxc⟩, h⟩ := h
  have hφ0 : μ φ ≠ 0 := fun h0 ↦ hpos y hyc (measure_mono_null (Set.singleton_subset_iff.2 hyφ) h0)
  refine ⟨hφ0, q, hq, ?_⟩
  have h0 : μ (φ ∩ q) = 0 := measure_mono_null (fun v hv ↦ by
    by_contra hvc
    exact (h ▸ (⟨⟨hv.2, not_not.1 hvc⟩, hv.1⟩ : v ∈ q ∩ c ∩ φ) : v ∈ (∅ : Set W))) hc
  rw [cond_apply hφ, h0, mul_zero]
  exact fun h0 ↦ hpos x hxc (measure_mono_null (Set.singleton_subset_iff.2 hxq) h0)

end Probabilistic

/-! ### Uninformative sentences: (3) and (4) -/

section Cancellation

open DTS

variable [MeasurableSpace W]

-- Relevance to the polar question of a live issue is relevance to the issue in the sense of
-- [merin-1999-relevance].
theorem probabilisticRelevant_polar_topic_iff {ctx : Context W} [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] {e : Set W} (he : MeasurableSet e) :
    ProbabilisticRelevant ctx.prior (polar ctx.topic) e ↔ ¬ irrelevant ctx e := by
  rw [probabilisticRelevant_polar_iff he ctx.topicMeasurable, irrelevant_iff_indepSet he]
  exact not_congr ⟨IndepSet.symm, IndepSet.symm⟩

/-- Two sentences that are independent given each answer and shift the odds in opposite
directions with the same strength have a conjunction that is not relevant, the configuration of
(3)B₁. -/
theorem not_probabilisticRelevant_inter {ctx : Context W} [IsProbabilityMeasure ctx.prior]
    [ctx.Nondegenerate] {a b : Set W} (ha : MeasurableSet a) (hb : MeasurableSet b)
    (hind : CondIndepIssue ctx a b) (h : bayesFactor ctx a * bayesFactor ctx b = 1) :
    ¬ ProbabilisticRelevant ctx.prior (polar ctx.topic) (a ∩ b) := by
  rw [probabilisticRelevant_polar_topic_iff (ha.inter hb), not_not, irrelevant]
  have hb0 : ctx.prior[|ctx.topicᶜ] b ≠ 0 := fun h0 ↦ by
    rw [bayesFactor_def ctx b, h0] at h
    rcases eq_or_ne (ctx.prior[|ctx.topic] b) 0 with h1 | h1
    · simp [h1] at h
    · rw [ENNReal.div_zero h1] at h
      rcases eq_or_ne (bayesFactor ctx a) 0 with h2 | h2
      · simp [h2] at h
      · simp [ENNReal.mul_top h2] at h
  have hBF := hind.bayesFactor_inter hb0
  rw [h, bayesFactor_def] at hBF
  have h0 : ctx.prior[|ctx.topicᶜ] (a ∩ b) ≠ 0 := fun h0 ↦ by
    rw [h0] at hBF
    rcases eq_or_ne (ctx.prior[|ctx.topic] (a ∩ b)) 0 with h1 | h1
    · simp [h1] at hBF
    · simp [ENNReal.div_zero h1] at hBF
  exact (ENNReal.div_eq_one_iff h0 (measure_ne_top _ _)).1 hBF

end Cancellation

/-! ### A model of (3) and (4)

A world settles whether Mary is coming, a three-valued coordinate for each parent, and whether
Bezos hates Gates. A parent reports the truth unless their coordinate is `2`, so each report
has reliability two thirds, and all worlds are equally probable. -/

section Model

/-- The worlds of the model. -/
abbrev World := Bool × Fin 3 × Fin 3 × Bool

/-- Mary is coming to the party. -/
abbrev coming : Set World := {w | w.1}

/-- Mary's father says that she is coming. -/
abbrev fatherSaysComing : Set World := {w | w.1 ↔ w.2.1 ≠ 2}

/-- Mary's mother says that she is coming. -/
abbrev motherSaysComing : Set World := {w | w.1 ↔ w.2.2.1 ≠ 2}

/-- Jeff Bezos hates Bill Gates. -/
abbrev bezos : Set World := {w | w.2.2.2}

/-- (3)B₁: the father says that she is coming and the mother says the opposite. -/
abbrev oppositeReports : Set World := fatherSaysComing ∩ motherSaysComingᶜ

/-- (4)B₁: the parents' reports conflict. -/
abbrev conflictingReports : Set World :=
  fatherSaysComing ∩ motherSaysComingᶜ ∪ fatherSaysComingᶜ ∩ motherSaysComing

private theorem relevant_iff {φ : Set World} :
    ProbabilisticRelevant (uniformOn Set.univ) (polar coming) φ ↔
      ¬ IndepSet φ coming (uniformOn Set.univ) :=
  probabilisticRelevant_polar_iff (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet

-- Each parent's report is relevant to whether Mary is coming.
theorem relevant_reports :
    ProbabilisticRelevant (uniformOn Set.univ) (polar coming) fatherSaysComing ∧
      ProbabilisticRelevant (uniformOn Set.univ) (polar coming) motherSaysComingᶜ := by
  simp only [relevant_iff, indepSet_uniformOn_iff, Set.univ_inter, Set.ncard_eq_toFinset_card']
  decide

/-- Informativity does not separate the sentences of (3) and (4): the opposite reports of
(3)B₁, the conflicting reports of (4)B₁ and the sentence about Bezos all leave the probability
that Mary is coming where it was. -/
theorem not_relevant :
    ¬ ProbabilisticRelevant (uniformOn Set.univ) (polar coming) oppositeReports ∧
      ¬ ProbabilisticRelevant (uniformOn Set.univ) (polar coming) conflictingReports ∧
      ¬ ProbabilisticRelevant (uniformOn Set.univ) (polar coming) bezos := by
  simp only [relevant_iff, not_not, indepSet_uniformOn_iff, Set.univ_inter,
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

variable {μ} [IsProbabilityMeasure μ]

-- The constraint blocks the polar question of an irrelevant sentence, as it blocks (10).
theorem not_accommodable_polar_self (hφ : MeasurableSet φ) (hQ : ∀ q ∈ Q.classes, MeasurableSet q)
    (h : ¬ ProbabilisticRelevant μ Q φ) : ¬ Accommodable μ φ Q (polar φ) := by
  rintro ⟨-, _, ⟨w, rfl⟩, hrel⟩
  change ProbabilisticRelevant μ Q ((polar φ).cell w) at hrel
  by_cases hw : w ∈ φ
  · exact h (polar_cell_of_mem hw ▸ hrel)
  · rw [polar_cell_of_notMem hw,
      probabilisticRelevant_iff_exists_not_indepSet hφ.compl hQ] at hrel
    obtain ⟨q, hq, hind⟩ := hrel
    rw [probabilisticRelevant_iff_exists_not_indepSet hφ hQ] at h
    exact hind (not_not.1 fun hn ↦ h ⟨q, hq, hn⟩ : IndepSet φ q μ).compl_left

/-- The constraint is met by the common refinement of the sentence's polar question with the
polar question of any sentence relevant to the QUD, as it is met by (11): whenever some sentence
is relevant to the QUD, every sentence that is neither certain nor excluded can be accommodated. -/
theorem accommodable_polar_inf_polar (hφ : MeasurableSet φ) (hψ : MeasurableSet ψ)
    (hQ : ∀ q ∈ Q.classes, MeasurableSet q) (h0 : μ φ ≠ 0) (h1 : μ φᶜ ≠ 0)
    (h : ProbabilisticRelevant μ Q ψ) : Accommodable μ φ Q (polar φ ⊓ polar ψ) := by
  obtain ⟨q, hq, hψq⟩ := (probabilisticRelevant_iff_exists_not_indepSet hψ hQ).1 h
  have hcell (w : W) : (polar φ ⊓ polar ψ).cell w = (polar φ).cell w ∩ (polar ψ).cell w :=
    cell_inf _ w
  have hmeas : ∀ s ∈ (polar φ ⊓ polar ψ).classes, MeasurableSet s := by
    rintro _ ⟨w, rfl⟩
    change MeasurableSet ((polar φ ⊓ polar ψ).cell w)
    rw [hcell]
    refine .inter ?_ ?_
    · by_cases hw : w ∈ φ
      · rwa [polar_cell_of_mem hw]
      · rw [polar_cell_of_notMem hw]
        exact hφ.compl
    · by_cases hw : w ∈ ψ
      · rwa [polar_cell_of_mem hw]
      · rw [polar_cell_of_notMem hw]
        exact hψ.compl
  have key : ∀ s : Set W, (s = φ ∩ ψ ∨ s = φᶜ ∩ ψ ∨ s = φᶜ ∩ ψᶜ) → s.Nonempty →
      s ∈ (polar φ ⊓ polar ψ).classes := by
    rintro s hs ⟨w, hw⟩
    refine ⟨w, ?_⟩
    change s = (polar φ ⊓ polar ψ).cell w
    rw [hcell]
    rcases hs with rfl | rfl | rfl
    · rw [polar_cell_of_mem hw.1, polar_cell_of_mem hw.2]
    · rw [polar_cell_of_notMem hw.1, polar_cell_of_mem hw.2]
    · rw [polar_cell_of_notMem hw.1, polar_cell_of_notMem hw.2]
  have off : ∀ s : Set W, s ⊆ φᶜ → μ s ≠ 0 → ¬ IndepSet φ s μ := fun s hs hs0 hind ↦ by
    have := hind.measure_inter_eq_mul
    rw [Set.disjoint_iff_inter_eq_empty.1 (Set.disjoint_left.2 fun x hx hx' ↦ hs hx' hx),
      measure_empty] at this
    exact mul_ne_zero h0 hs0 this.symm
  refine ⟨(probabilisticRelevant_iff_exists_not_indepSet hφ hmeas).2 ?_, ?_⟩
  · have : μ (φᶜ ∩ ψ) ≠ 0 ∨ μ (φᶜ ∩ ψᶜ) ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      refine h1 ?_
      rw [show φᶜ = φᶜ ∩ ψ ∪ φᶜ ∩ ψᶜ by
        rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]]
      exact measure_union_null hc.1 hc.2
    rcases this with hc | hc
    · exact ⟨_, key _ (.inr (.inl rfl)) (nonempty_of_measure_ne_zero hc),
        off _ Set.inter_subset_left hc⟩
    · exact ⟨_, key _ (.inr (.inr rfl)) (nonempty_of_measure_ne_zero hc),
        off _ Set.inter_subset_left hc⟩
  · have hne : ∀ s : Set W, ¬ IndepSet s q μ → s.Nonempty := fun s hs ↦ by
      by_contra hne
      exact hs (Set.not_nonempty_iff_eq_empty.1 hne ▸ indepSet_empty_left q)
    have hsplit : ¬ IndepSet (φ ∩ ψ) q μ ∨ ¬ IndepSet (φᶜ ∩ ψ) q μ := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      refine hψq ?_
      have := (hc.1.symm.union_right hc.2.symm
        (Set.disjoint_left.2 fun x hx hx' ↦ hx'.1 hx.1) (hQ q hq) (hφ.inter hψ)
        (hφ.compl.inter hψ)).symm
      rwa [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter] at this
    rcases hsplit with hc | hc
    · have hcl := key _ (.inl rfl) (hne _ hc)
      exact ⟨_, hcl, (probabilisticRelevant_iff_exists_not_indepSet (hmeas _ hcl) hQ).2
        ⟨q, hq, hc⟩⟩
    · have hcl := key _ (.inr (.inl rfl)) (hne _ hc)
      exact ⟨_, hcl, (probabilisticRelevant_iff_exists_not_indepSet (hmeas _ hcl) hQ).2
        ⟨q, hq, hc⟩⟩

-- In the model the constraint lets the sentence about Bezos through: the common refinement
-- of its polar question with that of the father's report can be accommodated, though its own polar
-- question cannot.
theorem accommodable_bezos :
    Accommodable (uniformOn Set.univ) bezos (polar coming)
        (polar bezos ⊓ polar fatherSaysComing) ∧
      ¬ Accommodable (uniformOn Set.univ) bezos (polar coming) (polar bezos) := by
  have hm (s : Set World) : MeasurableSet s := (Set.toFinite s).measurableSet
  refine ⟨accommodable_polar_inf_polar (hm _) (hm _) (fun q _ ↦ hm q) ?_ ?_ relevant_reports.1,
    not_accommodable_polar_self (hm _) (fun q _ ↦ hm q) not_relevant.2.2⟩
  · exact (uniformOn_ne_zero_iff Set.finite_univ).2 ⟨(true, 0, 0, true), trivial, rfl⟩
  · exact (uniformOn_ne_zero_iff Set.finite_univ).2 ⟨(true, 0, 0, false), trivial, by simp⟩

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
