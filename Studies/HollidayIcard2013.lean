module

public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Logic.ComparativeProbability.Patterns
public import Linglib.Logic.ComparativeProbability.Completeness
public import Linglib.Logic.ComparativeProbability.Defs
public import Linglib.Core.Probability.UniformOn

/-!
# Holliday and Icard (2013): Measure semantics and qualitative semantics for epistemic modals

Holliday and Icard compare semantics for the comparative epistemic modal *at least as likely
as* against the inference patterns of their Figure 1: Yalcin's V1–V7, V11, V12 and I1–I3, and
V13, which Lassiter suggested. Kratzer's world-ordering semantics, which lifts a preorder on
worlds to propositions by Lewis's l-lifting, validates the invalid patterns and misses V11 and
V13; Kratzer's later k-lifting does no better for disjoint propositions. Finitely additive
measures validate exactly the intended patterns, but so do the paper's two qualitative
alternatives, qualitatively additive measures and the m-lifting. What separates the two kinds
of additivity is Kraft, Pratt and Seidenberg's ordering on five worlds, the paper's World Cup
comparisons (3)–(6), which the paper doubts speakers find inconsistent.

## Main results

* `lLift_validities`, `disjunction_problem`, `lLift_refutes_V11_V13`: Fact 1. The l-lifting's
  V12, which Yalcin counts among the account's failures, follows from its I2.
* `measure_validities`, `qualAddMeasure_validities` and the refutations of I1–I3: Facts 2, 3.
* `mLift_validities`, `mLift_refutes_I_patterns`: Fact 5. By `measure_le_of_matchingLift` the
  m-lifting is sound for any measure that agrees with the world ordering on singletons.
* `worldCup_not_finitelyAdditive`, `fa_representable_iff_card_lt_five`: Theorem 8.

## Implementation notes

* The paper's finitely additive measures are mathlib's probability measures on a discrete
  measurable space; on the paper's finite spaces the two coincide.
* `□` and `◇` are the paper's quantifiers over the epistemic space, `A = Set.univ` and
  `A ≠ ∅`, with every world accessible, so V6 comes from non-triviality and V7 from
  monotonicity. The order-internal `◇A := ¬ ∅ ⩾ A` agrees with this for the liftings but, over
  the measures, only for regular ones.
* V8–V10, which Fact 1 names but Figure 1 leaves out, are not formalized.
* The refutations use the uniform measure on three worlds and the indiscriminate world order on
  two or three worlds. Theorems 2, 6 and 8 are represented by the model-theoretic results they
  rest on; Theorems 3–5 and 7 and Fact 4 concern the logics themselves.
* Figure 7's chain of four worlds shows the two liftings apart: only the l-lifting makes `{a}`
  more likely than `{b, c}`, and the m-lifting leaves `{a, d}` and `{b, c}` incomparable.

## TODO

* The FA-consistency of (3)–(6) is witnessed by the Kraft–Pratt–Seidenberg order of the
  substrate under a different labelling of the worlds; state it for the World Cup labelling.

## References

* [holliday-icard-2013]
* [yalcin-2010]
* [kratzer-1991]
* [kratzer-2012]
* [lewis-1973b]
* [halpern-2003]
* [van-der-hoek-1996]
* [kraft-pratt-seidenberg-1959]
-/

@[expose] public section

namespace HollidayIcard2013

open ComparativeProbability MeasureTheory ProbabilityTheory

variable {W : Type*}

/-- In the indiscriminate world order every world is at least as good as every other. -/
private instance {α : Type*} : IsPreorder α fun _ _ ↦ True where
  refl _ := trivial
  trans _ _ _ _ _ := trivial

/-! ### Fact 1: Kratzer's world-ordering semantics -/

section LLift

variable (ge_w : W → W → Prop) [IsPreorder W ge_w]

/-- The l-lifting of any preorder on worlds validates the three measure-invalid patterns I1–I3,
since it is right-union closed. This is Fact 1's disjunction problem. -/
theorem disjunction_problem :
    RightUnion (LewisLift ge_w) ∧ EquiprobabilityCollapse (LewisLift ge_w) ∧
      HamblinCollapse (LewisLift ge_w) :=
  have hI2 := equiprobabilityCollapse_of_rightUnion (rightUnion_lewisLift (r := ge_w))
  ⟨rightUnion_lewisLift, hI2, hamblinCollapse_of_equiprobabilityCollapse hI2⟩

/-- Over a nonempty preorder on worlds the l-lifting validates V1–V7 and V12 (Fact 1), the last
because it validates I2. -/
theorem lLift_validities [Nonempty W] :
    ProbablyToNotProbablyNot (LewisLift ge_w) ∧ ProbablyDistribInf (LewisLift ge_w) ∧
      ChancyDisjunctionIntro (LewisLift ge_w) ∧ Minimality (LewisLift ge_w) ∧
      Maximality (LewisLift ge_w) ∧ MustToProbably (LewisLift ge_w) (· = Set.univ) ∧
      ProbablyToMight (LewisLift ge_w) (· ≠ ∅) ∧ ComplementTransfer (LewisLift ge_w) :=
  ⟨probablyToNotProbablyNot, probablyDistribInf, chancyDisjunctionIntro, minimality,
    maximality, mustToProbably, probablyToMight,
    complementTransfer_of_equiprobabilityCollapse (disjunction_problem ge_w).2.1⟩

end LLift

/-- The l-lifting refutes V11 and V13 on two indiscriminate worlds (Fact 1). -/
theorem lLift_refutes_V11_V13 :
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬PositiveFormTransfer (LewisLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬StrictDisjunctionIntro (LewisLift ge_w)) := by
  refine ⟨⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ ?_⟩,
    ⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ ?_⟩⟩
  · exact (h Set.univ {0} (fun _ _ ↦ ⟨0, rfl, trivial⟩) probably_top).2
      fun _ _ ↦ ⟨1, by simp, trivial⟩
  · have hsd : ({0} : Set (Fin 2)) \ {1} = {0} := Set.sdiff_singleton_eq_self (by simp)
    refine (h {0} {1} ⟨lewisLift_empty _, fun h' ↦ ?_⟩).2 fun _ _ ↦ ⟨1, rfl, trivial⟩
    exact Set.singleton_ne_empty 0 (hsd ▸ lewisLift_empty_left_iff.1 h')

/-! ### Facts 2 and 3: finitely and qualitatively additive measures -/

section Measures

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Every probability measure validates V1–V7 and V11–V13 (Fact 2). -/
theorem measure_validities [MeasurableSpace W] [DiscreteMeasurableSpace W] (μ : Measure W)
    [IsProbabilityMeasure μ] :
    ProbablyToNotProbablyNot μ.inducedGe ∧ ProbablyDistribInf μ.inducedGe ∧
      ChancyDisjunctionIntro μ.inducedGe ∧ Minimality μ.inducedGe ∧ Maximality μ.inducedGe ∧
      MustToProbably μ.inducedGe (· = Set.univ) ∧ ProbablyToMight μ.inducedGe (· ≠ ∅) ∧
      PositiveFormTransfer μ.inducedGe ∧ ComplementTransfer μ.inducedGe ∧
      StrictDisjunctionIntro μ.inducedGe :=
  ⟨probablyToNotProbablyNot, probablyDistribInf, chancyDisjunctionIntro, minimality,
    maximality, mustToProbably, probablyToMight, positiveFormTransfer, complementTransfer,
    strictDisjunctionIntro⟩

/-- `uniform3` is the uniform measure on three worlds. -/
local notation "uniform3" => uniformOn (Set.univ : Set (Fin 3))

private theorem uniform3_not_I1 : ¬RightUnion (uniform3).inducedGe := fun h ↦ by
  have := h {0} {1} {2} (by simp [Measure.inducedGe, uniformOn_univ_le_iff])
    (by simp [Measure.inducedGe, uniformOn_univ_le_iff])
  simp only [Measure.inducedGe, uniformOn_univ_le_iff, Set.sup_eq_union, Set.singleton_union]
    at this
  rw [Set.ncard_pair (by decide), Set.ncard_singleton] at this
  omega

private theorem uniform3_probably_pair : Probably (uniform3).inducedGe {0, 1} := by
  have hc : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext x; fin_cases x <;> simp
  constructor <;>
    rw [Measure.inducedGe, uniformOn_univ_le_iff, hc, Set.ncard_pair (by decide),
      Set.ncard_singleton] <;> omega

private theorem uniform3_not_pair_univ : ¬(uniform3).inducedGe {0, 1} Set.univ := by
  rw [Measure.inducedGe, uniformOn_univ_le_iff, Set.ncard_pair (by decide), Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- The uniform measure on three worlds refutes each of I1–I3 (Fact 2). -/
theorem measures_refute_I_patterns :
    (∃ μ : Measure (Fin 3), IsProbabilityMeasure μ ∧ ¬RightUnion μ.inducedGe) ∧
    (∃ μ : Measure (Fin 3), IsProbabilityMeasure μ ∧ ¬EquiprobabilityCollapse μ.inducedGe) ∧
    (∃ μ : Measure (Fin 3), IsProbabilityMeasure μ ∧ ¬HamblinCollapse μ.inducedGe) :=
  ⟨⟨uniform3, inferInstance, uniform3_not_I1⟩,
    ⟨uniform3, inferInstance, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair.1)⟩,
    ⟨uniform3, inferInstance, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair)⟩⟩

/-- Qualitative additivity already yields V1–V7 and V11–V13 (Fact 3). -/
theorem qualAddMeasure_validities (m : QualAddMeasure K W) :
    ProbablyToNotProbablyNot m.inducedGe ∧ ProbablyDistribInf m.inducedGe ∧
      ChancyDisjunctionIntro m.inducedGe ∧ Minimality m.inducedGe ∧ Maximality m.inducedGe ∧
      MustToProbably m.inducedGe (· = Set.univ) ∧ ProbablyToMight m.inducedGe (· ≠ ∅) ∧
      PositiveFormTransfer m.inducedGe ∧ ComplementTransfer m.inducedGe ∧
      StrictDisjunctionIntro m.inducedGe :=
  ⟨probablyToNotProbablyNot, probablyDistribInf, chancyDisjunctionIntro, minimality,
    maximality, mustToProbably, probablyToMight, positiveFormTransfer, complementTransfer,
    strictDisjunctionIntro⟩

/-- The uniform measure, read as a qualitatively additive measure, refutes each of I1–I3
(Fact 3). -/
theorem qualAddMeasures_refute_I_patterns :
    (∃ m : QualAddMeasure ℝ (Fin 3), ¬RightUnion m.inducedGe) ∧
    (∃ m : QualAddMeasure ℝ (Fin 3), ¬EquiprobabilityCollapse m.inducedGe) ∧
    (∃ m : QualAddMeasure ℝ (Fin 3), ¬HamblinCollapse m.inducedGe) := by
  refine ⟨⟨(uniform3).toQualAdd, ?_⟩, ⟨(uniform3).toQualAdd, ?_⟩, ⟨(uniform3).toQualAdd, ?_⟩⟩ <;>
    rw [← Measure.inducedGe_eq_toQualAdd]
  exacts [uniform3_not_I1, fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair.1),
    fun h ↦ uniform3_not_pair_univ (h _ _ uniform3_probably_pair)]

/-- Every FA order on a finite set of worlds is represented by a qualitatively additive measure
(Theorem 6, after van der Hoek). -/
theorem fa_qualAdd_complete [Fintype W] (r : Set W → Set W → Prop) [IsQualitativeProbability r] :
    ∃ m : QualAddMeasure ℚ W, ∀ A B, r A B ↔ m.inducedGe A B :=
  exists_qualAddMeasure_repr r

end Measures

/-! ### Fact 5: the m-lifting -/

section MLift

variable (ge_w : W → W → Prop) [IsPreorder W ge_w]

theorem mLift_V13 [Finite W] : StrictDisjunctionIntro (MatchingLift ge_w) := by
  rintro A B ⟨-, hne⟩
  have hsub : B ⊂ A ∪ B := Set.ssubset_iff_subset_ne.2 ⟨Set.subset_union_right, fun h ↦ hne ?_⟩
  · refine ⟨matchingLift_of_subset Set.subset_union_right, fun h ↦ ?_⟩
    have h₁ : (A ∪ B).ncard ≤ B.ncard := h.ncard_le
    have h₂ := Set.ncard_lt_ncard hsub
    omega
  · rw [Set.sdiff_eq_empty.2 (Set.union_eq_right.1 h.symm)]
    exact matchingLift_empty _

/-- On a finite nonempty preorder the m-lifting validates V1–V7 and V11–V13 (Fact 5). -/
theorem mLift_validities [Finite W] [Nonempty W] :
    ProbablyToNotProbablyNot (MatchingLift ge_w) ∧ ProbablyDistribInf (MatchingLift ge_w) ∧
      ChancyDisjunctionIntro (MatchingLift ge_w) ∧ Minimality (MatchingLift ge_w) ∧
      Maximality (MatchingLift ge_w) ∧ MustToProbably (MatchingLift ge_w) (· = Set.univ) ∧
      ProbablyToMight (MatchingLift ge_w) (· ≠ ∅) ∧ PositiveFormTransfer (MatchingLift ge_w) ∧
      ComplementTransfer (MatchingLift ge_w) ∧ StrictDisjunctionIntro (MatchingLift ge_w) :=
  ⟨probablyToNotProbablyNot, probablyDistribInf, chancyDisjunctionIntro, minimality,
    maximality, mustToProbably, probablyToMight, positiveFormTransfer, complementTransfer,
    mLift_V13 ge_w⟩

end MLift

/-- The m-lifting refutes I1–I3, dissolving the disjunction problem (Fact 5). -/
theorem mLift_refutes_I_patterns :
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬RightUnion (MatchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬EquiprobabilityCollapse (MatchingLift ge_w)) ∧
    (∃ (W : Type) (ge_w : W → W → Prop),
      IsPreorder W ge_w ∧ ¬HamblinCollapse (MatchingLift ge_w)) := by
  have hcard : ∀ {n : ℕ} {A B : Set (Fin n)}, A.ncard < B.ncard →
      ¬MatchingLift (fun _ _ : Fin n ↦ True) A B :=
    fun h hm ↦ (not_le.2 h) hm.ncard_le
  have hc : ({0, 1} : Set (Fin 3))ᶜ = {2} := by ext x; fin_cases x <;> simp
  have hAAc : MatchingLift (fun _ _ : Fin 3 ↦ True) {0, 1} ({0, 1} : Set (Fin 3))ᶜ := by
    rw [hc]; exact matchingLift_singleton_iff.2 ⟨0, by simp, trivial⟩
  have h23 : ({0, 1} : Set (Fin 3)).ncard < (Set.univ : Set (Fin 3)).ncard := by
    rw [Set.ncard_pair (by decide), Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine ⟨⟨Fin 2, fun _ _ ↦ True, inferInstance, fun h ↦ hcard ?_
      (h {0} {0} {1} (refl_of _ _) (matchingLift_singleton_iff.2 ⟨0, rfl, trivial⟩))⟩,
    ⟨Fin 3, fun _ _ ↦ True, inferInstance, fun h ↦ hcard h23 (h _ Set.univ hAAc)⟩,
    ⟨Fin 3, fun _ _ ↦ True, inferInstance, fun h ↦ hcard h23 (h _ Set.univ ⟨hAAc, hcard ?_⟩)⟩⟩
  · show ({0} : Set (Fin 2)).ncard < (({0} : Set (Fin 2)) ∪ {1}).ncard
    rw [Set.singleton_union, Set.ncard_singleton, Set.ncard_pair (by decide)]
    decide
  · rw [hc, Set.ncard_singleton, Set.ncard_pair (by decide)]
    decide

/-- If the world ordering agrees with a measure on singletons, the m-lifting is sound for the
measure order (footnote 13). -/
theorem measure_le_of_matchingLift [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
    (μ : Measure W) (ge_w : W → W → Prop) (h : ∀ v u, ge_w v u ↔ μ {u} ≤ μ {v}) {A B : Set W}
    (hAB : MatchingLift ge_w A B) : μ B ≤ μ A := by
  classical
  obtain ⟨f, hf, hinj⟩ := hAB
  calc μ B = ∑ b ∈ B.toFinset, μ {b} := by rw [sum_measure_singleton, Set.coe_toFinset]
    _ ≤ ∑ b ∈ B.toFinset, μ {f b} :=
        Finset.sum_le_sum fun b hb ↦ (h _ _).mp (hf b (Set.mem_toFinset.mp hb)).2
    _ = ∑ a ∈ B.toFinset.image f, μ {a} := by
        rw [Finset.sum_image fun x hx y hy hxy ↦
          hinj (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy) hxy]
    _ = μ ↑(B.toFinset.image f) := sum_measure_singleton
    _ ≤ μ A := measure_mono fun a ha ↦ by
        rw [Finset.coe_image, Set.coe_toFinset] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        exact (hf b hb).1

/-! ### Figure 7: the chain `a ≻ b ≻ c ≻ d`

Worlds are `Fin 4`, with `0` the best; `ge_w u v` is `u ≤ v`. -/

theorem chain_pair_gt_pair :
    Strict (MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0, 1} {1, 2} ∧
      Strict (LewisLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0, 1} {1, 2} := by
  have hm : MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0, 1} {1, 2} :=
    ⟨fun b ↦ b - 1, fun b hb ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> decide, fun b₁ hb₁ b₂ hb₂ hf ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb₁ hb₂
      rcases hb₁ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;>
        first | rfl | exact absurd hf (by decide)⟩
  have hl : ¬ LewisLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0, 1} := by
    intro hd
    obtain ⟨a, ha, hle⟩ := hd (Set.mem_insert 0 {1})
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact absurd hle (by decide)
  exact ⟨⟨hm, fun h ↦ hl h.lewisLift⟩, ⟨hm.lewisLift, hl⟩⟩

theorem chain_singleton_vs_pair :
    Strict (LewisLift (· ≤ · : Fin 4 → Fin 4 → Prop)) {0} {1, 2} ∧
      ¬ MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {0} {1, 2} ∧
      ¬ MatchingLift (· ≤ · : Fin 4 → Fin 4 → Prop) {1, 2} {0} := by
  refine ⟨⟨fun b _ ↦ ⟨0, rfl, Fin.zero_le b⟩, fun hd ↦ ?_⟩, fun h ↦ ?_, ?_⟩
  · obtain ⟨a, ha, hle⟩ := hd rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> exact absurd hle (by decide)
  · have := h.ncard_le
    rw [Set.ncard_singleton, Set.ncard_pair (by decide)] at this
    omega
  · rintro ⟨f, hf, -⟩
    obtain ⟨hmem, hle⟩ := hf 0 rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h <;> rw [h] at hle <;> exact absurd hle (by decide)

/-- The m-lifting is not total, even over a linearly ordered set of worlds (before Fact 5). -/
theorem mLift_not_total :
    ∃ (W : Type) (ge_w : W → W → Prop), IsLinearOrder W ge_w ∧
      ∃ A B : Set W, ¬MatchingLift ge_w A B ∧ ¬MatchingLift ge_w B A := by
  refine ⟨Fin 4, (· ≤ ·), inferInstance, {0, 3}, {1, 2}, fun ⟨f, hf, hinj⟩ ↦ ?_,
    fun ⟨f, hf, _⟩ ↦ ?_⟩
  · have h1 := hf 1 (by simp)
    have h2 := hf 2 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
    exact absurd (hinj (by simp) (by simp) (show f 1 = f 2 by omega)) (by decide)
  · obtain ⟨h, hle⟩ := hf 0 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    omega

/-! ### Theorem 8: what separates FA from finite additivity -/

/-- Every FA order on `Fin n` is representable by a probability measure iff `n < 5`
(Theorem 8, after Kraft, Pratt and Seidenberg). -/
theorem fa_representable_iff_card_lt_five (n : ℕ) :
    (∀ r : Set (Fin n) → Set (Fin n) → Prop, IsQualitativeProbability r → Representable r) ↔
      n < 5 :=
  ⟨fun h ↦ by_contra fun hge ↦
      let ⟨r, hr, hnr⟩ := exists_nonrepresentable_fin (n := n) (by omega); hnr (h r hr),
    fun h r _ ↦ representable_of_card_lt_five r (by simpa using h)⟩

/-- No finite measure satisfies the World Cup comparisons (3)–(6). -/
theorem worldCup_not_finitelyAdditive (μ : Measure (Fin 5)) [IsFiniteMeasure μ] :
    ¬ (Strict μ.inducedGe {0, 4} {2, 3} ∧ Strict μ.inducedGe {1, 2} {0, 3} ∧
      Strict μ.inducedGe {3} {0, 2} ∧ Strict μ.inducedGe {0, 2, 3} {1, 4}) := by
  have pair : ∀ a b : Fin 5, a ≠ b → μ.real {a, b} = μ.real {a} + μ.real {b} := fun a b hab ↦ by
    rw [Set.insert_eq, measureReal_union (Set.disjoint_singleton.mpr hab) (.singleton b)]
  have triple : μ.real ({0, 2, 3} : Set (Fin 5)) = μ.real {0} + μ.real {2} + μ.real {3} := by
    rw [Set.insert_eq, measureReal_union (Set.disjoint_singleton_left.mpr (by simp)) .of_discrete,
      pair 2 3 (by decide), add_assoc]
  simp only [Strict, Measure.inducedGe_iff_real, not_le, triple,
    pair 0 4 (by decide), pair 2 3 (by decide), pair 1 2 (by decide), pair 0 3 (by decide),
    pair 0 2 (by decide), pair 1 4 (by decide)]
  intro ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, ⟨_, h4⟩⟩
  linarith

end HollidayIcard2013
