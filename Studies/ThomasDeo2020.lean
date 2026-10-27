module

public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Order.Setoid.Partition
public import Linglib.Semantics.Exhaustification.Pointwise
public import Linglib.Data.Examples.ThomasDeo2020

/-!
# Thomas and Deo (2020): The Interaction of *just* with Modified Scalar Predicates

Thomas and Deo analyse the approximative use of *just* with equatives and comparatives, *just as
tall as* and *just older than*. A degree is interpreted at a level of precision, the open interval
whose radius is the grain; an equative places the subject's degree above the infimum of the
standard's level and a comparative above its supremum. Equatives make stronger claims at finer
grains and comparatives at coarser ones. *Just* asserts the prejacent at the finest grain and
denies it at every coarser grain where it would be stronger, so it adds nothing to an equative
and gives a comparative an upper bound that cannot be cancelled.

## Main definitions

* `ThomasDeo2020.level`: the level of radius `ε` around a degree, (42)–(43).
* `ThomasDeo2020.equative`, `ThomasDeo2020.comparative`: the constructions at a grain, (45) and
  (49).
* `ThomasDeo2020.just`: approximative *just*, (44).

## Main results

* `ThomasDeo2020.isGranularity_level`, `ThomasDeo2020.not_isPartition_range_level`: a level is a
  granularity function, (40), that does not partition the scale.
* `ThomasDeo2020.level_eq_iUnion_cell`: a level is the union of the cells around its degree over
  all alignments of the grain, footnote 9.
* `ThomasDeo2020.equative_mono`, `ThomasDeo2020.comparative_anti`: (47) and (51).
* `ThomasDeo2020.just_equative`: with an equative *just* adds nothing, (48).
* `ThomasDeo2020.just_comparative_iff`, `ThomasDeo2020.just.not_comparative`: *just older than*
  holds at the finest grain and at no coarser one, (24).
* `ThomasDeo2020.just_equative_of_comparative`: *just as tall as, if not taller*, (16).
* `ThomasDeo2020.not_just_comparative_iff`: the two ways of denying *just older*, (31).
* `ThomasDeo2020.just_comparative_Ici_iff`: the negative component is exhaustification over the
  chain of grains, section 5.
* `ThomasDeo2020.not_equative_of_comparative`: the contradiction of (30).

## Implementation notes

Degrees form a linearly ordered additive group. A construction relates the grain, the standard
and the subject's maximal degree, which stands in for the existential over degrees of (45) and
(49); the infimum and supremum of the level are computed as in (46b) and (50b), `isGLB_level` and
`isLUB_level`. The endpoint clauses of (43) are not formalized: they leave the endpoint out of its
own level, against (40a), which the paper says levels satisfy. The finest grain of (44) and the
contextual grains are parameters; how magnitude, permitted error and roundness fix the finest
grain (section 4) and the role of expectations (section 3.4) are not formalized. The examples are
the rows of `Data.Examples.ThomasDeo2020`.

## References

* [thomas-deo-2020]
* [sauerland-stateva-2011]
* [kennedy-mcnally-2005]
* [coppock-beaver-2014]
* [beaver-clark-2008]
* [lasersohn-1999]
* [krifka-2007]
-/

@[expose] public section

namespace ThomasDeo2020

open Degree Exhaustification

variable {D : Type*} [AddCommGroup D] [LinearOrder D]

/-! ### Granularity levels, (40)–(43) -/

/-- The level of radius `ε` around `d`, (43) at a degree that is not an endpoint of the scale. -/
def level (ε d : D) : Set D := Set.Ioo (d - ε) (d + ε)

variable {ε ε₁ ε₂ εf d dc μx x : D} {G : Set D}

section Grain

variable [IsOrderedAddMonoid D]

theorem mem_level : x ∈ level ε d ↔ |x - d| < ε := by
  rw [level, Set.mem_Ioo, abs_sub_lt_iff, sub_lt_comm, sub_lt_iff_lt_add', and_comm,
    sub_lt_iff_lt_add']

theorem mem_level_self (hε : 0 < ε) : d ∈ level ε d := by simpa [mem_level]

/-- The level of radius `ε` is a granularity function of width `2 • ε`; the paper notes that the
properties in (40) hold for levels. -/
theorem isGranularity_level (hε : 0 < ε) : IsGranularity (level ε) (2 • ε) where
  mem_self _ := mem_level_self hε
  exists_Ioo_subset_subset_Icc d := ⟨d - ε, by
    rw [level, two_nsmul, show d - ε + (ε + ε) = d + ε by abel]
    exact ⟨le_rfl, Set.Ioo_subset_Icc_self⟩⟩

/-- Levels do not partition the scale, as the paper notes in introducing (43). -/
theorem not_isPartition_range_level [DenselyOrdered D] (hε : 0 < ε) :
    ¬ Setoid.IsPartition (Set.range (level ε)) := fun ⟨_, h⟩ ↦ by
  obtain ⟨m, hm0, hmε⟩ := exists_between hε
  obtain ⟨_, -, huniq⟩ := h 0
  have h₀ := huniq (level ε 0) ⟨⟨0, rfl⟩, mem_level_self hε⟩
  have hm := huniq (level ε m) ⟨⟨m, rfl⟩, by rwa [mem_level, zero_sub, abs_neg, abs_of_pos hm0]⟩
  have hmem : m - ε ∈ level ε 0 := by
    rw [mem_level, sub_zero, abs_sub_comm, abs_of_pos (sub_pos.2 hmε)]
    exact sub_lt_self ε hm0
  rw [h₀.trans hm.symm, mem_level, sub_sub_cancel_left, abs_neg, abs_of_pos hε] at hmem
  exact lt_irrefl ε hmem

-- (46b)
theorem isGLB_level [DenselyOrdered D] (hε : 0 < ε) : IsGLB (level ε d) (d - ε) :=
  isGLB_Ioo (Set.nonempty_Ioo.1 ⟨d, mem_level_self hε⟩)

-- (50b)
theorem isLUB_level [DenselyOrdered D] (hε : 0 < ε) : IsLUB (level ε d) (d + ε) :=
  isLUB_Ioo (Set.nonempty_Ioo.1 ⟨d, mem_level_self hε⟩)

/-- The level of radius `ε` around `d` is the union over alignments of the grain cells containing
`d` (footnote 9). -/
theorem level_eq_iUnion_cell {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    [FloorRing α] {ε : α} (hε : 0 < ε) (d : α) :
    level ε d = ⋃ t, {y | y - t ∈ (grain ε).cell (d - t)} := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_level]
  refine ⟨fun h ↦ ⟨min y d + ε / 2, ?_⟩, fun ⟨t, ht⟩ ↦ ?_⟩
  · have h0 := cell_grain hε 0
    rw [representative_eq_self_of_mem_zmultiples hε.ne' (zero_mem _), zero_sub, zero_add] at h0
    have key : ∀ z, min y d ≤ z → z - min y d < ε → z - (min y d + ε / 2) ∈ (grain ε).cell 0 :=
      fun z h₁ h₂ ↦ h0 ▸ ⟨by linarith, by linarith⟩
    have hd := key d (min_le_right y d) (by
      rcases min_choice y d with hm | hm <;> rw [hm] <;> linarith [(abs_sub_lt_iff.1 h).2])
    have hy := key y (min_le_left y d) (by
      rcases min_choice y d with hm | hm <;> rw [hm] <;> linarith [(abs_sub_lt_iff.1 h).1])
    exact (grain ε).trans hy ((grain ε).symm hd)
  · simpa using abs_sub_lt_of_grain hε ht

end Grain

/-! ### Constructions at a grain (sections 4.1 and 4.2) -/

/-- The equative at a grain holds when the subject's degree exceeds the infimum of the standard's
level, (45). -/
def equative (ε dc μx : D) : Prop := dc - ε < μx

/-- The comparative at a grain holds when the subject's degree exceeds the supremum of the
standard's level, (49). -/
def comparative (ε dc μx : D) : Prop := dc + ε < μx

theorem equative_iff : equative ε dc μx ↔ dc - ε < μx := Iff.rfl

theorem comparative_iff : comparative ε dc μx ↔ dc + ε < μx := Iff.rfl

/-- A construction at one grain is at least as strong as at another when it entails it at every
degree, the ranking of footnote 10. -/
def AtLeastAsStrong (p : D → D → Prop) (ε₁ ε₂ : D) : Prop := ∀ μx, p ε₁ μx → p ε₂ μx

/-- Approximative *just*, (44), asserts that the prejacent holds at the finest grain and at no grain
of the contextual set at which it would make a stronger claim. -/
def just (p : D → D → Prop) (G : Set D) (εf μx : D) : Prop :=
  p εf μx ∧ ∀ ε ∈ G, p ε μx → AtLeastAsStrong p εf ε

variable [IsOrderedAddMonoid D]

/-- An equative at a finer grain is at least as strong, (47). -/
theorem equative_mono (h : ε₁ ≤ ε₂) : AtLeastAsStrong (equative · dc) ε₁ ε₂ :=
  fun _ ↦ (sub_le_sub_left h dc).trans_lt

/-- A comparative at a coarser grain is at least as strong, (51). -/
theorem comparative_anti (h : ε₁ ≤ ε₂) : AtLeastAsStrong (comparative · dc) ε₂ ε₁ :=
  fun _ ↦ (add_le_add_right h dc).trans_lt

/-- At one grain a comparative and its reversed equative cannot both hold (30). -/
theorem not_equative_of_comparative {μF dS : D} (h : comparative ε dS μF) :
    ¬ equative ε μF dS :=
  fun h' ↦ lt_asymm h (sub_lt_iff_lt_add.1 h')

/-! ### Approximative *just* (44) -/

/-- With an equative the negative component is vacuous, so *just as tall as* is the equative at the
finest grain, (48). -/
theorem just_equative (hG : ∀ ε ∈ G, εf ≤ ε) :
    just (equative · dc) G εf μx ↔ equative εf dc μx :=
  ⟨And.left, fun h ↦ ⟨h, fun ε hε _ ↦ equative_mono (hG ε hε)⟩⟩

/-- An equative with *just* enforces no upper bound, (16), since the subject may exceed the standard
by any grain. -/
theorem just_equative_of_comparative (hG : ∀ ε ∈ G, εf ≤ ε) (hf : 0 ≤ εf) (hε : 0 ≤ ε)
    (h : comparative ε dc μx) : just (equative · dc) G εf μx :=
  (just_equative hG).2
    (lt_of_le_of_lt ((sub_le_self dc hf).trans (le_add_of_nonneg_right hε)) h)

/-- With a comparative the negative component excludes every coarser grain, so the upper bound
cannot be cancelled, (24). -/
theorem just.not_comparative (h : just (comparative · dc) G εf μx) (hε : ε ∈ G)
    (hlt : εf < ε) : ¬ comparative ε dc μx :=
  fun hc ↦ lt_irrefl (dc + ε) (h.2 ε hε hc (dc + ε) (add_lt_add_of_le_of_lt le_rfl hlt))

/-- *Just older than* holds when the comparative holds at the finest grain and at no coarser one. -/
theorem just_comparative_iff (hG : ∀ ε ∈ G, εf ≤ ε) :
    just (comparative · dc) G εf μx ↔
      dc + εf < μx ∧ ∀ ε ∈ G, εf < ε → μx ≤ dc + ε := by
  refine ⟨fun h ↦ ⟨h.1, fun ε hε hlt ↦ not_lt.1 (h.not_comparative hε hlt)⟩, fun h ↦ ⟨h.1, ?_⟩⟩
  intro ε hε hc
  rcases (hG ε hε).lt_or_eq with hlt | rfl
  · exact absurd hc (not_lt.2 (h.2 ε hε hlt))
  · exact fun _ h ↦ h

/-- Denying *just older* denies the comparative at the finest grain or asserts it at a coarser one,
that the subject is significantly older, (31). -/
theorem not_just_comparative_iff (hG : ∀ ε ∈ G, εf ≤ ε) :
    ¬ just (comparative · dc) G εf μx ↔
      μx ≤ dc + εf ∨ ∃ ε ∈ G, εf < ε ∧ dc + ε < μx := by
  rw [just_comparative_iff hG]
  constructor
  · intro h
    by_cases h1 : dc + εf < μx
    · push Not at h
      exact Or.inr (h h1)
    · exact Or.inl (not_lt.1 h1)
  · rintro (h | ⟨ε, hε, hlt, h2⟩) ⟨h1, h3⟩
    · exact absurd h1 (not_lt.2 h)
    · exact absurd h2 (not_lt.2 (h3 ε hε hlt))

/-- Over the grains no finer than the finest, the negative component of *just* with a
comparative is exhaustification against the strictly coarser grains, the stronger alternatives
of the chain (section 5). -/
theorem just_comparative_Ici_iff :
    just (comparative · dc) (Set.Ici εf) εf μx ↔ exhAgainst (· < ·) (comparative · dc μx) εf :=
  (just_comparative_iff fun _ hε ↦ hε).trans
    ⟨fun h ↦ ⟨h.1, fun ε hε ↦ not_lt.2 (h.2 ε (le_of_lt hε) hε)⟩,
      fun h ↦ ⟨h.1, fun ε _ hε ↦ not_lt.1 (h.2 ε hε)⟩⟩

theorem just_comparative_iff_succ {ε' : D} (his : εf < ε') (hleast : ∀ ε, εf < ε → ε' ≤ ε) :
    just (comparative · dc) (Set.Ici εf) εf μx ↔ dc + εf < μx ∧ μx ≤ dc + ε' := by
  rw [just_comparative_Ici_iff, exhAgainst_lt_iff_succ (A := (comparative · dc μx))
    (fun _ _ h ↦ comparative_anti h μx) his hleast, comparative_iff, comparative_iff, not_lt]

end ThomasDeo2020
