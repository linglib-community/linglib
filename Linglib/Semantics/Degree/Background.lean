module

public import Mathlib.Order.UpperLower.Closure
public import Linglib.Semantics.Degree.Delineation
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Degree.Measure.Basic

/-!
# Background orderings and threshold properties

In the states-based analysis of gradable predicates of Cariani, Santorio and Wellwood, which
builds on Wellwood's comparative and which the same authors apply to confidence reports, a
gradable predicate contributes two things: a background ordering of
states, the states of having some heat for *hot*, and in each context a threshold property, the
states that count as hot. The positive form says that the subject holds a state with the
threshold property. The comparative bypasses the threshold: an admissible measure of one of
the subject's states exceeds the greatest degree of the standard's. No covert positive morpheme
is needed, and neither form entails the other.

The background is a preorder `S` and a threshold property is an upper set `T` of it, the
monotonicity postulate of the analysis. A map `ρ : S → X` sends each state to its holder, or to
its theme, so the positive form of `x` is `x ∈ ρ '' T`, and the comparative of `a` over `b` is
`Degree.MaxComparative .gt (ρ · = a) (ρ · = b) μ` for an admissible measure `μ`. This file adds no
definitions. It records how the two components interact: the one inference from a comparative
to a positive form, upward monotonicity, holds on a total background and on no other.

Read as extensions, the threshold properties form a monotone delineation exactly when the
background is total, the parallel the authors draw with Klein's consistency postulate, and the
thresholds are degree thresholds pulled back along the measure exactly when the measure reflects
the background.

## Main statements

* `mem_image_of_maxComparative`: if `b` has the property and `a` has more of it than `b`, then
  `a` has the property, given an admissible measure and a total background.
* `maxComparative_and_not_mem_image`: the comparative does not entail the positive form.
* `isMonotoneOn_upperSets_iff`: the thresholds form a monotone delineation iff the background
  is total.
* `forall_isUpperSet_exists_preimage_iff`: the thresholds are pulled-back degree thresholds iff
  the measure reflects the background.

## References

* [cariani-santorio-wellwood-2023]
* [cariani-santorio-wellwood-2024]
* [wellwood-2015]
* [klein-1980]
-/

@[expose] public section

namespace Degree

open Set

variable {S X D : Type*} [Preorder S] [Preorder D] {ρ : S → X} {μ : S → D} {T : Set S}

/-! ### Upward monotonicity -/

theorem mem_image_of_maxComparative [@Std.Total S (· ≤ ·)] (hT : IsUpperSet T)
    (hμ : StrictMono μ) {a b : X} (hb : b ∈ ρ '' T)
    (h : MaxComparative .gt (ρ · = a) (ρ · = b) μ) : a ∈ ρ '' T :=
  let ⟨_, hs, hsb⟩ := hb
  let ⟨y, hya, hlt⟩ := h.exists_lt hsb
  ⟨y, hT (hμ.reflect_le hlt.le) hs, hya⟩

/-- Without admissibility upward monotonicity fails even on a total background. On `Bool` with
the measure reversed, `true` has the property `Ici true` and `false` measures above it. -/
example :
    (true : Bool) ∈ id '' Ici true ∧ MaxComparative .gt (· = false) (· = true) (fun b : Bool ↦ !b) ∧
      false ∉ id '' Ici true := by
  refine ⟨⟨true, mem_Ici.2 le_rfl, rfl⟩, (maxComparative_eq_iff _ _ _).2 (by decide), ?_⟩
  rintro ⟨u, hu, rfl⟩
  exact absurd (mem_Ici.1 hu) (by decide)

theorem not_mem_image_Ici_of_not_le {s t : S} (hst : ¬ s ≤ t) (hlt : μ s < μ t)
    (hs : ∀ u, ρ u = ρ s → u = s) (ht : ∀ u, ρ u = ρ t → u = t) :
    ρ s ∈ ρ '' Ici s ∧ MaxComparative .gt (ρ · = ρ t) (ρ · = ρ s) μ ∧ ρ t ∉ ρ '' Ici s :=
  ⟨⟨s, mem_Ici.2 le_rfl, rfl⟩,
    (maxComparative_iff_of_unique (P := (ρ · = ρ t)) (Q := (ρ · = ρ s)) rfl ht rfl hs).2 hlt,
    fun ⟨u, hu, hut⟩ ↦ hst (ht u hut ▸ hu)⟩

/-- The failure is realized by an admissible measure. On the componentwise order of `ℕ × ℕ`,
the sum of the coordinates is admissible and puts `(1, 0)` below the incomparable `(0, 2)`. -/
example :
    StrictMono (fun x : ℕ × ℕ ↦ x.1 + x.2) ∧ ¬ ((1, 0) : ℕ × ℕ) ≤ (0, 2) ∧
      (1, 0).1 + (1, 0).2 < (0, 2).1 + (0, 2).2 := by
  refine ⟨fun x y hxy ↦ ?_, by decide, by decide⟩
  rcases Prod.lt_iff.1 hxy with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> dsimp only <;> omega

/-! ### The comparative and the positive form -/

omit [Preorder S] in
theorem maxComparative_and_not_mem_image {s t : S} (hlt : μ t < μ s) (hsT : s ∉ T)
    (hs : ∀ u, ρ u = ρ s → u = s) (ht : ∀ u, ρ u = ρ t → u = t) :
    MaxComparative .gt (ρ · = ρ s) (ρ · = ρ t) μ ∧ ρ s ∉ ρ '' T :=
  ⟨(maxComparative_iff_of_unique (P := (ρ · = ρ s)) (Q := (ρ · = ρ t)) rfl hs rfl ht).2 hlt,
    fun ⟨u, hu, hus⟩ ↦ hsT (hs u hus ▸ hu)⟩

/-! ### Delineations and degree thresholds -/

section Thresholds

theorem isMonotoneOn_upperSets_iff :
    (⟨id⟩ : Delineation S).IsMonotoneOn {C | IsUpperSet C} ↔ ∀ s t : S, s ≤ t ∨ t ≤ s := by
  refine ⟨fun h s t ↦ by_contra fun hst ↦ ?_, fun htot C₁ h₁ C₂ h₂ a b ha hb hb₂ ↦ ?_⟩
  · obtain ⟨hst, hts⟩ := not_or.1 hst
    exact hts (h (Ici s) (isUpperSet_Ici s) (Ici t) (isUpperSet_Ici t) s t le_rfl hst le_rfl)
  · exact (htot a b).elim (fun hab ↦ absurd (h₁ hab ha) hb) fun hba ↦ h₂ hba hb₂

theorem exists_isUpperSet_of_maxComparative (hm : Monotone μ) {a b : X}
    (h : MaxComparative .gt (ρ · = a) (ρ · = b) μ) :
    ∃ T, IsUpperSet T ∧ a ∈ ρ '' T ∧ b ∉ ρ '' T := by
  obtain ⟨δ, hδ, s, hsa, hlt⟩ := h
  refine ⟨Ici s, isUpperSet_Ici s, ⟨s, mem_Ici.2 le_rfl, hsa⟩, ?_⟩
  rintro ⟨t, hst, htb⟩
  exact ((hδ.2 ⟨t, htb, rfl⟩).trans_lt hlt).not_ge (hm hst)

/-- Admissibility alone does not yield a separating threshold. With two tied states every
measure is admissible and every threshold holding of one holds of the other. The preorder is
passed explicitly, since `Bool`'s own order would otherwise be found. -/
example :
    let tied : Preorder Bool := Preorder.lift fun _ ↦ ()
    @StrictMono _ _ tied _ Bool.toNat ∧ MaxComparative .gt (· = true) (· = false) Bool.toNat ∧
      ∀ T : Set Bool, @IsUpperSet _ tied.toLE T → true ∈ T → false ∈ T :=
  ⟨fun _ _ h ↦ absurd h (lt_irrefl ()), (maxComparative_eq_iff _ _ _).2 Nat.zero_lt_one,
    fun _ hT ht ↦ hT trivial ht⟩

theorem maxComparative_of_exists_isUpperSet [@Std.Total S (· ≤ ·)] (hμ : StrictMono μ)
    {a b : X} (hb : ∃ δ, IsGreatest (μ '' {s | ρ s = b}) δ)
    (h : ∃ T, IsUpperSet T ∧ a ∈ ρ '' T ∧ b ∉ ρ '' T) :
    MaxComparative .gt (ρ · = a) (ρ · = b) μ := by
  obtain ⟨δ, hδ⟩ := hb
  obtain ⟨T, hT, ⟨s, hsT, hsa⟩, hbT⟩ := h
  obtain ⟨t, htb, rfl⟩ := hδ.1
  have hst : ¬ s ≤ t := fun hst ↦ hbT ⟨t, hT hst hsT, htb⟩
  exact ⟨_, hδ, s, hsa, hμ (lt_of_le_not_ge ((total_of (· ≤ ·) t s).resolve_right hst) hst)⟩

theorem maxComparative_iff_exists_isUpperSet [@Std.Total S (· ≤ ·)] (hμ : StrictMono μ)
    (hm : Monotone μ) {a b : X} (hb : ∃ δ, IsGreatest (μ '' {s | ρ s = b}) δ) :
    MaxComparative .gt (ρ · = a) (ρ · = b) μ ↔ ∃ T, IsUpperSet T ∧ a ∈ ρ '' T ∧ b ∉ ρ '' T :=
  ⟨exists_isUpperSet_of_maxComparative hm, maxComparative_of_exists_isUpperSet hμ hb⟩

theorem forall_isUpperSet_exists_preimage_iff :
    (∀ T : Set S, IsUpperSet T → ∃ U : Set D, IsUpperSet U ∧ T = μ ⁻¹' U) ↔
      ∀ a b, μ a ≤ μ b → a ≤ b := by
  refine ⟨fun h a b hab ↦ ?_, fun h T hT ↦ ⟨upperClosure (μ '' T), (upperClosure _).upper, ?_⟩⟩
  · obtain ⟨U, hU, hT⟩ := h (Ici a) (isUpperSet_Ici a)
    exact (Set.ext_iff.1 hT b).2 (hU hab ((Set.ext_iff.1 hT a).1 (mem_Ici.2 le_rfl)))
  · refine Set.ext fun s ↦ ⟨fun hs ↦ subset_upperClosure ⟨s, hs, rfl⟩, ?_⟩
    rintro ⟨_, ⟨t, ht, rfl⟩, hts⟩
    exact hT (h t s hts) ht

theorem total_of_reflect_le {D : Type*} [LinearOrder D] {μ : S → D}
    (h : ∀ a b, μ a ≤ μ b → a ≤ b) (s t : S) : s ≤ t ∨ t ≤ s :=
  (le_total (μ s) (μ t)).imp (h s t) (h t s)

theorem exists_isUpperSet_forall_ne_preimage {D : Type*} [LinearOrder D] (μ : S → D) {s t : S}
    (hst : ¬ s ≤ t) (hts : ¬ t ≤ s) :
    ∃ T : Set S, IsUpperSet T ∧ ∀ U : Set D, IsUpperSet U → T ≠ μ ⁻¹' U := by
  by_contra h
  push Not at h
  obtain h | h := total_of_reflect_le (forall_isUpperSet_exists_preimage_iff.1 h) s t
  exacts [hst h, hts h]

theorem preimage_Ici_apply_eq_Ici (h : ∀ a b, μ a ≤ μ b → a ≤ b) (hm : Monotone μ) (c : S) :
    μ ⁻¹' Set.Ici (μ c) = Ici c :=
  Set.ext fun s ↦ ⟨h c s, fun hs ↦ hm hs⟩

end Thresholds

end Degree
