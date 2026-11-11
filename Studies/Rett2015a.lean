module

public import Linglib.Data.Examples.Rett2015a
public import Linglib.Fragments.English.NumeralModifiers
public import Linglib.Semantics.Degree.Quantifier
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

/-!
# Rett (2015): Measure phrase equatives and modified numerals

An equative whose standard is a measure phrase, *as tall as 5ft*, tends to mean *at most*, where a
clausal equative means *at least*. Rett keeps one meaning for *as*, the comparison `≥`, and derives
the difference from implicature. Negating the stronger comparative makes a plural equative name
[the greatest measure among its correlates](##Rett2015a.strengthened_some_iff), which
[excludes a higher value and allows a lower one](##Rett2015a.exists_strengthened_iff), and a
negative antonym reverses the scale, so
[*as short as* names the least](##Rett2015a.as_short_as_iff). Competition with the bare measure
phrase [requires a range](##Rett2015a.acceptable_iff_judgment) unless the standard is high, and
scope [separates a universal DP from a modal](##Rett2015a.range_iff_judgment).

## Implementation notes

The existential over representative subgroups is an existential over a set `R`. The measure of a
plural subgroup is that of its tallest member, so `R` holds those members, and a correlate outside
`R` may exceed the standard, the exceptions the paper predicts. Heights are in inches.

## TODO

The evaluative branch of the M-implicature, (80), needs a contextual standard for each of (16),
(20) and (21). The extension to modals in §4 and the implicatures of the remaining Class B
modifiers are open, and *n or more* is not in the fragment.

## References

* [rett-2015a]
* [nouwen-2010]
* [geurts-nouwen-2007]
-/

@[expose] public section

namespace Rett2015a

open Quantifier Quantifier.Det Set OrderDual
open Comparison (maxOnScale mem_maxOnScale_dual mem_maxOnScale_gt mem_maxOnScale_lt)
open scoped Denotes

/-! ### Comparison and strengthening -/

section Strengthening

variable {E D : Type*} [LinearOrder D] {R : Set E} {μ : E → D} {n : D}

-- (35), (65): the equative with the negated comparative is *exactly*.
theorem maxIn_ge_and_not_gt_iff {X : Set D} :
    MaxIn (Comparison.ge.interval n) X ∧ ¬ MaxIn (Comparison.gt.interval n) X ↔
      MaxIn (Comparison.eq.interval n) X := by
  constructor
  · rintro ⟨⟨m, hm, h⟩, hn⟩
    exact ⟨m, le_antisymm (not_lt.1 fun hlt ↦ hn ⟨m, hlt, h⟩) hm, h⟩
  · rintro ⟨m, rfl, h⟩
    exact ⟨⟨m, le_rfl, h⟩, fun ⟨_, hlt, h'⟩ ↦ absurd (h'.unique h ▸ hlt : m < m) (lt_irrefl m)⟩

-- (47b), (70): the strengthened MPE and the strengthened bare measure phrase are synonymous.
theorem maxIn_eq_iff {X : Set D} :
    MaxIn (Comparison.eq.interval n) X ↔ n ∈ X ∧ ¬ ∃ d, n < d ∧ d ∈ X := by
  constructor
  · rintro ⟨m, rfl, h⟩
    exact ⟨h.1, fun ⟨_, hlt, hd⟩ ↦ (h.2 hd).not_gt hlt⟩
  · rintro ⟨hn, h⟩
    exact ⟨n, rfl, hn, fun d hd ↦ not_lt.1 fun hlt ↦ h ⟨d, hlt, hd⟩⟩

/-- An MP equative under the quantifier `Q` over its correlates with its Q-implicature: the
equative holds, (84a) and (86a), and the comparative does not, (84b) and (86b). -/
def Strengthened (Q : Quantifier E) (μ : E → D) (n : D) : Prop :=
  LowScope (MaxIn (Comparison.ge.interval n)) Q (Iic ∘ μ) ∧
    ¬ LowScope (MaxIn (Comparison.gt.interval n)) Q (Iic ∘ μ)

theorem lowScope_some_iff {c : Comparison} :
    LowScope (MaxIn (c.interval n)) (Det.some R) (Iic ∘ μ) ↔ ∃ x ∈ R, c.Rel (μ x) n := by
  rw [lowScope_maxIn]
  exact ⟨fun ⟨x, hx, h⟩ ↦ ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ ↦ ⟨x, hx, h⟩⟩

theorem lowScope_every_iff {c : Comparison} :
    LowScope (MaxIn (c.interval n)) (every R) (Iic ∘ μ) ↔ ∀ x ∈ R, c.Rel (μ x) n := by
  rw [lowScope_maxIn]
  rfl

/-- The plural MP equative with its Q-implicature is the "inclusive at most" reading: the standard
is the greatest of the correlates' measures. -/
theorem strengthened_some_iff :
    Strengthened (Det.some R) μ n ↔ n ∈ maxOnScale .gt (μ '' R) := by
  rw [Strengthened, lowScope_some_iff, lowScope_some_iff, mem_maxOnScale_gt]
  constructor
  · rintro ⟨⟨x, hx, hxn⟩, h⟩
    have hle : ∀ y ∈ R, μ y ≤ n := fun y hy ↦ not_lt.1 fun hlt ↦ h ⟨y, hy, hlt⟩
    exact ⟨⟨x, hx, le_antisymm (hle x hx) hxn⟩, forall_mem_image.2 hle⟩
  · rintro ⟨⟨x, hx, rfl⟩, hub⟩
    exact ⟨⟨x, hx, le_rfl⟩, fun ⟨y, hy, hlt⟩ ↦ (hub (mem_image_of_mem μ hy)).not_gt hlt⟩

-- (65c): a singular correlate is measured exactly.
theorem strengthened_some_singleton_iff {x : E} : Strengthened (Det.some {x}) μ n ↔ μ x = n := by
  rw [strengthened_some_iff, mem_maxOnScale_gt, image_singleton]
  exact ⟨fun h ↦ h.1.symm, fun h ↦ h ▸ isGreatest_singleton⟩

/-- A correlate may measure anything up to the standard and nothing above it, the contrast of (5):
the equative names the top of a range. -/
theorem exists_strengthened_iff {v n : D} :
    (∃ μ : Bool → D, Strengthened (Det.some univ) μ n ∧ μ false = v) ↔ v ≤ n := by
  constructor
  · rintro ⟨μ, h, rfl⟩
    exact (mem_maxOnScale_gt.1 (strengthened_some_iff.1 h)).2 (mem_image_of_mem μ (mem_univ _))
  · intro hv
    refine ⟨fun b ↦ b.rec v n, strengthened_some_iff.2 (mem_maxOnScale_gt.2 ?_), rfl⟩
    refine ⟨⟨true, trivial, rfl⟩, ?_⟩
    rintro _ ⟨b, -, rfl⟩
    cases b
    exacts [hv, le_rfl]

-- (81): a singular correlate allows only the standard.
theorem exists_strengthened_singleton_iff {v n : D} :
    (∃ μ : Unit → D, Strengthened (Det.some {()}) μ n ∧ μ () = v) ↔ v = n :=
  ⟨fun ⟨_, h, hv⟩ ↦ hv ▸ strengthened_some_singleton_iff.1 h,
    fun h ↦ ⟨fun _ ↦ v, strengthened_some_singleton_iff.2 h, rfl⟩⟩

/-- A negative antonym reads the measure on the reversed scale, so *as short as* names the least of
the correlates' measures, as in (11). -/
theorem as_short_as_iff :
    Strengthened (Det.some R) (toDual ∘ μ) (toDual n) ↔ n ∈ maxOnScale .lt (μ '' R) := by
  have h : (toDual ∘ μ) '' R = ofDual ⁻¹' (μ '' R) := by
    ext d
    exact ⟨fun ⟨x, hx, hd⟩ ↦ ⟨x, hx, hd⟩, fun ⟨x, hx, hd⟩ ↦ ⟨x, hx, hd⟩⟩
  rw [strengthened_some_iff, h]
  exact (mem_maxOnScale_dual (c := .gt)).symm

-- (84c) is the prose gloss, that the correlates differ, wherever the Q-implicature holds.
theorem not_every_iff_nontrivial (h : Strengthened (Det.some R) μ n) :
    ¬ every R {x | n ≤ μ x} ↔ (μ '' R).Nontrivial := by
  obtain ⟨⟨x, hx, rfl⟩, hub⟩ := mem_maxOnScale_gt.1 (strengthened_some_iff.1 h)
  have hle : ∀ y ∈ R, μ y ≤ μ x := fun y hy ↦ hub (mem_image_of_mem μ hy)
  constructor
  · intro hne
    obtain ⟨y, hy, hlt⟩ : ∃ y ∈ R, μ y < μ x := by
      by_contra hcon
      exact hne fun y hy ↦ not_lt.1 fun hlt ↦ hcon ⟨y, hy, hlt⟩
    exact ⟨_, mem_image_of_mem μ hx, _, mem_image_of_mem μ hy, hlt.ne'⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ hall
    exact hab ((le_antisymm (hle a ha) (hall ha)).trans (le_antisymm (hle b hb) (hall hb)).symm)

-- The MP construction is an R-alternative only over a punctual correlate value.
theorem subsingleton_and_strengthened_iff :
    (μ '' R).Subsingleton ∧ Strengthened (Det.some R) μ n ↔ R.Nonempty ∧ ∀ x ∈ R, μ x = n := by
  rw [strengthened_some_iff, mem_maxOnScale_gt]
  constructor
  · rintro ⟨hs, ⟨x, hx, rfl⟩, -⟩
    exact ⟨⟨x, hx⟩, fun y hy ↦ hs (mem_image_of_mem μ hy) (mem_image_of_mem μ hx)⟩
  · rintro ⟨⟨x, hx⟩, h⟩
    refine ⟨?_, ⟨x, hx, h x hx⟩, forall_mem_image.2 fun y hy ↦ (h y hy).le⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h a ha).trans (h b hb).symm

/-! ### Scope -/

-- (86c) is the implicature computed under the universal.
theorem lowScope_eq_every_iff :
    LowScope (MaxIn (Comparison.eq.interval n)) (every R) (Iic ∘ μ) ↔
      ∀ x ∈ R, MaxIn (Comparison.ge.interval n) (Iic (μ x)) ∧
        ¬ MaxIn (Comparison.gt.interval n) (Iic (μ x)) :=
  ⟨fun h _ hx ↦ maxIn_ge_and_not_gt_iff.2 (h hx), fun h _ hx ↦ maxIn_ge_and_not_gt_iff.1 (h _ hx)⟩

-- (87c) is the greatest lower bound of the heights across the accessible worlds.
theorem highScope_eq_every_iff :
    HighScope (MaxIn (Comparison.eq.interval n)) (every R) (Iic ∘ μ) ↔ IsGLB (μ '' R) n :=
  highScope_maxIn_singleton_every

-- The strengthened universal DP has no range to offer.
theorem not_nontrivial_of_lowScope_eq_every
    (h : LowScope (MaxIn (Comparison.eq.interval n)) (every R) (Iic ∘ μ)) :
    ¬ (μ '' R).Nontrivial := by
  have hμ := lowScope_every_iff.1 h
  rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩
  exact hab ((hμ a ha).trans (hμ b hb).symm)

end Strengthening

/-! ### Two heights -/

/-- Two correlates, of 5ft and 6ft. -/
def twoHeights : Fin 2 → ℕ := ![60, 72]

theorem strengthened_every_not_eq :
    Strengthened (every univ) twoHeights 60 ∧
      ¬ LowScope (MaxIn (Comparison.eq.interval 60)) (every univ) (Iic ∘ twoHeights) := by
  simp only [Strengthened, lowScope_every_iff]
  simp [twoHeights, Fin.forall_fin_two]

theorem eq_some_not_strengthened :
    LowScope (MaxIn (Comparison.eq.interval 60)) (Det.some univ) (Iic ∘ twoHeights) ∧
      ¬ Strengthened (Det.some univ) twoHeights 60 := by
  refine ⟨lowScope_some_iff.2 ⟨0, trivial, rfl⟩, fun h ↦ ?_⟩
  exact absurd (h.2 (lowScope_some_iff.2 ⟨1, trivial, by simp [twoHeights]⟩)) (by simp)

private theorem nontrivial_twoHeights : (twoHeights '' univ).Nontrivial :=
  ⟨60, ⟨0, trivial, rfl⟩, 72, ⟨1, trivial, rfl⟩, by decide⟩

private theorem isGLB_twoHeights : IsGLB (twoHeights '' univ) 60 := by
  constructor
  · rintro _ ⟨i, -, rfl⟩
    fin_cases i <;> simp [twoHeights]
  · exact fun d hd ↦ hd ⟨0, trivial, rfl⟩

open Examples in
/-- A range is compatible with the strengthened equative when the degree quantifier scopes over a
universal, as under *must*, and not when a universal DP scopes over it, the contrast of (86) and
(87). -/
theorem range_iff_judgment :
    ((∃ (μ : Fin 2 → ℕ) (n : ℕ), (μ '' univ).Nontrivial ∧
        LowScope (MaxIn (Comparison.eq.interval n)) (every univ) (Iic ∘ μ)) ↔
      ex_86.judgment = .acceptable) ∧
    ((∃ (μ : Fin 2 → ℕ) (n : ℕ), (μ '' univ).Nontrivial ∧
        HighScope (MaxIn (Comparison.eq.interval n)) (every univ) (Iic ∘ μ)) ↔
      ex_87.judgment = .acceptable) := by
  refine ⟨⟨fun ⟨_, _, hr, h⟩ ↦ absurd hr (not_nontrivial_of_lowScope_eq_every h),
      fun h ↦ absurd h (by decide)⟩, ⟨fun _ ↦ by decide, fun _ ↦ ?_⟩⟩
  exact ⟨twoHeights, 60, nontrivial_twoHeights, highScope_eq_every_iff.2 isGLB_twoHeights⟩

/-! ### Table 1 -/

/-- The scenarios of Table 1. -/
inductive Scenario where
  | s1 | s2 | s3 | s4 | s5
  deriving DecidableEq

open Scenario

/-- The heights of the three linguists in a scenario, in inches. -/
def Scenario.heights : Scenario → Fin 3 → ℕ
  | s1 => ![48, 48, 48]
  | s2 => ![72, 72, 72]
  | s3 => ![48, 54, 60]
  | s4 => ![60, 60, 60]
  | s5 => ![48, 60, 72]

open Examples in
/-- The row of a scenario. -/
def Scenario.row : Scenario → Datum
  | s1 => T1S1
  | s2 => T1S2
  | s3 => T1S3
  | s4 => T1S4
  | s5 => T1S5

/-- The MP equative *The linguists are as tall as 5ft* with both implicatures, (84a), (84b) and
(84c). -/
def Acceptable (s : Scenario) : Prop :=
  Strengthened (Det.some univ) s.heights 60 ∧ ¬ every univ {i | 60 ≤ s.heights i}

theorem acceptable_iff (s : Scenario) :
    Acceptable s ↔
      (∃ i, 60 ≤ s.heights i) ∧ (¬ ∃ i, 60 < s.heights i) ∧ ¬ ∀ i, 60 ≤ s.heights i := by
  simp only [Acceptable, Strengthened, lowScope_some_iff, mem_univ, true_and, Comparison.rel_ge,
    Comparison.rel_gt, and_assoc]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
    not_congr ⟨fun h i ↦ h (mem_univ i), fun h i _ ↦ h i⟩

/-- Table 1: the equative is acceptable with its implicatures only in the scenario with a range
that tops out at the standard. -/
theorem acceptable_iff_judgment (s : Scenario) : Acceptable s ↔ s.row.judgment = .acceptable := by
  rw [acceptable_iff]
  cases s <;> decide

-- The rows of Table 1: (84a), (84b) and (84c), which differs from the printed row at S1.
theorem exists_ge_iff (s : Scenario) : (∃ i, 60 ≤ s.heights i) ↔ s ≠ s1 := by
  cases s <;> decide

theorem not_exists_gt_iff (s : Scenario) : (¬ ∃ i, 60 < s.heights i) ↔ s ≠ s2 ∧ s ≠ s5 := by
  cases s <;> decide

theorem not_forall_ge_iff (s : Scenario) : (¬ ∀ i, 60 ≤ s.heights i) ↔ s ≠ s2 ∧ s ≠ s4 := by
  cases s <;> decide

-- The printed row is whether the linguists differ in height.
theorem exists_ne_iff (s : Scenario) : (∃ i j, s.heights i ≠ s.heights j) ↔ s = s3 ∨ s = s5 := by
  cases s <;> decide

/-! ### Continuations -/

/-- A continuation of an equative: the value it gives a correlate, the standard and the row. -/
structure Continuation where
  value : ℕ
  standard : ℕ
  row : Datum

open Examples

-- (3), (13): a clausal or DP equative is `≥`, its Q-implicature cancelable. (13) prints only the
-- direction of the difference, so any two values in that order serve.
theorem clausal_iff :
    ∀ c ∈ [Continuation.mk 15 10 ex_3a, ⟨10, 15, ex_3b⟩, ⟨2, 1, ex_13a⟩, ⟨1, 2, ex_13b⟩],
      MaxIn (Comparison.ge.interval c.standard) (Iic c.value) ↔
        c.row.judgment = .acceptable := by
  simp only [maxIn_Iic]
  decide

-- (5): an MPE over a range allows values up to its standard.
theorem range_iff :
    ∀ c ∈ [Continuation.mk 25 20 ex_5a, ⟨15, 20, ex_5b⟩],
      (∃ μ : Bool → ℕ, Strengthened (Det.some univ) μ c.standard ∧ μ false = c.value) ↔
        c.row.judgment = .acceptable := by
  simp only [exists_strengthened_iff]
  decide

-- (81): an MPE over a singular correlate allows only its standard, in inches.
theorem singular_iff :
    ∀ c ∈ [Continuation.mk 76 75 ex_81a, ⟨74, 75, ex_81b⟩],
      (∃ μ : Unit → ℕ, Strengthened (Det.some {()}) μ c.standard ∧ μ () = c.value) ↔
        c.row.judgment = .acceptable := by
  simp only [exists_strengthened_singleton_iff]
  decide

/-- The correlates that the two scenarios of (11) give the speaker's dates, in inches. -/
def dates (shortest : ℕ) : Fin 2 → ℕ := ![shortest, 70]

-- (11): *as short as 5′4″* needs a date of exactly that height.
theorem as_short_as_iff_judgment :
    (Strengthened (Det.some univ) (toDual ∘ dates 64) (toDual 64) ↔
        ex_11.judgment = .acceptable) ∧
      (Strengthened (Det.some univ) (toDual ∘ dates 66) (toDual 64) ↔
        ex_11_odd.judgment = .acceptable) := by
  simp only [as_short_as_iff, mem_maxOnScale_lt]
  refine ⟨⟨fun _ ↦ by decide, fun _ ↦ ⟨⟨0, trivial, rfl⟩, ?_⟩⟩,
    ⟨fun ⟨⟨i, _, hi⟩, _⟩ ↦ ?_, fun h ↦ absurd h (by decide)⟩⟩
  · rintro _ ⟨i, -, rfl⟩
    fin_cases i <;> simp [dates]
  · fin_cases i <;> simp [dates] at hi

/-! ### The modifiers -/

section Modifiers

open English.NumeralModifiers

attribute [local simp] asManyAs upTo moreThan under

-- (110): the exact amount verifies the Class B modifiers.
theorem classB_inclusive : ∀ w ∈ [asManyAs, upTo], w.modifierClass = some .classB ∧
    ∀ m ∈ ⟦w⟧, ∀ n, n ∈ m {n} := by
  simp [Numerals.NumeralModifier.modifierClass, Numerals.ModifierKind.modifierClass]

-- (109): the exact amount does not verify the Class A modifiers.
theorem classA_exclusive : ∀ w ∈ [moreThan, under], w.modifierClass = some .classA ∧
    ∀ m ∈ ⟦w⟧, ∀ n, n ∉ m {n} := by
  simp [Numerals.NumeralModifier.modifierClass, Numerals.ModifierKind.modifierClass]

end Modifiers

end Rett2015a
