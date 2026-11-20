module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.Hom.CompleteLattice
public import Linglib.Core.Order.UpperLower.Closure
public import Linglib.Core.Order.StrictBounds
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Core.Order.AntiAdditive
public import Mathlib.Order.Completion

/-!
# Degree quantifiers

A degree phrase says that the maximum of its degree predicate lies in an interval, `Quantifier.MaxIn
U X`. Under a quantifier `Q` it scopes low, applied to each entity's own degree property, or high,
applied to `Quantifier.scopeDegrees Q P`, the degrees at which `Q` holds. Over a monotone quantifier
on a finite domain, [a degree quantifier at an upper set takes scope without truth-conditional
effect](##Quantifier.highScope_maxIn_iff_lowScope); under an antitone one [the degree set has no
maximum](##Quantifier.not_isGreatest_scopeDegrees). The exact degree quantifier over `every` [names
the infimum of the measures](##Quantifier.highScope_maxIn_singleton_every) and over `some` [their
greatest](##Quantifier.highScope_maxIn_singleton_some). The max-quantified comparative
`MaxComparative c S T` relates the degrees `S` of a than-clause to the degrees `T` of a matrix
clause: `S` has a greatest degree, and some degree of `T` stands in `c` to it. On a linear scale
the strict comparative is `<` in the Dedekind–MacNeille completion of the scale, between the
principal cut of the greatest degree of `S` and the cut that `T` generates,
`maxComparative_gt_iff_principal_lt`, and every comparison of two degrees is the comparison of
their principal cuts, `Comparison.rel_principal`.

## Implementation notes

A measured degree property `Iic (μ x)` is a principal lower set and contains the bottom degree;
the structural lemmas ask only that each degree property be a lower set. For a count, the
cardinalities of the pluralities a numeral ranges over, `Iic` is pluralization with the empty sum
(`Mereology.card_image_fullAlgClosure`); Link's pluralization, without it, gives `Icc 1 n`
(`Mereology.card_image_algClosure`), and a collective predicate need give no lower set.

## References

* [heim-2001]
* [von-stechow-1984]
* [rullmann-1995]
* [hoeksema-1983]
* [bhatt-pancheva-2004]
-/

@[expose] public section

open Quantifier.Det Set

variable {α D : Type*}

namespace Quantifier

/-! ### Degree quantifiers and their scope

An entity's degree property is the set of degrees at which the scope holds of it, the degree
predicate `λd. φ(d)(x)`; for a measure `μ` it is `Iic ∘ μ`, the degrees the entity reaches. -/

section Scope
variable {Q : Quantifier α} {P : α → Set D} {d : D}

/-- The degrees at which `Q` holds of the entities whose degree property contains them, the
degree predicate abstracted over the scope of `Q`. -/
def scopeDegrees (Q : Quantifier α) (P : α → Set D) : Set D := {d | Q {x | d ∈ P x}}

theorem mem_scopeDegrees : d ∈ scopeDegrees Q P ↔ Q {x | d ∈ P x} := Iff.rfl

/-- A degree quantifier `𝒟` scoping under `Q`, applied to each entity's own degree property. -/
def LowScope (𝒟 : Quantifier D) (Q : Quantifier α) (P : α → Set D) : Prop :=
  Q {x | 𝒟 (P x)}

/-- A degree quantifier `𝒟` scoping over `Q`. -/
def HighScope (𝒟 : Quantifier D) (Q : Quantifier α) (P : α → Set D) : Prop :=
  𝒟 (scopeDegrees Q P)

theorem scopeDegrees_some (R : Set α) (P : α → Set D) :
    scopeDegrees (Det.some R) P = ⋃ x ∈ R, P x := by
  ext
  simp [mem_scopeDegrees, Det.some, Set.Nonempty]

theorem scopeDegrees_every (R : Set α) (P : α → Set D) :
    scopeDegrees (every R) P = ⋂ x ∈ R, P x := by
  ext
  simp [mem_scopeDegrees, every, Set.subset_def]

theorem scopeDegrees_no (R : Set α) (P : α → Set D) :
    scopeDegrees (no R) P = (scopeDegrees (Det.some R) P)ᶜ :=
  Set.ext fun _ ↦ no_iff_not_some

end Scope

section Preorder
variable [Preorder D] {Q : Quantifier α} {P : α → Set D} {μ : α → D} {d : D}

/-- The greatest element of `P` lies in `U`. These are the degree quantifiers of [heim-2001],
*-er than `t`* at `U = Ioi t`, *less than `t`* at `Iio t`, *exactly `δ` -er than `t`* at
`{t + δ}`, and the equative at `Ici t`. -/
def MaxIn (U X : Set D) : Prop := ∃ m ∈ U, IsGreatest X m

theorem maxIn_singleton {X : Set D} {a : D} : MaxIn {a} X ↔ IsGreatest X a := exists_eq_left

/-- At an upper set, the greatest degree of a set lies in it exactly when some degree of the set
does: the positive form of a degree property at a standard. -/
theorem maxIn_iff_inter_nonempty {U X : Set D} {m : D} (hU : IsUpperSet U) (h : IsGreatest X m) :
    MaxIn U X ↔ (X ∩ U).Nonempty :=
  ⟨fun ⟨n, hn, hg⟩ ↦ ⟨n, hg.1, hn⟩, fun ⟨_, hd, hdU⟩ ↦ ⟨m, hU (h.2 hd) hdU, h⟩⟩

theorem scopeDegrees_some_Iic (R : Set α) (μ : α → D) :
    scopeDegrees (Det.some R) (Iic ∘ μ) = lowerClosure (μ '' R) := by
  ext d
  simp [mem_scopeDegrees, Det.some, mem_lowerClosure, Set.Nonempty]

theorem scopeDegrees_every_Iic (R : Set α) (μ : α → D) :
    scopeDegrees (every R) (Iic ∘ μ) = lowerBounds (μ '' R) := by
  ext d
  exact (mem_lowerBounds.trans forall_mem_image).symm

theorem isLowerSet_scopeDegrees (hQ : Monotone Q) (hP : ∀ x, IsLowerSet (P x)) :
    IsLowerSet (scopeDegrees Q P) :=
  fun _ _ h hd ↦ hQ (fun x hx ↦ hP x h hx) hd

theorem isUpperSet_scopeDegrees (hQ : Antitone Q) (hP : ∀ x, IsLowerSet (P x)) :
    IsUpperSet (scopeDegrees Q P) :=
  fun _ _ h hd ↦ hQ (fun x hx ↦ hP x h hx) hd

/-- Under an antitone quantifier, negation, *at most n* or *refuse*, the degree set has no
maximum on a scale without a top, so the high-scope reading is a presupposition failure. -/
theorem not_isGreatest_scopeDegrees [NoMaxOrder D] (hQ : Antitone Q)
    (hP : ∀ x, IsLowerSet (P x)) : ¬ ∃ m, IsGreatest (scopeDegrees Q P) m :=
  fun ⟨_, hm⟩ ↦ (isUpperSet_scopeDegrees hQ hP).not_bddAbove ⟨_, hm.1⟩ hm.bddAbove

theorem scopeDegrees_eq_Iic (hQ : Monotone Q) (hP : ∀ x, IsLowerSet (P x)) {m : D}
    (hm : IsGreatest (scopeDegrees Q P) m) : scopeDegrees Q P = Iic m :=
  (mem_upperBounds_iff_subset_Iic.1 hm.2).antisymm
    ((isLowerSet_scopeDegrees hQ hP).Iic_subset hm.1)

end Preorder

section PartialOrder
variable [PartialOrder D] {U P : Set D} {Q : Quantifier α} {μ : α → D}

theorem maxIn_Iic {a : D} : MaxIn U (Iic a) ↔ a ∈ U :=
  ⟨fun ⟨_, hm, h⟩ ↦ h.unique isGreatest_Iic ▸ hm, fun h ↦ ⟨a, h, isGreatest_Iic⟩⟩

theorem maxIn_compl : MaxIn Uᶜ P ↔ (∃ m, IsGreatest P m) ∧ ¬ MaxIn U P :=
  ⟨fun ⟨m, hm, h⟩ ↦ ⟨⟨m, h⟩, fun ⟨_, hm', h'⟩ ↦ hm (h'.unique h ▸ hm')⟩,
    fun ⟨⟨m, h⟩, hn⟩ ↦ ⟨m, fun hm ↦ hn ⟨m, hm, h⟩, h⟩⟩

theorem lowScope_maxIn : LowScope (MaxIn U) Q (Iic ∘ μ) ↔ Q {x | μ x ∈ U} := by
  simp only [LowScope, Function.comp_apply, maxIn_Iic]

theorem lowScope_of_highScope (hQ : Monotone Q) (hU : IsUpperSet U)
    (h : HighScope (MaxIn U) Q (Iic ∘ μ)) : LowScope (MaxIn U) Q (Iic ∘ μ) :=
  let ⟨_, hmU, hm⟩ := h; lowScope_maxIn.2 (hQ (fun _ hx ↦ hU hx hmU) hm.1)

theorem highScope_every_of_lowScope {R : Set α} (hR : ∃ x ∈ R, ∀ y ∈ R, μ x ≤ μ y)
    (h : LowScope (MaxIn U) (every R) (Iic ∘ μ)) : HighScope (MaxIn U) (every R) (Iic ∘ μ) := by
  rw [lowScope_maxIn] at h
  obtain ⟨x₀, hx₀, hmin⟩ := hR
  exact ⟨μ x₀, h hx₀, fun y hy ↦ hmin y hy, fun _ hd ↦ hd hx₀⟩

/-- Over `every R` the greatest degree every `R`-witness reaches is the infimum of their measures.
-/
theorem highScope_maxIn_singleton_every {R : Set α} {m : D} :
    HighScope (MaxIn {m}) (every R) (Iic ∘ μ) ↔ IsGLB (μ '' R) m := by
  rw [HighScope, maxIn_singleton, scopeDegrees_every_Iic]; rfl

/-- Over `some R` the greatest degree some `R`-witness reaches is the greatest of their measures. -/
theorem highScope_maxIn_singleton_some {R : Set α} {m : D} :
    HighScope (MaxIn {m}) (Det.some R) (Iic ∘ μ) ↔ IsGreatest (μ '' R) m := by
  rw [HighScope, maxIn_singleton, scopeDegrees_some_Iic, isGreatest_lowerClosure_iff]

theorem lowScope_some_of_highScope {R : Set α}
    (h : HighScope (MaxIn U) (Det.some R) (Iic ∘ μ)) :
    LowScope (MaxIn U) (Det.some R) (Iic ∘ μ) := by
  obtain ⟨m, hmU, ⟨x, hx, hmx⟩, hub⟩ := h
  exact lowScope_maxIn.2 ⟨x, hx, show μ x ∈ U from hmx.antisymm (hub ⟨x, hx, le_rfl⟩) ▸ hmU⟩

end PartialOrder

section LinearOrder
variable [LinearOrder D] {U : Set D} {Q Q' : Quantifier α} {μ : α → D}

theorem exists_isGreatest_scopeDegrees [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (h : (scopeDegrees Q (Iic ∘ μ)).Nonempty) :
    ∃ x, IsGreatest (scopeDegrees Q (Iic ∘ μ)) (μ x) := by
  -- every degree of the set lies below a measured degree of the set
  have step : ∀ d ∈ scopeDegrees Q (Iic ∘ μ), ∃ x, d ≤ μ x ∧ μ x ∈ scopeDegrees Q (Iic ∘ μ) := by
    intro d hd
    have : Nonempty {x // d ≤ μ x} :=
      not_isEmpty_iff.1 fun h ↦ hQ₀ (hQ (fun x hx ↦ h.false ⟨x, hx⟩) hd)
    obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min fun x : {x // d ≤ μ x} ↦ μ x.1
    exact ⟨x₀, hx₀, hQ (fun x hx ↦ hmin ⟨x, hx⟩) hd⟩
  obtain ⟨d, hd⟩ := h
  obtain ⟨x₀, -, hx₀⟩ := step d hd
  have : Nonempty {x // μ x ∈ scopeDegrees Q (Iic ∘ μ)} := ⟨⟨x₀, hx₀⟩⟩
  obtain ⟨⟨m, hm⟩, hmax⟩ := Finite.exists_max fun x : {x // μ x ∈ scopeDegrees Q (Iic ∘ μ)} ↦ μ x.1
  refine ⟨m, hm, fun d hd ↦ ?_⟩
  obtain ⟨y, hdy, hy⟩ := step d hd
  exact hdy.trans (hmax ⟨y, hy⟩)

theorem highScope_of_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥) (hU : IsUpperSet U)
    (h : LowScope (MaxIn U) Q (Iic ∘ μ)) : HighScope (MaxIn U) Q (Iic ∘ μ) := by
  rw [lowScope_maxIn] at h
  have : Nonempty {x // μ x ∈ U} :=
    not_isEmpty_iff.1 fun h' ↦ hQ₀ (hQ (fun x hx ↦ h'.false ⟨x, hx⟩) h)
  obtain ⟨⟨x₀, hx₀⟩, hmin⟩ := Finite.exists_min fun x : {x // μ x ∈ U} ↦ μ x.1
  have hd₀ : μ x₀ ∈ scopeDegrees Q (Iic ∘ μ) := hQ (fun x hx ↦ hmin ⟨x, hx⟩) h
  obtain ⟨m, hm⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ ⟨_, hd₀⟩
  exact ⟨μ m, hU (hm.2 hd₀) hx₀, hm⟩

/-- Over a monotone quantifier on a finite domain, a degree quantifier at an upper set,
comparative or equative, takes scope without truth-conditional effect. -/
theorem highScope_maxIn_iff_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hU : IsUpperSet U) : HighScope (MaxIn U) Q (Iic ∘ μ) ↔ LowScope (MaxIn U) Q (Iic ∘ μ) :=
  ⟨lowScope_of_highScope hQ hU, highScope_of_lowScope hQ hQ₀ hU⟩

theorem highScope_maxIn_Iio_iff [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hne : (scopeDegrees Q (Iic ∘ μ)).Nonempty) {t : D} :
    HighScope (MaxIn (Iio t)) Q (Iic ∘ μ) ↔ ¬ Q {x | t ≤ μ x} := by
  have h := highScope_maxIn_iff_lowScope (μ := μ) hQ hQ₀ (IsUpperSet.Ici t)
  simp only [lowScope_maxIn, mem_Ici] at h
  rw [← compl_Ici, ← h]
  obtain ⟨x, hx⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ hne
  exact maxIn_compl.trans (and_iff_right ⟨_, hx⟩)

/-- Under the meet of a quantifier with an antitone one, *exactly n* as *at least n* and *at
most n*, the maximum of the degree set, when defined, is that of the other conjunct, so
high-scope *exactly two girls are taller than t* means *at least two*. -/
theorem isGreatest_scopeDegrees_of_inf {P : α → Set D} (hQ' : Antitone Q')
    (hP : ∀ x, IsLowerSet (P x)) {m : D} (h : IsGreatest (scopeDegrees (Q ⊓ Q') P) m) :
    IsGreatest (scopeDegrees Q P) m :=
  ⟨h.1.1, fun _ hd ↦ le_of_not_gt fun hmd ↦
    (h.2 ⟨hd, hQ' (fun x hx ↦ hP x hmd.le hx) h.1.2⟩).not_gt hmd⟩

theorem isGLB_compl_scopeDegrees [DenselyOrdered D] {P : α → Set D} (hQ : Monotone Q)
    (hP : ∀ x, IsLowerSet (P x)) {m : D} (hm : IsGreatest (scopeDegrees Q P) m) :
    IsGLB (scopeDegrees Q P)ᶜ m := by
  rw [scopeDegrees_eq_Iic hQ hP hm, compl_Iic]
  exact isGLB_Ioi

theorem isGLB_compl_scopeDegrees_iff [DenselyOrdered D] {P : α → Set D} (hQ : Monotone Q)
    (hP : ∀ x, IsLowerSet (P x)) {m : D} (h : ∃ m, IsGreatest (scopeDegrees Q P) m) :
    IsGLB (scopeDegrees Q P)ᶜ m ↔ IsGreatest (scopeDegrees Q P) m :=
  let ⟨_, hm'⟩ := h
  ⟨fun hg ↦ hg.unique (isGLB_compl_scopeDegrees hQ hP hm') ▸ hm', isGLB_compl_scopeDegrees hQ hP⟩

end LinearOrder

end Quantifier

/-! ### The max-quantified comparative

The clausal comparative of von Stechow and Rullmann relates the degrees `S` of the than-clause to
the degrees `T` of the matrix clause: `S` has a greatest degree, and some degree of `T` stands in
a comparison to it, *more* at `.gt` and *as* at `.ge`. At these it says that `S` has a greatest
degree and that some degree of `T` bounds `S`, strictly or weakly. When `T` has a greatest degree
it is `Quantifier.MaxIn` of the than-clause, and between lower sets it is inclusion. The matrix
degree is existential, so at `.le` and `.lt` the relation does not compare greatest degrees; a
downward comparison of a degree property is `Quantifier.MaxIn` at a lower interval. -/

section MaxComparative
variable [Preorder D] {c c' : Comparison} {R S T : Set D} {a b : D}

/-- The max-quantified comparative under the comparison `c` holds of the than-clause degrees `S`
and the matrix degrees `T` when `S` has a greatest degree `δ` and some degree of `T` stands in
`c` to `δ`. -/
def MaxComparative (c : Comparison) (S T : Set D) : Prop :=
  ∃ δ, IsGreatest S δ ∧ (T ∩ c.interval δ).Nonempty

/-- A max-quantified comparative entails the comparatives with weaker comparisons, the equative
from the strict comparative in particular. -/
theorem MaxComparative.mono (hc : ∀ a b : D, c.Rel a b → c'.Rel a b)
    (h : MaxComparative c S T) : MaxComparative c' S T :=
  let ⟨δ, hδ, d, hd, hr⟩ := h
  ⟨δ, hδ, d, hd, hc _ _ hr⟩

/-- The strict comparative holds when the than-clause has a greatest degree and some matrix
degree lies strictly above every degree of the than-clause. -/
theorem maxComparative_gt_iff :
    MaxComparative .gt S T ↔ (∃ δ, IsGreatest S δ) ∧ (T ∩ strictUpperBounds S).Nonempty :=
  ⟨fun ⟨δ, hδ, h⟩ ↦ ⟨⟨δ, hδ⟩, by rwa [hδ.strictUpperBounds_eq]⟩,
    fun ⟨⟨δ, hδ⟩, h⟩ ↦ ⟨δ, hδ, by rwa [hδ.strictUpperBounds_eq] at h⟩⟩

/-- The equative holds when the than-clause has a greatest degree and some matrix degree is an
upper bound of the than-clause. -/
theorem maxComparative_ge_iff :
    MaxComparative .ge S T ↔ (∃ δ, IsGreatest S δ) ∧ (T ∩ upperBounds S).Nonempty :=
  ⟨fun ⟨δ, hδ, h⟩ ↦ ⟨⟨δ, hδ⟩, by rwa [hδ.upperBounds_eq]⟩,
    fun ⟨⟨δ, hδ⟩, h⟩ ↦ ⟨δ, hδ, by rwa [hδ.upperBounds_eq] at h⟩⟩

theorem MaxComparative.exists_lt (h : MaxComparative .gt S T) (ha : a ∈ S) : ∃ d ∈ T, a < d :=
  let ⟨_, hδ, d, hd, hlt⟩ := h
  ⟨d, hd, (hδ.2 ha).trans_lt hlt⟩

/-- The max-quantified comparative is transitive, so *more P than Q* and *more Q than R* give
*more P than R* with no uniqueness assumption on any of the three sides. -/
theorem MaxComparative.trans (h₁ : MaxComparative .gt S T) (h₂ : MaxComparative .gt R S) :
    MaxComparative .gt R T :=
  let ⟨δ, hδ, _, hd, hlt⟩ := h₂
  let ⟨e, he, hlt'⟩ := h₁.exists_lt hd
  ⟨δ, hδ, e, he, hlt.trans hlt'⟩

@[simp]
theorem maxComparative_singleton : MaxComparative c {b} {a} ↔ c.Rel a b :=
  ⟨fun ⟨_, hδ, _, hd, hr⟩ ↦ mem_singleton_iff.1 hδ.1 ▸ mem_singleton_iff.1 hd ▸ hr,
    fun h ↦ ⟨b, isGreatest_singleton, a, rfl, h⟩⟩

/-- Under unique matrix and than-clause witnesses, the max-quantified comparative compares their
measures directly. -/
theorem maxComparative_image_iff_of_unique {μ : α → D} {P Q : Set α} {xa xb : α} (ha : xa ∈ P)
    (ha' : ∀ x ∈ P, x = xa) (hb : xb ∈ Q) (hb' : ∀ x ∈ Q, x = xb) :
    MaxComparative c (μ '' Q) (μ '' P) ↔ c.Rel (μ xa) (μ xb) := by
  rw [eq_singleton_iff_unique_mem.2 ⟨ha, ha'⟩, eq_singleton_iff_unique_mem.2 ⟨hb, hb'⟩,
    image_singleton, image_singleton, maxComparative_singleton]

/-- When the matrix degrees have a greatest degree `a`, the equative says that the greatest
than-clause degree is at most `a`. -/
theorem maxComparative_ge_iff_maxIn (hT : IsGreatest T a) :
    MaxComparative .ge S T ↔ Quantifier.MaxIn (Iic a) S :=
  ⟨fun ⟨δ, hδ, _, hd, hle⟩ ↦ ⟨δ, hle.trans (hT.2 hd), hδ⟩,
    fun ⟨δ, hle, hδ⟩ ↦ ⟨δ, hδ, a, hT.1, hle⟩⟩

/-- When the matrix degrees have a greatest degree `a`, the strict comparative says that the
greatest than-clause degree is below `a`. -/
theorem maxComparative_gt_iff_maxIn (hT : IsGreatest T a) :
    MaxComparative .gt S T ↔ Quantifier.MaxIn (Iio a) S :=
  ⟨fun ⟨δ, hδ, _, hd, hlt⟩ ↦ ⟨δ, lt_of_lt_of_le hlt (hT.2 hd), hδ⟩,
    fun ⟨δ, hlt, hδ⟩ ↦ ⟨δ, hδ, a, hT.1, hlt⟩⟩

/-- Into a lower set of matrix degrees, the equative is inclusion of a than-clause that has a
greatest degree. -/
theorem maxComparative_ge_iff_subset (hT : IsLowerSet T) :
    MaxComparative .ge S T ↔ (∃ δ, IsGreatest S δ) ∧ S ⊆ T :=
  ⟨fun ⟨δ, hδ, _, hd, hle⟩ ↦ ⟨⟨δ, hδ⟩, fun _ hs ↦ hT ((hδ.2 hs).trans hle) hd⟩,
    fun ⟨⟨δ, hδ⟩, h⟩ ↦ ⟨δ, hδ, δ, h hδ.1, le_rfl⟩⟩

theorem maxComparative_gt_image_iff_of_isGreatest [Preorder α] {μ : α → D} {P Q : Set α}
    {xa xb : α} (ha : IsGreatest P xa) (hμa : MonotoneOn μ P) (hb : IsGreatest Q xb)
    (hμb : MonotoneOn μ Q) : MaxComparative .gt (μ '' Q) (μ '' P) ↔ μ xb < μ xa :=
  (maxComparative_gt_iff_maxIn (hμa.map_isGreatest ha)).trans
    ⟨fun ⟨_, hm, hg⟩ ↦ (hg.2 ⟨xb, hb.1, rfl⟩).trans_lt hm,
      fun h ↦ ⟨_, h, hμb.map_isGreatest hb⟩⟩

end MaxComparative

section MaxComparativePartialOrder
variable [PartialOrder D] {S T : Set D} {a b : D}

@[simp]
theorem maxComparative_ge_Iic_Iic : MaxComparative .ge (Iic b) (Iic a) ↔ b ≤ a := by
  rw [maxComparative_ge_iff_maxIn isGreatest_Iic, Quantifier.maxIn_Iic, mem_Iic]

@[simp]
theorem maxComparative_gt_Iic_Iic : MaxComparative .gt (Iic b) (Iic a) ↔ b < a := by
  rw [maxComparative_gt_iff_maxIn isGreatest_Iic, Quantifier.maxIn_Iic, mem_Iio]

theorem MaxComparative.antisymm (ha : IsGreatest S a) (hb : IsGreatest T b)
    (h₁ : MaxComparative .ge S T) (h₂ : MaxComparative .ge T S) : a = b :=
  let ⟨_, hle, hm⟩ := (maxComparative_ge_iff_maxIn hb).1 h₁
  let ⟨_, hle', hm'⟩ := (maxComparative_ge_iff_maxIn ha).1 h₂
  (hm.unique ha ▸ hle : a ≤ b).antisymm (hm'.unique hb ▸ hle')

end MaxComparativePartialOrder

section MaxComparativeLinearOrder
variable [LinearOrder D] {S T : Set D} {a b : D}

theorem maxComparative_ge_total (ha : IsGreatest S a) (hb : IsGreatest T b) :
    MaxComparative .ge S T ∨ MaxComparative .ge T S :=
  (le_total a b).imp (fun h ↦ ⟨a, ha, b, hb.1, h⟩) fun h ↦ ⟨b, hb, a, ha.1, h⟩

theorem maxComparative_gt_trichotomy (ha : IsGreatest S a) (hb : IsGreatest T b) :
    MaxComparative .gt S T ∨ a = b ∨ MaxComparative .gt T S :=
  (lt_trichotomy a b).imp (fun h ↦ ⟨a, ha, b, hb.1, h⟩) <|
    Or.imp_right fun h ↦ ⟨b, hb, a, ha.1, h⟩

/-- Between lower sets, the strict comparative is strict inclusion of a than-clause that has a
greatest degree. -/
theorem maxComparative_gt_iff_ssubset (hS : IsLowerSet S) (hT : IsLowerSet T) :
    MaxComparative .gt S T ↔ (∃ δ, IsGreatest S δ) ∧ S ⊂ T := by
  refine ⟨fun ⟨δ, hδ, d, hd, hlt⟩ ↦ ⟨⟨δ, hδ⟩, fun _ hs ↦ hT ((hδ.2 hs).trans hlt.le) hd,
    fun h ↦ (hδ.2 (h hd)).not_gt hlt⟩, fun ⟨⟨δ, hδ⟩, h⟩ ↦ ?_⟩
  obtain ⟨d, hd, hdS⟩ := not_subset.1 h.2
  exact ⟨δ, hδ, d, hd, lt_of_not_ge fun hle ↦ hdS (hS hle hδ.1)⟩

end MaxComparativeLinearOrder

/-! ### Set-of-degrees comparative

The S-comparative of [hoeksema-1983] generalizes the point-standard comparative from a single
standard to a degree-set standard. Its extension is `μ ⁻¹' strictUpperBounds Δ`, the entities
measuring above every standard degree, and the binary comparator is its singleton case
(`strictUpperBounds_singleton`). It is the strict max-quantified comparative without the
requirement that the standard have a greatest degree (`maxComparative_gt_iff`). -/

section SetOfDegrees
variable [Preorder D] (μ : α → D) {Δ : Set D}

theorem mem_gtOverSet_iff_subset_Iio (y : α) : y ∈ μ ⁻¹' strictUpperBounds Δ ↔ Δ ⊆ Iio (μ y) :=
  Iff.rfl

theorem gtOverSet_isAntiAdditive : IsAntiAdditive (μ ⁻¹' strictUpperBounds ·) :=
  (isAntiAdditive_upperPolar (· < ·)).infHom_comp (CompleteLatticeHom.setPreimage μ)

theorem gtOverSet_eq_singleton_of_isGreatest {m : D} (hm : IsGreatest Δ m) :
    μ ⁻¹' strictUpperBounds Δ = μ ⁻¹' strictUpperBounds {m} := by
  ext y
  simp only [mem_gtOverSet_iff_subset_Iio, singleton_subset_iff, mem_Iio]
  exact ⟨(· hm.1), fun h _ hd ↦ (hm.2 hd).trans_lt h⟩

end SetOfDegrees

/-! ### Comparison in the completion

A set of degrees generates a cut of the scale, `Concept.ofObjects (· ≤ ·) S`, its least upper
bound in the Dedekind–MacNeille completion, and a set with a greatest degree generates the
principal cut of that degree. Comparing two degrees is comparing their principal cuts, along
`DedekindCut.principalEmbedding`, and the strict comparative compares the greatest than-clause
degree with the cut of the matrix degrees. -/

section Cut
open DedekindCut

theorem DedekindCut.ofObjects_eq_principal [PartialOrder D] {S : Set D} {δ : D}
    (h : IsGreatest S δ) : Concept.ofObjects (· ≤ ·) S = principal δ :=
  DedekindCut.ext' <| Set.ext fun _ ↦ ⟨fun hx ↦ hx h.1, fun hx _ hs ↦ (h.2 hs).trans hx⟩

theorem Comparison.rel_principal [PartialOrder D] (c : Comparison) {a b : D} :
    c.Rel (principal a) (principal b) ↔ c.Rel a b :=
  Comparison.rel_map_iff principalEmbedding c

variable [LinearOrder D] {S T : Set D} {a b : D}

/-- On a linear scale the strict comparative holds when the principal cut of the greatest
than-clause degree lies strictly below the cut the matrix degrees generate. -/
theorem maxComparative_gt_iff_principal_lt :
    MaxComparative .gt S T ↔
      ∃ δ, IsGreatest S δ ∧ principal δ < Concept.ofObjects (· ≤ ·) T := by
  refine exists_congr fun δ ↦ and_congr_right fun _ ↦ Iff.trans ?_ principal_lt_iff.symm
  exact ⟨fun ⟨t, ht, hlt⟩ ↦ ⟨t, fun _ hu ↦ hu ht, hlt⟩, fun ⟨_, hb, hlt⟩ ↦ by_contra fun hn ↦
    (hb (b := δ) fun t ht ↦ le_of_not_gt fun h ↦ hn ⟨t, ht, h⟩).not_gt hlt⟩

/-- When both sets have a greatest degree, the equative is `≤` of the cuts they generate. -/
theorem maxComparative_ge_iff_ofObjects_le (hS : IsGreatest S b) (hT : IsGreatest T a) :
    MaxComparative .ge S T ↔
      Concept.ofObjects (· ≤ ·) S ≤ Concept.ofObjects (· ≤ ·) T := by
  rw [ofObjects_eq_principal hS, ofObjects_eq_principal hT, principal_le_principal,
    maxComparative_ge_iff_maxIn hT]
  exact ⟨fun ⟨_, hm, h⟩ ↦ h.unique hS ▸ hm, fun h ↦ ⟨b, h, hS⟩⟩

/-- When both sets have a greatest degree, the strict comparative is `<` of the cuts they
generate. -/
theorem maxComparative_gt_iff_ofObjects_lt (hS : IsGreatest S b) (hT : IsGreatest T a) :
    MaxComparative .gt S T ↔
      Concept.ofObjects (· ≤ ·) S < Concept.ofObjects (· ≤ ·) T := by
  rw [ofObjects_eq_principal hS, ofObjects_eq_principal hT, principal_lt_principal,
    maxComparative_gt_iff_maxIn hT]
  exact ⟨fun ⟨_, hm, h⟩ ↦ h.unique hS ▸ hm, fun h ↦ ⟨b, h, hS⟩⟩

end Cut
