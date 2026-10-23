module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Order.Interval.Set.LinearOrder
public import Linglib.Core.Order.UpperLower.Closure
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Logic.Natural.Additivity

/-!
# Degree quantifiers

This file defines the denotations of degree phrases as quantifiers over degrees and their scope
relative to a quantifier over entities or worlds. A degree phrase says that the maximum of its
degree predicate lies in an interval, `MaxIn U X`; under a quantifier `Q` it scopes low, applied
to each entity's own degree property, or high, applied to `scopeDegrees Q P`, the degrees at which
`Q` holds. A measure `μ` gives each entity the degrees it reaches, `Iic ∘ μ`, and under `some` the
degree set is then the lower closure of the measures, the than-clause degree set. The
max-quantified comparative `MaxComparative c` compares a matrix witness with its greatest measure
by the comparison `c`.

## Main definitions

* `MaxIn U X`: the greatest element of `X` lies in `U`.
* `scopeDegrees Q P`: the degrees `d` such that `Q` holds of the entities `x` with `d ∈ P x`.
* `LowScope 𝒟 Q P`, `HighScope 𝒟 Q P`: the degree quantifier `𝒟` under and over `Q`.
* `MaxComparative c P Q μ`: the max-quantified comparative, the equative at `c = .ge`.
* `AbsoluteSuperlative μ C x`: `x` measures above every other member of `C`.

## Main results

* `highScope_maxIn_iff_lowScope`: over a monotone quantifier on a finite domain, a degree
  quantifier at an upper set takes scope without truth-conditional effect.
* `not_isGreatest_scopeDegrees`: under an antitone quantifier the degree set has no maximum.
* `highScope_maxIn_singleton_every`, `highScope_maxIn_singleton_some`: the exact degree
  quantifier over `every` names the infimum of the measures and over `some` their greatest.
* `isGreatest_scopeDegrees_of_inf`: under a meet with an antitone quantifier the maximum is the
  other conjunct's.
* `maxComparative_iff_of_unique`: with unique witnesses the max-quantified comparative is direct
  measure comparison.

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
* [heim-1999]
-/

@[expose] public section

namespace Degree

open NaturalLogic Quantifier Quantifier.GQ Set

variable {α D : Type*}

/-! ### Degree quantifiers and their scope

An entity's degree property is the set of degrees at which the scope holds of it, the degree
predicate `λd. φ(d)(x)`; for a measure `μ` it is `Iic ∘ μ`, the degrees the entity reaches. -/

section Scope
variable {Q : NP α} {P : α → Set D} {d : D}

/-- The degrees at which `Q` holds of the entities whose degree property contains them, the
degree predicate abstracted over the scope of `Q`. -/
def scopeDegrees (Q : NP α) (P : α → Set D) : Set D := {d | Q fun x ↦ d ∈ P x}

theorem mem_scopeDegrees : d ∈ scopeDegrees Q P ↔ Q fun x ↦ d ∈ P x := Iff.rfl

/-- A degree quantifier `𝒟` scoping under `Q`, applied to each entity's own degree property. -/
def LowScope (𝒟 : Set D → Prop) (Q : NP α) (P : α → Set D) : Prop :=
  Q fun x ↦ 𝒟 (P x)

/-- A degree quantifier `𝒟` scoping over `Q`. -/
def HighScope (𝒟 : Set D → Prop) (Q : NP α) (P : α → Set D) : Prop :=
  𝒟 (scopeDegrees Q P)

theorem scopeDegrees_some (R : α → Prop) (P : α → Set D) :
    scopeDegrees (GQ.some R) P = ⋃ (x) (_ : R x), P x := by
  ext
  simp [mem_scopeDegrees, GQ.some]

theorem scopeDegrees_every (R : α → Prop) (P : α → Set D) :
    scopeDegrees (every R) P = ⋂ (x) (_ : R x), P x := by
  ext
  simp [mem_scopeDegrees, every]

theorem scopeDegrees_no (R : α → Prop) (P : α → Set D) :
    scopeDegrees (no R) P = (scopeDegrees (GQ.some R) P)ᶜ := by
  ext
  exact (not_exists.trans (forall_congr' fun _ ↦ not_and)).symm

end Scope

section Preorder
variable [Preorder D] {Q : NP α} {P : α → Set D} {μ : α → D} {d : D}

/-- The greatest element of `P` lies in `U`. These are the degree quantifiers of [heim-2001],
*-er than `t`* at `U = Ioi t`, *less than `t`* at `Iio t`, *exactly `δ` -er than `t`* at
`{t + δ}`, and the equative at `Ici t`. -/
def MaxIn (U X : Set D) : Prop := ∃ m ∈ U, IsGreatest X m

theorem maxIn_singleton {X : Set D} {a : D} : MaxIn {a} X ↔ IsGreatest X a := exists_eq_left

theorem scopeDegrees_some_Iic (R : α → Prop) (μ : α → D) :
    scopeDegrees (GQ.some R) (Iic ∘ μ) = lowerClosure (μ '' {x | R x}) := by
  ext d
  simp [mem_scopeDegrees, GQ.some, mem_lowerClosure]

theorem scopeDegrees_every_Iic (R : α → Prop) (μ : α → D) :
    scopeDegrees (every R) (Iic ∘ μ) = lowerBounds (μ '' {x | R x}) := by
  ext d
  exact (mem_lowerBounds.trans forall_mem_image).symm

theorem isLowerSet_scopeDegrees (hQ : Monotone Q) (hP : ∀ x, IsLowerSet (P x)) :
    IsLowerSet (scopeDegrees Q P) :=
  fun _ _ h hd ↦ hQ (fun x hx ↦ hP x h hx) hd

theorem isUpperSet_scopeDegrees (hQ : Antitone Q) (hP : ∀ x, IsLowerSet (P x)) :
    IsUpperSet (scopeDegrees Q P) :=
  fun _ _ h hd ↦ hQ (fun x hx ↦ hP x h hx) hd

theorem not_isGreatest_scopeDegrees [NoMaxOrder D] (hQ : Antitone Q)
    (hP : ∀ x, IsLowerSet (P x)) : ¬ ∃ m, IsGreatest (scopeDegrees Q P) m :=
  fun ⟨_, hm⟩ ↦ (isUpperSet_scopeDegrees hQ hP).not_bddAbove ⟨_, hm.1⟩ hm.bddAbove

theorem scopeDegrees_eq_Iic (hQ : Monotone Q) (hP : ∀ x, IsLowerSet (P x)) {m : D}
    (hm : IsGreatest (scopeDegrees Q P) m) : scopeDegrees Q P = Iic m :=
  (mem_upperBounds_iff_subset_Iic.1 hm.2).antisymm
    ((isLowerSet_scopeDegrees hQ hP).Iic_subset hm.1)

end Preorder

section PartialOrder
variable [PartialOrder D] {U P : Set D} {Q : NP α} {μ : α → D}

theorem maxIn_Iic {a : D} : MaxIn U (Iic a) ↔ a ∈ U :=
  ⟨fun ⟨_, hm, h⟩ ↦ h.unique isGreatest_Iic ▸ hm, fun h ↦ ⟨a, h, isGreatest_Iic⟩⟩

theorem maxIn_compl : MaxIn Uᶜ P ↔ (∃ m, IsGreatest P m) ∧ ¬ MaxIn U P :=
  ⟨fun ⟨m, hm, h⟩ ↦ ⟨⟨m, h⟩, fun ⟨_, hm', h'⟩ ↦ hm (h'.unique h ▸ hm')⟩,
    fun ⟨⟨m, h⟩, hn⟩ ↦ ⟨m, fun hm ↦ hn ⟨m, hm, h⟩, h⟩⟩

theorem lowScope_maxIn : LowScope (MaxIn U) Q (Iic ∘ μ) ↔ Q fun x ↦ μ x ∈ U := by
  simp only [LowScope, Function.comp_apply, maxIn_Iic]

theorem lowScope_of_highScope (hQ : Monotone Q) (hU : IsUpperSet U)
    (h : HighScope (MaxIn U) Q (Iic ∘ μ)) : LowScope (MaxIn U) Q (Iic ∘ μ) :=
  let ⟨_, hmU, hm⟩ := h; lowScope_maxIn.2 (hQ (fun _ hx ↦ hU hx hmU) hm.1)

theorem highScope_every_of_lowScope {R : α → Prop} (hR : ∃ x, R x ∧ ∀ y, R y → μ x ≤ μ y)
    (h : LowScope (MaxIn U) (every R) (Iic ∘ μ)) : HighScope (MaxIn U) (every R) (Iic ∘ μ) := by
  rw [lowScope_maxIn] at h
  obtain ⟨x₀, hx₀, hmin⟩ := hR
  exact ⟨μ x₀, h x₀ hx₀, hmin, fun _ hd ↦ hd x₀ hx₀⟩

theorem highScope_maxIn_singleton_every {R : α → Prop} {m : D} :
    HighScope (MaxIn {m}) (every R) (Iic ∘ μ) ↔ IsGLB (μ '' {x | R x}) m := by
  rw [HighScope, maxIn_singleton, scopeDegrees_every_Iic]; rfl

theorem highScope_maxIn_singleton_some {R : α → Prop} {m : D} :
    HighScope (MaxIn {m}) (GQ.some R) (Iic ∘ μ) ↔ IsGreatest (μ '' {x | R x}) m := by
  rw [HighScope, maxIn_singleton, scopeDegrees_some_Iic, isGreatest_lowerClosure_iff]

theorem lowScope_some_of_highScope {R : α → Prop} (h : HighScope (MaxIn U) (GQ.some R) (Iic ∘ μ)) :
    LowScope (MaxIn U) (GQ.some R) (Iic ∘ μ) := by
  obtain ⟨m, hmU, ⟨x, hx, hmx⟩, hub⟩ := h
  exact lowScope_maxIn.2 ⟨x, hx, show μ x ∈ U from hmx.antisymm (hub ⟨x, hx, le_rfl⟩) ▸ hmU⟩

end PartialOrder

section LinearOrder
variable [LinearOrder D] {U : Set D} {Q Q' : NP α} {μ : α → D}

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

theorem highScope_maxIn_iff_lowScope [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hU : IsUpperSet U) : HighScope (MaxIn U) Q (Iic ∘ μ) ↔ LowScope (MaxIn U) Q (Iic ∘ μ) :=
  ⟨lowScope_of_highScope hQ hU, highScope_of_lowScope hQ hQ₀ hU⟩

theorem highScope_maxIn_Iio_iff [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥)
    (hne : (scopeDegrees Q (Iic ∘ μ)).Nonempty) {t : D} :
    HighScope (MaxIn (Iio t)) Q (Iic ∘ μ) ↔ ¬ Q fun x ↦ t ≤ μ x := by
  have h := highScope_maxIn_iff_lowScope (μ := μ) hQ hQ₀ (isUpperSet_Ici t)
  simp only [lowScope_maxIn, mem_Ici] at h
  rw [← compl_Ici, ← h]
  obtain ⟨x, hx⟩ := exists_isGreatest_scopeDegrees hQ hQ₀ hne
  exact maxIn_compl.trans (and_iff_right ⟨_, hx⟩)

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

/-! ### The max-quantified comparative

The clausal comparative of von Stechow and Rullmann: some matrix witness stands in a comparison to
the greatest measure of the than-clause witnesses, *more P than Q* at `.gt` and *as P as Q* at
`.ge`. Matrix and than-clause restrictions are independent predicates over a witness sort, so
heterogeneous comparatives are the general case. -/

section MaxComparative
variable [Preorder D] {c : Comparison} {P Q R : α → Prop} {μ : α → D}

/-- The max-quantified comparative under the comparison `c` holds when the measures of the
`Q`-witnesses have a greatest element `δ` and the measure of some `P`-witness stands in `c` to
`δ`. -/
def MaxComparative (c : Comparison) (P Q : α → Prop) (μ : α → D) : Prop :=
  ∃ δ, IsGreatest (μ '' {x | Q x}) δ ∧ ∃ x, P x ∧ c.Rel (μ x) δ

/-- A max-quantified comparative entails the comparatives with weaker comparisons, the equative
from the strict comparative in particular. -/
theorem MaxComparative.mono {c' : Comparison} (hc : ∀ a b : D, c.Rel a b → c'.Rel a b)
    (h : MaxComparative c P Q μ) : MaxComparative c' P Q μ :=
  let ⟨δ, hδ, x, hx, hr⟩ := h
  ⟨δ, hδ, x, hx, hc _ _ hr⟩

theorem MaxComparative.exists_lt (h : MaxComparative .gt P Q μ) {x : α} (hx : Q x) :
    ∃ y, P y ∧ μ x < μ y :=
  let ⟨_, hδ, y, hy, hlt⟩ := h
  ⟨y, hy, (hδ.2 ⟨x, hx, rfl⟩).trans_lt hlt⟩

/-- The max-quantified comparative is transitive, so *more P than Q* and *more Q than R* give
*more P than R* with no uniqueness assumption on any of the three sides. -/
theorem MaxComparative.trans (h₁ : MaxComparative .gt P Q μ) (h₂ : MaxComparative .gt Q R μ) :
    MaxComparative .gt P R μ :=
  let ⟨_, hδ, _, hy, hlt⟩ := h₂
  let ⟨z, hz, hlt'⟩ := h₁.exists_lt hy
  ⟨_, hδ, z, hz, hlt.trans hlt'⟩

theorem maxComparative_iff_of_unique {xa xb : α} (ha : P xa) (ha_unique : ∀ x, P x → x = xa)
    (hb : Q xb) (hb_unique : ∀ x, Q x → x = xb) :
    MaxComparative c P Q μ ↔ c.Rel (μ xa) (μ xb) := by
  have hQ : {x | Q x} = {xb} := Set.ext fun x ↦ ⟨hb_unique x, fun h ↦ h ▸ hb⟩
  refine ⟨fun ⟨δ, hδ, x, hx, hr⟩ ↦ ?_, fun hr ↦ ⟨_, hQ ▸ image_singleton ▸ isGreatest_singleton,
    xa, ha, hr⟩⟩
  rw [hQ, image_singleton] at hδ
  exact hδ.1 ▸ ha_unique x hx ▸ hr

theorem maxComparative_eq_iff (μ : α → D) (xa xb : α) :
    MaxComparative c (· = xa) (· = xb) μ ↔ c.Rel (μ xa) (μ xb) :=
  maxComparative_iff_of_unique rfl (fun _ h ↦ h) rfl (fun _ h ↦ h)

theorem maxComparative_gt_iff_of_isGreatest [Preorder α] {xa xb : α}
    (ha : IsGreatest {x | P x} xa) (hμa : MonotoneOn μ {x | P x})
    (hb : IsGreatest {x | Q x} xb) (hμb : MonotoneOn μ {x | Q x}) :
    MaxComparative .gt P Q μ ↔ μ xb < μ xa :=
  ⟨fun ⟨_, hδ, _, hx, hlt⟩ ↦
      (hδ.2 ⟨xb, hb.1, rfl⟩).trans_lt (hlt.trans_le (hμa hx ha.1 (ha.2 hx))),
    fun hlt ↦ ⟨_, hμb.map_isGreatest hb, xa, ha.1, hlt⟩⟩

end MaxComparative

section MaxComparativeLinearOrder
variable [LinearOrder D] {P Q : α → Prop} {μ : α → D} {a b : D}

theorem MaxComparative.antisymm (ha : IsGreatest (μ '' {x | P x}) a)
    (hb : IsGreatest (μ '' {x | Q x}) b) (h₁ : MaxComparative .ge P Q μ)
    (h₂ : MaxComparative .ge Q P μ) : a = b := by
  obtain ⟨b', hb', y, hy, hby⟩ := h₁
  obtain ⟨a', ha', x, hx, hax⟩ := h₂
  rw [ha.unique ha', hb.unique hb']
  exact (hax.trans (hb'.2 ⟨x, hx, rfl⟩)).antisymm (hby.trans (ha'.2 ⟨y, hy, rfl⟩))

theorem maxComparative_ge_total (ha : IsGreatest (μ '' {x | P x}) a)
    (hb : IsGreatest (μ '' {x | Q x}) b) :
    MaxComparative .ge P Q μ ∨ MaxComparative .ge Q P μ := by
  obtain ⟨x, hx, rfl⟩ := ha.1
  obtain ⟨y, hy, rfl⟩ := hb.1
  exact (le_total (μ y) (μ x)).imp (fun h ↦ ⟨_, hb, x, hx, h⟩) fun h ↦ ⟨_, ha, y, hy, h⟩

theorem maxComparative_gt_trichotomy (ha : IsGreatest (μ '' {x | P x}) a)
    (hb : IsGreatest (μ '' {x | Q x}) b) :
    MaxComparative .gt P Q μ ∨ a = b ∨ MaxComparative .gt Q P μ := by
  obtain ⟨x, hx, rfl⟩ := ha.1
  obtain ⟨y, hy, rfl⟩ := hb.1
  rcases lt_trichotomy (μ y) (μ x) with h | h | h
  · exact .inl ⟨_, hb, x, hx, h⟩
  · exact .inr (.inl h.symm)
  · exact .inr (.inr ⟨_, ha, y, hy, h⟩)

end MaxComparativeLinearOrder

/-! ### Set-of-degrees comparative

The S-comparative of [hoeksema-1983] generalizes the point-standard comparative from a single
standard to a degree-set standard. Its extension is `μ ⁻¹' strictUpperBounds Δ`, the entities
measuring above every standard degree, and the binary comparator is its singleton case
(`Comparison.bounds_singleton`). -/

section SetOfDegrees
variable [Preorder D] (μ : α → D) {Δ : Set D}

theorem mem_gtOverSet_iff_subset_Iio (y : α) : y ∈ μ ⁻¹' strictUpperBounds Δ ↔ Δ ⊆ Iio (μ y) :=
  Iff.rfl

theorem gtOverSet_isAntiAdditive : IsAntiAdditive (μ ⁻¹' strictUpperBounds ·) :=
  isAntiAdditive_forall_mem fun d y ↦ d < μ y

theorem gtOverSet_eq_singleton_of_isGreatest {m : D} (hm : IsGreatest Δ m) :
    μ ⁻¹' strictUpperBounds Δ = μ ⁻¹' strictUpperBounds {m} := by
  ext y
  simp only [mem_gtOverSet_iff_subset_Iio, singleton_subset_iff, mem_Iio]
  exact ⟨(· hm.1), fun h _ hd ↦ (hm.2 hd).trans_lt h⟩

theorem maxComparative_gt_iff_gtOverSet (P Q : α → Prop) :
    MaxComparative .gt P Q μ ↔
      (∃ δ, IsGreatest (μ '' {x | Q x}) δ) ∧
        ∃ x, P x ∧ x ∈ μ ⁻¹' strictUpperBounds (μ '' {x | Q x}) :=
  ⟨fun ⟨δ, hδ, x, hx, hlt⟩ ↦ ⟨⟨δ, hδ⟩, x, hx, fun _ hd ↦ (hδ.2 hd).trans_lt hlt⟩,
    fun ⟨⟨δ, hδ⟩, x, hx, hclear⟩ ↦ ⟨δ, hδ, x, hx, hclear hδ.1⟩⟩

end SetOfDegrees

/-! ### Superlatives

*-est* universally quantifies the comparative over a comparison class ([heim-1999]), the
semantic reflex of [bobaljik-2012]'s containment `[[[ADJ] CMPR] SPRL]`. -/

section Superlative
variable [LinearOrder D] {μ : α → D} {C : Set α} {x y : α}

/-- The absolute superlative holds of `x` when `x` is in the comparison class `C` and beats every
other member on the comparative. -/
def AbsoluteSuperlative (μ : α → D) (C : Set α) (x : α) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → μ y < μ x

theorem absoluteSuperlative_unique (hx : AbsoluteSuperlative μ C x)
    (hy : AbsoluteSuperlative μ C y) : x = y :=
  by_contra fun hne ↦ lt_asymm (hx.2 y hy.1 (Ne.symm hne)) (hy.2 x hx.1 hne)

theorem absoluteSuperlative_isGreatest (h : AbsoluteSuperlative μ C x) :
    IsGreatest (μ '' C) (μ x) :=
  ⟨mem_image_of_mem μ h.1, forall_mem_image.2 fun y hy ↦
    (eq_or_ne y x).elim (fun e ↦ e ▸ le_rfl) fun hne ↦ (h.2 y hy hne).le⟩

end Superlative

/-! ### Change of scale -/

section ChangeOfScale

variable {D' : Type*} [LinearOrder D] [LinearOrder D'] {μ : α → D}

theorem maxComparative_comp (f : D ↪o D') (c : Comparison) (P Q : α → Prop) :
    MaxComparative c P Q (f ∘ μ) ↔ MaxComparative c P Q μ := by
  rw [MaxComparative, MaxComparative, Set.image_comp]
  constructor
  · rintro ⟨_, hδ, x, hx, hr⟩
    obtain ⟨δ, -, rfl⟩ := hδ.1
    exact ⟨δ, f.strictMono.map_isGreatest.1 hδ, x, hx, (Comparison.rel_map_iff f c).1 hr⟩
  · rintro ⟨δ, hδ, x, hx, hr⟩
    exact ⟨f δ, f.strictMono.map_isGreatest.2 hδ, x, hx, (Comparison.rel_map_iff f c).2 hr⟩

end ChangeOfScale

end Degree
