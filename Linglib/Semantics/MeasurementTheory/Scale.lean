module

public import Mathlib.Data.Set.Image
public import Mathlib.Order.Monotone.Basic

/-!
# Scales and meaningful statements

A measure assigns degrees to things so that the order of the degrees is the order of the things.
Two measures of one order [differ by a strictly increasing map on the range of the
first](##forall_le_iff_le_iff_exists_strictMono), which makes the scale ordinal. A statement about
a measure is meaningful when every measure of the same structure gives it the same value. On an
ordinal scale that is [depending only on the order the measure
induces](##factorsThrough_preimage_le_iff), as [comparing two
measures](##factorsThrough_preimage_le_lt) does, and such a statement is
[invariant](##Function.FactorsThrough.invariant_strictMono) under every strictly increasing change
of scale.

## Implementation notes

A measure is a bare function and the order it represents is the one it induces, `μ ⁻¹'o (· ≤ ·)`,
so that two measures represent one order when `∀ a b, ν a ≤ ν b ↔ μ a ≤ μ b`. Depending only on
that order is `Function.FactorsThrough`.

## TODO

* For a finite domain and real degrees the reparametrization extends to an order isomorphism of
  the reals, so that the two notions of meaningfulness agree there.
* Extensive and difference structures, whose measures are unique up to a similarity and up to a
  positive affine map; `Aggregation` and `Degree.Measurement` take those classes as given.

## References

* [krantz-1971]
* [stevens-1946]
-/

@[expose] public section

open Function Set

variable {E D D' β : Type*}

/-! ### Ordinal scales -/

/-- Two measures order alike exactly when the second is a strictly increasing reparametrization
of the first on its range. -/
-- [krantz-1971] Theorem 1, p. 15
theorem forall_le_iff_le_iff_exists_strictMono [LinearOrder D] [LinearOrder D'] {μ : E → D}
    {ν : E → D'} :
    (∀ a b, ν a ≤ ν b ↔ μ a ≤ μ b) ↔
      ∃ g : range μ → D', StrictMono g ∧ ν = g ∘ rangeFactorization μ := by
  refine ⟨fun h ↦ ⟨fun d ↦ ν d.2.choose, fun d d' hdd ↦ ?_, funext fun a ↦ ?_⟩, ?_⟩
  · have hlt : μ d.2.choose < μ d'.2.choose := by rwa [d.2.choose_spec, d'.2.choose_spec]
    exact lt_of_not_ge fun hle ↦ hlt.not_ge ((h _ _).1 hle)
  · have he : μ (mem_range_self (f := μ) a).choose = μ a := (mem_range_self a).choose_spec
    exact le_antisymm ((h _ _).2 he.ge) ((h _ _).2 he.le)
  · rintro ⟨g, hg, rfl⟩ a b
    exact hg.le_iff_le

/-! ### Meaningful statements -/

/-- A function of measures depends only on the order the measure induces exactly when it agrees
on any two measures that order alike. -/
theorem factorsThrough_preimage_le_iff [LE D] {a : (E → D) → β} :
    FactorsThrough a (fun μ ↦ μ ⁻¹'o (· ≤ ·)) ↔
      ∀ μ ν : E → D, (∀ x y, μ x ≤ μ y ↔ ν x ≤ ν y) → a μ = a ν :=
  ⟨fun h _ _ hμν ↦ h (funext₂ fun x y ↦ propext (hμν x y)),
    fun h μ ν hμν ↦ h μ ν fun x y ↦ iff_of_eq (congrFun₂ hμν x y)⟩

/-- Comparing two measures depends only on the order the measure induces. -/
theorem factorsThrough_preimage_le_lt [LinearOrder D] (x y : E) :
    FactorsThrough (fun μ : E → D ↦ μ y < μ x) fun μ ↦ μ ⁻¹'o (· ≤ ·) :=
  factorsThrough_preimage_le_iff.2 fun μ ν h ↦ by
    simp only [← not_le, h x y]

/-- A function of measures is invariant under a class of changes of scale when none of them
changes its value. -/
def Invariant (S : Set (D → D)) (a : (E → D) → β) : Prop :=
  ∀ g ∈ S, ∀ μ, a (g ∘ μ) = a μ

theorem Invariant.mono {S T : Set (D → D)} (h : S ⊆ T) {a : (E → D) → β}
    (ha : Invariant T a) : Invariant S a :=
  fun g hg ↦ ha g (h hg)

/-- A function of measures that depends only on the induced order is invariant under every
strictly increasing change of scale. -/
theorem Function.FactorsThrough.invariant_strictMono [LinearOrder D] {a : (E → D) → β}
    (h : FactorsThrough a fun μ ↦ μ ⁻¹'o (· ≤ ·)) : Invariant {u : D → D | StrictMono u} a :=
  fun _ hu _ ↦ h (funext₂ fun _ _ ↦ propext (StrictMono.le_iff_le hu))

/-- Comparing two measures is meaningful on an ordinal scale. -/
theorem invariant_strictMono_lt [LinearOrder D] (a b : E) :
    Invariant {u : D → D | StrictMono u} fun μ ↦ μ b < μ a :=
  (factorsThrough_preimage_le_lt a b).invariant_strictMono
