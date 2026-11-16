module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.Image
public import Linglib.Semantics.MeasurementTheory.Homogeneity

/-!
# Ordinal scales

A measure represents an order when the order of its values is the order of the things measured. Two
measures of one order [differ by a strictly increasing map on the range of the
first](##MeasurementTheory.forall_le_iff_le_iff_exists_strictMono), which is what makes the scale
ordinal; on a finite domain they [differ by an order automorphism of the
degrees](##MeasurementTheory.exists_orderIso_comp_eq). A statement about a measure is reference
invariant when every measure of the same order gives it the same value, that is, when it [depends
only on the order the measure induces](##MeasurementTheory.factorsThrough_preimage_le_iff). Such a
statement is [invariant](##Function.FactorsThrough.invariant_univ) under every strictly increasing
change of scale, as [comparing two measures](##MeasurementTheory.invariant_univ_lt) is.

## Implementation notes

A measure is a bare function and the order it represents is the one it induces, `μ ⁻¹'o (· ≤ ·)`,
so that two measures represent one order when `∀ a b, ν a ≤ ν b ↔ μ a ≤ μ b`. Depending only on
that order is `Function.FactorsThrough`. The reparametrization is strictly increasing on the range
of the first measure, and need not extend to the whole degree type.

## TODO

* The converse of `Function.FactorsThrough.invariant_univ`, for maps on the range of a measure.
* Extensive and difference structures, whose measures differ by a similarity and by a positive
  affine map.

## References

* [krantz-1971]
* [luce-krantz-suppes-tversky-1990]
-/

@[expose] public section

open Function Set

namespace MeasurementTheory

variable {E D D' β : Type*}

/-- Two measures order alike exactly when the second is a strictly increasing reparametrization
of the first on its range. -/
-- [luce-krantz-suppes-tversky-1990] Theorem 22.2, p. 287, for an order
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

/-- On a finite domain two measures in an ordered field that order alike differ by an order
automorphism of the field. -/
-- [krantz-1971] Theorem 1, p. 15
theorem exists_orderIso_comp_eq [Finite E] {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {μ ν : E → K} (h : ∀ a b, ν a ≤ ν b ↔ μ a ≤ μ b) :
    ∃ g : K ≃o K, ν = g ∘ μ := by
  classical
  obtain ⟨g₀, hg₀, rfl⟩ := forall_le_iff_le_iff_exists_strictMono.1 h
  have : Fintype E := Fintype.ofFinite E
  let S : Finset K := Finset.univ.image μ
  have hmem (i : Fin S.card) : (S.orderEmbOfFin rfl i : K) ∈ range μ := by
    obtain ⟨e, -, he⟩ := Finset.mem_image.1 (S.orderEmbOfFin_mem rfl i)
    exact ⟨e, he⟩
  obtain ⟨g, -, hg⟩ := isPointHomogeneous_univ (K := K) S.card (fun i ↦ S.orderEmbOfFin rfl i)
    (fun i ↦ g₀ ⟨_, hmem i⟩) (S.orderEmbOfFin rfl).strictMono
    fun i j hij ↦ hg₀ (Subtype.mk_lt_mk.2 ((S.orderEmbOfFin rfl).strictMono hij))
  refine ⟨g, funext fun e ↦ ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, S.orderEmbOfFin rfl i = μ e := by
    have he : μ e ∈ (S : Set K) := Finset.mem_image_of_mem μ (Finset.mem_univ e)
    rwa [← Finset.range_orderEmbOfFin S rfl] at he
  calc g₀ (rangeFactorization μ e) = g₀ ⟨S.orderEmbOfFin rfl i, hmem i⟩ :=
        congrArg g₀ (Subtype.ext hi.symm)
    _ = g (S.orderEmbOfFin rfl i) := (hg i).symm
    _ = g (μ e) := by rw [hi]

/-- A function of measures depends only on the order the measure induces exactly when it agrees
on any two measures that order alike. -/
-- [luce-krantz-suppes-tversky-1990] Definition 22.1, p. 274
theorem factorsThrough_preimage_le_iff [LE D] {a : (E → D) → β} :
    FactorsThrough a (fun μ ↦ μ ⁻¹'o (· ≤ ·)) ↔
      ∀ μ ν : E → D, (∀ x y, μ x ≤ μ y ↔ ν x ≤ ν y) → a μ = a ν :=
  ⟨fun h _ _ hμν ↦ h (funext₂ fun x y ↦ propext (hμν x y)),
    fun h μ ν hμν ↦ h μ ν fun x y ↦ iff_of_eq (congrFun₂ hμν x y)⟩

/-- A function of measures that depends only on the induced order is invariant under every
strictly increasing change of scale. -/
theorem _root_.Function.FactorsThrough.invariant_univ [LE D] {a : (E → D) → β}
    (h : FactorsThrough a fun μ ↦ μ ⁻¹'o (· ≤ ·)) : Invariant (univ : Set (D ↪o D)) a :=
  fun g _ μ ↦ h (funext₂ fun x y ↦
    propext (show g (μ x) ≤ g (μ y) ↔ μ x ≤ μ y from g.map_rel_iff))

/-- Comparing two measures is invariant under every strictly increasing change of scale. -/
theorem invariant_univ_lt [LinearOrder D] (x y : E) :
    Invariant (univ : Set (D ↪o D)) fun μ : E → D ↦ μ y < μ x :=
  (factorsThrough_preimage_le_iff.2 fun μ ν h ↦ by simp only [← not_le, h x y]).invariant_univ

end MeasurementTheory
