module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Degree.Quotient

/-!
# The universal scale

A measure `μ : E → D` orders a finite comparison class `C` by a quasi-order whose classes are the
values `C.image μ`. Bale's universal degree of a member is the position of its class: one plus
the number of classes below it, over the number of classes, a rational between zero and one.
Universal degrees record positions and nothing else. They are unchanged by any order embedding of
the scale, and on a comparison class two measures give the same universal degrees exactly when
they induce the same quasi-order. Comparing two measures directly is not invariant under
rescaling one of them (`Degree.Comparison.forall_preimage_interval_eq_iff`), but comparing their
universal degrees is, which is what makes a comparison between different adjectives meaningful.

## Main definitions

* `Degree.relativeRank`: the position of a value in a finite scale, as a fraction of the scale.
* `Degree.universalDegree`: the universal degree of a member of a comparison class under a
  measure.

## Main statements

* `Degree.universalDegree_comp`: universal degrees are invariant under order embeddings of the
  scale.
* `Degree.ker_universalDegree`: on a comparison class, universal degrees are a complete invariant
  of the quasi-order the measure induces.
* `Degree.universalDegree_eq_iff`: two members share a universal degree exactly when they are
  equivalent in Cresswell's sense.

## Implementation notes

A comparison class is a `Finset`, Klein's comparison class made finite so that its classes can be
counted. The primary scale, the quotient of the restricted quasi-order, is order-isomorphic to
`C.image μ`, where universal degrees are computed; `ker_universalDegree` makes the choice of
measure immaterial.

## References

* [bale-2008]
* [cresswell-1976]
* [klein-1980]
-/

@[expose] public section

namespace Degree

open Finset

/-! ### Positions in a finite scale -/

section Rank

variable {D : Type*} [LinearOrder D]

/-- The relative rank of `d` in a finite scale `S` is the share of `S` at or below it, one plus
the number of values below `d` over the number of values. -/
def relativeRank (S : Finset D) (d : D) : ℚ := #(S.filter (· ≤ d)) / #S

theorem relativeRank_strictMonoOn (S : Finset D) : StrictMonoOn (relativeRank S) S := by
  intro a ha b hb hab
  have hS : (0 : ℚ) < #S := by exact_mod_cast card_pos.2 ⟨a, ha⟩
  rw [relativeRank, relativeRank, div_lt_div_iff_of_pos_right hS, Nat.cast_lt]
  refine card_lt_card ((ssubset_iff_of_subset
    (monotone_filter_right S fun x _ (hx : x ≤ a) ↦ hx.trans hab.le)).2 ⟨b, ?_, ?_⟩)
  · exact mem_filter.2 ⟨hb, le_rfl⟩
  · exact fun h ↦ (mem_filter.1 h).2.not_gt hab

theorem relativeRank_of_forall_le {S : Finset D} {d : D} (hd : d ∈ S) (h : ∀ x ∈ S, x ≤ d) :
    relativeRank S d = 1 := by
  rw [relativeRank, filter_true_of_mem h, div_self]
  exact_mod_cast (card_pos.2 ⟨d, hd⟩).ne'

theorem relativeRank_of_forall_ge {S : Finset D} {d : D} (hd : d ∈ S) (h : ∀ x ∈ S, d ≤ x) :
    relativeRank S d = 1 / #S := by
  rw [relativeRank, show S.filter (· ≤ d) = {d} by ext x; grind, card_singleton, Nat.cast_one]

theorem relativeRank_Icc {N n : ℕ} (hn : n ∈ Icc 1 N) : relativeRank (Icc 1 N) n = n / N := by
  rw [relativeRank, show (Icc 1 N).filter (· ≤ n) = Icc 1 n by ext k; grind]
  simp

end Rank

/-! ### Universal degrees -/

section Universal

variable {D D' E F : Type*} [LinearOrder D] [DecidableEq D] [LinearOrder D'] [DecidableEq D']

/-- The universal degree of `x` under the measure `μ` on the comparison class `C` is the relative
rank of its class among the classes of `C`. -/
def universalDegree (μ : E → D) (C : Finset E) (x : E) : ℚ := relativeRank (C.image μ) (μ x)

variable {μ : E → D} {C C' : Finset E} {x y : E}

theorem universalDegree_lt_iff (hx : x ∈ C) (hy : y ∈ C) :
    universalDegree μ C x < universalDegree μ C y ↔ μ x < μ y :=
  (relativeRank_strictMonoOn (C.image μ)).lt_iff_lt (mem_image_of_mem μ hx) (mem_image_of_mem μ hy)

@[simp] theorem universalDegree_comp (f : D ↪o D') (μ : E → D) (C : Finset E) :
    universalDegree (f ∘ μ) C = universalDegree μ C := by
  funext x
  simp only [universalDegree, relativeRank, ← image_image, filter_image, Function.comp_apply,
    f.le_iff_le, card_image_of_injective _ f.injective]

private theorem card_image_le_of_eq_imp {D₁ D₂ : Type*} [DecidableEq D₁] [DecidableEq D₂]
    [Nonempty E] {T : Finset E} (f : E → D₁) (g : E → D₂)
    (h : ∀ a ∈ T, ∀ b ∈ T, g a = g b → f a = f b) : #(T.image f) ≤ #(T.image g) := by
  refine card_le_card_of_injOn (fun d ↦ g (Function.invFunOn f T d)) ?_ ?_
  · intro d hd
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hd
    exact mem_image_of_mem g (Function.invFunOn_mem ⟨a, ha, rfl⟩)
  · intro d hd d' hd' hdd
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hd
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hd'
    rw [← Function.invFunOn_eq (f := f) ⟨a, ha, rfl⟩, ← Function.invFunOn_eq (f := f) ⟨b, hb, rfl⟩]
    exact h _ (Function.invFunOn_mem ⟨a, ha, rfl⟩) _ (Function.invFunOn_mem ⟨b, hb, rfl⟩) hdd

theorem universalDegree_congr {ν : E → D'} (h : ∀ a ∈ C, ∀ b ∈ C, μ a ≤ μ b ↔ ν a ≤ ν b)
    (hx : x ∈ C) : universalDegree μ C x = universalDegree ν C x := by
  have : Nonempty E := ⟨x⟩
  have card_image : ∀ T ⊆ C, #(T.image μ) = #(T.image ν) := fun T hT ↦
    have heq : ∀ a ∈ T, ∀ b ∈ T, μ a = μ b ↔ ν a = ν b := fun a ha b hb ↦ by grind
    (card_image_le_of_eq_imp μ ν fun a ha b hb ↦ (heq a ha b hb).2).antisymm
      (card_image_le_of_eq_imp ν μ fun a ha b hb ↦ (heq a ha b hb).1)
  rw [universalDegree, universalDegree, relativeRank, relativeRank, filter_image, filter_image,
    card_image _ (filter_subset _ _), card_image C subset_rfl,
    filter_congr fun a ha ↦ h a ha x hx]

/-- On a comparison class, universal degrees are a complete invariant of the quasi-order a
measure induces, so two measures give the same universal degrees exactly when they order the
class alike. -/
theorem ker_universalDegree (C : Finset E) :
    Setoid.ker (fun (μ : E → D) (x : C) ↦ universalDegree μ C x) =
      Setoid.ker fun (μ : E → D) (a b : C) ↦ μ a ≤ μ b := by
  ext μ ν
  simp only [Setoid.ker_def, funext_iff, eq_iff_iff]
  refine ⟨fun h a b ↦ ?_, fun h x ↦ universalDegree_congr (fun a ha b hb ↦ h ⟨a, ha⟩ ⟨b, hb⟩) x.2⟩
  rw [← not_lt, ← not_lt, ← universalDegree_lt_iff (μ := μ) b.2 a.2,
    ← universalDegree_lt_iff (μ := ν) b.2 a.2, h a, h b]

theorem universalDegree_eq_iff (hx : x ∈ C) (hy : y ∈ C) :
    universalDegree μ C x = universalDegree μ C y ↔
      (cresswellSetoid fun a b : C ↦ μ b ≤ μ a).r ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [universalDegree, universalDegree,
    (relativeRank_strictMonoOn _).injOn.eq_iff (mem_image_of_mem μ hx) (mem_image_of_mem μ hy)]
  refine ⟨fun h ↦ ⟨fun _ ↦ by simp only [h], fun _ ↦ by simp only [h]⟩, fun ⟨h, _⟩ ↦ ?_⟩
  exact le_antisymm ((h ⟨x, hx⟩).1 le_rfl) ((h ⟨y, hy⟩).2 le_rfl)

theorem universalDegree_lt_iff_of_image_eq {ν : F → D} {C' : Finset F} {y : F}
    (h : C.image μ = C'.image ν) (hx : x ∈ C) (hy : y ∈ C') :
    universalDegree μ C x < universalDegree ν C' y ↔ μ x < ν y := by
  rw [universalDegree, universalDegree, h]
  exact (relativeRank_strictMonoOn _).lt_iff_lt (h ▸ mem_image_of_mem μ hx)
    (mem_image_of_mem ν hy)

theorem universalDegree_eq_of_image_eq (h : C.image μ = C'.image μ) :
    universalDegree μ C = universalDegree μ C' :=
  funext fun _ ↦ by rw [universalDegree, universalDegree, h]

theorem universalDegree_of_forall_le (hx : x ∈ C) (h : ∀ y ∈ C, μ y ≤ μ x) :
    universalDegree μ C x = 1 :=
  relativeRank_of_forall_le (mem_image_of_mem μ hx) fun _ hd ↦ by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hd; exact h y hy

theorem universalDegree_of_forall_ge (hx : x ∈ C) (h : ∀ y ∈ C, μ x ≤ μ y) :
    universalDegree μ C x = 1 / #(C.image μ) :=
  relativeRank_of_forall_ge (mem_image_of_mem μ hx) fun _ hd ↦ by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hd; exact h y hy

theorem universalDegree_of_image_eq_Icc {μ : E → ℕ} {N : ℕ} (h : C.image μ = Icc 1 N)
    (hx : x ∈ C) : universalDegree μ C x = μ x / N := by
  rw [universalDegree, h, relativeRank_Icc (h ▸ mem_image_of_mem μ hx)]

end Universal

end Degree
