module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Order.RelIso.Basic

/-!
# Fixed points of maps that compute each coordinate from those below it

Let `r` be a well-founded relation on an index type `ι`, and let `F : (∀ i, β i) → ∀ i, β i` be a
map whose `i`-th coordinate depends only on the coordinates `r`-below `i`, that is
`DependsOn (F · i) {j | r j i}`. This file proves that `F` has exactly one fixed point,
`WellFounded.fixedPoint`, built by well-founded recursion, and that iterating `F` from any family
reaches it once the number of iterations exceeds a ranking of `r`, which in a finite index type
is its cardinality. Fixed points of two such maps compare when the maps do.

## Main definitions

* `WellFounded.fixedPoint`: the fixed point of a map computing each coordinate from those below

## Main results

* `WellFounded.isFixedPt_fixedPoint`, `WellFounded.eq_fixedPoint_of_isFixedPt`: it is the unique
  fixed point
* `WellFounded.fixedPoint_eq_iterate`, `WellFounded.fixedPoint_eq_iterate_card`: iteration reaches
  it past a ranking
* `WellFounded.fixedPoint_le_fixedPoint`: fixed points are ordered as the maps are
-/

@[expose] public section

namespace WellFounded

variable {ι : Type*} {β : ι → Type*} {r : ι → ι → Prop} {F G : (∀ i, β i) → ∀ i, β i}

theorem iterate_apply_eq_of_dependsOn (hF : ∀ i, DependsOn (F · i) {j | r j i})
    (rk : r →r ((· < ·) : ℕ → ℕ → Prop)) {k : ℕ} {i : ι} (hi : rk i < k) (x y : ∀ i, β i) :
    F^[k] x i = F^[k] y i := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hF i fun j (hj : r j i) ↦ ih (by have := rk.map_rel hj; omega)

variable [∀ i, Nonempty (β i)]

open Classical in
/-- The fixed point of a map computing each coordinate from those `r`-below it, by well-founded
recursion. Coordinates not below the current one are filled arbitrarily, which the map ignores. -/
noncomputable def fixedPoint (hr : WellFounded r) (F : (∀ i, β i) → ∀ i, β i) : ∀ i, β i :=
  hr.fix fun i rec ↦ F (fun j ↦ if h : r j i then rec j h else Classical.arbitrary _) i

variable (hr : WellFounded r) (hF : ∀ i, DependsOn (F · i) {j | r j i})
include hF

theorem isFixedPt_fixedPoint : Function.IsFixedPt F (hr.fixedPoint F) := by
  funext i
  conv_rhs => rw [fixedPoint, WellFounded.fix_eq]
  exact hF i fun j (hj : r j i) ↦ by simp only [hj, ↓reduceDIte]; rfl

variable {hr}

theorem eq_fixedPoint_of_isFixedPt {x : ∀ i, β i} (hx : Function.IsFixedPt F x) :
    x = hr.fixedPoint F := by
  funext i
  induction i using hr.induction with
  | _ i ih =>
    rw [← congrFun hx i, ← congrFun (isFixedPt_fixedPoint hr hF) i]
    exact hF i fun j hj ↦ ih j hj

theorem isFixedPt_iff_eq_fixedPoint {x : ∀ i, β i} :
    Function.IsFixedPt F x ↔ x = hr.fixedPoint F :=
  ⟨eq_fixedPoint_of_isFixedPt hF, fun h ↦ h ▸ isFixedPt_fixedPoint hr hF⟩

theorem fixedPoint_apply (i : ι) : hr.fixedPoint F i = F (hr.fixedPoint F) i :=
  (congrFun (isFixedPt_fixedPoint hr hF) i).symm

theorem fixedPoint_eq_iterate (rk : r →r ((· < ·) : ℕ → ℕ → Prop)) {n : ℕ} (hn : ∀ i, rk i < n)
    (x : ∀ i, β i) : hr.fixedPoint F = F^[n] x := by
  funext i
  rw [← (isFixedPt_fixedPoint hr hF).iterate n]
  exact iterate_apply_eq_of_dependsOn hF rk (hn i) _ _

omit hF [∀ i, Nonempty (β i)] in
open Classical in
theorem exists_relHom_lt_card [Fintype ι] (hr : WellFounded r) :
    ∃ rk : r →r ((· < ·) : ℕ → ℕ → Prop), ∀ i, rk i < Fintype.card ι := by
  have hT := hr.transGen
  have irrefl : ∀ i, ¬ Relation.TransGen r i i := fun i h ↦ @WellFounded.asymmetric _ _ hT i i h h
  refine ⟨⟨fun i ↦ (Finset.univ.filter (Relation.TransGen r · i)).card,
    fun {j i} h ↦ Finset.card_lt_card ?_⟩, fun i ↦ Finset.card_lt_card ?_⟩
  · refine (Finset.ssubset_iff_of_subset fun a ha ↦ ?_).2 ⟨j, ?_, fun hj ↦ irrefl j ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; exact ha.tail h
    · simpa using Relation.TransGen.single h
    · simpa using hj
  · exact Finset.filter_ssubset.2 ⟨i, Finset.mem_univ i, irrefl i⟩

theorem fixedPoint_eq_iterate_card [Fintype ι] (x : ∀ i, β i) :
    hr.fixedPoint F = F^[Fintype.card ι] x :=
  let ⟨rk, hrk⟩ := exists_relHom_lt_card hr
  fixedPoint_eq_iterate hF rk hrk x

omit hF in
theorem fixedPoint_le_fixedPoint [∀ i, Preorder (β i)] (hF : ∀ i, DependsOn (F · i) {j | r j i})
    (hG : ∀ i, DependsOn (G · i) {j | r j i}) (hFG : ∀ x y, x ≤ y → F x ≤ G y) :
    hr.fixedPoint F ≤ hr.fixedPoint G := by
  classical
  intro i
  induction i using hr.induction with
  | _ i ih =>
    let x : ∀ j, β j := fun j ↦ if r j i then hr.fixedPoint F j else hr.fixedPoint G j
    have hx : x ≤ hr.fixedPoint G := fun j ↦ by
      by_cases hj : r j i
      · simpa [x, hj] using ih j hj
      · simp [x, hj]
    have hFx : F (hr.fixedPoint F) i = F x i :=
      hF i fun j (hj : r j i) ↦ show hr.fixedPoint F j = x j by simp [x, hj]
    rw [fixedPoint_apply hF, fixedPoint_apply hG, hFx]
    exact hFG _ _ hx i

end WellFounded
