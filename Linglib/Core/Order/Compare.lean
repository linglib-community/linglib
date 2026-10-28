module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Compare
public import Mathlib.Order.Max

/-!
# Composition of comparisons

This file defines the composition of two comparison results. In a linear order the comparison of
`a` with `c` is constrained by the comparisons of `a` with `b` and of `b` with `c`: two `lt`
compose to `lt`, `eq` is an identity, and `lt` followed by `gt` leaves the result open.
`Ordering.comp o₁ o₂` is the set of results compatible with `o₁` followed by `o₂`, and
`compare_mem_comp` shows that the actual comparison lies in it. In a dense linear order without
endpoints the table is exact: every result it allows is realized by some intermediate point.

## Main declarations

* `Ordering.comp`: the composition table on `Ordering`.
* `Ordering.compare_mem_comp`: `compare a c` lies in `(compare a b).comp (compare b c)`.
* `Ordering.exists_compare_eq_of_mem_comp`: in a dense linear order without endpoints, a result
  in `o₁.comp o₂` is realized through an intermediate point.
* `Ordering.exists_fin_compare_eq`: finitely many points compare as their ranks do.

## Implementation notes

Extending a finite configuration of points by further points in a dense linear order without
endpoints is mathlib's back-and-forth step, `Order.PartialIso.definedAtLeft`.
-/

@[expose] public section

namespace Ordering

/-- The results of comparing `a` with `c` compatible with `a` comparing to `b` as `o₁` and `b`
to `c` as `o₂`, in a linear order. -/
def comp : Ordering → Ordering → Finset Ordering
  | lt, lt => {lt}
  | lt, eq => {lt}
  | lt, gt => ⊤
  | eq, o => {o}
  | gt, lt => ⊤
  | gt, eq => {gt}
  | gt, gt => {gt}

@[simp] theorem eq_comp (o : Ordering) : eq.comp o = {o} := rfl

@[simp] theorem comp_eq (o : Ordering) : o.comp eq = {o} := by cases o <;> rfl

variable {α : Type*} [LinearOrder α]

theorem compare_mem_comp (a b c : α) : compare a c ∈ (compare a b).comp (compare b c) := by
  rcases h₁ : compare a b with _ | _ | _ <;> rcases h₂ : compare b c with _ | _ | _ <;>
    simp only [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at h₁ h₂ <;>
    simp [comp, compare_lt_iff_lt, compare_gt_iff_gt, h₁, h₂] <;>
    first
      | exact h₁.trans h₂ | exact h₂.trans h₁ | exact h₁.trans_eq h₂
      | exact h₂.symm.trans_lt h₁

/-- In a dense linear order without endpoints, every result the composition table allows is
realized by some intermediate point. -/
theorem exists_compare_eq_of_mem_comp [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] {a c : α}
    {o₁ o₂ : Ordering} (h : compare a c ∈ o₁.comp o₂) :
    ∃ b, compare a b = o₁ ∧ compare b c = o₂ := by
  cases o₁ <;> cases o₂ <;>
    simp only [comp, Finset.mem_singleton, compare_lt_iff_lt, compare_eq_iff_eq,
      compare_gt_iff_gt] at h ⊢
  · exact exists_between h
  · exact ⟨c, h, rfl⟩
  · obtain ⟨b, hb⟩ := exists_gt (max a c)
    exact ⟨b, (le_max_left _ _).trans_lt hb, (le_max_right _ _).trans_lt hb⟩
  · exact ⟨a, rfl, h⟩
  · exact ⟨a, rfl, h⟩
  · exact ⟨a, rfl, h⟩
  · obtain ⟨b, hb⟩ := exists_lt (min a c)
    exact ⟨b, hb.trans_le (min_le_left _ _), hb.trans_le (min_le_right _ _)⟩
  · exact ⟨c, h, rfl⟩
  · exact (exists_between h).imp fun _ ↦ And.symm

/-- Finitely many points of a linear order compare as their ranks do, the numbers of points below
them, so that their order type is realized among as many natural numbers. -/
theorem exists_fin_compare_eq {n : ℕ} (f : Fin n → α) :
    ∃ g : Fin n → Fin n, ∀ x y, compare (g x) (g y) = compare (f x) (f y) := by
  classical
  let r : Fin n → ℕ := fun x ↦ (Finset.univ.filter fun y ↦ f y < f x).card
  have hr (x : Fin n) : r x < n := by
    simpa [r, Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card
      (Finset.filter_ssubset (p := fun y ↦ f y < f x).2 ⟨x, Finset.mem_univ x, lt_irrefl _⟩)
  have hlt {x y : Fin n} (h : f x < f y) : r x < r y :=
    Finset.card_lt_card <| (Finset.ssubset_iff_of_subset fun z hz ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.trans h).2 ⟨x, by simpa using h, by simp⟩
  refine ⟨fun x ↦ ⟨r x, hr x⟩, fun x y ↦ ?_⟩
  rcases lt_trichotomy (f x) (f y) with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt]; exact Fin.mk_lt_mk.2 (hlt h)
  · rw [compare_eq_iff_eq.2 h, compare_eq_iff_eq]; simp [r, h]
  · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt]; exact Fin.mk_lt_mk.2 (hlt h)

end Ordering
