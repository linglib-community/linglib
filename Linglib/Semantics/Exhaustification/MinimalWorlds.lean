module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Powerset
public import Linglib.Core.Order.Minimals

/-!
# Minimal-world exhaustification

This file defines Spector's minimal-world exhaustifier `exhMW ALT φ`, the worlds of the prejacent
`φ` whose set of true alternatives, `Preorder.satisfied (· ∈ ·) ALT`, is minimal among the
prejacent's worlds. These are Kratzer's best worlds, with the prejacent as modal base and the
negated alternatives as ordering source. Over finitely many alternatives every world of the
prejacent lies above a minimal one, so a satisfiable prejacent has minimal worlds. An
`IsMinimalCover` is a set of prejacent worlds representing the minimal worlds up to sharing their
true alternatives; the exhaustifiers of `InnocentExclusion` and `InnocentInclusion` are computed
from one.

## Main statements

* `Exhaustification.exhMW_eq_minimals`: minimal worlds are the minimal elements of the criteria
  preorder with the negated alternatives as criteria.
* `Exhaustification.exists_mem_exhMW_le`: over finitely many alternatives, every world of the
  prejacent lies above a minimal world.

## References

* [groenendijk-stokhof-1984]
* [spector-2016]
* [kratzer-1981]
-/

@[expose] public section

namespace Exhaustification

variable {W : Type*} (ALT : Set (Set W)) (φ : Set W)

/-- The minimal-world exhaustifier keeps the prejacent worlds whose set of true alternatives is
minimal among the prejacent's worlds. -/
def exhMW : Set W := {u | MinimalFor (· ∈ φ) (Preorder.satisfied (· ∈ ·) ALT) u}

variable {ALT φ} {u w : W}

theorem mem_exhMW : u ∈ exhMW ALT φ ↔ MinimalFor (· ∈ φ) (Preorder.satisfied (· ∈ ·) ALT) u :=
  Iff.rfl

theorem exhMW_subset : exhMW ALT φ ⊆ φ := fun _ h ↦ h.1

theorem mem_exhMW_iff_minimal : u ∈ exhMW ALT φ ↔ u ∈ φ ∧
    Minimal (· ∈ Preorder.satisfied (· ∈ ·) ALT '' φ) (Preorder.satisfied (· ∈ ·) ALT u) := by
  refine ⟨fun h ↦ ⟨h.1, ⟨u, h.1, rfl⟩, ?_⟩, fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv hvu ↦ h.2 ⟨v, hv, rfl⟩ hvu⟩⟩
  rintro _ ⟨v, hv, rfl⟩ hvu
  exact h.2 hv hvu

variable (ALT φ) in
/-- Minimal worlds are Kratzer's best worlds: the minimal elements of the criteria preorder whose
criteria are the negated alternatives. -/
theorem exhMW_eq_minimals :
    exhMW ALT φ = (Preorder.ofCriteria (fun w a ↦ w ∉ a) ALT).minimals φ := by
  have key (u v : W) : (Preorder.ofCriteria (fun w a ↦ w ∉ a) ALT).le u v ↔
      Preorder.satisfied (· ∈ ·) ALT u ⊆ Preorder.satisfied (· ∈ ·) ALT v := by
    simp only [Preorder.ofCriteria_le_iff, Set.subset_def, Preorder.mem_satisfied, not_imp_not]
    exact ⟨fun h a ⟨ha, hu⟩ ↦ ⟨ha, h a ha hu⟩, fun h a ha hu ↦ (h a ⟨ha, hu⟩).2⟩
  ext u
  simp only [mem_exhMW, MinimalFor, Preorder.mem_minimals_iff, key]

/-- Over finitely many alternatives, every world of the prejacent lies above a minimal world. -/
theorem exists_mem_exhMW_le (hfin : ALT.Finite) (hw : w ∈ φ) :
    ∃ u ∈ exhMW ALT φ, Preorder.satisfied (· ∈ ·) ALT u ⊆ Preorder.satisfied (· ∈ ·) ALT w := by
  obtain ⟨u, ⟨hu, huw⟩, hmin⟩ := Set.Finite.exists_minimalFor' (Preorder.satisfied (· ∈ ·) ALT)
    {v | v ∈ φ ∧ Preorder.satisfied (· ∈ ·) ALT v ⊆ Preorder.satisfied (· ∈ ·) ALT w}
    (hfin.finite_subsets.subset (Set.image_subset_iff.2 fun _ _ _ h ↦ h.1)) ⟨w, hw, le_rfl⟩
  exact ⟨u, ⟨hu, fun v hv hvu ↦ hmin ⟨hv, hvu.trans huw⟩ hvu⟩, huw⟩

theorem exhMW_nonempty (hfin : ALT.Finite) (hφ : φ.Nonempty) : (exhMW ALT φ).Nonempty :=
  let ⟨_, hw⟩ := hφ
  let ⟨u, hu, _⟩ := exists_mem_exhMW_le hfin hw
  ⟨u, hu⟩

theorem exhMW_univ : exhMW Set.univ φ = φ := by
  refine Set.Subset.antisymm (fun _ h ↦ h.1) fun u hu ↦ ⟨hu, fun v _ hvu ↦ ?_⟩
  obtain rfl : v = u := (hvu ⟨trivial, rfl⟩).2
  exact le_rfl

/-- Over finitely many worlds and alternatives, membership in the minimal worlds is decidable. -/
instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    [DecidablePred (· ∈ φ)] : DecidablePred (· ∈ exhMW (Set.range f) φ) := fun u ↦
  decidable_of_iff (u ∈ φ ∧ ∀ v, v ∈ φ → (∀ i, v ∈ f i → u ∈ f i) → ∀ i, u ∈ f i → v ∈ f i) <| by
    simp only [mem_exhMW, MinimalFor, Set.subset_def, Preorder.mem_satisfied, Set.mem_range,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff, exists_apply_eq_apply, true_and]

/-! ### Representative minimal worlds -/

variable (ALT φ) in
/-- A set of prejacent worlds represents the minimal worlds when every prejacent world lies above
one of its members and no member's true alternatives strictly include another's. -/
structure IsMinimalCover (M : Set W) : Prop where
  mem : ∀ v ∈ M, v ∈ φ
  le : ∀ w ∈ φ, ∃ v ∈ M, Preorder.satisfied (· ∈ ·) ALT v ⊆ Preorder.satisfied (· ∈ ·) ALT w
  antisymm : ∀ v ∈ M, ∀ u ∈ M,
    Preorder.satisfied (· ∈ ·) ALT u ⊆ Preorder.satisfied (· ∈ ·) ALT v →
      Preorder.satisfied (· ∈ ·) ALT v ⊆ Preorder.satisfied (· ∈ ·) ALT u

variable {M : Set W}

theorem IsMinimalCover.exhMW_eq (hM : IsMinimalCover ALT φ M) :
    exhMW ALT φ = {u | u ∈ φ ∧ ∃ v ∈ M, Preorder.satisfied (· ∈ ·) ALT v =
      Preorder.satisfied (· ∈ ·) ALT u} := by
  ext u
  refine ⟨fun ⟨hu, hmin⟩ ↦ ⟨hu, ?_⟩, fun ⟨hu, v, hv, hvu⟩ ↦ ⟨hu, fun x hx hxu ↦ ?_⟩⟩
  · obtain ⟨v, hv, hvu⟩ := hM.le u hu
    exact ⟨v, hv, hvu.antisymm (hmin (hM.mem v hv) hvu)⟩
  · obtain ⟨v', hv', hv'x⟩ := hM.le x hx
    exact hvu ▸ (hM.antisymm v hv v' hv' (hv'x.trans (hxu.trans hvu.ge))).trans hv'x

end Exhaustification
