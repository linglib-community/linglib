module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Powerset
public import Linglib.Core.Order.Minimals
public import Linglib.Logic.Nonmonotonic.PremiseOrdering

/-!
# Minimal-world exhaustification

This file defines Spector's minimal-world exhaustifier `exhMW ALT φ`: the worlds `w` of the
prejacent `φ` whose set of true alternatives `{a ∈ ALT | w ∈ a}` is minimal among the worlds of the
prejacent. These are Kratzer's best worlds, with the prejacent as modal base and the negated
alternatives as ordering source. Over finitely many alternatives every world of the prejacent lies
above a minimal one, so a satisfiable prejacent has minimal worlds. A minimal cover is a set of
worlds of the prejacent that represents the minimal worlds up to having the same true alternatives;
the exhaustifiers by innocent exclusion and innocent inclusion are computed from one.

## Main definitions

* `Exhaustification.exhMW ALT φ`: the worlds of `φ` whose set of true alternatives is minimal.
* `Exhaustification.IsMinimalCover ALT φ M`: `M` is a set of worlds of `φ` such that every world of
  `φ` lies above one of them and no two of them are strictly ordered.

## Main results

* `Exhaustification.exhMW_eq_minimals`: the minimal worlds are the best worlds of the prejacent
  under the premise set of the negated alternatives.
* `Exhaustification.exists_mem_exhMW_le`: over finitely many alternatives, every world of the
  prejacent lies above a minimal world.
* `Exhaustification.ofLowerSets_image_union_le_iff`: under the premises that some individuals lack a
  property and others have it, a world is at least as good as another when fewer of the first and
  more of the second have the property in it.

## References

* [groenendijk-stokhof-1984]
* [spector-2016]
* [kratzer-1981]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Exhaustification

variable {W : Type*} (ALT : Set (Set W)) (φ : Set W)

/-- The minimal-world exhaustifier keeps the prejacent worlds whose set of true alternatives is
minimal among the prejacent's worlds. -/
def exhMW : Set W := {u | MinimalFor (· ∈ φ) (fun w ↦ {a ∈ ALT | w ∈ a}) u}

variable {ALT φ} {u w : W}

theorem mem_exhMW : u ∈ exhMW ALT φ ↔ MinimalFor (· ∈ φ) (fun w ↦ {a ∈ ALT | w ∈ a}) u :=
  Iff.rfl

theorem exhMW_subset : exhMW ALT φ ⊆ φ := fun _ h ↦ h.1

theorem mem_exhMW_iff_minimal : u ∈ exhMW ALT φ ↔ u ∈ φ ∧
    Minimal (· ∈ (fun w ↦ {a ∈ ALT | w ∈ a}) '' φ) ({a ∈ ALT | u ∈ a}) := by
  refine ⟨fun h ↦ ⟨h.1, ⟨u, h.1, rfl⟩, ?_⟩, fun ⟨hu, h⟩ ↦ ⟨hu, fun v hv hvu ↦ h.2 ⟨v, hv, rfl⟩ hvu⟩⟩
  rintro _ ⟨v, hv, rfl⟩ hvu
  exact h.2 hv hvu

variable (ALT φ) in
/-- Minimal worlds are Kratzer's best worlds of the prejacent, with the negated alternatives as
the premises. -/
theorem exhMW_eq_minimals :
    exhMW ALT φ = (≤[compl '' ALT]).minimals φ := by
  have key (u v : W) : (≤[compl '' ALT]).le u v ↔
      {a ∈ ALT | u ∈ a} ⊆ {a ∈ ALT | v ∈ a} := by
    simp only [Preorder.ofLowerSets_le_iff, Set.forall_mem_image, Set.mem_compl_iff,
      Set.subset_def, Set.mem_ofPred_eq, not_imp_not]
    exact ⟨fun h a ⟨ha, hu⟩ ↦ ⟨ha, h ha hu⟩, fun h a ha hu ↦ (h a ⟨ha, hu⟩).2⟩
  ext u
  simp only [mem_exhMW, MinimalFor, Preorder.mem_minimals_iff, key]

/-- Over finitely many alternatives, every world of the prejacent lies above a minimal world. -/
theorem exists_mem_exhMW_le (hfin : ALT.Finite) (hw : w ∈ φ) :
    ∃ u ∈ exhMW ALT φ, {a ∈ ALT | u ∈ a} ⊆ {a ∈ ALT | w ∈ a} := by
  obtain ⟨u, ⟨hu, huw⟩, hmin⟩ := Set.Finite.exists_minimalFor' (fun w ↦ {a ∈ ALT | w ∈ a})
    {v | v ∈ φ ∧ {a ∈ ALT | v ∈ a} ⊆ {a ∈ ALT | w ∈ a}}
    (hfin.finite_subsets.subset (Set.image_subset_iff.2 fun _ _ _ h ↦ h.1)) ⟨w, hw, le_rfl⟩
  exact ⟨u, ⟨hu, fun v hv hvu ↦ hmin ⟨hv, hvu.trans huw⟩ hvu⟩, huw⟩

theorem exhMW_nonempty (hfin : ALT.Finite) (hφ : φ.Nonempty) : (exhMW ALT φ).Nonempty :=
  let ⟨_, hw⟩ := hφ
  let ⟨u, hu, _⟩ := exists_mem_exhMW_le hfin hw
  ⟨u, hu⟩

theorem exhMW_univ : exhMW Set.univ φ = φ := by
  refine Set.Subset.antisymm (fun _ h ↦ h.1) fun u hu ↦ ⟨hu, fun v _ hvu ↦ ?_⟩
  obtain rfl : u = v := (hvu (a := {v}) ⟨trivial, rfl⟩).2
  exact le_rfl

/-- Over finitely many worlds and alternatives, membership in the minimal worlds is decidable. -/
instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    [DecidablePred (· ∈ φ)] : DecidablePred (· ∈ exhMW (Set.range f) φ) := fun u ↦
  decidable_of_iff (u ∈ φ ∧ ∀ v, v ∈ φ → (∀ i, v ∈ f i → u ∈ f i) → ∀ i, u ∈ f i → v ∈ f i) <| by
    simp only [mem_exhMW, MinimalFor, Set.subset_def, Set.mem_ofPred_eq, Set.mem_range,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff, exists_apply_eq_apply, true_and]

instance [Fintype W] {ι : Type*} [Fintype ι] {f : ι → Set W} [∀ i, DecidablePred (· ∈ f i)]
    {A : Set ι} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ φ)] :
    DecidablePred (· ∈ exhMW (f '' A) φ) := fun u ↦
  decidable_of_iff (u ∈ φ ∧ ∀ v, v ∈ φ → (∀ i, i ∈ A → v ∈ f i → u ∈ f i) →
      ∀ i, i ∈ A → u ∈ f i → v ∈ f i) <| by
    simp only [mem_exhMW, MinimalFor, Set.subset_def, Set.mem_ofPred_eq, Set.mem_image,
      and_imp, forall_exists_index, forall_apply_eq_imp_iff₂]
    exact and_congr_right fun _ ↦ forall₂_congr fun v _ ↦
      ⟨fun h hvu i hi hui ↦ ⟨⟨i, hi, rfl⟩, h (fun a ha hva ↦ (hvu a ha hva).2) i hi hui⟩,
        fun h hvu i hi hui ↦ (h (fun a ha hva ↦ ⟨⟨a, ha, rfl⟩, hvu a ha hva⟩) i hi hui).2⟩

/-! ### Representative minimal worlds -/

variable (ALT φ) in
/-- A set of prejacent worlds represents the minimal worlds when every prejacent world lies above
one of its members and no member's true alternatives strictly include another's. -/
structure IsMinimalCover (M : Set W) : Prop where
  mem : ∀ v ∈ M, v ∈ φ
  le : ∀ w ∈ φ, ∃ v ∈ M, {a ∈ ALT | v ∈ a} ⊆ {a ∈ ALT | w ∈ a}
  antisymm : ∀ v ∈ M, ∀ u ∈ M,
    {a ∈ ALT | u ∈ a} ⊆ {a ∈ ALT | v ∈ a} →
      {a ∈ ALT | v ∈ a} ⊆ {a ∈ ALT | u ∈ a}

variable {M : Set W}

theorem IsMinimalCover.exhMW_eq (hM : IsMinimalCover ALT φ M) :
    exhMW ALT φ = {u | u ∈ φ ∧ ∃ v ∈ M, {a ∈ ALT | v ∈ a} =
      {a ∈ ALT | u ∈ a}} := by
  ext u
  refine ⟨fun ⟨hu, hmin⟩ ↦ ⟨hu, ?_⟩, fun ⟨hu, v, hv, hvu⟩ ↦ ⟨hu, fun x hx hxu ↦ ?_⟩⟩
  · obtain ⟨v, hv, hvu⟩ := hM.le u hu
    exact ⟨v, hv, hvu.antisymm (hmin (hM.mem v hv) hvu)⟩
  · obtain ⟨v', hv', hv'x⟩ := hM.le x hx
    exact hvu.ge.trans ((hM.antisymm v hv v' hv' (hv'x.trans (hxu.trans hvu.ge))).trans hv'x)

/-! ### The orderings of a property

A property `P : W → Set E` of individuals that varies with the world gives two families of
propositions for a set `s` of individuals: that an individual of `s` lacks the property, and that
it has it. As premises, the first family ranks a world lower when fewer individuals of `s` have
the property, and the second when more do. The two families together rank worlds by both at
once. -/

section Property

variable {E : Type*} (P : W → Set E) (s pos neg : Set E) (v w : W)

theorem ofLowerSets_image_notMem_le_iff :
    (v ≤[(fun x ↦ {u | x ∉ P u}) '' s] w) ↔ P v ∩ s ⊆ P w ∩ s := by
  rw [Preorder.ofLowerSets_image_le_iff]
  exact ⟨fun h x hx ↦ ⟨by_contra fun hw ↦ h x hx.2 hw hx.1, hx.2⟩,
    fun h x hx hw hv ↦ hw (h ⟨hv, hx⟩).1⟩

theorem ofLowerSets_image_mem_le_iff :
    (v ≤[(fun x ↦ {u | x ∈ P u}) '' s] w) ↔ P w ∩ s ⊆ P v ∩ s := by
  rw [Preorder.ofLowerSets_image_le_iff]
  exact ⟨fun h x hx ↦ ⟨h x hx.2 hx.1, hx.2⟩, fun h x hx hw ↦ (h ⟨hw, hx⟩).1⟩

/-- Under the premises that the individuals of `pos` lack the property and those of `neg` have it,
a world is at least as good as another when fewer individuals of `pos` and more of `neg` have the
property in it. -/
theorem ofLowerSets_image_union_le_iff :
    (v ≤[(fun x ↦ {u | x ∉ P u}) '' pos ∪ (fun x ↦ {u | x ∈ P u}) '' neg] w) ↔
      P v ∩ pos ⊆ P w ∩ pos ∧ P w ∩ neg ⊆ P v ∩ neg := by
  rw [← ofLowerSets_image_notMem_le_iff, ← ofLowerSets_image_mem_le_iff]
  simp only [Preorder.ofLowerSets_le_iff, Set.mem_union]
  exact ⟨fun h ↦ ⟨fun s hs ↦ h s (.inl hs), fun s hs ↦ h s (.inr hs)⟩,
    fun h s hs ↦ hs.elim (h.1 s) (h.2 s)⟩

end Property

end Exhaustification
