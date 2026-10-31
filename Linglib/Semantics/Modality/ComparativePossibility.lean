module

public import Linglib.Core.Order.Antisymmetrization
public import Mathlib.Basic.Rel
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Order.RelClasses

/-!
# Comparative possibility

This file defines comparative possibility, the lifting of a relation on worlds to a relation on
propositions. In Lewis's sense `A` is at least as possible as `B` when every `B`-world is
dominated by some `A`-world. Kratzer's revised notion compares only the worlds in exactly one of
the two propositions: `A` is at least as good a possibility as `B` unless some world of `B \ A`
strictly dominates every world of `A \ B`. Over a total relation the revised notion is Lewis's
notion applied to the two difference sets, and the strict part of Lewis's notion asks for a
single `A`-world strictly dominating every `B`-world.

## Main definitions

* `ComparativePossibility.Lewis`: Lewis's comparative possibility.
* `ComparativePossibility.Kratzer`: Kratzer's revised comparative possibility.

## Main statements

* `ComparativePossibility.asymmRel_lewis_iff`: the strict part over a total relation.
* `ComparativePossibility.kratzer_iff_lewis_sdiff`: the revised notion over a total relation.
* `ComparativePossibility.kratzer_sdiff_sdiff_iff`: the revised notion sees only the differences.

## References

* [lewis-1973b]
* [kratzer-1991]
* [kratzer-2012]
-/

@[expose] public section

namespace ComparativePossibility

variable {α : Type*}

/-- `Lewis r A B` says that `A` is at least as possible as `B`: every world of `B` is
`r`-dominated by some world of `A`, that is `B` lies in the image of `A` under `r`. -/
def Lewis (r : α → α → Prop) (A B : Set α) : Prop :=
  B ⊆ SetRel.image {p : α × α | r p.1 p.2} A

/-- `Kratzer r A B` says that `A` is at least as good a possibility as `B` in Kratzer's revised
sense: no world of `B \ A` strictly dominates every world of `A \ B` (Kratzer 2012, p. 41). -/
def Kratzer (r : α → α → Prop) (A B : Set α) : Prop :=
  ¬ ∃ b ∈ B \ A, ∀ a ∈ A \ B, AsymmRel r b a

variable {r : α → α → Prop} {A A' B B' C : Set α} {b : α}

/-! ### Lewis's comparative possibility -/

theorem lewis_iff : Lewis r A B ↔ ∀ b ∈ B, ∃ a ∈ A, r a b := Iff.rfl

theorem not_lewis_iff : ¬ Lewis r A B ↔ ∃ b ∈ B, ∀ a ∈ A, ¬ r a b := by
  simp [lewis_iff]

theorem lewis_empty (A : Set α) : Lewis r A ∅ := Set.empty_subset _

theorem lewis_empty_left_iff : Lewis r ∅ B ↔ B = ∅ := by
  rw [Lewis, SetRel.image_empty_right, Set.subset_empty_iff]

theorem lewis_singleton_iff : Lewis r A {b} ↔ ∃ a ∈ A, r a b :=
  Set.singleton_subset_iff

theorem lewis_of_subset [Std.Refl r] (h : B ⊆ A) : Lewis r A B :=
  fun b hb ↦ ⟨b, h hb, refl_of r b⟩

instance [Std.Refl r] : Std.Refl (Lewis r) := ⟨fun _ ↦ lewis_of_subset subset_rfl⟩

theorem Lewis.mono_left (h : Lewis r A B) (hA : A ⊆ A') : Lewis r A' B :=
  h.trans (SetRel.image_mono hA)

theorem Lewis.anti_right (h : Lewis r A B) (hB : B' ⊆ B) : Lewis r A B' :=
  hB.trans h

theorem Lewis.union (hB : Lewis r A B) (hC : Lewis r A C) : Lewis r A (B ∪ C) :=
  Set.union_subset hB hC

theorem Lewis.trans [IsTrans α r] (hAB : Lewis r A B) (hBC : Lewis r B C) : Lewis r A C :=
  fun _ hc ↦
    let ⟨_, hb, hbc⟩ := hBC hc
    let ⟨a, ha, hab⟩ := hAB hb
    ⟨a, ha, _root_.trans hab hbc⟩

instance [IsTrans α r] : IsTrans (Set α) (Lewis r) := ⟨fun _ _ _ ↦ Lewis.trans⟩

/-- Over a total relation any two propositions compare. -/
instance [Std.Total r] : Std.Total (Lewis r) where
  total _ _ := or_iff_not_imp_left.2 fun h a ha ↦
    let ⟨b, hb, hab⟩ := not_lewis_iff.1 h
    ⟨b, hb, (total_of r a b).resolve_left (hab a ha)⟩

/-- Over a total relation, `A` is more possible than `B` exactly when some world of `A` strictly
dominates every world of `B`. -/
theorem asymmRel_lewis_iff [Std.Total r] :
    AsymmRel (Lewis r) A B ↔ ∃ a ∈ A, ∀ b ∈ B, AsymmRel r a b := by
  refine ⟨fun ⟨_, h⟩ ↦ ?_, fun ⟨a, ha, h⟩ ↦ ⟨fun b hb ↦ ⟨a, ha, (h b hb).1⟩, fun h' ↦ ?_⟩⟩
  · obtain ⟨a, ha, hab⟩ := not_lewis_iff.1 h
    exact ⟨a, ha, fun b hb ↦ ⟨(total_of r a b).resolve_right (hab b hb), hab b hb⟩⟩
  · obtain ⟨b, hb, hba⟩ := h' ha
    exact (h b hb).2 hba

/-! ### Kratzer's revised comparative possibility -/

theorem kratzer_iff : Kratzer r A B ↔ ∀ b ∈ B \ A, ∃ a ∈ A \ B, ¬ AsymmRel r b a := by
  simp [Kratzer, and_assoc]

/-- The revised notion sees only the worlds in exactly one of the two propositions. -/
theorem kratzer_sdiff_sdiff_iff : Kratzer r (A \ B) (B \ A) ↔ Kratzer r A B := by
  rw [Kratzer, Kratzer, sdiff_eq_left.2 disjoint_sdiff_sdiff, sdiff_eq_left.2 disjoint_sdiff_sdiff]

theorem kratzer_of_subset (h : B ⊆ A) : Kratzer r A B := fun ⟨_, hb, _⟩ ↦ hb.2 (h hb.1)

instance : Std.Refl (Kratzer r) := ⟨fun _ ↦ kratzer_of_subset subset_rfl⟩

theorem kratzer_univ_iff : Kratzer r A Set.univ ↔ A = Set.univ := by
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun h ↦ h ▸ kratzer_of_subset subset_rfl⟩
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem A).1 hne
  exact h ⟨b, ⟨Set.mem_univ b, hb⟩, fun a ha ↦ absurd (Set.mem_univ a) ha.2⟩

/-- Over a total relation, `A` is at least as good a possibility as `B` exactly when `A \ B` is
at least as possible as `B \ A` in Lewis's sense. -/
theorem kratzer_iff_lewis_sdiff [Std.Total r] : Kratzer r A B ↔ Lewis r (A \ B) (B \ A) := by
  rw [Kratzer, ← asymmRel_lewis_iff, AsymmRel, not_and_not_right]
  exact ⟨fun h ↦ (total_of (Lewis r) (A \ B) (B \ A)).elim id h, fun h _ ↦ h⟩

/-- When `A` is disjoint from both alternatives the revised notion is closed under their union,
the disjunction problem it shares with Lewis's notion. -/
theorem kratzer_union_of_disjoint (hB : Disjoint A B) (hC : Disjoint A C) (hAB : Kratzer r A B)
    (hAC : Kratzer r A C) : Kratzer r A (B ∪ C) := by
  rintro ⟨b, ⟨hb | hb, hbA⟩, hall⟩
  · exact hAB ⟨b, ⟨hb, hbA⟩, fun a ha ↦
      hall a ⟨ha.1, fun h ↦ h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩
  · exact hAC ⟨b, ⟨hb, hbA⟩, fun a ha ↦
      hall a ⟨ha.1, fun h ↦ h.elim (Set.disjoint_left.mp hB ha.1) (Set.disjoint_left.mp hC ha.1)⟩⟩

end ComparativePossibility
