module

public import Linglib.Semantics.Mereology.Classical
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Hovda (2009): What is Classical Mereology?

Classical mereology can be axiomatized with least upper bounds in place of fusions: a partial
order in which every nonempty set has a least upper bound, with Weak Supplementation and
Filtration, the principle that a part of the least upper bound of a set overlaps a member of
the set. Filtration cannot be replaced by a condition on binary sums alone.

For an infinite set `A`, let `FiniteOrUniv A` be the nonempty subsets of `A` that are finite or
all of `A`, ordered by inclusion. Every nonempty set of them has a least upper bound
(`FiniteOrUniv.exists_isLUB`), the union if it is finite and `A` otherwise. Strong
Supplementation holds (`FiniteOrUniv.strongSupplementation`), and so does the paper's
Distributivity for binary sums: a part of `y ⊔ z` is part of `y`, part of `z`, or the sum of a
part of each (`FiniteOrUniv.distributivity`). The structure is not a classical mereology
(`FiniteOrUniv.not_isClassical`): the least upper bound of the singletons other than `{a}` is
`A`, of which `{a}` is a part that overlaps none of them.

## Implementation notes

The paper states the model with Weak Supplementation; the stronger principle holds in it.
Distributivity is stated with `IsLUB` on pairs, the structure being given no binary
sum operation of its own. The paper presents the model as satisfying the definition of a
part-of structure of Landman and the lattice sorts of Krifka, which are not formalized here
from their own texts.

## References

* [hovda-2009]
-/

@[expose] public section

namespace Hovda2009

open Mereology Set

/-- The nonempty subsets of `A` that are finite or all of `A`. -/
abbrev FiniteOrUniv (A : Type*) : Type _ := {S : Set A // S.Nonempty ∧ (S.Finite ∨ S = univ)}

namespace FiniteOrUniv

variable {A : Type*} {x y z s : FiniteOrUniv A}

/-- The singleton of `a`. -/
def single (a : A) : FiniteOrUniv A := ⟨{a}, singleton_nonempty a, .inl (finite_singleton a)⟩

theorem overlap_iff : Overlap x y ↔ (x.1 ∩ y.1).Nonempty :=
  ⟨fun ⟨z, hzx, hzy⟩ ↦ z.2.1.mono (subset_inter hzx hzy), fun ⟨a, hax, hay⟩ ↦
    ⟨single a, singleton_subset_iff.2 hax, singleton_subset_iff.2 hay⟩⟩

/-- Strong Supplementation holds: what is not part of `x` has a member outside `x`, whose
singleton does not overlap `x`. -/
theorem strongSupplementation : StrongSupplementation (FiniteOrUniv A) := fun x y hyx ↦
  let ⟨a, hay, hax⟩ := not_subset.1 hyx
  ⟨single a, singleton_subset_iff.2 hay, fun h ↦ hax (by simpa [single] using overlap_iff.1 h)⟩

variable [Infinite A]

/-- Every nonempty set has a least upper bound: its union if that is finite, and `A`
otherwise. -/
theorem exists_isLUB (S : Set (FiniteOrUniv A)) (hS : S.Nonempty) : ∃ u, IsLUB S u := by
  obtain ⟨x₀, hx₀⟩ := hS
  by_cases hU : (⋃ x ∈ S, x.1).Finite
  · exact ⟨⟨⋃ x ∈ S, x.1, x₀.2.1.mono (subset_biUnion_of_mem (u := fun x ↦ x.1) hx₀), .inl hU⟩,
      fun x hx ↦ subset_biUnion_of_mem (u := fun x ↦ x.1) hx, fun u hu ↦ iUnion₂_subset hu⟩
  · refine ⟨⟨univ, univ_nonempty, .inr rfl⟩, fun x _ ↦ subset_univ _, fun u hu ↦ ?_⟩
    rcases u.2.2 with hfin | huniv
    · exact absurd (hfin.subset (iUnion₂_subset hu)) hU
    · exact huniv.ge

omit [Infinite A] in
theorem isLUB_pair_iff : IsLUB {y, z} s ↔ s.1 = y.1 ∪ z.1 := by
  have hmem : (y.1 ∪ z.1).Nonempty ∧ ((y.1 ∪ z.1).Finite ∨ y.1 ∪ z.1 = univ) :=
    ⟨y.2.1.inl, by
      rcases y.2.2 with hy | hy
      · rcases z.2.2 with hz | hz
        · exact .inl (hy.union hz)
        · exact .inr (by rw [hz, union_univ])
      · exact .inr (by rw [hy, univ_union])⟩
  have hlub : IsLUB {y, z} (⟨y.1 ∪ z.1, hmem⟩ : FiniteOrUniv A) :=
    ⟨by rintro _ (rfl | rfl); exacts [subset_union_left, subset_union_right],
      fun u hu ↦ union_subset (hu (.inl rfl)) (hu (.inr rfl))⟩
  exact ⟨fun h ↦ congrArg Subtype.val (h.unique hlub), fun h ↦ by
    rwa [show s = ⟨y.1 ∪ z.1, hmem⟩ from Subtype.ext h]⟩

/-- Distributivity: a part of the sum of `y` and `z` is part of `y`, part of `z`, or the sum of
a part of each. -/
theorem distributivity (hs : IsLUB {y, z} s) (hx : x ≤ s) :
    x ≤ y ∨ x ≤ z ∨ ∃ y' ≤ y, ∃ z' ≤ z, IsLUB {y', z'} x := by
  have hs' : s.1 = y.1 ∪ z.1 := isLUB_pair_iff.1 hs
  have hxs : x.1 ⊆ y.1 ∪ z.1 := hs' ▸ hx
  by_cases hxy : x ≤ y
  · exact .inl hxy
  by_cases hxz : x ≤ z
  · exact .inr (.inl hxz)
  obtain ⟨a, hax, hay⟩ := not_subset.1 hxy
  obtain ⟨b, hbx, hbz⟩ := not_subset.1 hxz
  have hfin : x.1.Finite := by
    refine x.2.2.resolve_right fun hx ↦ ?_
    have huniv : y.1 ∪ z.1 = univ := univ_subset_iff.1 (by rwa [hx] at hxs)
    rcases y.2.2 with hy | hy
    · rcases z.2.2 with hz | hz
      · exact infinite_univ (huniv ▸ hy.union hz)
      · exact hxz (show x.1 ⊆ z.1 by rw [hz]; exact subset_univ _)
    · exact hxy (show x.1 ⊆ y.1 by rw [hy]; exact subset_univ _)
  refine .inr (.inr ⟨⟨x.1 ∩ y.1, ⟨b, hbx, (hxs hbx).resolve_right hbz⟩,
      .inl (hfin.subset inter_subset_left)⟩, inter_subset_right,
    ⟨x.1 ∩ z.1, ⟨a, hax, (hxs hax).resolve_left hay⟩, .inl (hfin.subset inter_subset_left)⟩,
    inter_subset_right, isLUB_pair_iff.2 ?_⟩)
  rw [← inter_union_distrib_left, inter_eq_left.2 hxs]

/-- The singletons other than `{a}` have least upper bound `A`, of which `{a}` is a part that
overlaps none of them. -/
theorem isLUB_singles_not_overlap (a : A) :
    IsLUB {x : FiniteOrUniv A | ∃ b ≠ a, x = single b} ⟨univ, univ_nonempty, .inr rfl⟩ ∧
      ∀ x ∈ {x : FiniteOrUniv A | ∃ b ≠ a, x = single b}, ¬ Overlap (single a) x := by
  refine ⟨⟨fun x _ ↦ subset_univ _, fun u hu ↦ ?_⟩, ?_⟩
  · have hsub : {a}ᶜ ⊆ u.1 := fun b hb ↦ hu ⟨b, hb, rfl⟩ (mem_singleton b)
    rcases u.2.2 with hfin | huniv
    · exact absurd (hfin.subset hsub) (finite_singleton a).infinite_compl
    · exact huniv.ge
  · rintro _ ⟨b, hb, rfl⟩ h
    exact hb (by simpa [single, eq_comm] using overlap_iff.1 h)

/-- The structure is not a classical mereology: in one, the least upper bound of a nonempty
set is its fusion, each part of which overlaps a member. -/
theorem not_isClassical : ¬ IsClassical (FiniteOrUniv A) := fun h ↦ by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨hlub, hno⟩ := isLUB_singles_not_overlap a
  have hne : {x : FiniteOrUniv A | ∃ b ≠ a, x = single b}.Nonempty := ⟨single b, b, hb, rfl⟩
  obtain ⟨x, hx, ho⟩ := (hlub.isFusion h.remainder hne).2 (single a)
    (show (single a).1 ⊆ univ from subset_univ _)
  exact hno x hx ho

end FiniteOrUniv

end Hovda2009
