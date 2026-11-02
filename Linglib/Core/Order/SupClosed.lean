module

public import Mathlib.Order.SupClosed
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.CompleteLattice.Finset

/-!
# The sup-closure of an indexed family

[UPSTREAM] candidate for `Mathlib/Order/SupClosed.lean`.

The sup-closure of the image of a set of indices is the set of sups of the family over the
nonempty finite sets of those indices, and dually for the inf-closure. For a family of sets
these are the unions and the intersections of its members over nonempty finite sets of indices.
Closing a set under sups does not change its infimum, nor closing it under infs its supremum.

## Main results

* `mem_supClosure_image`, `mem_infClosure_image`: membership in the closure of an image.
* `Set.mem_supClosure_image`, `Set.mem_infClosure_image`: the same for a family of sets.
* `sInf_supClosure`, `sSup_infClosure`: the closures keep the infimum and the supremum.
-/

public section

variable {ι α : Type*}

section SemilatticeSup

variable [SemilatticeSup α] {f : ι → α} {s : Set ι} {a : α}

@[to_dual]
theorem mem_supClosure_image :
    a ∈ supClosure (f '' s) ↔ ∃ (t : Finset ι) (ht : t.Nonempty), ↑t ⊆ s ∧ t.sup' ht f = a := by
  classical
  constructor
  · rintro ⟨T, hT, hTs, rfl⟩
    obtain ⟨t, hts, rfl⟩ := Finset.subset_set_image_iff.1 hTs
    exact ⟨t, Finset.image_nonempty.1 hT, hts, by simp [Finset.sup'_image]⟩
  · rintro ⟨t, ht, hts, rfl⟩
    exact finsetSup'_mem_supClosure ht fun i hi ↦ Set.mem_image_of_mem f (hts hi)

end SemilatticeSup

@[to_dual]
theorem sInf_supClosure [CompleteLattice α] (s : Set α) : sInf (supClosure s) = sInf s :=
  le_antisymm (sInf_le_sInf subset_supClosure) <| le_sInf <| supClosure_min
    (fun _ ↦ sInf_le) fun _ ha _ _ ↦ le_sup_of_le_left ha

namespace Set

variable {W : Type*} {f : ι → Set W} {s : Set ι} {q : Set W}

theorem mem_supClosure_image :
    q ∈ supClosure (f '' s) ↔ ∃ t : Finset ι, t.Nonempty ∧ ↑t ⊆ s ∧ ⋃ i ∈ t, f i = q := by
  simp only [_root_.mem_supClosure_image, Finset.sup'_eq_sup, Finset.sup_set_eq_biUnion]
  exact ⟨fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩, fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩⟩

theorem mem_infClosure_image :
    q ∈ infClosure (f '' s) ↔ ∃ t : Finset ι, t.Nonempty ∧ ↑t ⊆ s ∧ ⋂ i ∈ t, f i = q := by
  simp only [_root_.mem_infClosure_image, Finset.inf'_eq_inf, Finset.inf_set_eq_iInter]
  exact ⟨fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩, fun ⟨t, ht, h⟩ ↦ ⟨t, ht, h⟩⟩

theorem mem_supClosure_range :
    q ∈ supClosure (Set.range f) ↔ ∃ t : Finset ι, t.Nonempty ∧ ⋃ i ∈ t, f i = q := by
  simp [← Set.image_univ, Set.mem_supClosure_image]

theorem mem_infClosure_range :
    q ∈ infClosure (Set.range f) ↔ ∃ t : Finset ι, t.Nonempty ∧ ⋂ i ∈ t, f i = q := by
  simp [← Set.image_univ, Set.mem_infClosure_image]

theorem supClosure_range_eq_image :
    supClosure (Set.range f) = (fun t : Finset ι ↦ ⋃ i ∈ t, f i) '' {t | t.Nonempty} := by
  ext q
  simp only [Set.mem_supClosure_range, Set.mem_image, Set.mem_ofPred_eq]

theorem infClosure_range_eq_image :
    infClosure (Set.range f) = (fun t : Finset ι ↦ ⋂ i ∈ t, f i) '' {t | t.Nonempty} := by
  ext q
  simp only [Set.mem_infClosure_range, Set.mem_image, Set.mem_ofPred_eq]

theorem sInter_supClosure (S : Set (Set W)) : ⋂₀ supClosure S = ⋂₀ S :=
  _root_.sInf_supClosure S

end Set
