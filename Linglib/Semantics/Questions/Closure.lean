module

public import Linglib.Semantics.Questions.HamblinSet
public import Linglib.Core.Order.OfCriteria
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.CompleteLattice.Finset
public import Linglib.Core.Order.SupClosed

/-!
# Hamblin sets closed under conjunction or disjunction

A wh-question over atomic answers `a i` denotes, under Dayal's sum-closed restrictor, the closure
of the atoms under conjunction, `infClosure (Set.range a)`, the conjunctions over nonempty groups
of atoms; under Spector's higher-order quantification, pruned to disjunctions of atoms as in Fox,
it denotes their closure under disjunction, `supClosure (Set.range a)`. Both families are read
off the atoms true at a world, `Preorder.satisfied` with the atoms as criteria, and both induce
the same partition, the kernel of that map. Closing a finite family under conjunction reduces
Dayal's presupposition to the existence of a true member.

## References

* [dayal-1996]
* [spector-2008]
* [fox-2007]
* [fox-2018]
-/

public section

namespace Question

variable {W ι : Type*} {a : ι → Set W}

@[simp] theorem mem_satisfied_iff {w : W} {i : ι} :
    i ∈ Preorder.satisfied (fun v i ↦ v ∈ a i) Set.univ w ↔ w ∈ a i :=
  Preorder.mem_satisfied_univ

theorem mem_biInter_iff_subset {S : Finset ι} {w : W} :
    w ∈ ⋂ i ∈ S, a i ↔ ↑S ⊆ Preorder.satisfied (fun v i ↦ v ∈ a i) Set.univ w :=
  Set.mem_iInter₂.trans ⟨fun h _ hi ↦ ⟨trivial, h _ hi⟩, fun h _ hi ↦ (h hi).2⟩

theorem partition_infClosure_range :
    partition (infClosure (Set.range a)) =
      Setoid.ker (Preorder.satisfied (fun v i ↦ v ∈ a i) Set.univ) := by
  ext v w
  rw [partition_iff, Setoid.ker_def]
  constructor
  · intro h
    ext i
    simpa only [Preorder.mem_satisfied, Set.mem_univ, true_and] using
      h _ (subset_infClosure (Set.mem_range_self i))
  · intro h q hq
    obtain ⟨S, -, rfl⟩ := Set.mem_infClosure_range.1 hq
    rw [mem_biInter_iff_subset, mem_biInter_iff_subset, h]

theorem partition_supClosure_range :
    partition (supClosure (Set.range a)) =
      Setoid.ker (Preorder.satisfied (fun v i ↦ v ∈ a i) Set.univ) := by
  ext v w
  rw [partition_iff, Setoid.ker_def]
  constructor
  · intro h
    ext i
    simpa only [Preorder.mem_satisfied, Set.mem_univ, true_and] using
      h _ (subset_supClosure (Set.mem_range_self i))
  · intro h q hq
    obtain ⟨S, -, rfl⟩ := Set.mem_supClosure_range.1 hq
    simp only [Set.ext_iff, Preorder.mem_satisfied, Set.mem_univ, true_and] at h
    simp only [Set.mem_iUnion, exists_prop, h]

theorem partition_infClosure_range_eq_supClosure_range :
    partition (infClosure (Set.range a)) = partition (supClosure (Set.range a)) :=
  partition_infClosure_range.trans partition_supClosure_range.symm

/-- The conjunction of the members true at a world is the strongest true member of the closure
of a finite family under conjunction. -/
theorem isStrongestTrueAnswer_infClosure_image {s : Set ι} {w : W} (hs : s.Finite)
    (h : ∃ i ∈ s, w ∈ a i) :
    IsStrongestTrueAnswer (infClosure (a '' s)) w (⋂ i ∈ {i ∈ s | w ∈ a i}, a i) := by
  obtain ⟨i, his, hi⟩ := h
  have hT : {i ∈ s | w ∈ a i}.Finite := hs.subset (Set.sep_subset _ _)
  refine ⟨⟨Set.mem_infClosure_image.2 ⟨hT.toFinset, ⟨i, by simp [his, hi]⟩,
    by simp +contextual [Set.subset_def], by simp⟩, by simp +contextual⟩, ?_⟩
  rintro _ ⟨hq, hw⟩
  obtain ⟨t, -, hts, rfl⟩ := Set.mem_infClosure_image.1 hq
  exact Set.subset_iInter₂ fun j hj ↦
    Set.biInter_subset_of_mem (s := {i ∈ s | w ∈ a i}) ⟨hts hj, Set.mem_iInter₂.1 hw j hj⟩

theorem presupposition_infClosure_image {s : Set ι} (hs : s.Finite) :
    presupposition (infClosure (a '' s)) = ⋃ i ∈ s, a i := by
  refine Set.ext fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ⟨_, isStrongestTrueAnswer_infClosure_image hs
    (by simpa using h)⟩⟩
  obtain ⟨_, hq, hw⟩ := h.exists_mem
  obtain ⟨t, ⟨i, hi⟩, hts, rfl⟩ := Set.mem_infClosure_image.1 hq
  exact Set.mem_biUnion (hts hi) (Set.mem_iInter₂.1 hw i hi)

end Question
