module

public import Linglib.Semantics.Questions.Exhaustivity
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
the same partition, the kernel of that map.

## References

* [dayal-1996]
* [spector-2008]
* [fox-2007]
* [fox-2018]
-/

@[expose] public section

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

end Question
