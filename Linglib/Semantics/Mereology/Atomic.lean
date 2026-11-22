module

public import Linglib.Semantics.Mereology.Basic
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Lattice

/-!
# Atomic part structures

A part structure with a null individual is atomic, mathlib's `IsAtomic`, if every individual
other than `⊥` has an atom as a part. Classical mereology leaves the choice open: count domains
are taken to be atomic, while events, matter and time need not be. In an atomic generalized
Boolean algebra every individual is the least upper bound of its atoms
(`Mereology.isLUB_atomsBelow`) and parthood is inclusion of atoms
(`Mereology.atomsBelowEmbedding`), which is what lets sums be treated as sets. In a distributive
lattice an atom is part of a join only by being part of one of the two
(`IsAtom.le_sup_iff`), so the atoms of a join are the atoms of the two
(`Mereology.atomsBelow_sup`).

## References

* [champollion-krifka-2016]
-/

@[expose] public section

/-- An atom is part of a join iff it is part of one of the two, as *Ann* is part of the sum of
some girls only by being one of them. -/
theorem IsAtom.le_sup_iff {α : Type*} [DistribLattice α] [OrderBot α] {a x y : α}
    (ha : IsAtom a) : a ≤ x ⊔ y ↔ a ≤ x ∨ a ≤ y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.elim le_sup_of_le_left le_sup_of_le_right⟩
  by_contra hno
  rw [not_or] at hno
  have hx : a ⊓ x = ⊥ := (ha.le_iff.1 inf_le_left).resolve_right fun e ↦ hno.1 (inf_eq_left.1 e)
  have hy : a ⊓ y = ⊥ := (ha.le_iff.1 inf_le_left).resolve_right fun e ↦ hno.2 (inf_eq_left.1 e)
  have : a ⊓ (x ⊔ y) = ⊥ := by rw [inf_sup_left, hx, hy, sup_bot_eq]
  exact ha.1 ((inf_eq_left.2 h).symm.trans this)

namespace Mereology

variable {α : Type*}

section PartialOrder

variable [PartialOrder α] [OrderBot α] {x y : α}

theorem atomsBelow_nonempty [IsAtomic α] (hx : x ≠ ⊥) : (atomsBelow x).Nonempty :=
  (eq_bot_or_exists_atom_le x).resolve_left hx

theorem atomsBelow_mono (h : x ≤ y) : atomsBelow x ⊆ atomsBelow y :=
  fun _ ha ↦ ⟨ha.1, ha.2.trans h⟩

end PartialOrder

/-- The atoms of a join are the atoms of the two. -/
theorem atomsBelow_sup [DistribLattice α] [OrderBot α] (x y : α) :
    atomsBelow (x ⊔ y) = atomsBelow x ∪ atomsBelow y :=
  Set.ext fun _ ↦ ⟨fun ha ↦ (ha.1.le_sup_iff.1 ha.2).imp (⟨ha.1, ·⟩) (⟨ha.1, ·⟩),
    fun ha ↦ ha.elim (atomsBelow_mono le_sup_left ·) (atomsBelow_mono le_sup_right ·)⟩

section Boolean

variable [GeneralizedBooleanAlgebra α] [IsAtomic α] {x y : α}

/-- In an atomic generalized Boolean algebra, parthood is inclusion of atoms. -/
theorem atomsBelow_subset_iff : atomsBelow x ⊆ atomsBelow y ↔ x ≤ y := by
  refine ⟨fun h ↦ ?_, atomsBelow_mono⟩
  by_contra hxy
  obtain ⟨a, ha, hle⟩ :=
    (eq_bot_or_exists_atom_le (x \ y)).resolve_left (mt sdiff_eq_bot_iff.1 hxy)
  exact ha.1 (le_bot_iff.1
    ((le_inf hle (h ⟨ha, hle.trans sdiff_le⟩).2).trans inf_sdiff_self_left.le))

/-- An individual of an atomic generalized Boolean algebra is the sum of its atoms. -/
theorem isLUB_atomsBelow (x : α) : IsLUB (atomsBelow x) x :=
  ⟨fun _ h ↦ h.2, fun _ hu ↦ atomsBelow_subset_iff.1 fun _ ha ↦ ⟨ha.1, hu ha⟩⟩

variable (α) in
/-- An atomic generalized Boolean algebra embeds in the sets of its atoms, parthood going to
inclusion. -/
def atomsBelowEmbedding : α ↪o Set α :=
  OrderEmbedding.ofMapLEIff atomsBelow fun _ _ ↦ atomsBelow_subset_iff

@[simp]
theorem atomsBelowEmbedding_apply (x : α) : atomsBelowEmbedding α x = atomsBelow x := rfl

end Boolean

/-! ### Atomicity and sums

Atomicity is not preserved along sums, so the number of a coordination is not a function of its
conjuncts' numbers. -/

section

variable {E β : Type*} [SemilatticeSup E] [OrderBot E] [SemilatticeSup β] {a b : E}

/-- No map preserving sums identifies two distinct atoms while keeping atoms apart from
non-atoms: an atom summed with itself is an atom, and summed with another is not. -/
theorem not_forall_isAtom_iff_of_map_eq (f : SupHom E β) (hab : a ≠ b) (ha : IsAtom a)
    (hb : IsAtom b) (hf : f a = f b) : ¬ ∀ x y, f x = f y → (IsAtom x ↔ IsAtom y) := by
  intro hat
  have h₁ : f a = f (b ⊔ a) := by rw [map_sup, ← hf, sup_idem]
  exact not_isAtom_sup_of_ne hb ha (Ne.symm hab) ((hat _ _ h₁).1 ha)

end

end Mereology
