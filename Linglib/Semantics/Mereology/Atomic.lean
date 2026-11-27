module

public import Linglib.Core.Order.Grade
public import Mathlib.Order.Interval.Finset.Defs
public import Linglib.Semantics.Mereology.Basic
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Lattice

/-!
# Atomic part structures

A part structure with a null individual is atomic, mathlib's `IsAtomic`, if every individual
other than `⊥` has an atom as a part. Classical mereology leaves the choice open: count domains
are taken to be atomic, while events, matter and time need not be. In an atomic generalized
Boolean algebra an individual is the sum of its atoms and parthood is inclusion of atoms, which is
what lets sums be treated as sets and counted by `Mereology.atomCount`.

## Main definitions

* `Mereology.atomsBelowEmbedding`: an atomic generalized Boolean algebra embeds in the sets of its
  atoms.
* `Mereology.gradeMinOrder`: where individuals have finitely many parts, the algebra is graded by
  the number of atoms.

## Main results

* `IsAtom.le_sup_iff`, `Mereology.atomsBelow_sup`: in a distributive lattice an atom is part of a
  join only by being part of one of the two, so the atoms of a join are the atoms of the two.
* `Mereology.isLUB_atomsBelow`: an individual is the least upper bound of its atoms.
* `Mereology.isGreatest_atomCount_mem_iff`: the largest part of `c` whose number of atoms lies in
  a set of positive numbers is `c`, and there is one only where the number of atoms of `c` does.

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

@[simp] theorem atomsBelow_bot : atomsBelow (⊥ : α) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ha ↦ ha.1.1 (le_bot_iff.1 ha.2)

@[simp] theorem atomCount_bot : atomCount α ⊥ = 0 := by
  rw [atomCount_eq_ncard, atomsBelow_bot, Set.ncard_empty]

end PartialOrder

/-- The atoms of a join are the atoms of the two. -/
theorem atomsBelow_sup [DistribLattice α] [OrderBot α] (x y : α) :
    atomsBelow (x ⊔ y) = atomsBelow x ∪ atomsBelow y :=
  Set.ext fun _ ↦ ⟨fun ha ↦ (ha.1.le_sup_iff.1 ha.2).imp (⟨ha.1, ·⟩) (⟨ha.1, ·⟩),
    fun ha ↦ ha.elim (atomsBelow_mono le_sup_left ·) (atomsBelow_mono le_sup_right ·)⟩

/-- Taking an atom away takes that atom away from the atoms. -/
theorem atomsBelow_sdiff_of_isAtom [GeneralizedBooleanAlgebra α] {a x : α} (ha : IsAtom a) :
    atomsBelow (x \ a) = atomsBelow x \ {a} := by
  ext z
  simp only [mem_atomsBelow, le_sdiff, Set.mem_sdiff, Set.mem_singleton_iff, and_assoc]
  refine and_congr_right fun hz ↦ and_congr_right fun _ ↦ ⟨?_, fun hne ↦ ?_⟩
  · rintro h rfl
    exact hz.1 (disjoint_self.1 h)
  · exact hz.disjoint_of_ne ha hne

section Boolean

variable [GeneralizedBooleanAlgebra α] [IsAtomic α] {c x y : α}

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

theorem atomCount_strictMono (hfin : ∀ x : α, (atomsBelow x).Finite) :
    StrictMono (atomCount α) := fun x y h ↦ by
  simp only [atomCount_eq_ncard]
  exact Set.ncard_lt_ncard
    ⟨atomsBelow_mono h.le, fun hs ↦ h.not_ge (atomsBelow_subset_iff.1 hs)⟩ (hfin y)

theorem atomCount_of_covBy (hfin : ∀ x : α, (atomsBelow x).Finite) (h : x ⋖ y) :
    atomCount α y = atomCount α x + 1 := by
  obtain ⟨d, hd, hdy⟩ := (eq_bot_or_exists_atom_le (y \ x)).resolve_left
    (mt sdiff_eq_bot_iff.1 h.lt.not_ge)
  have hdx : ¬ d ≤ x := fun hx ↦ hd.1 (le_bot_iff.1 ((le_inf hx hdy).trans inf_sdiff_self_right.le))
  have hy : x ⊔ d = y := (h.eq_or_eq le_sup_left (sup_le h.le (hdy.trans sdiff_le))).resolve_left
    fun he ↦ hdx (he ▸ le_sup_right)
  rw [atomCount_eq_ncard, atomCount_eq_ncard, ← hy, atomsBelow_sup, atomsBelow_of_isAtom hd,
    Set.union_singleton, Set.ncard_insert_of_notMem (fun h : d ∈ atomsBelow x ↦ hdx h.2) (hfin x)]

/-- An atomic generalized Boolean algebra whose individuals have finitely many parts is graded by
the number of atoms. -/
@[reducible] noncomputable def gradeMinOrder [LocallyFiniteOrderBot α] : GradeMinOrder ℕ α :=
  have hfin (x : α) : (atomsBelow x).Finite := (Set.finite_Iic x).subset fun _ h ↦ h.2
  { grade := atomCount α
    grade_strictMono := atomCount_strictMono hfin
    covBy_grade := fun _ _ h ↦ Order.covBy_iff_add_one_eq.2 (atomCount_of_covBy hfin h).symm
    isMin_grade := fun a ha ↦ by
      rw [isMin_iff_eq_bot.1 ha, atomCount_bot]
      exact isMin_bot }

/-- Among the parts of `c` whose number of atoms lies in `S`, one that the others are parts of is
`c`: the largest sum of so many atoms of `c` exists only where `c` has so many. -/
theorem isGreatest_atomCount_mem_iff {S : Set ℕ} (h0 : 0 ∉ S) :
    IsGreatest {x | x ≤ c ∧ atomCount α x ∈ S} x ↔ x = c ∧ atomCount α c ∈ S := by
  refine ⟨fun ⟨⟨hxc, hx⟩, hub⟩ ↦ ?_, by rintro ⟨rfl, h⟩; exact ⟨⟨le_rfl, h⟩, fun _ h ↦ h.1⟩⟩
  suffices x = c from ⟨this, this ▸ hx⟩
  by_contra hne
  have hn : (atomsBelow x).ncard ≠ 0 := fun h ↦ h0 (by rwa [atomCount_eq_ncard, h] at hx)
  obtain ⟨d, hd, hdc⟩ := (eq_bot_or_exists_atom_le (c \ x)).resolve_left
    (mt sdiff_eq_bot_iff.1 fun h ↦ hne (hxc.antisymm h))
  have hfin : (atomsBelow x).Finite := Set.finite_of_ncard_ne_zero hn
  obtain ⟨a, ha⟩ := (Set.ncard_pos hfin).1 (Nat.pos_of_ne_zero hn)
  have hdx : ¬ d ≤ x := fun h ↦ hd.1 (le_bot_iff.1 ((le_inf h hdc).trans inf_sdiff_self_right.le))
  have hcard : atomCount α (x \ a ⊔ d) = atomCount α x := by
    rw [atomCount_eq_ncard, atomCount_eq_ncard, atomsBelow_sup,
      atomsBelow_sdiff_of_isAtom ha.1, atomsBelow_of_isAtom hd, Set.union_singleton,
      Set.ncard_insert_of_notMem (fun h : d ∈ atomsBelow x \ {a} ↦ hdx h.1.2) hfin.sdiff,
      Set.ncard_sdiff_singleton_add_one ha hfin]
  exact hdx (le_sup_right.trans
    (hub ⟨sup_le (sdiff_le.trans hxc) (hdc.trans sdiff_le), hcard ▸ hx⟩))

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
