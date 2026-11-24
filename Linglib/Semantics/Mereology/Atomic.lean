module

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

## Main results

* `IsAtom.le_sup_iff`, `Mereology.atomsBelow_sup`: in a distributive lattice an atom is part of a
  join only by being part of one of the two, so the atoms of a join are the atoms of the two.
* `Mereology.isLUB_atomsBelow`: an individual is the least upper bound of its atoms.
* `Mereology.isGreatest_atomCount_iff`: the largest part of `c` with `n` atoms is `c`, and there
  is one only where `c` has `n` atoms.
* `Mereology.minimal_ne_bot_and_not_isAtom_iff`: the minimal individuals that are neither null nor
  atoms are those with two atoms.

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

/-- Among the parts of `c` with `n` atoms, one that the others are parts of is `c`: there is a
largest sum of `n` atoms of `c` only where `c` has `n` atoms. -/
theorem isGreatest_atomCount_iff {n : ℕ} (hn : n ≠ 0) :
    IsGreatest {x | x ≤ c ∧ atomCount α x = n} x ↔ x = c ∧ atomCount α c = n := by
  simp only [atomCount_eq_ncard]
  refine ⟨fun ⟨⟨hxc, hx⟩, hub⟩ ↦ ?_, by rintro ⟨rfl, h⟩; exact ⟨⟨le_rfl, h⟩, fun _ h ↦ h.1⟩⟩
  suffices x = c from ⟨this, this ▸ hx⟩
  by_contra hne
  obtain ⟨d, hd, hdc⟩ := (eq_bot_or_exists_atom_le (c \ x)).resolve_left
    (mt sdiff_eq_bot_iff.1 fun h ↦ hne (hxc.antisymm h))
  have hfin : (atomsBelow x).Finite := Set.finite_of_ncard_ne_zero (hx ▸ hn)
  obtain ⟨a, ha⟩ := (Set.ncard_pos hfin).1 (hx ▸ Nat.pos_of_ne_zero hn)
  have hdx : ¬ d ≤ x := fun h ↦ hd.1 (le_bot_iff.1 ((le_inf h hdc).trans inf_sdiff_self_right.le))
  have hcard : (atomsBelow (x \ a ⊔ d)).ncard = n := by
    rw [atomsBelow_sup, atomsBelow_sdiff_of_isAtom ha.1, atomsBelow_of_isAtom hd,
      Set.union_singleton, Set.ncard_insert_of_notMem
        (fun h : d ∈ atomsBelow x \ {a} ↦ hdx h.1.2) hfin.sdiff,
      Set.ncard_sdiff_singleton_add_one ha hfin, hx]
  exact hdx (le_sup_right.trans (hub ⟨sup_le (sdiff_le.trans hxc) (hdc.trans sdiff_le), hcard⟩))

/-- The minimal individuals that are neither null nor atoms are those with two atoms. -/
theorem minimal_ne_bot_and_not_isAtom_iff :
    Minimal (fun y : α ↦ y ≠ ⊥ ∧ ¬ IsAtom y) x ↔ atomCount α x = 2 := by
  rw [atomCount_eq_ncard]
  constructor
  · rintro ⟨⟨hx, hxa⟩, hmin⟩
    obtain ⟨a, ha, hax⟩ := (eq_bot_or_exists_atom_le x).resolve_left hx
    obtain ⟨b, hb, hbx⟩ := (eq_bot_or_exists_atom_le (x \ a)).resolve_left
      (mt sdiff_eq_bot_iff.1 fun h ↦ hxa ((ha.le_iff.1 h).resolve_left hx ▸ ha))
    have hab : a ≠ b := by
      rintro rfl
      exact ha.1 (le_bot_iff.1 ((le_inf hbx le_rfl).trans inf_sdiff_self_left.le))
    have hle : x ≤ a ⊔ b := hmin ⟨fun h ↦ ha.1 (le_bot_iff.1 (le_sup_left.trans h.le)),
      fun h ↦ hab (((h.le_iff.1 le_sup_left).resolve_left ha.1).trans
        ((h.le_iff.1 le_sup_right).resolve_left hb.1).symm)⟩ (sup_le hax (hbx.trans sdiff_le))
    rw [hle.antisymm (sup_le hax (hbx.trans sdiff_le)), atomsBelow_sup, atomsBelow_of_isAtom ha,
      atomsBelow_of_isAtom hb, Set.singleton_union, Set.ncard_pair hab]
  · intro h
    obtain ⟨a, b, hab, hx⟩ := Set.ncard_eq_two.1 h
    have ha : a ∈ atomsBelow x := hx ▸ Set.mem_insert _ _
    have hb : b ∈ atomsBelow x := hx ▸ Set.mem_insert_of_mem _ rfl
    refine ⟨⟨fun h ↦ ha.1.1 (le_bot_iff.1 (h ▸ ha.2)), fun hx' ↦ hab
      (((hx'.le_iff.1 ha.2).resolve_left ha.1.1).trans
        ((hx'.le_iff.1 hb.2).resolve_left hb.1.1).symm)⟩, fun y ⟨hy, hya⟩ hyx ↦ ?_⟩
    obtain ⟨d, hd, hdy⟩ := (eq_bot_or_exists_atom_le y).resolve_left hy
    obtain ⟨e, he, hey⟩ := (eq_bot_or_exists_atom_le (y \ d)).resolve_left
      (mt sdiff_eq_bot_iff.1 fun h ↦ hya ((hd.le_iff.1 h).resolve_left hy ▸ hd))
    have hde : d ≠ e := by
      rintro rfl
      exact hd.1 (le_bot_iff.1 ((le_inf hey le_rfl).trans inf_sdiff_self_left.le))
    have hd' : d ∈ ({a, b} : Set α) := hx ▸ ⟨hd, hdy.trans hyx⟩
    have he' : e ∈ ({a, b} : Set α) := hx ▸ ⟨he, (hey.trans sdiff_le).trans hyx⟩
    refine atomsBelow_subset_iff.1 (hx ▸ ?_)
    rintro z (rfl | rfl) <;> rcases hd' with rfl | rfl <;> rcases he' with rfl | rfl <;>
      first | exact ⟨hd, hdy⟩ | exact ⟨he, hey.trans sdiff_le⟩ | exact absurd rfl hde

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
