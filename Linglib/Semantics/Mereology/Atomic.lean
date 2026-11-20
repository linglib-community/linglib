module

public import Linglib.Semantics.Mereology.Sum
public import Mathlib.Order.Hom.Lattice

/-!
# Atomic and atomless part structures

A part structure is atomic if every non-null individual has an atom as a part, and atomless if
every non-null individual has a non-null proper part. Classical mereology leaves the choice
open: count domains are taken to be atomic, while events, matter and time need not be. In an
atomic structure every individual [is the sum of its atoms](##Mereology.isSum_atomsBelow), the
atoms of a sum [are those of its members](##Mereology.IsSum.atomsBelow_eq), and if the structure
is strongly supplemented parthood is [inclusion of atoms](##Mereology.atomsBelowEmbedding), which
is what lets sums be treated as sets.

## References

* [champollion-krifka-2016]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

/-- A part structure is atomic ([champollion-krifka-2016]) if every non-null individual has an
atom as a part. -/
class Atomic (α : Type*) [PartialOrder α] : Prop where
  exists_atom_le ⦃x : α⦄ : ¬ IsBot x → ∃ a, Atom a ∧ a ≤ x

/-- A part structure is atomless ([champollion-krifka-2016]) if every non-null individual has a
non-null proper part. -/
class Atomless (α : Type*) [PartialOrder α] : Prop where
  exists_lt ⦃x : α⦄ : ¬ IsBot x → ∃ y < x, ¬ IsBot y

section PartialOrder

variable [PartialOrder α] {x y : α}

instance [WellFoundedLT α] : Atomic α := ⟨fun _ h ↦ exists_atom_le h⟩

instance [OrderBot α] [IsAtomic α] : Atomic α where
  exists_atom_le x hx :=
    let ⟨a, ha, hax⟩ := (eq_bot_or_exists_atom_le x).resolve_left (mt isBot_iff_eq_bot.2 hx)
    ⟨a, atom_iff_isAtom.2 ha, hax⟩

/-- A part structure is atomless iff it has no atoms. -/
theorem atomless_iff : Atomless α ↔ ∀ x : α, ¬ Atom x :=
  ⟨fun h x hx ↦ let ⟨y, hy, hy0⟩ := h.exists_lt hx.not_isBot; hy.ne (hx.eq hy.le hy0),
    fun h ↦ ⟨fun x hx ↦ by
      by_contra! hall
      exact h x ⟨hx, fun y hy hyx ↦
        (eq_or_lt_of_le hyx).elim (·.ge) fun hlt ↦ absurd (hall y hlt) hy⟩⟩⟩

/-- In a part structure that is atomic and atomless every individual is null. -/
theorem isBot_of_atomic_of_atomless [Atomic α] [Atomless α] (x : α) : IsBot x := by
  by_contra hx
  obtain ⟨a, ha, -⟩ := Atomic.exists_atom_le hx
  exact atomless_iff.1 ‹_› a ha

/-- A non-null individual of an atomic part structure has an atom below it. -/
theorem atomsBelow_nonempty [Atomic α] (hx : ¬ IsBot x) : (atomsBelow x).Nonempty :=
  Atomic.exists_atom_le hx

/-- An individual of an atomic part structure is the sum of its atoms. -/
theorem isSum_atomsBelow [Atomic α] (x : α) : IsSum (atomsBelow x) x :=
  ⟨fun _ h ↦ h.2, fun _ hy hy0 ↦
    let ⟨a, ha, hay⟩ := Atomic.exists_atom_le hy0
    ⟨a, ⟨ha, hay.trans hy⟩, (Overlap.of_le ha.not_isBot hay).symm⟩⟩

theorem atomsBelow_mono (h : x ≤ y) : atomsBelow x ⊆ atomsBelow y :=
  fun _ ha ↦ ⟨ha.1, ha.2.trans h⟩

/-- The atoms of a sum are the atoms of its members. -/
theorem IsSum.atomsBelow_eq {P : Set α} {t : α} (h : IsSum P t) :
    atomsBelow t = ⋃ x ∈ P, atomsBelow x := by
  refine Set.Subset.antisymm (fun a ha ↦ ?_)
    (Set.iUnion₂_subset fun x hx ↦ atomsBelow_mono (h.1 x hx))
  obtain ⟨x, hx, q, hq, hqa, hqx⟩ := h.2 a ha.2 ha.1.not_isBot
  exact Set.mem_iUnion₂.2 ⟨x, hx, ha.1, ha.1.eq hqa hq ▸ hqx⟩

/-- The sum of a set of atoms has exactly those atoms as parts. -/
theorem IsSum.atomsBelow_eq_of_forall_atom {S : Set α} {t : α} (h : IsSum S t)
    (hS : ∀ a ∈ S, Atom a) : atomsBelow t = S := by
  rw [h.atomsBelow_eq]
  exact Set.Subset.antisymm
    (Set.iUnion₂_subset fun a ha ↦ (atomsBelow_of_atom (hS a ha)).subset.trans
      (Set.singleton_subset_iff.2 ha))
    fun a ha ↦ Set.mem_iUnion₂.2 ⟨a, ha, hS a ha, le_rfl⟩

/-- The atoms of a join are the atoms of the two. -/
theorem atomsBelow_sup {α : Type*} [SemilatticeSup α] [SupIsSum α] (x y : α) :
    atomsBelow (x ⊔ y) = atomsBelow x ∪ atomsBelow y := by
  rw [(isSum_sup x y).atomsBelow_eq]
  ext a
  simp only [Set.mem_iUnion, Set.mem_union]
  exact ⟨by rintro ⟨_, rfl | rfl, h⟩ <;> simp [h], by
    rintro (h | h)
    exacts [⟨x, .inl rfl, h⟩, ⟨y, .inr rfl, h⟩]⟩

variable [Atomic α]

/-- Two individuals overlap iff they share an atom. -/
theorem overlap_iff_exists_atom : Overlap x y ↔ ∃ a, Atom a ∧ a ≤ x ∧ a ≤ y :=
  ⟨fun ⟨_, hz, hzx, hzy⟩ ↦ let ⟨a, ha, haz⟩ := Atomic.exists_atom_le hz
    ⟨a, ha, haz.trans hzx, haz.trans hzy⟩, fun ⟨a, ha, hax, hay⟩ ↦ ⟨a, ha.not_isBot, hax, hay⟩⟩

variable [StronglySupplemented α]

/-- In an atomic strongly supplemented part structure, parthood is inclusion of atoms. -/
theorem atomsBelow_subset_iff : atomsBelow x ⊆ atomsBelow y ↔ x ≤ y :=
  ⟨fun h ↦ le_of_forall_overlap fun _ hz hz0 ↦
    let ⟨a, ha, haz⟩ := Atomic.exists_atom_le hz0
    ⟨a, ha.not_isBot, haz, (h ⟨ha, haz.trans hz⟩).2⟩, atomsBelow_mono⟩

variable (α) in
/-- An atomic strongly supplemented part structure embeds in the sets of its atoms, parthood
going to inclusion. -/
def atomsBelowEmbedding : α ↪o Set α :=
  OrderEmbedding.ofMapLEIff atomsBelow fun _ _ ↦ atomsBelow_subset_iff

@[simp]
theorem atomsBelowEmbedding_apply (x : α) : atomsBelowEmbedding α x = atomsBelow x := rfl

end PartialOrder

/-- An atom is part of a join iff it is part of one of the two, as *Ann* is part of the sum of
some girls only by being one of them. -/
theorem Atom.le_sup_iff [SemilatticeSup α] [SupIsSum α] {a x y : α} (ha : Atom a) :
    a ≤ x ⊔ y ↔ a ≤ x ∨ a ≤ y := by
  have h := congrArg (a ∈ ·) (atomsBelow_sup x y)
  simpa [atomsBelow, ha] using h

/-! ### Atomicity and sums

Atomicity is not preserved along sums, so the number of a coordination is not a function of its
conjuncts' numbers. -/

section

variable {E β : Type*} [SemilatticeSup E] [SemilatticeSup β] {a b : E}

/-- No map preserving sums identifies two distinct atoms while keeping atoms apart from
non-atoms: an atom summed with itself is an atom, and summed with another is not. -/
theorem not_forall_atom_iff_of_map_eq (f : SupHom E β) (hab : a ≠ b) (ha : Atom a) (hb : Atom b)
    (hf : f a = f b) : ¬ ∀ x y, f x = f y → (Atom x ↔ Atom y) := by
  intro hat
  have h₁ : f a = f (b ⊔ a) := by rw [map_sup, ← hf, sup_idem]
  have hsum : Atom (b ⊔ a) := (hat _ _ h₁).1 ha
  have h₂ : b ⊔ a ≤ a := hsum.2 ha.1 le_sup_right
  exact hab (le_antisymm (ha.2 hb.1 (le_sup_left.trans h₂)) (le_sup_left.trans h₂))

end

end Mereology
