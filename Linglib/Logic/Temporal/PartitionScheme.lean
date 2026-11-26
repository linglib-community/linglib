module

public import Linglib.Core.Relation.SetRel
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Partition schemes and weak composition

A partition scheme on a set `U` divides the pairs of `U` into *basic relations*, closed under
converse ([ligozat-renz-2004]): the three ways two points of a line can stand, or the relations
of Allen between two intervals. We give a scheme by the map `index` sending a pair to its basic
relation. A set `C` of basic relations is read as their union `S.rel C`, the pairs whose index
lies in `C`. Reading is a homomorphism of complete Boolean algebras, takes converses to
converses, and is injective when every basic relation is nonempty.

The *weak composition* `S.weakComp C D` of two sets of basic relations is the set of the basic
relations that the composite `S.rel C ○ S.rel D` meets, the best approximation to the composite
within the scheme. The composite lies in the reading of the weak composition, and the two are
equal exactly when the composite is a union of basic relations. In the terms of
[ligozat-renz-2004], reading is a weak representation of the algebra of sets of basic relations
under weak composition, and a representation where it is injective and every weak composition is
a composite.

## Main definitions

* `PartitionScheme`: an index map on pairs with a converse on indices.
* `PartitionScheme.rel`: the relation of a set of basic relations.
* `PartitionScheme.relHom`: reading as a homomorphism of complete lattices.
* `PartitionScheme.weakComp`: weak composition.

## Main results

* `PartitionScheme.rel_comp_subset`: the composite lies in the reading of the weak composition.
* `PartitionScheme.rel_weakComp_subset_iff`: the two are equal exactly when the composite is a
  union of basic relations.
* `PartitionScheme.rel_subset_rel_iff`: reading is faithful when every basic relation is nonempty.
* `PartitionScheme.inter_weakComp_nonempty_iff`: a weak composition meets a set of basic
  relations exactly when the composite meets its reading.

## Implementation notes

* A scheme is its index map and not a family of relations, so that the basic relations partition
  the pairs by construction and reading is a preimage, to which mathlib's
  `CompleteLatticeHom.setPreimage` and `Function.Surjective.preimage_subset_preimage_iff` apply.
* [ligozat-renz-2004] ask that the basic relations be nonempty and that the diagonal be one of
  them. Here nonemptiness is the hypothesis `Function.Surjective S.index` where it is used, since
  a time with one point realizes only equality, and the diagonal may be a union of basic
  relations, as when point intervals are told apart from proper ones.

## References

* [ligozat-renz-2004]
-/

@[expose] public section

open SetRel

/-- A partition scheme on `U` with basic relations indexed by `K`: each pair stands in one basic
relation, and read the other way it stands in the converse one ([ligozat-renz-2004]). -/
structure PartitionScheme (U K : Type*) where
  /-- The basic relation in which a pair stands. -/
  index : U × U → K
  /-- The converse of a basic relation. -/
  inv : K → K
  /-- A pair read the other way stands in the converse relation. -/
  index_swap : ∀ p, index p.swap = inv (index p)

namespace PartitionScheme

variable {U K : Type*} (S : PartitionScheme U K) {C D E : Set K} {x y : U} {k : K}

/-- The relation of a set of basic relations, their union. -/
def rel (C : Set K) : SetRel U U := S.index ⁻¹' C

@[simp] theorem mem_rel : (x, y) ∈ S.rel C ↔ S.index (x, y) ∈ C := .rfl

/-- Reading a set of basic relations as a relation preserves arbitrary unions and
intersections. -/
def relHom : CompleteLatticeHom (Set K) (SetRel U U) := CompleteLatticeHom.setPreimage S.index

@[simp] theorem coe_relHom : ⇑S.relHom = S.rel := rfl

@[simp] theorem rel_empty : S.rel ∅ = ∅ := rfl

@[simp] theorem rel_univ : S.rel Set.univ = Set.univ := rfl

theorem rel_union (C D : Set K) : S.rel (C ∪ D) = S.rel C ∪ S.rel D := rfl

theorem rel_inter (C D : Set K) : S.rel (C ∩ D) = S.rel C ∩ S.rel D := rfl

theorem rel_compl (C : Set K) : S.rel Cᶜ = (S.rel C)ᶜ := rfl

@[gcongr] theorem rel_mono (h : C ⊆ D) : S.rel C ⊆ S.rel D := Set.preimage_mono h

/-- The converse of the relation of `C` is the relation of the converses of `C`. -/
theorem inv_rel (C : Set K) : (S.rel C).inv = S.rel (S.inv ⁻¹' C) := by
  ext ⟨x, y⟩
  exact (congrArg (· ∈ C) (S.index_swap (x, y))).to_iff

/-- Where every basic relation is nonempty, the relations of two sets of basic relations are
ordered as the sets are. -/
theorem rel_subset_rel_iff (h : Function.Surjective S.index) : S.rel C ⊆ S.rel D ↔ C ⊆ D :=
  h.preimage_subset_preimage_iff

theorem rel_injective (h : Function.Surjective S.index) : Function.Injective S.rel :=
  h.preimage_injective

/-! ### Weak composition -/

/-- The weak composition of two sets of basic relations: the basic relations that the composite
of their relations meets ([ligozat-renz-2004]). -/
def weakComp (C D : Set K) : Set K := S.index '' (S.rel C ○ S.rel D)

theorem mem_weakComp :
    k ∈ S.weakComp C D ↔
      ∃ x y z, S.index (x, y) ∈ C ∧ S.index (y, z) ∈ D ∧ S.index (x, z) = k := by
  constructor
  · rintro ⟨⟨x, z⟩, ⟨y, h₁, h₂⟩, rfl⟩
    exact ⟨x, y, z, h₁, h₂, rfl⟩
  · rintro ⟨x, y, z, h₁, h₂, rfl⟩
    exact ⟨(x, z), ⟨y, h₁, h₂⟩, rfl⟩

@[gcongr] theorem weakComp_mono {C' D' : Set K} (hC : C ⊆ C') (hD : D ⊆ D') :
    S.weakComp C D ⊆ S.weakComp C' D' :=
  Set.image_mono (SetRel.comp_subset_comp (S.rel_mono hC) (S.rel_mono hD))

/-- The composite of two relations lies in the relation of their weak composition. -/
theorem rel_comp_subset (C D : Set K) : S.rel C ○ S.rel D ⊆ S.rel (S.weakComp C D) :=
  fun p hp ↦ ⟨p, hp, rfl⟩

/-- The relation of a weak composition is the composite exactly when the composite is a union of
basic relations: a pair with the index of a pair of the composite is in the composite. -/
theorem rel_weakComp_subset_iff :
    S.rel (S.weakComp C D) ⊆ S.rel C ○ S.rel D ↔
      ∀ p ∈ S.rel C ○ S.rel D, ∀ q, S.index q = S.index p → q ∈ S.rel C ○ S.rel D :=
  ⟨fun h p hp _ hq ↦ h ⟨p, hp, hq.symm⟩, fun h q ⟨p, hp, hq⟩ ↦ h p hp q hq.symm⟩

theorem rel_weakComp_eq_iff :
    S.rel (S.weakComp C D) = S.rel C ○ S.rel D ↔ S.rel (S.weakComp C D) ⊆ S.rel C ○ S.rel D :=
  ⟨fun h ↦ h.subset, fun h ↦ h.antisymm (S.rel_comp_subset C D)⟩

/-- A weak composition meets a set of basic relations exactly when the composite meets its
relation. -/
theorem inter_weakComp_nonempty_iff :
    (S.weakComp C D ∩ E).Nonempty ↔ ((S.rel C ○ S.rel D) ∩ S.rel E).Nonempty := by
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hE⟩
    exact ⟨p, hp, hE⟩
  · rintro ⟨p, hp, hE⟩
    exact ⟨_, ⟨p, hp, rfl⟩, hE⟩

end PartitionScheme
