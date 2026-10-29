module

public import Linglib.Core.Order.Concept

/-!
# Representation of ortholattices by orthogonality relations

This file embeds an ortholattice with a join-dense subset `V` into the ortholattice of concepts of
an orthogonality relation, onto it when the lattice is complete. The points are the nonzero
elements of `V`, two points are orthogonal when one lies below the complement of the other, and `a`
is represented by the points below it. This is the converse of the construction of an ortholattice
from an orthogonality relation in `Core/Order/Concept.lean`. The representation is MacLaren's:
an orthocomplemented poset embeds in the closed sets of its orthogonality relation, and a
join-dense subset has the same closed sets. Holliday and Mandelkern state the combination for
ortholattices.

## Main definitions

* `JoinDense V`: every element of `L` is the least upper bound of the elements of `V` below it.
* `InvolutiveCompl.Orthogonal V`: the orthogonality relation `a ≤ bᶜ` on the nonzero
  elements of `V`.
* `InvolutiveCompl.represent V`: the concept of the points below an element.

## Main results

* `InvolutiveCompl.represent_le_iff`, `represent_inf`, `represent_compl`,
  `represent_sup`: `represent V` is an ortholattice embedding for any join-dense `V`.
* `InvolutiveCompl.represent_surjective`: on a complete lattice the embedding is onto.

## Implementation notes

The embedding uses only the order-reversing involution. The ortholattice laws
are needed only for orthogonality to be irreflexive, which makes the concepts an ortholattice.

## References

* [maclaren-1964]
* [holliday-mandelkern-2024]
-/

@[expose] public section

open Order Set

/-- A set `V` is join-dense in `L` when every element is the least upper bound of the elements
    of `V` below it. -/
def JoinDense {L : Type*} [Preorder L] (V : Set L) : Prop :=
  ∀ a : L, IsLUB (V ∩ Set.Iic a) a

namespace InvolutiveCompl

variable {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]

/-- The points of the representation over `V` are the nonzero elements of `V`. -/
abbrev Point (V : Set L) : Type _ := ↥(V \ {⊥})

/-- Two points are orthogonal when one lies below the complement of the other ([maclaren-1964]
    Theorem 2.5; [holliday-mandelkern-2024] Theorem 4.13, where compatibility is `a ≰ ¬b`). -/
def Orthogonal (V : Set L) (a b : Point V) : Prop := a.1 ≤ b.1ᶜ

@[simp] theorem orthogonal_iff {V : Set L} {a b : Point V} :
    Orthogonal V a b ↔ a.1 ≤ b.1ᶜ := Iff.rfl

instance (V : Set L) : Std.Symm (Orthogonal V) :=
  ⟨fun _ _ h ↦ InvolutiveCompl.le_compl_comm.mp h⟩

instance [IsOrtholattice L] (V : Set L) : Std.Irrefl (Orthogonal V) :=
  ⟨fun a h ↦ a.2.2 <| (IsOrtholattice.disjoint_of_le_compl h).eq_bot_of_le le_rfl⟩

/-- `represent V a` is the concept whose extent is the points below `a`. -/
def represent (V : Set L) (a : L) : Concept (Point V) (Point V) (Orthogonal V) :=
  Concept.ofObjects (Orthogonal V) {b | b.1 ≤ a}

variable {V : Set L}

theorem upperPolar_Iic (hV : JoinDense V) (x : L) :
    upperPolar (Orthogonal V) {c : Point V | c.1 ≤ x} = {d | x ≤ d.1ᶜ} := by
  ext d
  simp only [mem_upperPolar_iff, Set.mem_ofPred_eq, orthogonal_iff]
  constructor
  · intro h
    refine (isLUB_le_iff (hV x)).mpr ?_
    rintro b ⟨hbV, hbx⟩
    rcases eq_or_ne b ⊥ with rfl | hb0
    · exact bot_le
    · exact @h ⟨b, hbV, hb0⟩ hbx
  · intro h c hc
    exact hc.trans h

theorem isExtent_Iic (hV : JoinDense V) (a : L) :
    IsExtent (Orthogonal V) {b : Point V | b.1 ≤ a} := by
  have key : {d : Point V | a ≤ d.1ᶜ} = {d : Point V | d.1 ≤ aᶜ} := by
    ext d; exact InvolutiveCompl.le_compl_comm
  rw [isExtent_iff, upperPolar_Iic hV a, key,
      ← upperPolar_eq_lowerPolar (Orthogonal V), upperPolar_Iic hV aᶜ]
  ext e
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, InvolutiveCompl.le_compl_comm,
      InvolutiveCompl.compl_compl]

theorem represent_extent (hV : JoinDense V) (a : L) :
    (represent V a).extent = {b : Point V | b.1 ≤ a} :=
  Concept.extent_ofObjects_of_isExtent (isExtent_Iic hV a)

/-! ### The representation is an order-embedding preserving the lattice operations -/

/-- `represent V` preserves and reflects the order. -/
theorem represent_le_iff (hV : JoinDense V) {a a' : L} :
    represent V a ≤ represent V a' ↔ a ≤ a' := by
  rw [← Concept.extent_subset_extent_iff]
  simp only [represent_extent hV]
  constructor
  · intro h
    refine (isLUB_le_iff (hV a)).mpr ?_
    rintro b ⟨hbV, hba⟩
    rcases eq_or_ne b ⊥ with rfl | hb0
    · exact bot_le
    · exact @h ⟨b, hbV, hb0⟩ hba
  · intro h b hb
    exact hb.trans h

/-- `represent` preserves meets (`Concept` inf is extent intersection). -/
theorem represent_inf (hV : JoinDense V) (a a' : L) :
    represent V (a ⊓ a') = represent V a ⊓ represent V a' := by
  apply Concept.ext
  simp only [Concept.extent_inf, represent_extent hV]
  ext b
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_inf_iff]

theorem represent_top (hV : JoinDense V) : represent V (⊤ : L) = ⊤ :=
  top_le_iff.mp <| by
    rw [← Concept.extent_subset_extent_iff, represent_extent hV]; exact fun b _ ↦ le_top

theorem represent_bot (hV : JoinDense V) : represent V (⊥ : L) = ⊥ :=
  le_bot_iff.mp <| by
    rw [← Concept.extent_subset_extent_iff, represent_extent hV]
    exact fun b hb ↦ absurd (le_bot_iff.mp hb) b.2.2

/-- `represent V` sends complements to orthocomplements ([maclaren-1964] Theorem 2.3). -/
theorem represent_compl (hV : JoinDense V) (a : L) :
    represent V aᶜ = (represent V a)ᶜ := by
  apply Concept.ext
  rw [Concept.extent_compl, ← Concept.upperPolar_extent]
  simp only [represent_extent hV]
  rw [upperPolar_Iic hV]
  ext b
  exact InvolutiveCompl.le_compl_comm

/-- `represent` preserves joins (from `⊓`- and `ᶜ`-preservation via De Morgan). -/
theorem represent_sup (hV : JoinDense V) (a a' : L) :
    represent V (a ⊔ a') = represent V a ⊔ represent V a' := by
  rw [show a ⊔ a' = (aᶜ ⊓ a'ᶜ)ᶜ by
        rw [InvolutiveCompl.compl_inf, InvolutiveCompl.compl_compl,
            InvolutiveCompl.compl_compl],
      represent_compl hV, represent_inf hV, represent_compl hV, represent_compl hV,
      InvolutiveCompl.compl_inf, InvolutiveCompl.compl_compl,
      InvolutiveCompl.compl_compl]

end InvolutiveCompl

/-! ### On a complete lattice the representation is onto -/

namespace InvolutiveCompl

variable {L : Type*} [CompleteLattice L] [InvolutiveCompl L] {V : Set L}

/-- On a complete lattice a concept represents the join of its extent, so a complete ortholattice
is isomorphic to the concepts of the orthogonality relation on a join-dense subset
([maclaren-1964] Theorems 2.4 and 2.5; [holliday-mandelkern-2024] Theorem 4.13). -/
theorem represent_surjective (hV : JoinDense V) : Function.Surjective (represent V) := by
  intro c
  refine ⟨sSup (Subtype.val '' c.extent), Concept.ext ?_⟩
  rw [represent_extent hV]
  ext b
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun hb ↦ ?_, fun hb ↦ le_sSup ⟨b, hb, rfl⟩⟩
  rw [← c.lowerPolar_intent, mem_lowerPolar_iff]
  intro d hd
  refine orthogonal_iff.2 (hb.trans (sSup_le ?_))
  rintro _ ⟨e, he, rfl⟩
  exact orthogonal_iff.1 (Concept.rel_extent_intent he hd)

end InvolutiveCompl
