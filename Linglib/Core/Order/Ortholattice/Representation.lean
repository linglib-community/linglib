module

public import Linglib.Core.Order.Concept
public import Mathlib.Order.Hom.Basic

/-!
# Representation of ortholattices by orthogonality relations

MacLaren's representation sends an ortholattice `L` with a join-dense subset `V` into the
concepts of an orthogonality relation: the points are the nonzero elements of `V`, two points are
orthogonal when one lies below the complement of the other, and `a` goes to the concept of the
points below it. This is [an order embedding](##OrthoConcept.principalEmbedding) preserving
[meets](##OrthoConcept.principal_inf), [joins](##OrthoConcept.principal_sup) and
[complements](##OrthoConcept.principal_compl), and on a complete lattice, where
[every concept is the image of the join of its extent](##OrthoConcept.principal_sSup_extent), it
is [an order isomorphism](##OrthoConcept.principalIso).

## Main definitions

* `JoinDense V`: every element of `L` is the least upper bound of the elements of `V` below it.
* `OrthoConcept.Orthogonal V`: the orthogonality relation `a ≤ bᶜ` on the nonzero elements of
  `V`, and `OrthoConcept V` its concepts.
* `OrthoConcept.principal V`: the concept of the points below an element.
* `OrthoConcept.principalEmbedding`, `OrthoConcept.principalIso`: `principal V` as an order
  embedding for join-dense `V`, and as an order isomorphism on a complete lattice.

## Main statements

* `OrthoConcept.principal_le_principal`, `principal_inf`, `principal_sup`, `principal_compl`:
  `principal V` preserves and reflects the order and preserves the ortholattice operations.
* `OrthoConcept.principal_surjective`: on a complete lattice every concept is principal.

## Implementation notes

The representation is the converse of the construction of an ortholattice from an orthogonality
relation in `Core/Order/Concept.lean`. It uses only the order-reversing involution; the
ortholattice laws are needed only for orthogonality to be irreflexive, which makes the concepts an
ortholattice. Surjectivity needs no join-density, which only makes the order reflected. The names
follow mathlib's `DedekindCut`, the concepts of `≤`, with its `principal`, `principalEmbedding`
and `principalIso`; `OrthoConcept` is the library's name for the concepts of orthogonality.

## References

* [maclaren-1964]
-/

@[expose] public section

open Order Set

/-- A set `V` is join-dense in `L` when every element is the least upper bound of the elements
    of `V` below it. -/
def JoinDense {L : Type*} [Preorder L] (V : Set L) : Prop :=
  ∀ a : L, IsLUB (V ∩ Set.Iic a) a

namespace OrthoConcept

variable {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]

omit [InvolutiveCompl L] in
/-- The points over `V` are the nonzero elements of `V`. -/
abbrev Point (V : Set L) : Type _ := ↥(V \ {⊥})

/-- Two points are orthogonal when one lies below the complement of the other
    ([maclaren-1964] Theorem 2.5). -/
def Orthogonal (V : Set L) (a b : Point V) : Prop := a.1 ≤ b.1ᶜ

@[simp] theorem orthogonal_iff {V : Set L} {a b : Point V} :
    Orthogonal V a b ↔ a.1 ≤ b.1ᶜ := Iff.rfl

instance (V : Set L) : Std.Symm (Orthogonal V) :=
  ⟨fun _ _ h ↦ InvolutiveCompl.le_compl_comm.mp h⟩

instance [IsOrtholattice L] (V : Set L) : Std.Irrefl (Orthogonal V) :=
  ⟨fun a h ↦ a.2.2 <| (IsOrtholattice.disjoint_of_le_compl h).eq_bot_of_le le_rfl⟩

end OrthoConcept

/-- The **orthogonality concepts** over `V` are the concepts of orthogonality on the nonzero
    elements of `V`, the closed sets of [maclaren-1964]'s representation. -/
abbrev OrthoConcept {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L] (V : Set L) :
    Type _ :=
  Concept (OrthoConcept.Point V) (OrthoConcept.Point V) (OrthoConcept.Orthogonal V)

namespace OrthoConcept

variable {L : Type*} [Lattice L] [BoundedOrder L] [InvolutiveCompl L]

/-- `principal V a` is the concept whose extent is the points below `a`. -/
def principal (V : Set L) (a : L) : OrthoConcept V :=
  Concept.ofObjects (Orthogonal V) {b | b.1 ≤ a}

variable {V : Set L}

omit [InvolutiveCompl L] in
private theorem le_of_forall_point_le (hV : JoinDense V) {a x : L}
    (h : ∀ b : Point V, b.1 ≤ a → b.1 ≤ x) : a ≤ x := by
  refine (isLUB_le_iff (hV a)).mpr ?_
  rintro b ⟨hbV, hba⟩
  rcases eq_or_ne b ⊥ with rfl | hb0
  · exact bot_le
  · exact h ⟨b, hbV, hb0⟩ hba

private theorem upperPolar_setOf_le (hV : JoinDense V) (x : L) :
    upperPolar (Orthogonal V) {c : Point V | c.1 ≤ x} = {d | x ≤ d.1ᶜ} := by
  ext d
  simp only [mem_upperPolar_iff, Set.mem_ofPred_eq, orthogonal_iff]
  exact ⟨fun h ↦ le_of_forall_point_le hV fun b hb ↦ h hb, fun h c hc ↦ hc.trans h⟩

private theorem isExtent_setOf_le (hV : JoinDense V) (a : L) :
    IsExtent (Orthogonal V) {b : Point V | b.1 ≤ a} := by
  have key : {d : Point V | a ≤ d.1ᶜ} = {d : Point V | d.1 ≤ aᶜ} := by
    ext d; exact InvolutiveCompl.le_compl_comm
  rw [isExtent_iff, upperPolar_setOf_le hV a, key,
      ← upperPolar_eq_lowerPolar (Orthogonal V), upperPolar_setOf_le hV aᶜ]
  ext e
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, InvolutiveCompl.le_compl_comm,
      InvolutiveCompl.compl_compl]

theorem extent_principal (hV : JoinDense V) (a : L) :
    (principal V a).extent = {b : Point V | b.1 ≤ a} :=
  Concept.extent_ofObjects_of_isExtent (isExtent_setOf_le hV a)

/-! ### The representation preserves the order and the operations -/

/-- `principal V` preserves and reflects the order. -/
theorem principal_le_principal (hV : JoinDense V) {a b : L} :
    principal V a ≤ principal V b ↔ a ≤ b := by
  rw [← Concept.extent_subset_extent_iff, extent_principal hV, extent_principal hV]
  exact ⟨fun h ↦ le_of_forall_point_le hV fun c hc ↦ h hc, fun h c hc ↦ hc.trans h⟩

/-- `principal V` as an order embedding, for join-dense `V`. -/
def principalEmbedding (hV : JoinDense V) : L ↪o OrthoConcept V :=
  OrderEmbedding.ofMapLEIff (principal V) fun _ _ ↦ principal_le_principal hV

@[simp] theorem coe_principalEmbedding (hV : JoinDense V) :
    ⇑(principalEmbedding hV) = principal V :=
  rfl

/-- `principal V` preserves meets (`Concept` inf is extent intersection). -/
theorem principal_inf (hV : JoinDense V) (a b : L) :
    principal V (a ⊓ b) = principal V a ⊓ principal V b := by
  apply Concept.ext
  simp only [Concept.extent_inf, extent_principal hV]
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, le_inf_iff]

theorem principal_top (hV : JoinDense V) : principal V (⊤ : L) = ⊤ :=
  top_le_iff.mp <| by
    rw [← Concept.extent_subset_extent_iff, extent_principal hV]; exact fun b _ ↦ le_top

theorem principal_bot (hV : JoinDense V) : principal V (⊥ : L) = ⊥ :=
  le_bot_iff.mp <| by
    rw [← Concept.extent_subset_extent_iff, extent_principal hV]
    exact fun b hb ↦ absurd (le_bot_iff.mp hb) b.2.2

/-- `principal V` sends complements to orthocomplements ([maclaren-1964] Theorem 2.3). -/
theorem principal_compl (hV : JoinDense V) (a : L) :
    principal V aᶜ = (principal V a)ᶜ := by
  apply Concept.ext
  rw [Concept.extent_compl, ← Concept.upperPolar_extent]
  simp only [extent_principal hV]
  rw [upperPolar_setOf_le hV]
  ext b
  exact InvolutiveCompl.le_compl_comm

/-- `principal V` preserves joins (from `⊓`- and `ᶜ`-preservation via De Morgan). -/
theorem principal_sup (hV : JoinDense V) (a b : L) :
    principal V (a ⊔ b) = principal V a ⊔ principal V b := by
  rw [show a ⊔ b = (aᶜ ⊓ bᶜ)ᶜ by
        rw [InvolutiveCompl.compl_inf, InvolutiveCompl.compl_compl,
            InvolutiveCompl.compl_compl],
      principal_compl hV, principal_inf hV, principal_compl hV, principal_compl hV,
      InvolutiveCompl.compl_inf, InvolutiveCompl.compl_compl,
      InvolutiveCompl.compl_compl]

end OrthoConcept

/-! ### On a complete lattice the representation is onto -/

namespace OrthoConcept

variable {L : Type*} [CompleteLattice L] [InvolutiveCompl L] {V : Set L}

/-- On a complete lattice a concept is the principal concept of the join of its extent
    ([maclaren-1964] Theorems 2.4 and 2.5). -/
theorem principal_sSup_extent (c : OrthoConcept V) :
    principal V (sSup (Subtype.val '' c.extent)) = c := by
  refine (congrArg (Concept.ofObjects (Orthogonal V)) ?_).trans Concept.ofObjects_extent
  ext b
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun hb ↦ ?_, fun hb ↦ le_sSup ⟨b, hb, rfl⟩⟩
  rw [← c.lowerPolar_intent, mem_lowerPolar_iff]
  intro d hd
  refine orthogonal_iff.2 (hb.trans (sSup_le ?_))
  rintro _ ⟨e, he, rfl⟩
  exact orthogonal_iff.1 (Concept.rel_extent_intent he hd)

theorem principal_surjective : Function.Surjective (principal V) :=
  fun c ↦ ⟨_, principal_sSup_extent c⟩

/-- On a complete lattice with a join-dense `V`, `principal V` is an order isomorphism onto the
    concepts of orthogonality ([maclaren-1964] Theorems 2.4 and 2.5). -/
noncomputable def principalIso (hV : JoinDense V) : L ≃o OrthoConcept V :=
  OrderIso.ofSurjective (principalEmbedding hV) principal_surjective

@[simp] theorem coe_principalIso (hV : JoinDense V) : ⇑(principalIso hV) = principal V :=
  rfl

end OrthoConcept
