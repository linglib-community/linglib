module

public import Linglib.Core.Order.Concept
public import Linglib.Core.Order.Ortholattice.Hom
public import Linglib.Core.Relation.SetRel
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.PFilter

/-!
# Representation of ortholattices by proper filters

Goldblatt's representation sends an ortholattice `L` into the concepts of an orthogonality
relation on its proper filters: two filters are orthogonal when one contains the complement of an
element of the other, and `a` goes to the concept of the filters containing it. This is
[an order embedding](##Order.ProperFilter.embedOrderEmbedding) and [an ortholattice
homomorphism](##Order.ProperFilter.embedHom). A
map `□` preserving finite meets gives the relation under which `F` accesses `G` when `G` contains
everything necessary at `F`, and when `□` is deflationary [`□` of the filters containing `a` is
the filters containing `□a`](##Order.ProperFilter.core_setOf_mem).

## Implementation notes

Harding, McDonald and Peinado call the frame of proper filters Goldblatt's orthoframe and identify
its concepts with the canonical completion of `L`, beside MacLaren's orthoframe of nonzero
elements in `Core/Order/Ortholattice/Representation.lean`, whose concepts are the MacNeille
completion. Proper filters carry operators that elements need not: MacLaren's points carry `□`
when every filter `{c | a ≤ □c}` is principal, as for the quantifier of a monadic ortholattice,
and proper filters need no such condition. Unlike MacLaren's, this representation is not onto even
for complete `L`, as Harding, McDonald and Peinado observe against Goldblatt, so it has no
counterpart of `OrthoConcept.principalIso`.

## References

* [goldblatt-1975]
* [harding-mcdonald-peinado-2025]
-/

@[expose] public section

open Set SetRel

namespace Order

/-- The proper filters of `L`, the points of Goldblatt's representation. -/
abbrev ProperFilter (L : Type*) [Lattice L] [OrderBot L] : Type _ :=
  {F : PFilter L // ⊥ ∉ F}

namespace PFilter

variable {L M : Type*} [Lattice L]

/-- The upward closure of the image of a filter under a monotone map. -/
def map [Preorder M] (f : L →o M) (G : PFilter L) : PFilter M :=
  IsPFilter.toPFilter <| IsPFilter.of_def (F := {b | ∃ a ∈ G, f a ≤ b})
    (G.nonempty.elim fun a ha ↦ ⟨f a, a, ha, le_rfl⟩)
    (fun _ ⟨a, ha, hab⟩ _ ⟨a', ha', hab'⟩ ↦ ⟨f (a ⊓ a'), ⟨_, G.inf_mem ha ha', le_rfl⟩,
      (f.mono inf_le_left).trans hab, (f.mono inf_le_right).trans hab'⟩)
    fun hxy ⟨a, ha, hax⟩ ↦ ⟨a, ha, hax.trans hxy⟩

theorem mem_map [Preorder M] {f : L →o M} {G : PFilter L} {b : M} :
    b ∈ G.map f ↔ ∃ a ∈ G, f a ≤ b := Iff.rfl

/-- The preimage of a filter under a map preserving finite meets. -/
def comap [OrderTop L] [Lattice M] [OrderTop M] (f : InfTopHom L M) (G : PFilter M) :
    PFilter L :=
  IsPFilter.toPFilter <| IsPFilter.of_def (F := {a | f a ∈ G}) ⟨⊤, by simp⟩
    (fun a ha a' ha' ↦ ⟨a ⊓ a', by simpa [map_inf] using G.inf_mem ha ha', inf_le_left,
      inf_le_right⟩)
    fun hxy h ↦ PFilter.mem_of_le (OrderHomClass.mono f hxy) h

theorem mem_comap [OrderTop L] [Lattice M] [OrderTop M] {f : InfTopHom L M} {G : PFilter M}
    {a : L} : a ∈ G.comap f ↔ f a ∈ G := Iff.rfl

end PFilter

namespace ProperFilter

variable {L : Type*} [Lattice L] [BoundedOrder L]

instance : SetLike (ProperFilter L) L where
  coe F := (F.1 : Set L)
  coe_injective _ _ h := Subtype.ext (SetLike.coe_injective h)

@[simp] theorem mem_val {F : ProperFilter L} {a : L} : a ∈ F.1 ↔ a ∈ F := Iff.rfl

theorem bot_notMem (F : ProperFilter L) : ⊥ ∉ F := F.2

@[simp] theorem top_mem (F : ProperFilter L) : ⊤ ∈ F := F.1.top_mem

theorem mem_of_le (F : ProperFilter L) {a b : L} (h : a ≤ b) (ha : a ∈ F) : b ∈ F :=
  F.1.mem_of_le h ha

theorem inf_mem (F : ProperFilter L) {a b : L} (ha : a ∈ F) (hb : b ∈ F) : a ⊓ b ∈ F :=
  F.1.inf_mem ha hb

@[simp] theorem inf_mem_iff (F : ProperFilter L) {a b : L} : a ⊓ b ∈ F ↔ a ∈ F ∧ b ∈ F :=
  F.1.inf_mem_iff

/-- The principal filter of a nonzero element. -/
def principal {a : L} (ha : a ≠ ⊥) : ProperFilter L :=
  ⟨PFilter.principal a, fun h ↦ ha (le_bot_iff.mp h)⟩

@[simp] theorem mem_principal {a b : L} (ha : a ≠ ⊥) : b ∈ principal ha ↔ a ≤ b := Iff.rfl

/-! ### The relation of a meet-preserving operator -/

variable {box : InfTopHom L L}

/-- The filter `{a | □a ∈ F}`, proper when `□` is deflationary. -/
def nec (hT : ∀ a, box a ≤ a) (F : ProperFilter L) : ProperFilter L :=
  ⟨F.1.comap box, fun h ↦ F.bot_notMem <| by
    have h' := PFilter.mem_comap.mp h
    rwa [le_bot_iff.mp (hT ⊥)] at h'⟩

theorem mem_nec {hT : ∀ a, box a ≤ a} {F : ProperFilter L} {a : L} :
    a ∈ nec hT F ↔ box a ∈ F := Iff.rfl

variable (box) in
/-- `F` accesses `G` when `G` contains everything necessary at `F`. -/
def access : SetRel (ProperFilter L) (ProperFilter L) :=
  {(F, G) | ∀ a, box a ∈ F → a ∈ G}

theorem mem_access {F G : ProperFilter L} : F ~[access box] G ↔ ∀ a, box a ∈ F → a ∈ G :=
  Iff.rfl

theorem access_nec (hT : ∀ a, box a ≤ a) (F : ProperFilter L) : F ~[access box] nec hT F :=
  mem_access.2 fun _ h ↦ mem_nec.2 h

/-- `□` of the filters containing `a` is the filters containing `□a`. -/
theorem core_setOf_mem (hT : ∀ a, box a ≤ a) (a : L) :
    (access box).core {F : ProperFilter L | a ∈ F} = {F | box a ∈ F} :=
  Set.ext fun F ↦ ⟨fun h ↦ mem_nec.1 (show a ∈ nec hT F from h (access_nec hT F)),
    fun h _ hFG ↦ mem_access.1 hFG a h⟩

theorem isRefl_access (hT : ∀ a, box a ≤ a) : (access box).IsRefl :=
  ⟨fun F ↦ mem_access.2 fun a h ↦ F.mem_of_le (hT a) h⟩

/-! ### Orthogonality and the representation -/

variable [InvolutiveCompl L]

/-- Two proper filters are orthogonal when one contains the complement of an element of the
other ([goldblatt-1975]). -/
def Orthogonal (F G : ProperFilter L) : Prop := ∃ a ∈ F, aᶜ ∈ G

instance : Std.Symm (Orthogonal (L := L)) :=
  ⟨fun _ _ ⟨a, ha, hac⟩ ↦ ⟨aᶜ, hac, by rwa [InvolutiveCompl.compl_compl]⟩⟩

instance [IsOrtholattice L] : Std.Irrefl (Orthogonal (L := L)) :=
  ⟨fun F ⟨a, ha, hac⟩ ↦ F.bot_notMem <| by
    have h := F.inf_mem ha hac
    rwa [IsOrtholattice.inf_compl_eq_bot] at h⟩

theorem upperPolar_setOf_mem (a : L) :
    upperPolar Orthogonal {F : ProperFilter L | a ∈ F} = {G | aᶜ ∈ G} := by
  ext G
  refine ⟨fun h ↦ ?_, fun haG F haF ↦ ⟨a, haF, haG⟩⟩
  rcases eq_or_ne a ⊥ with rfl | ha
  · rw [InvolutiveCompl.compl_bot]; exact G.top_mem
  · obtain ⟨c, hc, hcG⟩ :=
      h (show principal ha ∈ {F : ProperFilter L | a ∈ F} from (mem_principal ha).2 le_rfl)
    exact G.mem_of_le (InvolutiveCompl.compl_le_compl ((mem_principal ha).1 hc)) hcG

theorem isExtent_setOf_mem (a : L) : IsExtent Orthogonal {F : ProperFilter L | a ∈ F} := by
  refine isExtent_iff_lowerPolar_upperPolar_subset.2 fun F hF ↦ ?_
  rw [upperPolar_setOf_mem] at hF
  by_contra haF
  have hac : aᶜ ≠ ⊥ := fun h ↦ haF <| by
    rw [← InvolutiveCompl.compl_compl a, h, InvolutiveCompl.compl_bot]; exact F.top_mem
  obtain ⟨c, hc, hca⟩ :=
    hF (show principal hac ∈ {G : ProperFilter L | aᶜ ∈ G} from (mem_principal hac).2 le_rfl)
  exact haF <| F.mem_of_le
    (InvolutiveCompl.compl_le_compl_iff_le.mp ((mem_principal hac).1 hca)) hc

/-- `a` as the concept of the proper filters containing it ([goldblatt-1975]). -/
def embed (a : L) : Concept (ProperFilter L) (ProperFilter L) Orthogonal :=
  .ofIsExtent _ _ (isExtent_setOf_mem a)

@[simp] theorem coe_embed (a : L) : (embed a : Set (ProperFilter L)) = {F | a ∈ F} := rfl

theorem embed_le_embed {a b : L} : embed a ≤ embed b ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h F hF ↦ F.mem_of_le h hF⟩
  rcases eq_or_ne a ⊥ with rfl | ha
  · exact bot_le
  · have hmem : principal ha ∈ (embed b : Set (ProperFilter L)) :=
      SetLike.coe_subset_coe.mpr h ((mem_principal ha).2 le_rfl)
    exact (mem_principal ha).1 hmem

theorem embed_inf (a b : L) : embed (a ⊓ b) = embed a ⊓ embed b :=
  SetLike.coe_injective <| by
    rw [Concept.coe_inf, coe_embed, coe_embed, coe_embed]
    exact Set.ext fun F ↦ F.inf_mem_iff (a := a) (b := b)

theorem embed_top : embed (⊤ : L) = ⊤ :=
  SetLike.coe_injective <| by
    rw [coe_embed, Concept.coe_top]
    exact Set.ext fun F ↦ iff_of_true F.top_mem trivial

theorem embed_compl (a : L) : embed aᶜ = (embed a)ᶜ :=
  SetLike.coe_injective <| by rw [Concept.coe_compl, coe_embed, coe_embed, upperPolar_setOf_mem]

/-- `embed` as an order embedding. -/
def embedOrderEmbedding : L ↪o Concept (ProperFilter L) (ProperFilter L) Orthogonal :=
  OrderEmbedding.ofMapLEIff embed fun _ _ ↦ embed_le_embed

@[simp] theorem coe_embedOrderEmbedding : ⇑(embedOrderEmbedding (L := L)) = embed := rfl

/-- `embed` as an ortholattice homomorphism ([goldblatt-1975]). -/
def embedHom : OrtholatticeHom L (Concept (ProperFilter L) (ProperFilter L) Orthogonal) :=
  .ofInfTopHom ⟨⟨embed, embed_inf⟩, embed_top⟩ embed_compl

@[simp] theorem coe_embedHom : ⇑(embedHom (L := L)) = embed := rfl

@[simp] theorem embedHom_apply (a : L) : embedHom a = embed a := rfl

theorem embed_bot : embed (⊥ : L) = ⊥ :=
  map_bot embedHom

theorem embed_sup (a b : L) : embed (a ⊔ b) = embed a ⊔ embed b :=
  map_sup embedHom a b

end ProperFilter

end Order
