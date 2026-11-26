module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Closure
public import Mathlib.Logic.Relation

/-!
# Correspondences, closures and equivalences of relations as sets of pairs

`[UPSTREAM]` supplements to `Mathlib/Basic/Rel.lean`.

A *correspondence* is a set-valued function `f : α → Set β`. Its graph is the relation
`SetRel.cgraph f` that relates `a` to the members of `f a`, the set of pairs that mathlib's
`HasOpenCGraph` is a predicate of. Correspondences and relations are the same thing
(`SetRel.cgraphOrderIso`), and a relation on a type is reflexive, symmetric or transitive exactly
when its correspondence satisfies the matching condition on the sets `f a`.

The core and the preimage of a relation are dual under complement, the core is antitone in the
relation, and a relation is determined by its preimages. The transitive closure `SetRel.transGen`
is a closure operator whose closed elements are the transitive relations. The asymmetric part
`SetRel.asymmetrize` is what is left of a relation outside mathlib's symmetric part
`SetRel.symmetrize`. Composition distributes over union.

## Main definitions

* `SetRel.cgraph`: the graph of a correspondence, as a relation.
* `SetRel.cgraphOrderIso`: correspondences are relations.
* `SetRel.transGen`: the transitive closure, as a closure operator.
* `SetRel.asymmetrize`: the asymmetric part.
* `SetRel.IsPreorder`, `SetRel.IsEquiv`: preorders and equivalence relations.

## Implementation notes

`SetRel.comp_union` and `SetRel.union_comp` are the statements of mathlib pull request 44241 and
go when it is merged and the pin moves past it.
-/

@[expose] public section

namespace SetRel

variable {α β : Type*} {R R₁ R₂ : SetRel α β} {t : Set β} {a b c : α}

/-! ### Core and preimage -/

theorem core_compl (R : SetRel α β) (t : Set β) : R.core tᶜ = (R.preimage t)ᶜ := by
  ext; grind

theorem preimage_compl (R : SetRel α β) (t : Set β) : R.preimage tᶜ = (R.core t)ᶜ := by
  rw [← compl_compl (R.preimage _), ← core_compl, compl_compl]

theorem core_iInter {ι : Sort*} (R : SetRel α β) (t : ι → Set β) :
    R.core (⋂ i, t i) = ⋂ i, R.core (t i) :=
  image_core_gc.u_iInf

theorem core_sInter (R : SetRel α β) (S : Set (Set β)) : R.core (⋂₀ S) = ⋂ t ∈ S, R.core t :=
  image_core_gc.u_sInf

@[gcongr]
theorem core_subset_core_left (h : R₁ ⊆ R₂) : R₂.core t ⊆ R₁.core t :=
  fun _ ha _ hb ↦ ha (h hb)

/-! ### Relations are determined by their images and preimages -/

/-- Relations are ordered as their images are. -/
theorem image_le_image_iff : R₁.image ≤ R₂.image ↔ R₁ ⊆ R₂ :=
  ⟨fun h ⟨a, _⟩ r ↦ by
      obtain ⟨_, rfl, r'⟩ := h {a} ⟨a, rfl, r⟩
      exact r',
    fun h _ ↦ image_subset_image_left h⟩

/-- Relations are ordered as their preimages are. -/
theorem preimage_le_preimage_iff : R₁.preimage ≤ R₂.preimage ↔ R₁ ⊆ R₂ :=
  (image_le_image_iff (R₁ := R₁.inv) (R₂ := R₂.inv)).trans
    ⟨fun h ↦ by simpa using inv_mono h, inv_mono⟩

/-! ### Decidability over finite types -/

instance [Fintype β] (R : SetRel α β) (t : Set β) (a : α) [∀ b, Decidable (a ~[R] b)]
    [DecidablePred (· ∈ t)] : Decidable (a ∈ R.core t) :=
  decidable_of_iff (∀ b, a ~[R] b → b ∈ t) mem_core.symm

instance [Fintype β] (R : SetRel α β) (t : Set β) (a : α) [∀ b, Decidable (a ~[R] b)]
    [DecidablePred (· ∈ t)] : Decidable (a ∈ R.preimage t) :=
  decidable_of_iff (∃ b ∈ t, a ~[R] b) mem_preimage.symm

instance [Fintype α] (R : SetRel α β) (s : Set α) (b : β) [∀ a, Decidable (a ~[R] b)]
    [DecidablePred (· ∈ s)] : Decidable (b ∈ R.image s) :=
  decidable_of_iff (∃ a ∈ s, a ~[R] b) mem_image.symm

instance [Fintype β] (R : SetRel α β) (a : α) [∀ b, Decidable (a ~[R] b)] : Decidable (a ∈ R.dom) :=
  decidable_of_iff (∃ b, a ~[R] b) mem_dom.symm

instance [Fintype α] (R : SetRel α β) (b : β) [∀ a, Decidable (a ~[R] b)] : Decidable (b ∈ R.cod) :=
  decidable_of_iff (∃ a, a ~[R] b) mem_cod.symm

/-! ### Converse -/

theorem inv_image_prodMap {γ δ : Type*} (f : α → γ) (g : β → δ) (R : SetRel α β) :
    SetRel.inv (Prod.map f g '' R) = Prod.map g f '' R.inv := by
  ext ⟨x, y⟩; simp only [mem_inv, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq]; grind

/-! ### Composition and union -/

theorem comp_union {γ : Type*} (R : SetRel α β) (S S' : SetRel β γ) :
    R ○ (S ∪ S') = (R ○ S) ∪ (R ○ S') := by
  grind

theorem union_comp {γ : Type*} (R R' : SetRel α β) (S : SetRel β γ) :
    (R ∪ R') ○ S = (R ○ S) ∪ (R' ○ S) := by
  grind

/-! ### Reflexive relations -/

instance isRefl_id : (SetRel.id : SetRel α α).IsRefl := ⟨fun _ ↦ rfl⟩

/-! ### Irreflexive relations -/

/-- A relation is irreflexive exactly when no point lies in the image of its own singleton. -/
theorem forall_disjoint_image_singleton_iff {R : SetRel α α} :
    (∀ a, Disjoint (R.image {a}) {a}) ↔ R.IsIrrefl := by
  simp only [Set.disjoint_singleton_right, mem_image, Set.mem_singleton_iff, exists_eq_left]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.irrefl⟩

/-! ### Preorders and equivalence relations -/

/-- `R` is a preorder: reflexive and transitive. -/
protected abbrev IsPreorder (R : SetRel α α) : Prop := _root_.IsPreorder α (· ~[R] ·)

/-- `R` is an equivalence relation: reflexive, symmetric and transitive. -/
protected abbrev IsEquiv (R : SetRel α α) : Prop := _root_.IsEquiv α (· ~[R] ·)

instance isPreorder_univ : SetRel.IsPreorder (Set.univ : SetRel α α) where
  refl _ := trivial
  trans _ _ _ _ _ := trivial

instance isPreorder_id : SetRel.IsPreorder (SetRel.id : SetRel α α) where
  refl _ := rfl
  trans _ _ _ := Eq.trans

instance isPreorder_inter {R₁ R₂ : SetRel α α} [R₁.IsPreorder] [R₂.IsPreorder] :
    (R₁ ∩ R₂).IsPreorder where
  refl _ := ⟨R₁.rfl, R₂.rfl⟩
  trans _ _ _ h h' := ⟨R₁.trans h.1 h'.1, R₂.trans h.2 h'.2⟩

instance isEquiv_univ : SetRel.IsEquiv (Set.univ : SetRel α α) where
  symm _ _ _ := trivial

instance isEquiv_id : SetRel.IsEquiv (SetRel.id : SetRel α α) where
  symm _ _ := Eq.symm

instance isEquiv_inter {R₁ R₂ : SetRel α α} [R₁.IsEquiv] [R₂.IsEquiv] : (R₁ ∩ R₂).IsEquiv where
  symm _ _ h := ⟨R₁.symm h.1, R₂.symm h.2⟩

/-! ### The asymmetric part -/

section Asymmetrize

variable {R R₁ R₂ : SetRel α α} {a b : α}

variable (R) in
/-- The pairs a relation relates in one direction only, the complement of its symmetric part
`SetRel.symmetrize` within it. -/
def asymmetrize : SetRel α α := R \ R.inv

@[simp, grind =] theorem mem_asymmetrize : a ~[R.asymmetrize] b ↔ a ~[R] b ∧ ¬ b ~[R] a := .rfl

theorem asymmetrize_subset_self : R.asymmetrize ⊆ R := Set.sdiff_subset

theorem asymmetrize_eq_sdiff_symmetrize : R.asymmetrize = R \ R.symmetrize := by
  ext ⟨a, b⟩; simp [symmetrize, asymmetrize]

instance isIrrefl_asymmetrize : R.asymmetrize.IsIrrefl := ⟨fun _ h ↦ h.2 h.1⟩

instance isTrans_asymmetrize [R.IsTrans] : R.asymmetrize.IsTrans :=
  ⟨fun _ _ _ h h' ↦ ⟨R.trans h.1 h'.1, fun h'' ↦ h.2 (R.trans h'.1 h'')⟩⟩

instance [DecidablePred (· ∈ R)] : DecidablePred (· ∈ R.asymmetrize) := fun p ↦
  inferInstanceAs (Decidable (p ∈ R ∧ ¬ (p.2, p.1) ∈ R))

theorem asymmetrize_image_prodMap {β : Type*} {f : α → β} (hf : Function.Injective f) :
    asymmetrize (Prod.map f f '' R) = Prod.map f f '' R.asymmetrize := by
  rw [asymmetrize, inv_image_prodMap, ← Set.image_sdiff (hf.prodMap hf)]; rfl

end Asymmetrize

/-! ### Correspondences -/

/-- The graph of a correspondence `f : α → Set β`, the relation of `a` to every member of
`f a`. -/
def cgraph (f : α → Set β) : SetRel α β := {p | p.2 ∈ f p.1}

variable {f g : α → Set β} {y : β}

@[simp, grind =] theorem mem_cgraph : a ~[cgraph f] y ↔ y ∈ f a := .rfl

theorem mem_core_cgraph : a ∈ (cgraph f).core t ↔ f a ⊆ t := .rfl

theorem mem_preimage_cgraph : a ∈ (cgraph f).preimage t ↔ (f a ∩ t).Nonempty :=
  ⟨fun ⟨b, hb, hab⟩ ↦ ⟨b, hab, hb⟩, fun ⟨b, hab, hb⟩ ↦ ⟨b, hb, hab⟩⟩

theorem dom_cgraph (f : α → Set β) : (cgraph f).dom = {a | (f a).Nonempty} := rfl

instance (f : α → Set β) [∀ a, DecidablePred (· ∈ f a)] : DecidablePred (· ∈ cgraph f) :=
  fun p ↦ inferInstanceAs (Decidable (p.2 ∈ f p.1))

theorem image_cgraph (f : α → Set β) (s : Set α) :
    (cgraph f).image s = ⋃ a ∈ s, f a := by
  ext; simp [image]

@[simp] theorem image_cgraph_singleton (f : α → Set β) (a : α) :
    (cgraph f).image {a} = f a := by
  ext; simp [image]

theorem image_singleton_eq_ball_inv (R : SetRel α β) (a : α) : R.image {a} = R.inv.ball a := by
  ext; simp [image]

/-- A relation is the graph of the correspondence sending a point to the points it relates
to. -/
theorem cgraph_ball_inv (R : SetRel α β) : cgraph (fun a ↦ R.inv.ball a) = R := rfl

@[gcongr]
theorem cgraph_subset_cgraph (h : f ≤ g) : cgraph f ⊆ cgraph g := fun _ hb ↦ h _ hb

@[simp] theorem cgraph_subset_cgraph_iff : cgraph f ⊆ cgraph g ↔ f ≤ g :=
  ⟨fun h _ _ hb ↦ h (mem_cgraph.2 hb), cgraph_subset_cgraph⟩

/-- Correspondences are relations: the graph of a correspondence is an order isomorphism, whose
inverse sends a relation to the correspondence of each point to the points it relates to. -/
def cgraphOrderIso : (α → Set β) ≃o SetRel α β where
  toFun := cgraph
  invFun R a := R.inv.ball a
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := cgraph_subset_cgraph_iff

@[simp] theorem coe_cgraphOrderIso : ⇑(cgraphOrderIso : (α → Set β) ≃o SetRel α β) = cgraph :=
  rfl

@[simp] theorem cgraphOrderIso_symm_apply (R : SetRel α β) (a : α) :
    cgraphOrderIso.symm R a = R.inv.ball a := rfl

theorem isRefl_cgraph_iff {f : α → Set α} : (cgraph f).IsRefl ↔ ∀ a, a ∈ f a :=
  ⟨fun h ↦ h.refl, fun h ↦ ⟨h⟩⟩

theorem isSymm_cgraph_iff {f : α → Set α} : (cgraph f).IsSymm ↔ ∀ a, ∀ b ∈ f a, a ∈ f b :=
  ⟨fun h a b hb ↦ h.symm a b hb, fun h ↦ ⟨fun a b hb ↦ h a b hb⟩⟩

theorem isTrans_cgraph_iff {f : α → Set α} : (cgraph f).IsTrans ↔ ∀ a, ∀ b ∈ f a, f b ⊆ f a :=
  ⟨fun h a b hb c hc ↦ h.trans a b c hb hc, fun h ↦ ⟨fun a b _ hb hc ↦ h a b hb hc⟩⟩

/-! ### Transitive closure -/

/-- The transitive closure of a relation, as a closure operator: the closed relations are the
transitive ones. -/
def transGen : ClosureOperator (SetRel α α) :=
  .ofPred (fun R ↦ {p | Relation.TransGen (· ~[R] ·) p.1 p.2}) SetRel.IsTrans
    (fun _ _ h ↦ .single h) (fun _ ↦ ⟨fun _ _ _ ↦ Relation.TransGen.trans⟩)
    (fun _ S h hS ⟨a, b⟩ hab ↦ haveI := hS
      Relation.transGen_minimal (r' := (· ~[S] ·)) (fun _ _ h' ↦ h h') a b hab)

variable {R : SetRel α α} {s : Set α}

@[simp, grind =] theorem mem_transGen :
    a ~[transGen R] b ↔ Relation.TransGen (· ~[R] ·) a b := .rfl

theorem isClosed_transGen_iff : transGen.IsClosed R ↔ R.IsTrans := .rfl

theorem subset_transGen : R ⊆ transGen R := transGen.le_closure R

instance isTrans_transGen : (transGen R).IsTrans := transGen.isClosed_closure R

instance isPreorder_transGen [R.IsRefl] : (transGen R).IsPreorder where
  refl a := .single (R.refl a)
  trans _ _ _ := (transGen R).trans

instance isSymm_transGen [R.IsSymm] : (transGen R).IsSymm where
  symm a b h := by
    change Relation.TransGen (· ~[R] ·) a b at h
    induction h with
    | single h => exact .single (R.symm h)
    | tail _ h ih => exact Relation.TransGen.head (R.symm h) ih

/-- The transitive closure of `R` is the least transitive relation containing `R`. -/
theorem transGen_subset_iff {S : SetRel α α} [S.IsTrans] : transGen R ⊆ S ↔ R ⊆ S :=
  ClosureOperator.IsClosed.closure_le_iff (isClosed_transGen_iff.2 inferInstance)

@[gcongr]
theorem transGen_mono {R₁ R₂ : SetRel α α} (h : R₁ ⊆ R₂) : transGen R₁ ⊆ transGen R₂ :=
  transGen.monotone h

@[simp] theorem transGen_eq_self [R.IsTrans] : transGen R = R :=
  ClosureOperator.IsClosed.closure_eq (isClosed_transGen_iff.2 inferInstance)

theorem core_transGen_subset_core : (transGen R).core s ⊆ R.core s :=
  core_subset_core_left subset_transGen

theorem core_transGen : (transGen R).core s = ⋂ n, R.core^[n + 1] s := by
  ext a
  simp only [Set.mem_iInter]
  refine ⟨fun h n ↦ ?_, fun h b hab ↦ ?_⟩
  · induction n generalizing s with
    | zero => exact fun b hab ↦ h (.single hab)
    | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih fun b hab c hbc ↦ h (Relation.TransGen.tail hab hbc)
  · suffices ∀ {b}, Relation.TransGen (· ~[R] ·) a b → ∃ n, ∀ t, a ∈ R.core^[n + 1] t → b ∈ t by
      obtain ⟨n, hn⟩ := this hab
      exact hn s (h n)
    intro b hab
    induction hab with
    | single h => exact ⟨0, fun _ ht ↦ ht h⟩
    | tail _ hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, fun t ht ↦ hn (R.core t)
        (by rwa [Function.iterate_succ_apply] at ht) hbc⟩

end SetRel
