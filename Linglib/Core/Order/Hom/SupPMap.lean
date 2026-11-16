module

public import Linglib.Core.Order.SetRel

/-!
# Partially defined join homomorphisms

A `SupPMap α β`, written `α →⊔. β`, is a map into `β` from a subset of `α` closed under joins,
preserving joins, as mathlib's `LinearPMap` is a linear map from a submodule. `[UPSTREAM]`.
[Its graph](##SupPMap.graph) is a relation closed under joins that relates each argument to one
value, and [every such relation is the graph](##SetRel.graph_toSupPMap) of a partially defined
join homomorphism on its domain.

## Implementation notes

Mathlib has no bundled subsemilattice, so the domain is a set with a proof of `SupClosed`, and
`SetRel.toSupPMap` takes the two conditions on the relation as hypotheses where
`Submodule.toLinearPMap` falls back on the zero map.
-/

@[expose] public section

open Set
open scoped SetRel

/-- A partially defined join homomorphism: a map into `β` from a subset of `α` closed under
joins, preserving joins. -/
structure SupPMap (α β : Type*) [SemilatticeSup α] [SemilatticeSup β] where
  /-- The domain of the map. -/
  domain : Set α
  /-- The domain is closed under joins. -/
  supClosed_domain : SupClosed domain
  /-- The map itself. -/
  toFun : domain → β
  /-- The map preserves joins. -/
  map_sup' : ∀ a b : domain, toFun ⟨a ⊔ b, supClosed_domain a.2 b.2⟩ = toFun a ⊔ toFun b

@[inherit_doc] infixr:25 " →⊔. " => SupPMap

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

namespace SupPMap

instance : CoeFun (α →⊔. β) fun f ↦ f.domain → β := ⟨toFun⟩

@[simp]
theorem toFun_eq_coe (f : α →⊔. β) (a : f.domain) : f.toFun a = f a := rfl

theorem map_sup (f : α →⊔. β) (a b : f.domain) :
    f ⟨a ⊔ b, f.supClosed_domain a.2 b.2⟩ = f a ⊔ f b :=
  f.map_sup' a b

/-- A partially defined join homomorphism is monotone on its domain. -/
theorem mono (f : α →⊔. β) : Monotone f := fun a b h ↦ by
  have hb : (⟨a ⊔ b, f.supClosed_domain a.2 b.2⟩ : f.domain) = b :=
    Subtype.ext (sup_eq_right.2 h)
  rw [← hb, f.map_sup]
  exact le_sup_left

/-- A join homomorphism as a partially defined one, defined everywhere. -/
def ofSupHom {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) : α →⊔. β where
  domain := univ
  supClosed_domain := supClosed_univ
  toFun a := f a
  map_sup' _ _ := SupHomClass.map_sup f _ _

/-- The graph of a partially defined join homomorphism, as a relation. -/
def graph (f : α →⊔. β) : SetRel α β := {(a, b) | ∃ h : a ∈ f.domain, f ⟨a, h⟩ = b}

@[simp]
theorem mem_graph {f : α →⊔. β} {a : α} {b : β} :
    a ~[f.graph] b ↔ ∃ h : a ∈ f.domain, f ⟨a, h⟩ = b :=
  .rfl

@[simp]
theorem dom_graph (f : α →⊔. β) : f.graph.dom = f.domain :=
  Set.ext fun _ ↦ ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨_, h, rfl⟩⟩

theorem supClosed_graph (f : α →⊔. β) : SupClosed f.graph := by
  rintro ⟨a, _⟩ ⟨ha, rfl⟩ ⟨b, _⟩ ⟨hb, rfl⟩
  exact ⟨f.supClosed_domain ha hb, f.map_sup ⟨a, ha⟩ ⟨b, hb⟩⟩

/-- The graph relates each argument to one value. -/
theorem injOn_fst_graph (f : α →⊔. β) : InjOn Prod.fst f.graph := by
  rintro ⟨a, _⟩ ⟨_, rfl⟩ ⟨_, _⟩ ⟨_, rfl⟩ (rfl : a = _)
  rfl

@[simp]
theorem graph_ofSupHom {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) :
    (ofSupHom f).graph = Function.graph f :=
  Set.ext fun _ ↦ ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨mem_univ _, h⟩⟩

end SupPMap

namespace SetRel

variable {R : SetRel α β}

/-- A relation closed under joins that relates each argument to one value, as a partially
defined join homomorphism on its domain. -/
noncomputable def toSupPMap (R : SetRel α β) (hR : SupClosed R) (hf : InjOn Prod.fst R) :
    α →⊔. β where
  domain := R.dom
  supClosed_domain := fun _ ⟨_, ha⟩ _ ⟨_, hb⟩ ↦ ⟨_, hR ha hb⟩
  toFun a := a.2.choose
  map_sup' a b := congr_arg Prod.snd
    (hf (Exists.choose_spec (⟨_, hR a.2.choose_spec b.2.choose_spec⟩ : (a ⊔ b : α) ∈ R.dom))
      (hR a.2.choose_spec b.2.choose_spec) rfl)

@[simp]
theorem domain_toSupPMap (hR : SupClosed R) (hf : InjOn Prod.fst R) :
    (R.toSupPMap hR hf).domain = R.dom :=
  rfl

/-- A relation closed under joins that relates each argument to one value is the graph of its
partially defined join homomorphism. -/
@[simp]
theorem graph_toSupPMap (hR : SupClosed R) (hf : InjOn Prod.fst R) :
    (R.toSupPMap hR hf).graph = R :=
  Set.ext fun ⟨a, b⟩ ↦
    ⟨fun ⟨h, hb⟩ ↦ hb ▸ h.choose_spec, fun hab ↦
      have h : a ∈ R.dom := ⟨b, hab⟩
      ⟨h, congr_arg Prod.snd (hf h.choose_spec hab rfl)⟩⟩

end SetRel
