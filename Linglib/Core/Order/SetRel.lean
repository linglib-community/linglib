module

public import Mathlib.Basic.Rel
public import Mathlib.Order.Hom.Lattice
public import Mathlib.Order.SupClosed

/-!
# Relations between ordered types

`[UPSTREAM]` supplements to `Mathlib/Order/SupClosed.lean` for a relation between two ordered
types, as a set of pairs in their product. A relation between join-semilattices that is closed
under joins of pairs is the relational form of a join homomorphism:
[the graph of a function is closed under joins](##SetRel.supClosed_graph_iff) exactly when the
function preserves them, and such a relation
[sends sets closed under joins to sets closed under joins](##SupClosed.relImage).
-/

@[expose] public section

open Set Function
open scoped SetRel

variable {α β : Type*}

namespace SetRel

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {R : SetRel α β}

@[simp]
theorem supClosed_inv : SupClosed R.inv ↔ SupClosed R :=
  ⟨fun h _ ha _ hb ↦ h (a := Prod.swap _) ha (b := Prod.swap _) hb, fun h _ ha _ hb ↦ h ha hb⟩

alias ⟨_, _root_.SupClosed.relInv⟩ := supClosed_inv

/-- The graph of a function is closed under joins iff the function preserves them. -/
theorem supClosed_graph_iff {f : α → β} :
    SupClosed (graph f) ↔ ∀ a b, f (a ⊔ b) = f a ⊔ f b :=
  ⟨fun h a b ↦ h (a := (a, f a)) rfl (b := (b, f b)) rfl,
    fun h _ ha _ hb ↦ (h _ _).trans (congr_arg₂ (· ⊔ ·) ha hb)⟩

theorem supClosed_graph {F : Type*} [FunLike F α β] [SupHomClass F α β] (f : F) :
    SupClosed (graph f) :=
  supClosed_graph_iff.2 (map_sup f)

end SemilatticeSup

/-- The graph of a function relates each argument to one value. -/
theorem injOn_fst_graph (f : α → β) : InjOn Prod.fst (graph f) :=
  fun _ ha _ hb h ↦ Prod.ext h (ha.symm.trans ((congr_arg f h).trans hb))

/-- The graph of a function relates each value to one argument iff the function is injective. -/
theorem injOn_snd_graph_iff {f : α → β} : InjOn Prod.snd (graph f) ↔ Injective f :=
  ⟨fun h a b hab ↦ congr_arg Prod.fst (h (x₁ := (a, f a)) rfl (x₂ := (b, f b)) rfl hab),
    fun h _ ha _ hb hab ↦ Prod.ext (h (ha.trans (hab.trans hb.symm))) hab⟩

end SetRel

/-- The image of a set closed under joins, under a relation closed under joins, is closed under
joins. -/
theorem SupClosed.relImage [SemilatticeSup α] [SemilatticeSup β] {R : SetRel α β} {s : Set α}
    (hR : SupClosed R) (hs : SupClosed s) : SupClosed (R.image s) :=
  fun _ ⟨_, ha, hab⟩ _ ⟨_, ha', hab'⟩ ↦ ⟨_, hs ha ha', hR hab hab'⟩
