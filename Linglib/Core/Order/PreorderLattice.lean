module

public import Mathlib.Order.CompleteLattice.Defs

/-!
# The complete lattice of preorders on a type

The preorders on a type, ordered by inclusion of their relations, [form a complete
lattice](##instCompleteLattice), as the equivalence relations on a type do
(`Setoid.completeLattice`). The top preorder relates every two elements, the bottom preorder is
equality, and the infimum of a family relates two elements when every member of the family does.

## Implementation notes

[UPSTREAM] candidate: mathlib orders `Setoid α` in `Mathlib.Data.Setoid.Basic` but not
`Preorder α`. `ofLE` supplies the strict order because the default proof of `lt_iff_le_not_ge`
fails when the relation is assembled from another preorder's `≤`, as the meet's is.

Instance search keys the `DecidableRel` instances of `⊤` and `⊥` on `≤` alone, so the instance of
`⊥` also decides any preorder whose relation unfolds to an equation, such as `r a b = true` for a
`Bool`-valued `r`. A preorder given as a term needs its own instance.
-/

@[expose] public section

namespace Preorder

variable {α : Type*}

/-- The preorder of a reflexive transitive relation, with `a < b ↔ a ≤ b ∧ ¬ b ≤ a`. -/
@[reducible] def ofLE (r : α → α → Prop) (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c) : Preorder α where
  le := r
  le_refl := hrefl
  le_trans := htrans
  lt a b := r a b ∧ ¬ r b a
  lt_iff_le_not_ge _ _ := Iff.rfl

/-- Preorders are ordered by inclusion: `p ≤ q` when `q` relates every pair that `p` does. -/
instance : LE (Preorder α) where
  le p q := ∀ ⦃a b⦄, p.le a b → q.le a b

instance : PartialOrder (Preorder α) where
  lt p q := p ≤ q ∧ ¬ q ≤ p
  le_refl _ _ _ h := h
  le_trans _ _ _ hpq hqr _ _ h := hqr (hpq h)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm _ _ hpq hqp := Preorder.ext fun _ _ ↦ ⟨(hpq ·), (hqp ·)⟩

instance : InfSet (Preorder α) where
  sInf S := ofLE (fun a b ↦ ∀ p ∈ S, p.le a b) (fun a p _ ↦ p.le_refl a)
    (fun a b c hab hbc p hp ↦ p.le_trans a b c (hab p hp) (hbc p hp))

instance instCompleteLattice : CompleteLattice (Preorder α) :=
  { completeLatticeOfInf (Preorder α) fun _ ↦
      ⟨fun _ hp _ _ h ↦ h _ hp, fun _ hr _ _ h _ hr' ↦ hr hr' h⟩ with
    inf p q := ofLE (fun a b ↦ p.le a b ∧ q.le a b) (fun a ↦ ⟨p.le_refl a, q.le_refl a⟩)
      fun a b c hab hbc ↦ ⟨p.le_trans a b c hab.1 hbc.1, q.le_trans a b c hab.2 hbc.2⟩
    inf_le_left _ _ _ _ h := h.1
    inf_le_right _ _ _ _ h := h.2
    le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ h, h₂ h⟩
    top := ofLE (fun _ _ ↦ True) (fun _ ↦ trivial) fun _ _ _ _ _ ↦ trivial
    le_top _ _ _ _ := trivial
    bot := ofLE (· = ·) (fun _ ↦ rfl) fun _ _ _ ↦ Eq.trans
    bot_le p _ _ h := h ▸ p.le_refl _ }

@[simp] theorem top_le (a b : α) : (⊤ : Preorder α).le a b := trivial

@[simp] theorem bot_le_iff {a b : α} : (⊥ : Preorder α).le a b ↔ a = b := Iff.rfl

instance : DecidableRel (⊤ : Preorder α).le := fun _ _ ↦ isTrue trivial

instance [DecidableEq α] : DecidableRel (⊥ : Preorder α).le := fun a b ↦ decEq a b

end Preorder
