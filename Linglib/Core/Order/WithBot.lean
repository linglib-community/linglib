module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Cover
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.UpperLower.Basic

/-!
# An order and the same order with a least element adjoined

[UPSTREAM] candidate for `Mathlib/Order/WithBot.lean` and `Mathlib/Order/Hom/WithTopBot.lean`.

For a partial order `α`, the elements of `WithBot α` other than `⊥` are those of `α`, and an
order `β` with a least element is `WithBot` of its other elements
(`OrderIso.withBotSubtypeNeBot`). Along the coercion `α → WithBot α` the notions that mention
`⊥` are notions of `α` that do not: an atom is a minimal element (`WithBot.isAtom_coe`), two
elements are disjoint iff they have no common lower bound (`WithBot.disjoint_coe`), and a set is
a lower set iff it is one once `⊥` is adjoined (`WithBot.isLowerSet_insert_bot_image`).
-/

@[expose] public section

namespace WithBot

variable {α : Type*} [PartialOrder α] {a b : α} {s : Set α}

/-- An atom of `WithBot α` is a minimal element of `α`. -/
@[simp] theorem isAtom_coe : IsAtom (a : WithBot α) ↔ IsMin a := by
  rw [← _root_.bot_covBy_iff, bot_covBy_coe]

/-- Two elements of `α` are disjoint in `WithBot α` iff they have no common lower bound. -/
theorem disjoint_coe : Disjoint (a : WithBot α) b ↔ ∀ c, c ≤ a → ¬ c ≤ b := by
  refine ⟨fun h c ha hb ↦ coe_ne_bot (le_bot_iff.1 (h (coe_le_coe.2 ha) (coe_le_coe.2 hb))),
    fun h c ha hb ↦ ?_⟩
  induction c with
  | bot => exact le_rfl
  | coe c => exact absurd (coe_le_coe.1 hb) (h c (coe_le_coe.1 ha))

/-- A set of `α` is a lower set iff it is one in `WithBot α` once `⊥` is adjoined to it. -/
theorem isLowerSet_insert_bot_image :
    IsLowerSet (insert ⊥ ((↑) '' s : Set (WithBot α))) ↔ IsLowerSet s := by
  constructor
  · intro h a b hba ha
    rcases h (coe_le_coe.2 hba) (.inr ⟨a, ha, rfl⟩) with h0 | ⟨c, hc, hcb⟩
    · exact absurd h0 coe_ne_bot
    · exact coe_injective hcb ▸ hc
  · rintro h a b hba (rfl | ⟨c, hc, rfl⟩)
    · exact .inl (le_bot_iff.1 hba)
    · induction b with
      | bot => exact .inl rfl
      | coe b => exact .inr ⟨b, h (coe_le_coe.1 hba) hc, rfl⟩

end WithBot

/-- An order with a least element is its other elements with a least element adjoined. -/
noncomputable def OrderIso.withBotSubtypeNeBot (β : Type*) [PartialOrder β] [OrderBot β] :
    WithBot {x : β // x ≠ ⊥} ≃o β := by
  classical exact
  { toFun := fun x ↦ x.recBotCoe ⊥ (↑)
    invFun := fun b ↦ if h : b = ⊥ then ⊥ else ((⟨b, h⟩ : {x : β // x ≠ ⊥}) : WithBot _)
    left_inv := fun x ↦ by
      induction x with
      | bot => simp
      | coe x => simp [x.2]
    right_inv := fun b ↦ by by_cases h : b = ⊥ <;> simp [h]
    map_rel_iff' := fun {a b} ↦ by
      induction a with
      | bot => simp
      | coe a =>
        induction b with
        | bot => simpa using a.2
        | coe b => simp }

@[simp] theorem OrderIso.withBotSubtypeNeBot_bot {β : Type*} [PartialOrder β] [OrderBot β] :
    OrderIso.withBotSubtypeNeBot β ⊥ = ⊥ := rfl

@[simp] theorem OrderIso.withBotSubtypeNeBot_coe {β : Type*} [PartialOrder β] [OrderBot β]
    (x : {x : β // x ≠ ⊥}) : OrderIso.withBotSubtypeNeBot β x = x := rfl
