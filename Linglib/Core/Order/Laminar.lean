module

public import Linglib.Core.Order.LeftLinear
public import Mathlib.Order.Disjoint

/-!
# Laminar sets

A set of elements of an order with a bottom is [laminar](##IsLaminar) when any two of its members
are comparable or disjoint, as a family of sets is when any two are nested or share no element.
Laminar sets and forests are two views of one structure: the principal up-sets of a left-linear
order [are laminar](##IsLeftLinear.isLaminar_range_Ici), and the members of a laminar set other
than the bottom [are left-linear](##IsLaminar.isLeftLinear) under the reverse order.
-/

@[expose] public section

variable {α : Type*} [PartialOrder α] [OrderBot α] {S T : Set α} {a b m : α}

/-- A set of elements of an order with a bottom is laminar when any two of its members are
comparable or disjoint. -/
def IsLaminar (S : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → a ≤ b ∨ b ≤ a ∨ Disjoint a b

namespace IsLaminar

theorem mono (hT : IsLaminar T) (h : S ⊆ T) : IsLaminar S :=
  fun _ ha _ hb ↦ hT (h ha) (h hb)

/-- Two members of a laminar set above a common element other than the bottom are comparable. -/
theorem le_total_of_le (hS : IsLaminar S) (ha : a ∈ S) (hb : b ∈ S) (hm : m ≠ ⊥)
    (hma : m ≤ a) (hmb : m ≤ b) : a ≤ b ∨ b ≤ a :=
  (or_assoc.2 (hS ha hb)).resolve_right fun h ↦ hm (le_bot_iff.1 (h hma hmb))

/-- The members of a laminar set other than the bottom form a forest under the reverse order. -/
theorem isLeftLinear (hS : IsLaminar S) : IsLeftLinear {a // a ∈ S ∧ a ≠ ⊥}ᵒᵈ :=
  isLeftLinear_orderDual_iff.2 fun a b c ha hb ↦ hS.le_total_of_le a.2.1 b.2.1 c.2.2 ha hb

end IsLaminar

/-- The principal up-sets of a left-linear order are laminar. -/
theorem IsLeftLinear.isLaminar_range_Ici {M : Type*} [PartialOrder M] [IsLeftLinear M] :
    IsLaminar (Set.range (Set.Ici : M → Set M)) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  by_cases hab : a ≤ b
  · exact .inr (.inl (Set.Ici_subset_Ici.2 hab))
  by_cases hba : b ≤ a
  · exact .inl (Set.Ici_subset_Ici.2 hba)
  · exact .inr (.inr (IsLeftLinear.disjoint_Ici_iff.2 ⟨hab, hba⟩))
