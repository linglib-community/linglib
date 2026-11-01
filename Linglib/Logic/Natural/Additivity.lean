module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Set.Basic

/-!
# Anti-additive and anti-multiplicative maps

This file defines anti-additive maps, which send joins to meets, and anti-multiplicative maps,
which send meets to joins. They are the join- and meet-preserving maps into the order dual, so
both are antitone. Zwarts grades negative expressions by such properties: *no one* is
anti-additive, and *not*, which also commutes with complementation, is antimorphic. Over Boolean
algebras the antimorphic maps are exactly the maps that are both anti-additive and
anti-multiplicative and exchange `⊥` with `⊤`.

## Main definitions

* `NaturalLogic.IsAntiAdditive`: `f (p ⊔ q) = f p ⊓ f q`.
* `NaturalLogic.IsAntiMultiplicative`: `f (p ⊓ q) = f p ⊔ f q`.

## Main statements

* `NaturalLogic.isAntiAdditive_compl`: complementation in a Heyting algebra is anti-additive.
* `NaturalLogic.IsAntiAdditive.map_compl_iff`: an anti-additive map between Boolean algebras
  commutes with complementation iff it is anti-multiplicative and exchanges `⊥` with `⊤`.

## Implementation notes

Zwarts and Icard state the definitions for maps between Boolean algebras; only the join and the
meet are needed.

## References

* [zwarts-1998]
* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

variable {α β : Type*}

section Semilattice

/-- A map is anti-additive if it sends joins to meets ([zwarts-1998] (107)). -/
def IsAntiAdditive [SemilatticeSup α] [SemilatticeInf β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊔ q) = f p ⊓ f q

/-- A map is anti-multiplicative if it sends meets to joins ([icard-2012] Definition 1.7). -/
def IsAntiMultiplicative [SemilatticeInf α] [SemilatticeSup β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊓ q) = f p ⊔ f q

theorem IsAntiAdditive.antitone [SemilatticeSup α] [SemilatticeInf β] {f : α → β}
    (h : IsAntiAdditive f) : Antitone f :=
  Monotone.of_map_sup (β := βᵒᵈ) h

theorem IsAntiMultiplicative.antitone [SemilatticeInf α] [SemilatticeSup β] {f : α → β}
    (h : IsAntiMultiplicative f) : Antitone f :=
  Monotone.of_map_inf (β := βᵒᵈ) h

end Semilattice

/-! ### Complementation -/

theorem isAntiAdditive_compl [HeytingAlgebra α] : IsAntiAdditive (compl : α → α) :=
  fun _ _ ↦ compl_sup

theorem isAntiMultiplicative_compl [BooleanAlgebra α] : IsAntiMultiplicative (compl : α → α) :=
  fun _ _ ↦ compl_inf

/-- [zwarts-1998]'s antimorphic maps (114) are the anti-additive maps that commute with
complementation. Between Boolean algebras they are the anti-additive and anti-multiplicative maps
that send `⊤` to `⊥` and `⊥` to `⊤`, [icard-2012]'s completely anti-additive and completely
anti-multiplicative maps (Definition 1.7). -/
theorem IsAntiAdditive.map_compl_iff [BooleanAlgebra α] [BooleanAlgebra β] {f : α → β}
    (h : IsAntiAdditive f) :
    (∀ x, f xᶜ = (f x)ᶜ) ↔ f ⊤ = ⊥ ∧ IsAntiMultiplicative f ∧ f ⊥ = ⊤ := by
  refine ⟨fun hc ↦ ?_, fun ⟨ht, hm, hb⟩ x ↦ ?_⟩
  · have ht : f ⊤ = ⊥ := by rw [← sup_compl_eq_top (x := ⊥), h, hc, inf_compl_self]
    refine ⟨ht, fun p q ↦ ?_, by rw [← compl_top, hc, ht, compl_bot]⟩
    rw [← compl_compl (p ⊓ q), compl_inf, hc, h, hc, hc, compl_inf, compl_compl, compl_compl]
  · exact (IsCompl.of_eq (by rw [← h, compl_sup_eq_top, ht])
      (by rw [← hm, compl_inf_eq_bot, hb])).eq_compl

/-! ### Maps on sets -/

section Set

variable {γ δ : Type*}

theorem isAntiAdditive_iff_mem {f : Set γ → Set δ} :
    IsAntiAdditive f ↔ ∀ p q x, x ∈ f (p ∪ q) ↔ x ∈ f p ∧ x ∈ f q := by
  simp only [IsAntiAdditive, Set.sup_eq_union, Set.inf_eq_inter, Set.ext_iff,
    Set.mem_inter_iff]

theorem isAntiAdditive_forall_mem (P : γ → δ → Prop) :
    IsAntiAdditive fun (X : Set γ) (y : δ) ↦ ∀ x ∈ X, P x y :=
  fun _ _ ↦ funext fun _ ↦ propext <| by simp [or_imp, forall_and]

end Set

end NaturalLogic
