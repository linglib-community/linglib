module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.CompleteLattice.Basic

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

* `NaturalLogic.IsAntiAdditive.comp_map_sup`, `NaturalLogic.IsAntiAdditive.map_inf_comp`,
  `NaturalLogic.isAntiAdditive_iInf`: closure under composition with join- and meet-preserving
  maps and under pointwise infima.
* `NaturalLogic.isAntiAdditive_compl`: complementation in a Heyting algebra is anti-additive.
* `NaturalLogic.IsAntiAdditive.map_compl_iff`: an anti-additive map between Boolean algebras
  commutes with complementation iff it is anti-multiplicative and exchanges `⊥` with `⊤`.

## Implementation notes

Zwarts and Icard state the definitions for maps between Boolean algebras; only the join and the
meet are needed. Anti-multiplicativity and its lemmas are generated from anti-additivity by
`to_dual`.

## References

* [zwarts-1998]
* [icard-2012]
-/

@[expose] public section

namespace NaturalLogic

variable {α β γ : Type*}

/-- A map is anti-additive if it sends joins to meets ([zwarts-1998] (107)). -/
@[to_dual IsAntiMultiplicative
  /-- A map is anti-multiplicative if it sends meets to joins ([icard-2012] Definition 1.7). -/]
def IsAntiAdditive [Max α] [Min β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊔ q) = f p ⊓ f q

@[to_dual]
theorem IsAntiAdditive.antitone [SemilatticeSup α] [SemilatticeInf β] {f : α → β}
    (h : IsAntiAdditive f) : Antitone f :=
  Monotone.of_map_sup (β := βᵒᵈ) h

/-! ### Closure -/

@[to_dual]
theorem IsAntiAdditive.comp_map_sup [Max α] [Min β] [Max γ] {f : α → β} {g : γ → α}
    (hf : IsAntiAdditive f) (hg : ∀ a b, g (a ⊔ b) = g a ⊔ g b) : IsAntiAdditive (f ∘ g) :=
  fun p q ↦ (congrArg f (hg p q)).trans (hf _ _)

@[to_dual]
theorem IsAntiAdditive.map_inf_comp [Max α] [Min β] [Min γ] {f : α → β} {g : β → γ}
    (hf : IsAntiAdditive f) (hg : ∀ a b, g (a ⊓ b) = g a ⊓ g b) : IsAntiAdditive (g ∘ f) :=
  fun p q ↦ (congrArg g (hf p q)).trans (hg _ _)

/-- Anti-additive maps are closed under pointwise infima, generalizing the binary case of
[icard-2012] Lemma 1.12. -/
@[to_dual isAntiMultiplicative_iSup]
theorem isAntiAdditive_iInf {ι : Sort*} [Max α] [CompleteLattice β] {f : ι → α → β}
    (h : ∀ i, IsAntiAdditive (f i)) : IsAntiAdditive fun a ↦ ⨅ i, f i a :=
  fun p q ↦ (iInf_congr fun i ↦ h i p q).trans iInf_inf_eq

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

variable {δ : Type*}

theorem isAntiAdditive_iff_mem {f : Set γ → Set δ} :
    IsAntiAdditive f ↔ ∀ p q x, x ∈ f (p ∪ q) ↔ x ∈ f p ∧ x ∈ f q := by
  simp only [IsAntiAdditive, Set.sup_eq_union, Set.inf_eq_inter, Set.ext_iff,
    Set.mem_inter_iff]

theorem isAntiAdditive_forall_mem (P : γ → δ → Prop) :
    IsAntiAdditive fun (X : Set γ) (y : δ) ↦ ∀ x ∈ X, P x y :=
  fun _ _ ↦ funext fun _ ↦ propext <| by simp [or_imp, forall_and]

end Set

end NaturalLogic
