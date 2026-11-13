module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Concept
public import Mathlib.Order.Hom.Lattice

/-!
# Anti-additive and anti-multiplicative maps

This file defines anti-additive maps, which send joins to meets, and anti-multiplicative maps,
which send meets to joins. They are [the join- and meet-preserving maps into the order
dual](##IsAntiAdditive.toSupHom), so both are antitone, and they are closed under composition with
lattice homomorphisms and under pointwise infima. The [polar](##isAntiAdditive_upperPolar) of a
relation is anti-additive. Zwarts grades negative expressions by such properties: *no one* is
anti-additive, and *not*, which also commutes with complementation, is antimorphic. Over Boolean
algebras the antimorphic maps are [exactly](##IsAntiAdditive.map_compl_iff) the maps that are both
anti-additive and anti-multiplicative and exchange `⊥` with `⊤`.

## Implementation notes

Zwarts and Icard state the definitions for maps between Boolean algebras; only the join and the
meet are needed. The properties are predicates on a function, as `Antitone` is, since a
grammatical operator is asked whether it has them. Anti-multiplicativity and its lemmas are
generated from anti-additivity by `to_dual`.

## References

* [zwarts-1998]
* [icard-2012]
-/

@[expose] public section
variable {F α β γ : Type*}

/-- A map is anti-additive if it sends joins to meets ([zwarts-1998] (107)). -/
@[to_dual IsAntiMultiplicative
  /-- A map is anti-multiplicative if it sends meets to joins ([icard-2012] Definition 1.7). -/]
def IsAntiAdditive [Max α] [Min β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊔ q) = f p ⊓ f q

@[to_dual]
theorem IsAntiAdditive.antitone [SemilatticeSup α] [SemilatticeInf β] {f : α → β}
    (h : IsAntiAdditive f) : Antitone f :=
  Monotone.of_map_sup (β := βᵒᵈ) h

/-! ### Homomorphisms into the order dual -/

/-- An anti-additive map as a join-preserving map into the order dual. -/
@[to_dual /-- An anti-multiplicative map as a meet-preserving map into the order dual. -/]
def IsAntiAdditive.toSupHom [Max α] [Min β] {f : α → β} (h : IsAntiAdditive f) : SupHom α βᵒᵈ :=
  ⟨OrderDual.toDual ∘ f, h⟩

/-- A join-preserving map into the order dual is anti-additive. -/
@[to_dual isAntiMultiplicative_ofDual_comp
  /-- A meet-preserving map into the order dual is anti-multiplicative. -/]
theorem isAntiAdditive_ofDual_comp [Max α] [Min β] [FunLike F α βᵒᵈ] [SupHomClass F α βᵒᵈ]
    (g : F) : IsAntiAdditive (OrderDual.ofDual ∘ g) :=
  fun p q ↦ congrArg OrderDual.ofDual (map_sup g p q)

/-! ### Closure -/

@[to_dual]
theorem IsAntiAdditive.comp_map_sup [Max α] [Min β] [Max γ] {f : α → β} {g : γ → α}
    (hf : IsAntiAdditive f) (hg : ∀ a b, g (a ⊔ b) = g a ⊔ g b) : IsAntiAdditive (f ∘ g) :=
  fun p q ↦ (congrArg f (hg p q)).trans (hf _ _)

@[to_dual]
theorem IsAntiAdditive.map_inf_comp [Max α] [Min β] [Min γ] {f : α → β} {g : β → γ}
    (hf : IsAntiAdditive f) (hg : ∀ a b, g (a ⊓ b) = g a ⊓ g b) : IsAntiAdditive (g ∘ f) :=
  fun p q ↦ (congrArg g (hf p q)).trans (hg _ _)

/-- An anti-additive map after a join-preserving homomorphism is anti-additive. -/
@[to_dual]
theorem IsAntiAdditive.comp_supHom [Max α] [Min β] [Max γ] [FunLike F γ α] [SupHomClass F γ α]
    {f : α → β} (hf : IsAntiAdditive f) (g : F) : IsAntiAdditive (f ∘ g) :=
  hf.comp_map_sup (map_sup g)

/-- A meet-preserving homomorphism after an anti-additive map is anti-additive. -/
@[to_dual]
theorem IsAntiAdditive.infHom_comp [Max α] [Min β] [Min γ] [FunLike F β γ] [InfHomClass F β γ]
    {f : α → β} (g : F) (hf : IsAntiAdditive f) : IsAntiAdditive (g ∘ f) :=
  hf.map_inf_comp (map_inf g)

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

/-- The polar of a relation is anti-additive: what is related to everything in a union is
related to everything in each part. -/
theorem isAntiAdditive_upperPolar (r : γ → δ → Prop) : IsAntiAdditive (upperPolar r) :=
  upperPolar_union r

theorem isAntiAdditive_lowerPolar (r : γ → δ → Prop) : IsAntiAdditive (lowerPolar r) :=
  lowerPolar_union r

end Set

