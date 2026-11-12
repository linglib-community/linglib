/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Flat
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Setoid.Basic

/-!
# Patterns and subsumption

A pattern over a type of positions gives each position its content and says which positions are
coindexed. A slot below a maximal element is a variable, and coindexed variables are filled alike,
as the second root consonant of the Damascus Arabic template $C_1aC_2C_2aaC_3$ is. Patterns are
ordered by subsumption: `s ≤ t` when `t` has at least the content and at least the coindexation
of `s`. This is the subsumption of [shieber-1986] and [carpenter-1992] for feature structures of
depth one, with coindexation as reentrancy.

A word is a pattern whose slots are all maximal, and a pattern written as a row of constants and
named variables subsumes exactly [its substitution instances](##ofTerms_le_ofItem_iff). The meet
of two patterns is their least general generalization in the sense of [plotkin-1970]: it coindexes
two positions exactly when both do. A schema that relates two words is a pattern over the disjoint
union of their positions, and once it coindexes a position of each, the pairs it subsumes are
[not a product of conditions on the words separately](##setOf_le_ofItem_sumElim_ne_prod).

## Implementation notes

Positions that carry the same maximal content are always coindexed. Without this condition a
constant written twice could be coindexed or not, giving two patterns with the same instances.
The index type of a schema's notation is not part of a pattern: `Pattern.ofSubscript` and
`Pattern.ofTerms` keep only which positions share an index.

## References

* [shieber-1986]
* [carpenter-1992]
* [plotkin-1970]
* [booij-2019]
-/

@[expose] public section

namespace Flat
variable {α : Type*} {x : Flat α}

/-- Over a nonempty type the maximal slots are the committed ones. -/
theorem isMax_iff_ne_bot [Nonempty α] : IsMax x ↔ x ≠ ⊥ :=
  ⟨by rintro h rfl; exact not_coe_le_bot (Classical.arbitrary α) (h bot_le), isMax_of_ne_bot⟩

instance [Nonempty α] [DecidableEq α] (x : Flat α) : Decidable (IsMax x) :=
  decidable_of_iff _ isMax_iff_ne_bot.symm

end Flat

namespace ConstructionMorphology

variable {P Q P₁ P₂ X α β : Type*}

/-- A pattern over the positions `P` gives each position its content and says which positions are
coindexed. -/
@[ext]
structure Pattern (P α : Type*) [LE α] where
  /-- The content at each position. -/
  content : P → α
  /-- The coindexation of positions. -/
  coindex : Setoid P
  /-- Coindexed positions carry the same content. -/
  content_eq : ∀ ⦃p q⦄, coindex p q → content p = content q
  /-- Positions that carry the same maximal content are coindexed. -/
  coindex_of_isMax : ∀ ⦃p q⦄, content p = content q → IsMax (content p) → coindex p q

namespace Pattern

/-! ### Constructors -/

section LE
variable [LE α]

/-- The pattern with content `c` whose coindexation is `r` together with the sameness of maximal
content. -/
def of (c : P → α) (r : Setoid P) (h : r ≤ Setoid.ker c) : Pattern P α where
  content := c
  coindex :=
    { r := fun p q ↦ r p q ∨ c p = c q ∧ IsMax (c p)
      iseqv :=
        ⟨fun p ↦ .inl (r.refl' p),
          fun hpq ↦ hpq.imp r.symm' fun ⟨he, hm⟩ ↦ ⟨he.symm, he ▸ hm⟩,
          fun hpq hqk ↦ by
            rcases hpq with hpq | ⟨he, hm⟩ <;> rcases hqk with hqk | ⟨he', hm'⟩
            · exact .inl (r.trans' hpq hqk)
            · exact .inr ⟨(h hpq).trans he', (h hpq).symm ▸ hm'⟩
            · exact .inr ⟨he.trans (h hqk), hm⟩
            · exact .inr ⟨he.trans he', hm⟩⟩ }
  content_eq := fun _ _ hpq ↦ hpq.elim (fun hr ↦ h hr) And.left
  coindex_of_isMax := fun _ _ he hm ↦ .inr ⟨he, hm⟩

@[simp] theorem content_of (c : P → α) (r : Setoid P) (h) : (of c r h).content = c := rfl

theorem coindex_of_iff {c : P → α} {r : Setoid P} {h} {p q : P} :
    (of c r h).coindex p q ↔ r p q ∨ c p = c q ∧ IsMax (c p) :=
  Iff.rfl

/-- An item as a pattern, coindexed only where it carries the same maximal content. -/
def ofItem (w : P → α) : Pattern P α := of w ⊥ bot_le

/-- The pattern of a subscripting of positions by indices and the content of each index. -/
def ofSubscript (pos : P → X) (body : X → α) : Pattern P α :=
  of (body ∘ pos) (Setoid.ker pos) fun _ _ h ↦ congrArg body h

/-- The pattern read at the positions `Q` through `f`. -/
def comap (f : Q → P) (s : Pattern P α) : Pattern Q α where
  content := s.content ∘ f
  coindex := s.coindex.comap f
  content_eq := fun _ _ h ↦ s.content_eq h
  coindex_of_isMax := fun _ _ he hm ↦ s.coindex_of_isMax he hm

theorem comap_ofItem (f : Q → P) (hf : f.Injective) (w : P → α) :
    (ofItem w).comap f = ofItem (w ∘ f) :=
  Pattern.ext rfl <| Setoid.ext fun _ _ ↦ or_congr hf.eq_iff Iff.rfl

end LE

/-- A pattern written as a row of constants and named variables, as $C_1aC_2C_2aaC_3$. -/
def ofTerms (t : P → β ⊕ X) : Pattern P (Flat β) :=
  ofSubscript t (Sum.elim Flat.some fun _ ↦ ⊥)

/-! ### Subsumption -/

section PartialOrder
variable [PartialOrder α] {s t : Pattern P α} {w : P → α}

/-- Subsumption: `s ≤ t` when `t` has at least the content and at least the coindexation of
`s`. -/
instance : PartialOrder (Pattern P α) :=
  PartialOrder.lift (fun s ↦ (s.content, s.coindex)) fun _ _ h ↦
    Pattern.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem le_def : s ≤ t ↔ s.content ≤ t.content ∧ s.coindex ≤ t.coindex := Iff.rfl

theorem comap_mono (f : Q → P) : Monotone (comap (α := α) f) :=
  fun _ _ h ↦ ⟨fun q ↦ h.1 (f q), fun _ _ hq ↦ h.2 hq⟩

theorem ofItem_mono : Monotone (ofItem : (P → α) → Pattern P α) := fun _ _ h ↦
  ⟨h, fun p q hpq ↦ hpq.imp id fun ⟨he, hm⟩ ↦
    have hp := hm.eq_of_le (h p)
    ⟨hp.symm.trans ((he ▸ hm).eq_of_le (h q) ▸ he), hp ▸ hm⟩⟩

/-- A pattern subsumes an item whose slots are all maximal exactly when the item extends its
content and fills coindexed positions alike. -/
theorem le_ofItem_iff (hw : ∀ p, IsMax (w p)) :
    s ≤ ofItem w ↔ s.content ≤ w ∧ s.coindex ≤ Setoid.ker w :=
  and_congr_right fun _ ↦
    ⟨fun h _ _ hpq ↦ (h hpq).elim (congrArg w) And.left, fun h p _ hpq ↦ .inr ⟨h hpq, hw p⟩⟩

/-- The pairs of items that a pattern over two sets of positions subsumes are not the product of
a set of first items and a set of second items, once the pattern coindexes a position of each and
two pairs fill those positions differently. -/
theorem setOf_le_ofItem_sumElim_ne_prod {s : Pattern (P₁ ⊕ P₂) α}
    {w₁ w₁' : P₁ → α} {w₂ w₂' : P₂ → α} (h : s ≤ ofItem (Sum.elim w₁ w₂))
    (h' : s ≤ ofItem (Sum.elim w₁' w₂')) {a : P₁} {b : P₂}
    (hab : s.coindex (.inl a) (.inr b)) (hne : w₁ a ≠ w₂' b) (A : Set (P₁ → α))
    (B : Set (P₂ → α)) :
    {(x, y) : (P₁ → α) × (P₂ → α) | s ≤ ofItem (Sum.elim x y)} ≠ A ×ˢ B := fun hAB ↦ by
  have hm x y := Set.ext_iff.1 hAB (x, y)
  have hs : s ≤ ofItem (Sum.elim w₁ w₂') :=
    (hm w₁ w₂').2 ⟨((hm _ _).1 h).1, ((hm _ _).1 h').2⟩
  exact hne ((hs.2 hab).elim (fun e ↦ nomatch e) And.left)

end PartialOrder

/-- The meet of two patterns has the meet of their content and coindexes two positions exactly
when both do. -/
instance [SemilatticeInf α] : SemilatticeInf (Pattern P α) where
  inf s t :=
    { content := s.content ⊓ t.content
      coindex := s.coindex ⊓ t.coindex
      content_eq := fun p q h ↦ by
        simp only [Pi.inf_apply, s.content_eq h.1, t.content_eq h.2]
      coindex_of_isMax := fun p q he hm ↦ by
        have he' : s.content p ⊓ t.content p = s.content q ⊓ t.content q := he
        have hs := hm.eq_of_le (inf_le_left : s.content p ⊓ t.content p ≤ s.content p)
        have ht := hm.eq_of_le (inf_le_right : s.content p ⊓ t.content p ≤ t.content p)
        have hs' := hm.eq_of_le (he' ▸ inf_le_left : s.content p ⊓ t.content p ≤ s.content q)
        have ht' := hm.eq_of_le (he' ▸ inf_le_right : s.content p ⊓ t.content p ≤ t.content q)
        exact ⟨s.coindex_of_isMax (hs.symm.trans hs') (hs ▸ hm),
          t.coindex_of_isMax (ht.symm.trans ht') (ht ▸ hm)⟩ }
  inf_le_left _ _ := ⟨inf_le_left, inf_le_left⟩
  inf_le_right _ _ := ⟨inf_le_right, inf_le_right⟩
  le_inf _ _ _ h₁ h₂ := ⟨le_inf h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩

/-! ### Rows of constants and variables -/

/-- The words that a row of constants and variables subsumes are its substitution instances. -/
theorem ofTerms_le_ofItem_iff [Nonempty β] {t : P → β ⊕ X} {g : P → β} :
    ofTerms t ≤ ofItem (Flat.some ∘ g) ↔ ∃ x : X → β, g = Sum.elim id x ∘ t := by
  refine (le_ofItem_iff (w := Flat.some ∘ g) fun p ↦ Flat.isMax_coe _).trans ?_
  constructor
  · rintro ⟨hc, hk⟩
    have hf : g.FactorsThrough t := fun p q e ↦ Flat.coe_injective (hk (.inl e))
    refine ⟨fun v ↦ Function.extend t g (fun _ ↦ Classical.arbitrary β) (.inr v),
      funext fun p ↦ ?_⟩
    have hp := hc p
    simp only [ofTerms, ofSubscript, content_of, Function.comp_apply] at hp ⊢
    rcases e : t p with b | v
    · rw [e] at hp
      exact (Flat.coe_le_coe.1 hp).symm
    · rw [Sum.elim_inr, ← e, hf.extend_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨fun p ↦ ?_, fun p q hpq ↦ ?_⟩
    · simp only [ofTerms, ofSubscript, content_of, Function.comp_apply]
      rcases t p with b | v
      · exact le_rfl
      · exact bot_le
    · rcases hpq with hpq | ⟨he, hm⟩
      · exact congrArg (fun y ↦ Flat.some (Sum.elim id x y)) hpq
      · simp only [Function.comp_apply] at he hm
        simp only [Setoid.ker_def, Function.comp_apply]
        rcases ep : t p with b | v <;> rcases eq : t q with b' | v' <;> rw [ep] at he hm <;>
          rw [eq] at he
        · exact he
        · exact absurd he Flat.coe_ne_bot
        · exact absurd he.symm Flat.coe_ne_bot
        · exact absurd rfl (Flat.isMax_iff_ne_bot.1 hm)

/-- The pairs of words that a row over two sets of positions subsumes are the two readings of one
substitution. -/
theorem ofTerms_sumElim_le_ofItem_iff [Nonempty β] {t₁ : P₁ → β ⊕ X} {t₂ : P₂ → β ⊕ X}
    {g₁ : P₁ → β} {g₂ : P₂ → β} :
    ofTerms (Sum.elim t₁ t₂) ≤ ofItem (Sum.elim (Flat.some ∘ g₁) (Flat.some ∘ g₂)) ↔
      ∃ x : X → β, g₁ = Sum.elim id x ∘ t₁ ∧ g₂ = Sum.elim id x ∘ t₂ := by
  rw [← Sum.comp_elim, ofTerms_le_ofItem_iff]
  simp only [Sum.comp_elim, Sum.elim_eq_iff]

/-! ### Decidability -/

instance [LE α] [DecidableEq α] [∀ a : α, Decidable (IsMax a)] (c : P → α) (r : Setoid P) (h)
    [DecidableRel r] : DecidableRel (of c r h).coindex :=
  fun p q ↦ inferInstanceAs (Decidable (r p q ∨ c p = c q ∧ IsMax (c p)))

instance [LE α] [DecidableEq P] [DecidableEq α] [∀ a : α, Decidable (IsMax a)] (w : P → α) :
    DecidableRel (ofItem w).coindex :=
  fun p q ↦ inferInstanceAs (Decidable (p = q ∨ w p = w q ∧ IsMax (w p)))

instance [LE α] [DecidableEq X] [DecidableEq α] [∀ a : α, Decidable (IsMax a)] (pos : P → X)
    (body : X → α) : DecidableRel (ofSubscript pos body).coindex :=
  fun p q ↦ inferInstanceAs
    (Decidable (pos p = pos q ∨ body (pos p) = body (pos q) ∧ IsMax (body (pos p))))

instance [Nonempty β] [DecidableEq β] [DecidableEq X] (t : P → β ⊕ X) :
    DecidableRel (ofTerms t).coindex :=
  inferInstanceAs (DecidableRel (ofSubscript t _).coindex)

instance [LE α] (f : Q → P) (s : Pattern P α) [DecidableRel s.coindex] :
    DecidableRel (s.comap f).coindex :=
  fun p q ↦ inferInstanceAs (Decidable (s.coindex (f p) (f q)))

instance [SemilatticeInf α] (s t : Pattern P α) [DecidableRel s.coindex]
    [DecidableRel t.coindex] : DecidableRel (s ⊓ t).coindex :=
  fun p q ↦ inferInstanceAs (Decidable (s.coindex p q ∧ t.coindex p q))

instance [PartialOrder α] [Fintype P] [DecidableLE (P → α)] (s t : Pattern P α)
    [DecidableRel s.coindex] [DecidableRel t.coindex] : Decidable (s ≤ t) :=
  inferInstanceAs (Decidable (s.content ≤ t.content ∧ ∀ ⦃p q⦄, s.coindex p q → t.coindex p q))

end Pattern
end ConstructionMorphology
