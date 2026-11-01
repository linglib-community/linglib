module

public import Linglib.Logic.ComparativeProbability.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.RelClasses

/-!
# Basic API for qualitative probabilities

This file proves the basic API of qualitative probabilities. On a Boolean algebra, qualitative
additivity is equivalent to cancelling a common context disjoint from both sides, the form in
which Kraft, Pratt and Seidenberg and Scott print additivity; with it, comparisons with
disjoint sides merge and removing a null event changes no comparison. A qualitative probability
pulls back along any map that preserves differences and does not send `⊤` to a null event, so
along preimages of sets and along images of an injection whose range is not null.

## Main statements

* `isQualitativeAdditive_iff`: qualitative additivity is context cancellation.
* `isQualitativeProbability_iff`: de Finetti's axioms in their printed form.
* `rel_sup_sup`: comparisons with disjoint sides merge.
* `rel_sdiff_sdiff_iff`: removing a null event changes no comparison.
* `isQualitativeProbability_preimage`, `isQualitativeProbability_image`: pulling back along maps.
* `exists_not_rel_empty_singleton`: a finite carrier has an atom that is not null.

## References

* [kraft-pratt-seidenberg-1959]
* [scott-1964]
-/

@[expose] public section

namespace ComparativeProbability

section Context

variable {α : Type*} [BooleanAlgebra α] {r : α → α → Prop}

/-- A common context `c` disjoint from both sides cancels, so `a ⊔ c ≿ b ⊔ c ↔ a ≿ b`. -/
theorem rel_sup_sup_right_iff [IsQualitativeAdditive r] {a b c : α} (hca : Disjoint c a)
    (hcb : Disjoint c b) : r (a ⊔ c) (b ⊔ c) ↔ r a b := by
  rw [qadd (r := r) a b, qadd (r := r) (a ⊔ c) (b ⊔ c), sup_comm b c, ← sdiff_sdiff_left,
    sup_sdiff_right_self, sdiff_eq_left.mpr hca.symm, sup_comm a c, ← sdiff_sdiff_left,
    sup_sdiff_left_self, sdiff_eq_left.mpr hcb.symm]

theorem rel_sup_sup_right [IsQualitativeAdditive r] {a b c : α} (h : r a b)
    (hca : Disjoint c a) (hcb : Disjoint c b) : r (a ⊔ c) (b ⊔ c) :=
  (rel_sup_sup_right_iff hca hcb).mpr h

/-- A relation is qualitatively additive iff every common context disjoint from both sides
    cancels, the additivity axiom (A) of [kraft-pratt-seidenberg-1959] (p. 408) and axiom (v)
    of de Finetti's in [scott-1964] (p. 246). -/
theorem isQualitativeAdditive_iff : IsQualitativeAdditive r ↔
    ∀ a b c : α, Disjoint c a → Disjoint c b → (r (a ⊔ c) (b ⊔ c) ↔ r a b) := by
  refine ⟨fun _ _ _ _ ↦ rel_sup_sup_right_iff, fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  have := h (a \ b) (b \ a) (a ⊓ b) disjoint_inf_sdiff (inf_comm b a ▸ disjoint_inf_sdiff)
  rwa [sup_sdiff_inf, inf_comm, sup_sdiff_inf] at this

/-- **De Finetti's axioms as printed.** A relation is a qualitative probability iff `⊥` is not
    at least as likely as `⊤`, every event is at least as likely as `⊥`, any two events compare,
    the relation is transitive, and a common context disjoint from both sides cancels: axioms
    (i)–(v) as [scott-1964] lists them (p. 246). -/
theorem isQualitativeProbability_iff : IsQualitativeProbability r ↔
    ¬r ⊥ ⊤ ∧ (∀ a, r a ⊥) ∧ (∀ a b, r a b ∨ r b a) ∧ (∀ a b c, r a b → r b c → r a c) ∧
      ∀ a b c, Disjoint c a → Disjoint c b → (r a b ↔ r (a ⊔ c) (b ⊔ c)) := by
  refine ⟨fun _ ↦ ⟨IsNontrivial.bot_not_ge_top, rel_bot, total_of r, fun _ _ _ ↦ trans_of r,
    fun _ _ _ hca hcb ↦ (rel_sup_sup_right_iff hca hcb).symm⟩, fun ⟨h₁, h₂, h₃, h₄, h₅⟩ ↦ ?_⟩
  have := isQualitativeAdditive_iff.mpr fun a b c hca hcb ↦ (h₅ a b c hca hcb).symm
  exact { bot_not_ge_top := h₁, rel_bot' := h₂, total := h₃, trans := h₄ }

/-- Removing an event `n` at most as likely as `⊥` changes no comparison. -/
theorem rel_sdiff_sdiff_iff [IsLikelihoodMono r] [IsQualitativeAdditive r] [IsTrans α r]
    {n : α} (hn : r ⊥ n) {a b : α} : r (a \ n) (b \ n) ↔ r a b := by
  have h (x : α) : r (x \ n) x := by
    rw [qadd (r := r), sdiff_eq_bot_iff.mpr sdiff_le, sdiff_sdiff_right_self]
    exact trans_of r hn (mono _ _ inf_le_right)
  exact ⟨fun hab ↦ trans_of r (mono _ _ sdiff_le) (trans_of r hab (h b)),
    fun hab ↦ trans_of r (h a) (trans_of r hab (mono _ _ sdiff_le))⟩

/-- Two comparisons with disjoint left sides and disjoint right sides merge into their joins,
    even when a left side overlaps a right side. -/
theorem rel_sup_sup [IsQualitativeAdditive r] [IsTrans α r] {a₁ b₁ a₂ b₂ : α} (h₁ : r a₁ b₁)
    (h₂ : r a₂ b₂) (ha : Disjoint a₁ a₂) (hb : Disjoint b₁ b₂) : r (a₁ ⊔ a₂) (b₁ ⊔ b₂) := by
  -- add context to each side, pass through `b₂ ⊔ a₁`, and restore the pivot `a₁ ⊓ b₂`
  have e₁ : (a₂ ⊔ a₁ \ b₂) ⊔ a₁ ⊓ b₂ = a₁ ⊔ a₂ := by
    rw [sup_assoc, sup_comm (a₁ \ b₂), sup_inf_sdiff, sup_comm]
  have e₂ : (b₁ ⊔ b₂ \ a₁) ⊔ a₁ ⊓ b₂ = b₁ ⊔ b₂ := by
    rw [sup_assoc, inf_comm a₁, sup_comm (b₂ \ a₁), sup_inf_sdiff]
  rw [← e₁, ← e₂]
  refine rel_sup_sup_right (trans_of r (b := b₂ ⊔ a₁) ?_ ?_)
    ((ha.mono_left inf_le_left).sup_right (disjoint_sdiff_self_right.mono_left inf_le_right))
    ((hb.symm.mono_left inf_le_right).sup_right (disjoint_sdiff_self_right.mono_left inf_le_left))
  · have h := rel_sup_sup_right h₂ (ha.mono_left sdiff_le) disjoint_sdiff_self_left
    rwa [sup_sdiff_self_right] at h
  · have h := rel_sup_sup_right h₁ disjoint_sdiff_self_left (hb.symm.mono_left sdiff_le)
    rwa [sup_sdiff_self_right, sup_comm a₁ b₂] at h

/-- A qualitative probability pulls back along a map `f` that preserves differences, comparing
    events by their images under `f`, provided `f ⊤` is not at most as likely as `⊥`. -/
theorem isQualitativeProbability_preimage {β : Type*} [BooleanAlgebra β]
    [IsQualitativeProbability r] {f : β → α} (hf : ∀ a b, f (a \ b) = f a \ f b)
    (htop : ¬r ⊥ (f ⊤)) : IsQualitativeProbability (f ⁻¹'o r) := by
  have hbot : f ⊥ = ⊥ := by simpa using hf ⊥ ⊥
  exact
    { bot_not_ge_top := by rwa [Order.Preimage, hbot]
      rel_bot' a := by rw [Order.Preimage, hbot]; exact rel_bot _
      qadd a b := by rw [Order.Preimage, Order.Preimage, hf, hf]; exact qadd _ _ }

end Context

/-! ### Qualitative probabilities on sets -/

variable {α W : Type*} {r : Set W → Set W → Prop}

theorem rel_empty [IsLikelihoodMono r] (A : Set W) : r A ∅ := rel_bot (r := r) A

theorem not_rel_empty_univ [IsNontrivial r] : ¬r ∅ Set.univ :=
  IsNontrivial.bot_not_ge_top (r := r)

/-- A qualitative probability pulls back along preimages, comparing sets by their preimages. -/
instance [IsQualitativeProbability r] (f : W → α) :
    IsQualitativeProbability (Set.preimage f ⁻¹'o r) :=
  isQualitativeProbability_preimage (Set.preimage_sdiff f) not_rel_empty_univ

/-- A qualitative probability pulls back along the image of an injection `f`, comparing sets by
    their images, when the range of `f` is not null. -/
theorem isQualitativeProbability_image [IsQualitativeProbability r] {f : α → W}
    (hf : Function.Injective f) (hnt : ¬r ∅ (Set.range f)) :
    IsQualitativeProbability (Set.image f ⁻¹'o r) :=
  isQualitativeProbability_preimage (Set.image_sdiff hf)
    (by rwa [Set.top_eq_univ, Set.image_univ])

/-- An empty carrier has no qualitative probability, since there `∅ = Set.univ`. -/
theorem not_isQualitativeProbability_of_isEmpty [IsEmpty W] (r : Set W → Set W → Prop) :
    ¬IsQualitativeProbability r := fun _ ↦
  not_rel_empty_univ (by rw [Set.eq_empty_of_isEmpty (Set.univ : Set W)]; exact refl_of r ∅)

/-- On a finite carrier some atom is not null, since were every singleton at most as likely
    as `∅`, so would be `Set.univ`. -/
theorem exists_not_rel_empty_singleton [Finite W] (r : Set W → Set W → Prop)
    [IsQualitativeProbability r] : ∃ i, ¬r ∅ {i} := by
  by_contra hall
  push Not at hall
  cases nonempty_fintype W
  suffices h : ∀ S : Finset W, r ∅ ↑S from
    not_rel_empty_univ (by simpa using h Finset.univ)
  intro S
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.coe_empty]; exact refl_of r _
  | insert a S ha ih =>
    rw [Finset.coe_insert, Set.insert_eq]
    simpa using rel_sup_sup (hall a) ih disjoint_bot_left (by simpa using ha)

end ComparativeProbability
