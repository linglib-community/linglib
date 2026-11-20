module

public import Linglib.Semantics.Mereology.Fusion
public import Mathlib.Order.CompleteBooleanAlgebra
public import Linglib.Semantics.Mereology.Solid

/-!
# Classical mereology

A classical mereology is a partial order in which every nonempty set has a least upper bound
and Remainder holds: if `x` is not part of `y`, something has as parts exactly the parts of `x`
that do not overlap `y`. This is `Mereology.IsClassical`, the axiom system of
[cotnoir-varzi-2021]. It is the same theory as Strong Supplementation with a Leśniewski fusion
of every nonempty set (`Mereology.isClassical_iff`), the axiomatization by supplementation and
sums defined from overlap.

A classical mereology with two elements has no least one. A complete Boolean algebra without
its least element is a classical mereology (`Mereology.isClassical_subtype_ne_bot`), and a
classical mereology with a least element adjoined is a complete Boolean algebra
(`Mereology.IsClassical.completeBooleanAlgebra`).

The theory with a null element, stated with solid overlap, is `Mereology.IsClassicalMereology`.
Adjoining a null element to a classical mereology gives one
(`Mereology.IsClassical.isClassicalMereology_withBot`).

## Implementation notes

Unrestricted fusion quantifies over sets. The first-order axiom schema, over formulas, has
models that are not complete Boolean algebras, and the representation theorem is for the
second-order form.

The part structures of [krifka-1989] and [krifka-1998] have binary sums and a remainder
principle, not arbitrary sums, so they are weaker than classical mereology; those of
[champollion-krifka-2016] and [hovda-2009] are classical mereologies with no null element.
[hovda-2009] shows that binary distributivity with weak supplementation and arbitrary least
upper bounds does not give a classical mereology on an infinite domain.

## References

* [cotnoir-varzi-2021], [cotnoir-varzi-2019], [champollion-krifka-2016], [champollion-2017],
  [hovda-2009], [krifka-1989], [krifka-1998]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

section IsClassical

variable {X B : Type*} [PartialOrder X]

variable (X) in
/-- Classical mereology: a partial order with Unrestricted Fusion (A.5), every nonempty set
having a least upper bound, and Remainder (A.4). -/
structure IsClassical : Prop where
  exists_isLUB : ∀ s : Set X, s.Nonempty → ∃ x, IsLUB s x
  remainder : Remainder X

/-- In a classical mereology two overlapping individuals have a product, the least upper bound
of their common parts. -/
theorem IsClassical.products (h : IsClassical X) : Products X := fun x y hxy ↦
  let ⟨p, hp⟩ := h.exists_isLUB {z | z ≤ x ∧ z ≤ y} hxy
  ⟨p, by rintro _ (rfl | rfl); exacts [hp.2 fun _ hz ↦ hz.1, hp.2 fun _ hz ↦ hz.2],
    fun _ hz ↦ hp.1 ⟨hz (.inl rfl), hz (.inr rfl)⟩⟩

/-- Strong Supplementation with unrestricted Leśniewski fusions gives Remainder. -/
theorem remainder_of_strong_of_fusion (hS : StrongSupplementation X)
    (hF : ∀ s : Set X, s.Nonempty → ∃ x, IsFusion s x) : Remainder X := fun x y hxy ↦ by
  obtain ⟨z₀, hz₀x, hz₀y⟩ := hS hxy
  obtain ⟨r, hr⟩ := hF {w | w ≤ x ∧ ¬ Overlap w y} ⟨z₀, hz₀x, hz₀y⟩
  have hlub := hr.isLUB hS
  refine ⟨r, fun w ↦ ⟨fun hw ↦ ⟨hw.trans (hlub.2 fun _ h ↦ h.1), ?_⟩, fun hw ↦ hlub.1 hw⟩⟩
  rintro ⟨c, hcw, hcy⟩
  obtain ⟨m, hm, d, hdc, hdm⟩ := hr.2 c (hcw.trans hw)
  exact hm.2 ⟨d, hdm, hdc.trans hcy⟩

/-- The axiomatization by Strong Supplementation and unrestricted Leśniewski fusion is the
same theory. -/
theorem isClassical_iff : IsClassical X ↔
    StrongSupplementation X ∧ ∀ s : Set X, s.Nonempty → ∃ x, IsFusion s x :=
  ⟨fun h ↦ ⟨h.remainder.strong, fun s hs ↦
      let ⟨x, hx⟩ := h.exists_isLUB s hs; ⟨x, hx.isFusion h.remainder hs⟩⟩,
    fun ⟨hS, hF⟩ ↦ ⟨fun s hs ↦ let ⟨x, hx⟩ := hF s hs; ⟨x, hx.isLUB hS⟩,
      remainder_of_strong_of_fusion hS hF⟩⟩

/-- A complete Boolean algebra without its least element is a classical mereology. -/
theorem isClassical_subtype_ne_bot [CompleteBooleanAlgebra B] :
    IsClassical {x : B // x ≠ ⊥} where
  exists_isLUB s hs := by
    obtain ⟨a, ha⟩ := hs
    have hne : sSup (Subtype.val '' s) ≠ ⊥ :=
      fun h ↦ a.2 (le_bot_iff.1 ((le_sSup (Set.mem_image_of_mem Subtype.val ha)).trans h.le))
    refine ⟨⟨_, hne⟩, fun x hx ↦ le_sSup (α := B) ⟨x, hx, rfl⟩, fun u hu ↦
      sSup_le (α := B) ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hu hx
  remainder := fun x y hxy ↦ by
    have hne : (x : B) \ y ≠ ⊥ := fun h ↦ hxy (sdiff_eq_bot_iff.1 h)
    refine ⟨⟨_, hne⟩, fun w ↦ ?_⟩
    rw [overlap_subtype_ne_bot, not_not]
    exact le_sdiff

/-- Solid overlap of two elements with a least element adjoined is their overlap. -/
theorem solidOverlap_coe {a b : X} : SolidOverlap (a : WithBot X) b ↔ Overlap a b := by
  constructor
  · rintro ⟨z, hz, hza, hzb⟩
    induction z with
    | bot => exact absurd isBot_bot hz
    | coe c => exact ⟨c, WithBot.coe_le_coe.1 hza, WithBot.coe_le_coe.1 hzb⟩
  · rintro ⟨c, hca, hcb⟩
    exact ⟨c, fun h ↦ WithBot.not_coe_le_bot c (h ⊥), WithBot.coe_le_coe.2 hca,
      WithBot.coe_le_coe.2 hcb⟩

/-- A classical mereology with a least element adjoined is a classical mereology with a null
element, in the solid sense. -/
theorem IsClassical.isClassicalMereology_withBot (h : IsClassical X) :
    IsClassicalMereology (WithBot X) where
  exists_not_overlap x y hxy := by
    induction x with
    | bot => exact absurd bot_le hxy
    | coe a =>
      have ha : ¬ IsBot (a : WithBot X) := fun hb ↦ WithBot.not_coe_le_bot a (hb ⊥)
      induction y with
      | bot => exact ⟨a, le_rfl, ha, fun ho ↦ ho.not_isBot_right isBot_bot⟩
      | coe b =>
        obtain ⟨z, hza, hzb⟩ := h.remainder.strong
          (fun h' ↦ hxy (WithBot.coe_le_coe.2 h') : ¬ a ≤ b)
        exact ⟨z, WithBot.coe_le_coe.2 hza, fun hb ↦ WithBot.not_coe_le_bot z (hb ⊥),
          fun ho ↦ hzb (solidOverlap_coe.1 ho)⟩
  exists_isSum P hP := by
    by_cases hne : ∃ a : X, (a : WithBot X) ∈ P
    · obtain ⟨t, ht⟩ := h.exists_isLUB {a : X | (a : WithBot X) ∈ P} hne
      have hf := IsLUB.isFusion h.remainder (s := {a : X | (a : WithBot X) ∈ P}) hne ht
      refine ⟨t, fun x hx ↦ ?_, fun y hy hy0 ↦ ?_⟩
      · induction x with
        | bot => exact bot_le
        | coe a => exact WithBot.coe_le_coe.2 (hf.1 a hx)
      · induction y with
        | bot => exact absurd isBot_bot hy0
        | coe c =>
          obtain ⟨a, ha, ho⟩ := hf.2 c (WithBot.coe_le_coe.1 hy)
          exact ⟨a, ha, solidOverlap_coe.2 ho⟩
    · refine ⟨⊥, fun x hx ↦ ?_, fun y hy hy0 ↦ absurd (isBot_iff_eq_bot.2 (le_bot_iff.1 hy)) hy0⟩
      induction x with
      | bot => exact le_rfl
      | coe a => exact absurd ⟨a, hx⟩ hne

/-- A classical mereology with a least element adjoined is a complete Boolean algebra, with the
order of `WithBot`. -/
@[reducible] noncomputable def IsClassical.completeBooleanAlgebra (h : IsClassical X) :
    CompleteBooleanAlgebra (WithBot X) :=
  haveI := h.isClassicalMereology_withBot
  IsClassicalMereology.toCompleteBooleanAlgebra

theorem IsClassical.completeBooleanAlgebra_le (h : IsClassical X) :
    h.completeBooleanAlgebra.toLE = (inferInstance : LE (WithBot X)) := rfl

end IsClassical

end Mereology
