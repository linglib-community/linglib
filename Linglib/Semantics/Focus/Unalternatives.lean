/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Set.NAry
public import Linglib.Core.Computability.Edge
public import Linglib.Semantics.Composition.WithAlternatives

/-!
# Unalternative semantics

In Büring's unalternative semantics the focal targets of a constituent play the part of its focus
value, so a meaning is a `WithAlternatives` whose alternatives are its focal targets. What a
constituent excludes are its unalternatives. A terminal excludes nothing, so it is `focused`. A
branching node excludes whatever is composed from an unalternative of a daughter (Propagation),
and whatever its own restriction on one daughter excludes: a weak restriction excludes narrow
focus on her, and a strong restriction everything else. Default metrical weights put a weak
restriction on the weak daughter, and prosodic reversal a strong restriction on the daughter it
promotes. Focus Reset leaves a constituent only its literal meaning, as `unfeatured` does.

## Main definitions

* `Focus.narrow`: the targets of narrow focus on one daughter of a node.
* `Focus.Restriction`, `Focus.excluded`: the weak and the strong restriction, and what each
  excludes.
* `Focus.propagated`: the targets a node excludes by Propagation.
* `WithAlternatives.node`: a branching node of unalternative semantics.

## Main results

* `WithAlternatives.alternatives_node`: under a bijective composition, the targets of a node are
  the pointwise composition of its daughters' targets, minus what its restriction excludes.
* `WithAlternatives.not_wellFormed_node_strong`: a strong restriction excludes the literal
  meaning of its node, against Rooth's containment constraint.
* `WithAlternatives.alternatives_node_left_strong_eq_empty`: a strong restriction over a sister
  that excludes her own literal meaning leaves no target.

## Implementation notes

Büring restricts the alternatives of a constituent to the natural meanings of its type. Here the
alternatives are all values of the type, so a model chooses types of natural meanings, and a node
composes its daughters by a fixed operation `op`. Büring's pointwise combination `⊗` is
`Set.image2 op`.

## References

* [buring-2015]
-/

@[expose] public section

open Set Function

namespace Focus

variable {α β γ : Type*} (op : α → β → γ) (a : α) (b : β)

/-- The targets of narrow focus on daughter `e` of a node whose daughters have ordinary values
`a` and `b` vary that daughter and hold her sister at her ordinary value. -/
def narrow : Edge → Set γ
  | .left => image2 op {a}ᶜ {b}
  | .right => image2 op {a} {b}ᶜ

/-- A restriction on a daughter is weak or strong. -/
inductive Restriction
  | weak
  | strong
  deriving DecidableEq, Repr, Fintype

/-- A weak restriction on daughter `e` excludes narrow focus on her, and a strong restriction
excludes every other target. -/
def excluded (e : Edge) : Restriction → Set γ
  | .weak => narrow op a b e
  | .strong => (narrow op a b e)ᶜ

/-- Propagation excludes every target composed from an unalternative of either daughter. -/
def propagated (u : Set α) (v : Set β) : Set γ := image2 op univ v ∪ image2 op u univ

variable {op a b}

@[simp] theorem narrow_left : narrow op a b .left = image2 op {a}ᶜ {b} := rfl

@[simp] theorem narrow_right : narrow op a b .right = image2 op {a} {b}ᶜ := rfl

@[simp] theorem excluded_weak (e : Edge) : excluded op a b e .weak = narrow op a b e := rfl

@[simp] theorem excluded_strong (e : Edge) : excluded op a b e .strong = (narrow op a b e)ᶜ := rfl

/-- Narrow focus on a daughter excludes the literal meaning of the node. -/
theorem notMem_narrow (hop : Injective2 op) (e : Edge) : op a b ∉ narrow op a b e := by
  cases e <;> rintro ⟨x, hx, y, hy, h⟩ <;> obtain ⟨rfl, rfl⟩ := hop h
  exacts [hx rfl, hy rfl]

theorem disjoint_narrow_left_right (hop : Injective2 op) :
    Disjoint (narrow op a b .left) (narrow op a b .right) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, _, rfl, rfl⟩ ⟨_, rfl, y, hy, h⟩
  exact hx (hop h).1.symm

/-- A strong restriction on a daughter excludes narrow focus on her sister. -/
theorem narrow_swap_subset_excluded_strong (hop : Injective2 op) (e : Edge) :
    narrow op a b e.swap ⊆ excluded op a b e .strong := by
  cases e
  exacts [(disjoint_narrow_left_right hop).subset_compl_left,
    (disjoint_narrow_left_right hop).subset_compl_right]

/-- Under a bijective composition, the targets Propagation leaves are composed from targets of
both daughters. -/
theorem compl_propagated (hop : Bijective (uncurry op)) (u : Set α) (v : Set β) :
    (propagated op u v)ᶜ = image2 op uᶜ vᶜ := by
  have : univ ×ˢ v ∪ u ×ˢ univ = (uᶜ ×ˢ vᶜ)ᶜ := by
    rw [compl_prod_eq_union, compl_compl, compl_compl, union_comm]
  rw [propagated, ← image_uncurry_prod, ← image_uncurry_prod, ← image_union, this,
    image_compl_eq hop, compl_compl, image_uncurry_prod]

end Focus

namespace WithAlternatives

open Focus

variable {α β γ : Type*} {op : α → β → γ} {e : Edge} {r : Restriction}
  {d₁ : WithAlternatives α} {d₂ : WithAlternatives β}

/-- A branching node of unalternative semantics composes its daughters by `op`, and its targets
are those that neither Propagation nor its restriction `r` on daughter `e` excludes. -/
def node (op : α → β → γ) (e : Edge) (r : Restriction) (d₁ : WithAlternatives α)
    (d₂ : WithAlternatives β) : WithAlternatives γ where
  ordinary := op d₁.ordinary d₂.ordinary
  alternatives := (propagated op d₁.alternativesᶜ d₂.alternativesᶜ ∪
    excluded op d₁.ordinary d₂.ordinary e r)ᶜ

@[simp] theorem ordinary_node : (node op e r d₁ d₂).ordinary = op d₁.ordinary d₂.ordinary := rfl

/-- The unalternatives of a node are those Propagation and its restriction exclude. -/
theorem compl_alternatives_node :
    (node op e r d₁ d₂).alternativesᶜ = propagated op d₁.alternativesᶜ d₂.alternativesᶜ ∪
      excluded op d₁.ordinary d₂.ordinary e r :=
  compl_compl _

/-- Under a bijective composition, the targets of a node are composed pointwise from the targets
of its daughters, as Roothian focus values are, less what the node's restriction excludes. -/
theorem alternatives_node (hop : Bijective (uncurry op)) :
    (node op e r d₁ d₂).alternatives =
      image2 op d₁.alternatives d₂.alternatives \ excluded op d₁.ordinary d₂.ordinary e r := by
  rw [node, compl_union, compl_propagated hop, compl_compl, compl_compl, sdiff_eq]

/-- The weak and the strong restriction on a daughter divide between them the targets that
Propagation leaves. -/
theorem alternatives_node_weak_union_strong :
    (node op e .weak d₁ d₂).alternatives ∪ (node op e .strong d₁ d₂).alternatives =
      (propagated op d₁.alternativesᶜ d₂.alternativesᶜ)ᶜ := by
  simp only [node, excluded_weak, excluded_strong, compl_union, compl_compl,
    ← inter_union_distrib_left, compl_union_self, inter_univ]

theorem disjoint_alternatives_node_weak_strong :
    Disjoint (node op e .weak d₁ d₂).alternatives (node op e .strong d₁ d₂).alternatives := by
  simp only [node, excluded_weak, excluded_strong, compl_union, compl_compl]
  exact disjoint_compl_left.mono inter_subset_right inter_subset_right

/-- A weak restriction keeps the literal meaning of a node whose daughters keep theirs. -/
theorem WellFormed.node_weak (hop : Injective2 op) (h₁ : d₁.WellFormed) (h₂ : d₂.WellFormed) :
    (node op e .weak d₁ d₂).WellFormed := by
  simp only [WellFormed, node, propagated, excluded_weak, mem_compl_iff, mem_union, not_or]
  refine ⟨⟨?_, ?_⟩, notMem_narrow hop e⟩
  · rintro ⟨x, -, y, hy, h⟩
    exact hy (by rwa [(hop h).2])
  · rintro ⟨x, hx, y, -, h⟩
    exact hx (by rwa [(hop h).1])

/-- A strong restriction excludes the literal meaning of its node. -/
theorem not_wellFormed_node_strong (hop : Injective2 op) :
    ¬ (node op e .strong d₁ d₂).WellFormed :=
  fun h ↦ h (.inr (notMem_narrow hop e))

/-- A strong restriction on the left daughter leaves no target when her sister excludes her own
literal meaning. -/
theorem alternatives_node_left_strong_eq_empty (h : ¬ d₂.WellFormed) :
    (node op .left .strong d₁ d₂).alternatives = ∅ := by
  refine eq_empty_of_forall_notMem fun t ht ↦ ?_
  simp only [node, excluded_strong, mem_compl_iff, mem_union, not_or, not_not] at ht
  obtain ⟨hp, x, -, y, rfl, rfl⟩ := ht
  exact hp (.inl (mem_image2_of_mem (mem_univ x) h))

/-- A strong restriction on the right daughter leaves no target when her sister excludes her own
literal meaning. -/
theorem alternatives_node_right_strong_eq_empty (h : ¬ d₁.WellFormed) :
    (node op .right .strong d₁ d₂).alternatives = ∅ := by
  refine eq_empty_of_forall_notMem fun t ht ↦ ?_
  simp only [node, excluded_strong, mem_compl_iff, mem_union, not_or, not_not] at ht
  obtain ⟨hp, x, rfl, y, -, rfl⟩ := ht
  exact hp (.inr (mem_image2_of_mem h (mem_univ y)))

end WithAlternatives
