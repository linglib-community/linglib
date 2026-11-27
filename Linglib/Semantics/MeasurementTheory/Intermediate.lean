module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Semantics.MeasurementTheory.Invariance

/-!
# Intermediate measures

A measure of things that can be combined, such as the temperature of bodies of water or the
goodness of propositions, is intermediate when the degree of a combination lies between the
degrees of its parts. For a measure `m : β → α` of the elements of a lattice in a linear order we
ask that `m (a ⊔ b) ∈ Set.uIcc (m a) (m b)` whenever `a` and `b` are disjoint.

The positive form of a measure is the preimage of a set `s` of degrees, such as `Set.Ioi θ`. We
show that the positive form of an intermediate measure is closed under disjoint joins when `s` is
order-connected. When `s` is an upper set its complement is order-connected as well, so a disjoint
join in the positive form has a part in it. On a Boolean algebra it follows that if `a ⊔ b = ⊤`,
`a` is in the positive form and `bᶜ` is not, then `a ⊓ b` is in it. Intermediacy depends only on
the order a measure induces, so it is invariant under every strictly increasing change of scale.

## Main definitions

* `MeasurementTheory.IsIntermediate`: the degree of a disjoint join lies between the degrees of
  its parts.

## Main results

* `MeasurementTheory.isIntermediate_iff`: intermediacy in terms of the order alone.
* `MeasurementTheory.IsIntermediate.sup_mem`: the preimage of an order-connected set is closed
  under disjoint joins.
* `MeasurementTheory.IsIntermediate.mem_of_sup_mem`: a disjoint join in the preimage of an upper
  set has a part in it.
* `MeasurementTheory.IsIntermediate.inf_mem`: agglomeration for an exhaustive pair.
* `MeasurementTheory.invariant_univ_isIntermediate`: intermediacy is invariant under strictly
  increasing changes of scale.

## Implementation notes

[lassiter-2017] states intermediacy for a weak order on the things measured, and adds that the
combination of two things of unequal degree lies strictly between them unless one of them has zero
weight in it. That clause refers to the weights of a particular measure and is not part of
`IsIntermediate`, which a measure with `m (a ⊔ b) = max (m a) (m b)` therefore satisfies too.
Things are combined by the join of disjoint elements, which is disjunction for propositions and
the sum for portions of matter.

## References

* [lassiter-2017]
-/

@[expose] public section

open Set

namespace MeasurementTheory

variable {β α : Type*} [LinearOrder α]

section SemilatticeSup

variable [SemilatticeSup β] [OrderBot β] {m : β → α} {s : Set α} {a b : β}

/-- A measure is intermediate when the degree of a join of disjoint elements lies between the
degrees of the two. -/
def IsIntermediate (m : β → α) : Prop :=
  ∀ ⦃a b⦄, Disjoint a b → m (a ⊔ b) ∈ uIcc (m a) (m b)

theorem isIntermediate_iff : IsIntermediate m ↔
    ∀ ⦃a b⦄, Disjoint a b → m b ≤ m a → m b ≤ m (a ⊔ b) ∧ m (a ⊔ b) ≤ m a := by
  refine ⟨fun h a b hd hle ↦ by simpa [mem_uIcc, hle] using h hd, fun h a b hd ↦ ?_⟩
  rcases le_total (m b) (m a) with hle | hle
  · exact mem_uIcc.2 (.inr (h hd hle))
  · exact mem_uIcc.2 (.inl (sup_comm b a ▸ h hd.symm hle))

namespace IsIntermediate

variable (hm : IsIntermediate m)
include hm

/-- The preimage of an order-connected set of degrees under an intermediate measure is closed
under disjoint joins. -/
theorem sup_mem [s.OrdConnected] (hd : Disjoint a b) (ha : m a ∈ s) (hb : m b ∈ s) :
    m (a ⊔ b) ∈ s :=
  OrdConnected.uIcc_subset ‹_› ha hb (hm hd)

/-- A disjoint join whose degree lies in an upper set has a part whose degree does. -/
theorem mem_of_sup_mem (hs : IsUpperSet s) (hd : Disjoint a b) (h : m (a ⊔ b) ∈ s)
    (ha : m a ∉ s) : m b ∈ s :=
  by_contra fun hb ↦ have := hs.compl.ordConnected; hm.sup_mem (s := sᶜ) hd ha hb h

theorem comp_monotone {γ : Type*} [LinearOrder γ] {g : α → γ} (hg : Monotone g) :
    IsIntermediate (g ∘ m) :=
  fun _ _ hd ↦ hg.image_uIcc_subset (mem_image_of_mem g (hm hd))

theorem comp_antitone {γ : Type*} [LinearOrder γ] {g : α → γ} (hg : Antitone g) :
    IsIntermediate (g ∘ m) :=
  fun _ _ hd ↦ hg.image_uIcc_subset (mem_image_of_mem g (hm hd))

end IsIntermediate

/-- Intermediacy is invariant under every strictly increasing change of scale. -/
theorem invariant_univ_isIntermediate :
    Invariant (univ : Set (α ↪o α)) (IsIntermediate : (β → α) → Prop) :=
  fun g _ m ↦ propext <| forall₃_congr fun a b _ ↦ by
    simp [mem_uIcc, g.le_iff_le]

end SemilatticeSup

/-- When `a` and `b` exhaust a Boolean algebra, `a` has its degree in an upper set and the
complement of `b` does not, the meet of `a` and `b` has its degree in it. -/
theorem IsIntermediate.inf_mem [BooleanAlgebra β] {m : β → α} {s : Set α} {a b : β}
    (hm : IsIntermediate m) (hs : IsUpperSet s) (h : a ⊔ b = ⊤) (ha : m a ∈ s)
    (hb : m bᶜ ∉ s) : m (a ⊓ b) ∈ s := by
  refine hm.mem_of_sup_mem hs (disjoint_compl_left.mono_right inf_le_right) ?_ hb
  rwa [sup_inf_left, compl_sup_eq_top, inf_top_eq,
    sup_eq_right.2 (codisjoint_iff_compl_le_left.1 (codisjoint_iff.2 h))]

end MeasurementTheory
