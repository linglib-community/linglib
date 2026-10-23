/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Minimals

/-!
# Ordering semantics

Ordering semantics evaluates a modal or a conditional by ranking the worlds of a domain under a
preorder, `v ≤ u` meaning that `v` comes at least as close as `u` to an ideal or to the world of
evaluation. Lewis's truth condition needs neither comparability nor the Limit Assumption: `t` is
a necessity over the domain when every world of the domain has one at least as close below which
every world of the domain is a `t`-world. Kratzer's necessity over a modal base and an ordering
source is this condition, and good possibility, which Portner and Rubinstein take from Kratzer as
local necessity, asks for a single such world. The necessities over a domain are closed under
intersection, the good possibilities are not.

Under the Limit Assumption necessity is truth at the minimal worlds, on a total preorder it is
good possibility, and when the domain has a closest world all three coincide. The domain is the
accessible worlds of Kratzer's modals, the antecedent-worlds of Lewis's counterfactuals, and the
information of Veltman's expectation states.

## Main definitions

* `OrderingSemantics.IsNecessity p s t`: every world of `s` has one at least as close all of
  whose worlds of `s` at least as close are in `t`.
* `OrderingSemantics.IsGoodPossibility p s t`: some world of `s` has only `t`-worlds among the
  worlds of `s` at least as close.

## Main statements

* `OrderingSemantics.isNecessity_iff_minimals_subset`: under the Limit Assumption necessity is
  truth at the minimal worlds.
* `OrderingSemantics.isNecessity_iff_isGoodPossibility_of_total`: on a total preorder necessity
  is good possibility.
* `OrderingSemantics.isGoodPossibility_iff_isNecessity_of_least`: when the domain has a closest
  world the two coincide.
* `OrderingSemantics.exists_not_isGoodPossibility_inter`: the good possibilities are not closed
  under intersection; `OrderingSemantics/Topology.lean` reads both forces in the lower-set
  topology.

## References

* [lewis-1981]
* [lewis-1973]
* [kratzer-2012]
* [portner-rubinstein-2020]
-/

@[expose] public section

namespace OrderingSemantics

variable {W : Type*} {p : Preorder W} {s t t' : Set W}

/-- `t` is a necessity over `s` when every world of `s` has a world of `s` at least as close, all
of whose worlds of `s` at least as close are in `t`. -/
def IsNecessity (p : Preorder W) (s t : Set W) : Prop :=
  ∀ u ∈ s, ∃ v ∈ s, p.le v u ∧ ∀ w ∈ s, p.le w v → w ∈ t

/-- `t` is a good possibility over `s` when some world of `s` has only `t`-worlds among the
worlds of `s` at least as close. -/
def IsGoodPossibility (p : Preorder W) (s t : Set W) : Prop :=
  ∃ v ∈ s, ∀ w ∈ s, p.le w v → w ∈ t

/-! ### Closure properties -/

theorem IsNecessity.mono (h : IsNecessity p s t) (htt' : t ⊆ t') : IsNecessity p s t' :=
  fun u hu ↦
    let ⟨v, hv, hvu, hvt⟩ := h u hu
    ⟨v, hv, hvu, fun w hw hwv ↦ htt' (hvt w hw hwv)⟩

theorem isNecessity_univ (p : Preorder W) (s : Set W) : IsNecessity p s .univ :=
  fun u hu ↦ ⟨u, hu, p.le_refl u, fun _ _ _ ↦ trivial⟩

theorem IsNecessity.inter (h : IsNecessity p s t) (h' : IsNecessity p s t') :
    IsNecessity p s (t ∩ t') := fun u hu ↦
  let ⟨v, hv, hvu, hvt⟩ := h u hu
  let ⟨v', hv', hv'v, hv't'⟩ := h' v hv
  ⟨v', hv', p.le_trans _ _ _ hv'v hvu,
    fun w hw hwv' ↦ ⟨hvt w hw (p.le_trans _ _ _ hwv' hv'v), hv't' w hw hwv'⟩⟩

theorem IsGoodPossibility.mono (h : IsGoodPossibility p s t) (htt' : t ⊆ t') :
    IsGoodPossibility p s t' :=
  let ⟨v, hv, hvt⟩ := h
  ⟨v, hv, fun w hw hwv ↦ htt' (hvt w hw hwv)⟩

theorem exists_not_isGoodPossibility_inter :
    ∃ (p : Preorder Bool) (t t' : Set Bool), IsGoodPossibility p .univ t ∧
      IsGoodPossibility p .univ t' ∧ ¬ IsGoodPossibility p .univ (t ∩ t') :=
  ⟨⊥, {true}, {false}, ⟨true, trivial, fun _ _ h ↦ h⟩, ⟨false, trivial, fun _ _ h ↦ h⟩,
    fun ⟨v, _, h⟩ ↦
      let ⟨h₁, h₂⟩ := h v trivial rfl
      Bool.noConfusion ((show v = true from h₁).symm.trans (show v = false from h₂))⟩

/-! ### Necessity and the minimal worlds -/

theorem IsNecessity.minimals_subset (h : IsNecessity p s t) : p.minimals s ⊆ t := fun m hm ↦
  let ⟨_, hv, hvm, hvt⟩ := h m hm.1
  hvt m hm.1 (hm.2 hv hvm)

theorem isNecessity_of_minimals_subset (hlim : ∀ u ∈ s, ∃ v ∈ p.minimals s, p.le v u)
    (h : p.minimals s ⊆ t) : IsNecessity p s t := fun u hu ↦
  let ⟨v, hv, hvu⟩ := hlim u hu
  ⟨v, hv.1, hvu, fun _ hw hwv ↦
    h ⟨hw, fun ⦃_⦄ hx hxw ↦ p.le_trans _ _ _ hwv (hv.2 hx (p.le_trans _ _ _ hxw hwv))⟩⟩

theorem isNecessity_iff_minimals_subset (hlim : ∀ u ∈ s, ∃ v ∈ p.minimals s, p.le v u) :
    IsNecessity p s t ↔ p.minimals s ⊆ t :=
  ⟨IsNecessity.minimals_subset, isNecessity_of_minimals_subset hlim⟩

/-! ### Necessity and good possibility -/

theorem IsNecessity.isGoodPossibility (h : IsNecessity p s t) (hs : s.Nonempty) :
    IsGoodPossibility p s t :=
  let ⟨_, hu⟩ := hs
  let ⟨v, hv, _, hvt⟩ := h _ hu
  ⟨v, hv, hvt⟩

theorem IsGoodPossibility.isNecessity_of_total (htot : Std.Total p.le)
    (h : IsGoodPossibility p s t) : IsNecessity p s t := by
  obtain ⟨v, hv, hvt⟩ := h
  intro u hu
  rcases htot.total v u with hvu | huv
  · exact ⟨v, hv, hvu, hvt⟩
  · exact ⟨u, hu, p.le_refl u, fun w hw hwu ↦ hvt w hw (p.le_trans _ _ _ hwu huv)⟩

theorem isNecessity_iff_isGoodPossibility_of_total (htot : Std.Total p.le) (hs : s.Nonempty) :
    IsNecessity p s t ↔ IsGoodPossibility p s t :=
  ⟨fun h ↦ h.isGoodPossibility hs, fun h ↦ h.isNecessity_of_total htot⟩

/-! ### A closest world

When some world of the domain is at least as close as every world of the domain, necessity, good
possibility and truth at the minimal worlds all reduce to truth at the worlds at least as close
as it. -/

section Least

variable {b : W} (hb : b ∈ s) (hleast : ∀ v ∈ s, p.le b v)
include hb hleast

theorem isGoodPossibility_iff_of_least : IsGoodPossibility p s t ↔ ∀ w ∈ s, p.le w b → w ∈ t :=
  ⟨fun ⟨v, hv, hvt⟩ w hw hwb ↦ hvt w hw (p.le_trans _ _ _ hwb (hleast v hv)),
    fun h ↦ ⟨b, hb, h⟩⟩

theorem isNecessity_iff_of_least : IsNecessity p s t ↔ ∀ w ∈ s, p.le w b → w ∈ t :=
  ⟨fun h w hw hwb ↦
      let ⟨v, hv, _, hvt⟩ := h b hb
      hvt w hw (p.le_trans _ _ _ hwb (hleast v hv)),
    fun h u hu ↦ ⟨b, hb, hleast u hu, h⟩⟩

theorem minimals_subset_iff_of_least : p.minimals s ⊆ t ↔ ∀ w ∈ s, p.le w b → w ∈ t :=
  ⟨fun h _ hw hwb ↦ h ⟨hw, fun ⦃_⦄ hx _ ↦ p.le_trans _ _ _ hwb (hleast _ hx)⟩,
    fun h m hm ↦ h m hm.1 (hm.2 hb (hleast m hm.1))⟩

theorem isGoodPossibility_iff_isNecessity_of_least :
    IsGoodPossibility p s t ↔ IsNecessity p s t :=
  (isGoodPossibility_iff_of_least hb hleast).trans (isNecessity_iff_of_least hb hleast).symm

end Least

end OrderingSemantics
