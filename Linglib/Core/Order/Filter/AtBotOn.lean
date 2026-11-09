/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.OfCriteria
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Minimal

/-!
# The bottom of a ranking within a domain

`Filter.atBotOn f s` is the filter of sets that hold toward the bottom of the ranking `f` within
the domain `s`: `t` belongs to it when every point of `s` has a point of `s` ranked at or below
it, all of whose points of `s` ranked at or below are in `t`. Equivalently, `t` contains a lower
set of `s` that is coinitial in `s`. On a codirected order, over the whole type and ranked by the
identity, it is [`atBot`](##Filter.atBotOn_id_univ), but it needs neither directedness nor minimal
points: when every point lies above a minimal one it is [the principal filter of the minimal
points](##Filter.atBotOn_eq_principal), and in general its sets obey [the rules of preferential
consequence](##Filter.atBotOn_inter_of_mem) under changes of domain.

This is Lewis's truth condition for counterfactuals and Kratzer's for necessity with an ordering
source, both over a ranking of worlds; ranked by the criteria a point satisfies, it is
[premise semantics](##Filter.mem_atBotOn_satisfied_iff).

## Implementation notes

The ranking is a map into a preordered type, as for `MinimalFor`, so that a family of orders on
one type, such as an ordering of worlds that varies with the world of evaluation, needs no order
instance on the type. An order given as data enters through its principal down-sets
([`atBotOn_downSet`](##Filter.atBotOn_downSet)).

## References

* [lewis-1981]
* [burgess-1981]
-/

@[expose] public section

open Set

namespace Filter

variable {W β : Type*} [Preorder β] {f : W → β} {s s' t t' : Set W} {v : W}

/-- The sets that hold toward the bottom of the ranking `f` within `s`: every point of `s` has a
point of `s` ranked at or below it, all of whose points of `s` ranked at or below are in the set. -/
def atBotOn (f : W → β) (s : Set W) : Filter W where
  sets := {t | ∀ u ∈ s, ∃ v ∈ s, f v ≤ f u ∧ ∀ w ∈ s, f w ≤ f v → w ∈ t}
  univ_sets u hu := ⟨u, hu, le_rfl, fun _ _ _ ↦ trivial⟩
  sets_of_superset h htt' u hu :=
    let ⟨v, hv, hvu, hvt⟩ := h u hu
    ⟨v, hv, hvu, fun w hw hwv ↦ htt' (hvt w hw hwv)⟩
  inter_sets h h' u hu :=
    let ⟨v, hv, hvu, hvt⟩ := h u hu
    let ⟨v', hv', hv'v, hv't'⟩ := h' v hv
    ⟨v', hv', hv'v.trans hvu, fun w hw hwv' ↦ ⟨hvt w hw (hwv'.trans hv'v), hv't' w hw hwv'⟩⟩

theorem mem_atBotOn :
    t ∈ atBotOn f s ↔ ∀ u ∈ s, ∃ v ∈ s, f v ≤ f u ∧ ∀ w ∈ s, f w ≤ f v → w ∈ t :=
  Iff.rfl

theorem self_mem_atBotOn : s ∈ atBotOn f s :=
  fun u hu ↦ ⟨u, hu, le_rfl, fun _ hw _ ↦ hw⟩

theorem atBotOn_neBot_iff : (atBotOn f s).NeBot ↔ s.Nonempty := by
  rw [← forall_mem_nonempty_iff_neBot]
  refine ⟨fun h ↦ h s self_mem_atBotOn, fun ⟨u, hu⟩ t ht ↦ ?_⟩
  obtain ⟨v, hv, -, hvt⟩ := ht u hu
  exact ⟨v, hvt v hv le_rfl⟩

/-- On a codirected order, over the whole type and ranked by the identity, the filter is
`atBot`. -/
theorem atBotOn_id_univ [IsCodirectedOrder β] [Nonempty β] : atBotOn (id : β → β) univ = atBot := by
  ext t
  rw [mem_atBot_sets, mem_atBotOn]
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ u _ ↦ ?_⟩
  · obtain ⟨v, -, -, hv⟩ := h (Classical.arbitrary β) trivial
    exact ⟨v, fun b hb ↦ hv b trivial hb⟩
  · obtain ⟨c, hcu, hca⟩ := exists_le_le u a
    exact ⟨c, trivial, hcu, fun w _ hwc ↦ ha w (hwc.trans hca)⟩

/-- The order pulled back along a ranking is that ranking. -/
@[simp] theorem atBotOn_lift (g : W → β) (s : Set W) :
    @atBotOn W W (Preorder.lift g) id s = atBotOn g s :=
  rfl

/-- An order given as data is the ranking by its principal down-sets. -/
theorem atBotOn_downSet (p : Preorder W) (s : Set W) :
    atBotOn (fun w ↦ {v | p.le v w}) s = @atBotOn W W p id s := by
  have key (a b : W) : {v | p.le v a} ⊆ {v | p.le v b} ↔ p.le a b :=
    ⟨fun h ↦ h (p.le_refl a), fun h _ hv ↦ p.le_trans _ _ _ hv h⟩
  ext t
  simp only [mem_atBotOn, key, id]

/-! ### A single point below which the set holds -/

theorem exists_of_mem_atBotOn (h : t ∈ atBotOn f s) (hs : s.Nonempty) :
    ∃ v ∈ s, ∀ w ∈ s, f w ≤ f v → w ∈ t :=
  let ⟨_, hu⟩ := hs
  let ⟨v, hv, _, hvt⟩ := h _ hu
  ⟨v, hv, hvt⟩

/-- On a total order a set holds toward the bottom of a nonempty domain exactly when it holds at
every point of the domain ranked at or below a single one. -/
theorem mem_atBotOn_iff_exists [Std.Total (α := β) (· ≤ ·)] (hs : s.Nonempty) :
    t ∈ atBotOn f s ↔ ∃ v ∈ s, ∀ w ∈ s, f w ≤ f v → w ∈ t := by
  refine ⟨fun h ↦ exists_of_mem_atBotOn h hs, fun ⟨v, hv, hvt⟩ u hu ↦ ?_⟩
  rcases total_of (· ≤ ·) (f v) (f u) with hvu | huv
  · exact ⟨v, hv, hvu, hvt⟩
  · exact ⟨u, hu, le_rfl, fun w hw hwu ↦ hvt w hw (hwu.trans huv)⟩

/-! ### Minimal points -/

theorem setOf_minimalFor_subset_of_mem_atBotOn (h : t ∈ atBotOn f s) :
    {x | MinimalFor (· ∈ s) f x} ⊆ t := fun m hm ↦
  let ⟨_, hv, hvm, hvt⟩ := h m hm.1
  hvt m hm.1 (hm.2 hv hvm)

theorem mem_atBotOn_of_setOf_minimalFor_subset
    (hlim : ∀ u ∈ s, ∃ v, MinimalFor (· ∈ s) f v ∧ f v ≤ f u)
    (h : {x | MinimalFor (· ∈ s) f x} ⊆ t) : t ∈ atBotOn f s := fun u hu ↦
  let ⟨v, hv, hvu⟩ := hlim u hu
  ⟨v, hv.1, hvu, fun _ hw hwv ↦
    h ⟨hw, fun ⦃_⦄ hx hxw ↦ hwv.trans (hv.2 hx (hxw.trans hwv))⟩⟩

/-- When every point of `s` lies above a minimal one, the filter is the principal filter of the
minimal points. -/
theorem atBotOn_eq_principal (hlim : ∀ u ∈ s, ∃ v, MinimalFor (· ∈ s) f v ∧ f v ≤ f u) :
    atBotOn f s = 𝓟 {x | MinimalFor (· ∈ s) f x} :=
  Filter.ext fun _ ↦ ⟨setOf_minimalFor_subset_of_mem_atBotOn,
    mem_atBotOn_of_setOf_minimalFor_subset hlim⟩

theorem atBotOn_eq_principal_of_wellFoundedLT [WellFoundedLT β] :
    atBotOn f s = 𝓟 {x | MinimalFor (· ∈ s) f x} :=
  atBotOn_eq_principal fun u hu ↦
    let ⟨v, hv⟩ := exists_minimalFor_of_wellFoundedLT (fun x ↦ x ∈ s ∧ f x ≤ f u) f ⟨u, hu, le_rfl⟩
    ⟨v, ⟨hv.1.1, fun _ hx hxv ↦ hv.2 ⟨hx, hxv.trans hv.1.2⟩ hxv⟩, hv.1.2⟩

theorem atBotOn_eq_pure (hv : v ∈ s) (hle : ∀ u ∈ s, f v ≤ f u)
    (hlt : ∀ u ∈ s, f u ≤ f v → u = v) : atBotOn f s = pure v := by
  have hmin : {x | MinimalFor (· ∈ s) f x} = {v} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨hv, fun u hu _ ↦ hle u hu⟩,
      fun u hu ↦ hlt u hu.1 (hu.2 hv (hle u hu.1))⟩
  rw [atBotOn_eq_principal fun u hu ↦ ⟨v, (Set.ext_iff.1 hmin v).2 rfl, hle u hu⟩, hmin,
    principal_singleton]

/-! ### A least point -/

section Least

variable {b : W} (hb : b ∈ s) (hleast : ∀ v ∈ s, f b ≤ f v)
include hb hleast

theorem mem_atBotOn_iff_of_least : t ∈ atBotOn f s ↔ ∀ w ∈ s, f w ≤ f b → w ∈ t :=
  ⟨fun h w hw hwb ↦
      let ⟨v, hv, _, hvt⟩ := h b hb
      hvt w hw (hwb.trans (hleast v hv)),
    fun h u hu ↦ ⟨b, hb, hleast u hu, h⟩⟩

theorem setOf_minimalFor_subset_iff_of_least :
    {x | MinimalFor (· ∈ s) f x} ⊆ t ↔ ∀ w ∈ s, f w ≤ f b → w ∈ t :=
  ⟨fun h _ hw hwb ↦ h ⟨hw, fun ⦃_⦄ hx _ ↦ hwb.trans (hleast _ hx)⟩,
    fun h m hm ↦ h m hm.1 (hm.2 hb (hleast m hm.1))⟩

end Least

/-! ### Changing the domain

The filters of one ranking over different domains obey the rules of preferential consequence,
with no assumption of minimal points ([burgess-1981]). -/

/-- What holds toward the bottom of two domains holds toward the bottom of their union. -/
theorem atBotOn_union_le : atBotOn f (s ∪ s') ≤ atBotOn f s ⊔ atBotOn f s' := by
  have key {s s' t : Set W} (h : t ∈ atBotOn f s) (h' : t ∈ atBotOn f s') (u : W) (hu : u ∈ s) :
      ∃ v ∈ s ∪ s', f v ≤ f u ∧ ∀ w ∈ s ∪ s', f w ≤ f v → w ∈ t := by
    obtain ⟨v, hv, hvu, hvt⟩ := h u hu
    by_cases hx : ∃ x ∈ s', f x ≤ f v
    · obtain ⟨x, hx, hxv⟩ := hx
      obtain ⟨y, hy, hyx, hyt⟩ := h' x hx
      have hyv := hyx.trans hxv
      exact ⟨y, .inr hy, hyv.trans hvu, fun w hw hwy ↦
        hw.elim (fun hw ↦ hvt w hw (hwy.trans hyv)) (fun hw ↦ hyt w hw hwy)⟩
    · exact ⟨v, .inl hv, hvu, fun w hw hwv ↦
        hw.elim (fun hw ↦ hvt w hw hwv) (fun hw ↦ absurd ⟨w, hw, hwv⟩ hx)⟩
  intro t ht u hu
  obtain ⟨h, h'⟩ := mem_sup.1 ht
  exact hu.elim (key h h' u) fun hu ↦ Set.union_comm s' s ▸ key h' h u hu

/-- What holds toward the bottom of a domain restricted to `t` holds toward the bottom of the
domain wherever `t` holds. -/
theorem atBotOn_inf_principal_le : atBotOn f s ⊓ 𝓟 t ≤ atBotOn f (s ∩ t) := fun a ha ↦
  mem_inf_principal.2 fun u hu ↦ by
    by_cases hx : ∃ x ∈ s ∩ t, f x ≤ f u
    · obtain ⟨x, hx, hxu⟩ := hx
      obtain ⟨v, hv, hvx, hva⟩ := ha x hx
      exact ⟨v, hv.1, hvx.trans hxu, fun w hw hwv hwt ↦ hva w ⟨hw, hwt⟩ hwv⟩
    · exact ⟨u, hu, le_rfl, fun w hw hwu hwt ↦ absurd ⟨w, ⟨hw, hwt⟩, hwu⟩ hx⟩

/-- Restricting a domain to one of its sets leaves the filter unchanged: cautious monotonicity
and cut. -/
theorem atBotOn_inter_of_mem (ht : t ∈ atBotOn f s) : atBotOn f (s ∩ t) = atBotOn f s := by
  refine le_antisymm (fun a ha u hu ↦ ?_) fun a ha ↦ ?_
  · obtain ⟨v, hv, hvu, hvta⟩ := inter_mem ht ha u hu.1
    exact ⟨v, ⟨hv, (hvta v hv le_rfl).1⟩, hvu, fun w hw hwv ↦ (hvta w hw.1 hwv).2⟩
  · exact mem_of_superset (inter_mem ht (mem_inf_principal.1 (atBotOn_inf_principal_le ha)))
      fun _ hx ↦ hx.2 hx.1

/-- On a total order, restricting a domain to a set that frequently holds toward its bottom
restricts the filter to that set: rational monotonicity. -/
theorem atBotOn_inter_of_frequently [Std.Total (α := β) (· ≤ ·)] (ht : ∃ᶠ x in atBotOn f s, x ∈ t) :
    atBotOn f (s ∩ t) = atBotOn f s ⊓ 𝓟 t := by
  refine le_antisymm (fun a ha ↦ ?_) atBotOn_inf_principal_le
  have hb : {x | x ∈ t → x ∈ a} ∈ atBotOn f s := mem_inf_principal.1 ha
  suffices hb' : {x | x ∈ t → x ∈ a} ∈ atBotOn f (s ∩ t) from
    mem_of_superset (inter_mem hb' (mem_of_superset self_mem_atBotOn Set.inter_subset_right))
      fun _ hx ↦ hx.1 hx.2
  obtain ⟨x₀, hx₀, h₀⟩ : ∃ x₀ ∈ s, ∀ v ∈ s, f v ≤ f x₀ → ∃ z ∈ s, f z ≤ f v ∧ z ∈ t := by
    by_contra! hcon
    exact ht hcon
  intro u hu
  obtain ⟨y, hy, hyu, hyx₀, hyb⟩ : ∃ y ∈ s, f y ≤ f u ∧ f y ≤ f x₀ ∧
      ∀ w ∈ s, f w ≤ f y → w ∈ {x | x ∈ t → x ∈ a} := by
    obtain ⟨y₁, hy₁, hy₁u, hy₁b⟩ := hb u hu.1
    rcases total_of (· ≤ ·) (f y₁) (f x₀) with h | h
    · exact ⟨y₁, hy₁, hy₁u, h, hy₁b⟩
    · obtain ⟨y₂, hy₂, hy₂x₀, hy₂b⟩ := hb x₀ hx₀
      exact ⟨y₂, hy₂, hy₂x₀.trans (h.trans hy₁u), hy₂x₀, hy₂b⟩
  obtain ⟨z, hz, hzy, hzt⟩ := h₀ y hy hyx₀
  exact ⟨z, ⟨hz, hzt⟩, hzy.trans hyu, fun w hw hwz ↦ hyb w hw.1 (hwz.trans hzy)⟩

/-! ### Premise semantics

Ranked by the criteria a point satisfies, more being better, the filter can be stated without
points: the sets of criteria satisfied together at some point of the domain stand in for the
points, and inclusion among them for the order. -/

/-- The order derived from criteria is the ranking by the criteria satisfied. -/
theorem atBotOn_ofCriteria {C : Type*} (sat : W → C → Prop) (crit : Set C) (s : Set W) :
    @atBotOn W W (Preorder.ofCriteria sat crit) id s =
      atBotOn (OrderDual.toDual ∘ Preorder.satisfied sat crit) s := by
  ext t
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    Preorder.satisfied_subset_iff, id]

/-- Ranked by the criteria satisfied, `t` holds toward the bottom of `s` exactly when every set of
criteria satisfied together at some point of `s` extends, within the criteria, to a set satisfied
together at some point of `s` and only at points of `t`. -/
theorem mem_atBotOn_satisfied_iff {C : Type*} {sat : W → C → Prop} {crit : Set C} :
    t ∈ atBotOn (OrderDual.toDual ∘ Preorder.satisfied sat crit) s ↔
      ∀ B ⊆ crit, (∃ u ∈ s, ∀ c ∈ B, sat u c) → ∃ D ⊆ crit, (∃ v ∈ s, ∀ c ∈ D, sat v c) ∧
        B ⊆ D ∧ ∀ w ∈ s, (∀ c ∈ D, sat w c) → w ∈ t := by
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    Preorder.satisfied_subset_iff, Preorder.ofCriteria_le_iff]
  refine ⟨fun h B hB ⟨u, hu, huB⟩ ↦ ?_, fun h u hu ↦ ?_⟩
  · obtain ⟨v, hv, hvu, hvt⟩ := h u hu
    exact ⟨Preorder.satisfied sat crit v, Set.sep_subset _ _, ⟨v, hv, fun _ hc ↦ hc.2⟩,
      fun c hc ↦ ⟨hB hc, hvu c (hB hc) (huB c hc)⟩,
      fun w hw hwD ↦ hvt w hw fun c hc hvc ↦ hwD c ⟨hc, hvc⟩⟩
  · obtain ⟨D, hD, ⟨v, hv, hvD⟩, hBD, hDt⟩ :=
      h (Preorder.satisfied sat crit u) (Set.sep_subset _ _) ⟨u, hu, fun _ hc ↦ hc.2⟩
    exact ⟨v, hv, fun c hc huc ↦ hvD c (hBD ⟨hc, huc⟩),
      fun w hw hwv ↦ hDt w hw fun c hc ↦ hwv c (hD hc) (hvD c hc)⟩

end Filter
