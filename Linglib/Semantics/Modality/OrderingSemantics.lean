/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Minimals
public import Mathlib.Order.Filter.Map

/-!
# Ordering semantics

Ordering semantics evaluates a modal or a conditional by ranking the worlds of a domain under a
preorder, `v ≤ u` meaning that `v` comes at least as close as `u` to an ideal or to the world of
evaluation. The necessities over a domain form a filter: `t` belongs to it when every world of the
domain has one at least as close below which every world of the domain is a `t`-world. This is
Lewis's truth condition, which needs neither comparability nor the Limit Assumption. Kratzer's
necessity over a modal base and an ordering source, Lewis's counterfactual over the accessible
antecedent-worlds and the consequence relation of a preferential model are each membership in
it. Good possibility, which Portner and Rubinstein take from Kratzer as
local necessity, asks for a single such world, and the good possibilities are not closed under
intersection.

Under the Limit Assumption the filter is the principal filter of the minimal worlds, and when one
world of the domain lies strictly below every other it is the point filter of that world. On a
total preorder necessity over a nonempty domain is good possibility.

The filters of one preorder over different domains obey the rules of preferential consequence.
A domain is a necessity over itself, what is necessary over two domains is necessary over their
union, and restricting a domain to one of its necessities leaves its filter unchanged. On a total
preorder, restricting a domain to a proposition possible over it restricts its filter to that
proposition.

## Main definitions

* `OrderingSemantics.necessityFilter p s`: the filter of necessities over `s` under `p`.
* `OrderingSemantics.IsGoodPossibility p s t`: some world of `s` has only `t`-worlds among the
  worlds of `s` at least as close.

## Main statements

* `OrderingSemantics.necessityFilter_eq_principal`: under the Limit Assumption the filter is the
  principal filter of the minimal worlds.
* `OrderingSemantics.necessityFilter_inter_of_mem`: restricting a domain to one of its necessities
  leaves its filter unchanged.
* `OrderingSemantics.necessityFilter_inter_of_frequently`: on a total preorder, restricting a
  domain to a proposition possible over it restricts its filter to that proposition.
* `OrderingSemantics.mem_necessityFilter_iff_isGoodPossibility_of_total`: on a total preorder
  necessity is good possibility.

## References

* [lewis-1981]
* [lewis-1973b]
* [burgess-1981]
* [kratzer-2012]
* [portner-rubinstein-2020]
-/

@[expose] public section

open Filter

namespace OrderingSemantics

variable {W : Type*} {p : Preorder W} {s s' t t' : Set W} {v : W}

/-- The filter of necessities over `s` under `p`: `t` belongs to it when every world of `s` has a
world of `s` at least as close, all of whose worlds of `s` at least as close are in `t`. -/
def necessityFilter (p : Preorder W) (s : Set W) : Filter W where
  sets := {t | ∀ u ∈ s, ∃ v ∈ s, p.le v u ∧ ∀ w ∈ s, p.le w v → w ∈ t}
  univ_sets u hu := ⟨u, hu, p.le_refl u, fun _ _ _ ↦ trivial⟩
  sets_of_superset h htt' u hu :=
    let ⟨v, hv, hvu, hvt⟩ := h u hu
    ⟨v, hv, hvu, fun w hw hwv ↦ htt' (hvt w hw hwv)⟩
  inter_sets h h' u hu :=
    let ⟨v, hv, hvu, hvt⟩ := h u hu
    let ⟨v', hv', hv'v, hv't'⟩ := h' v hv
    ⟨v', hv', p.le_trans _ _ _ hv'v hvu,
      fun w hw hwv' ↦ ⟨hvt w hw (p.le_trans _ _ _ hwv' hv'v), hv't' w hw hwv'⟩⟩

theorem mem_necessityFilter :
    t ∈ necessityFilter p s ↔ ∀ u ∈ s, ∃ v ∈ s, p.le v u ∧ ∀ w ∈ s, p.le w v → w ∈ t :=
  Iff.rfl

theorem self_mem_necessityFilter : s ∈ necessityFilter p s :=
  fun u hu ↦ ⟨u, hu, p.le_refl u, fun _ hw _ ↦ hw⟩

theorem necessityFilter_neBot_iff : (necessityFilter p s).NeBot ↔ s.Nonempty := by
  rw [← forall_mem_nonempty_iff_neBot]
  refine ⟨fun h ↦ h s self_mem_necessityFilter, fun ⟨u, hu⟩ t ht ↦ ?_⟩
  obtain ⟨v, hv, -, hvt⟩ := ht u hu
  exact ⟨v, hvt v hv (p.le_refl v)⟩

/-- `t` is a good possibility over `s` when some world of `s` has only `t`-worlds among the
worlds of `s` at least as close. -/
def IsGoodPossibility (p : Preorder W) (s t : Set W) : Prop :=
  ∃ v ∈ s, ∀ w ∈ s, p.le w v → w ∈ t

theorem IsGoodPossibility.mono (h : IsGoodPossibility p s t) (htt' : t ⊆ t') :
    IsGoodPossibility p s t' :=
  let ⟨v, hv, hvt⟩ := h
  ⟨v, hv, fun w hw hwv ↦ htt' (hvt w hw hwv)⟩

/-- The good possibilities are not closed under intersection. Under the identity order on `Bool`
each world is a branch of its own, so `{true}` and `{false}` are good possibilities and their empty
intersection is not. -/
theorem exists_not_isGoodPossibility_inter :
    ∃ (p : Preorder Bool) (t t' : Set Bool), IsGoodPossibility p .univ t ∧
      IsGoodPossibility p .univ t' ∧ ¬ IsGoodPossibility p .univ (t ∩ t') :=
  ⟨⊥, {true}, {false}, ⟨true, trivial, fun _ _ h ↦ h⟩, ⟨false, trivial, fun _ _ h ↦ h⟩,
    fun ⟨v, _, h⟩ ↦
      let ⟨h₁, h₂⟩ := h v trivial rfl
      Bool.noConfusion ((show v = true from h₁).symm.trans (show v = false from h₂))⟩

/-! ### Necessity and the minimal worlds -/

theorem minimals_subset_of_mem_necessityFilter (h : t ∈ necessityFilter p s) :
    p.minimals s ⊆ t := fun m hm ↦
  let ⟨_, hv, hvm, hvt⟩ := h m hm.1
  hvt m hm.1 (hm.2 hv hvm)

theorem mem_necessityFilter_of_minimals_subset (hlim : ∀ u ∈ s, ∃ v ∈ p.minimals s, p.le v u)
    (h : p.minimals s ⊆ t) : t ∈ necessityFilter p s := fun u hu ↦
  let ⟨v, hv, hvu⟩ := hlim u hu
  ⟨v, hv.1, hvu, fun _ hw hwv ↦
    h ⟨hw, fun ⦃_⦄ hx hxw ↦ p.le_trans _ _ _ hwv (hv.2 hx (p.le_trans _ _ _ hxw hwv))⟩⟩

/-- Under the Limit Assumption, that every world of `s` lies above a minimal one, the filter is
the principal filter of the minimal worlds. -/
theorem necessityFilter_eq_principal (hlim : ∀ u ∈ s, ∃ v ∈ p.minimals s, p.le v u) :
    necessityFilter p s = 𝓟 (p.minimals s) :=
  Filter.ext fun _ ↦ ⟨minimals_subset_of_mem_necessityFilter,
    mem_necessityFilter_of_minimals_subset hlim⟩

theorem necessityFilter_eq_principal_of_wellFounded (hwf : WellFounded p.lt) :
    necessityFilter p s = 𝓟 (p.minimals s) :=
  necessityFilter_eq_principal fun _ ↦ Preorder.exists_le_mem_minimals hwf

theorem necessityFilter_eq_pure (hv : v ∈ s) (hle : ∀ u ∈ s, p.le v u)
    (hlt : ∀ u ∈ s, p.le u v → u = v) : necessityFilter p s = pure v := by
  have hmin : p.minimals s = {v} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨⟨hv, fun u hu _ ↦ hle u hu⟩,
      fun u hu ↦ hlt u hu.1 (hu.2 hv (hle u hu.1))⟩
  rw [necessityFilter_eq_principal fun u hu ↦ ⟨v, hmin ▸ rfl, hle u hu⟩, hmin,
    principal_singleton]

/-! ### Necessity and good possibility -/

theorem isGoodPossibility_of_mem_necessityFilter (h : t ∈ necessityFilter p s)
    (hs : s.Nonempty) : IsGoodPossibility p s t :=
  let ⟨_, hu⟩ := hs
  let ⟨v, hv, _, hvt⟩ := h _ hu
  ⟨v, hv, hvt⟩

theorem IsGoodPossibility.mem_necessityFilter_of_total (htot : Std.Total p.le)
    (h : IsGoodPossibility p s t) : t ∈ necessityFilter p s := by
  obtain ⟨v, hv, hvt⟩ := h
  intro u hu
  rcases htot.total v u with hvu | huv
  · exact ⟨v, hv, hvu, hvt⟩
  · exact ⟨u, hu, p.le_refl u, fun w hw hwu ↦ hvt w hw (p.le_trans _ _ _ hwu huv)⟩

theorem mem_necessityFilter_iff_isGoodPossibility_of_total (htot : Std.Total p.le)
    (hs : s.Nonempty) : t ∈ necessityFilter p s ↔ IsGoodPossibility p s t :=
  ⟨fun h ↦ isGoodPossibility_of_mem_necessityFilter h hs,
    fun h ↦ h.mem_necessityFilter_of_total htot⟩

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

theorem mem_necessityFilter_iff_of_least :
    t ∈ necessityFilter p s ↔ ∀ w ∈ s, p.le w b → w ∈ t :=
  ⟨fun h w hw hwb ↦
      let ⟨v, hv, _, hvt⟩ := h b hb
      hvt w hw (p.le_trans _ _ _ hwb (hleast v hv)),
    fun h u hu ↦ ⟨b, hb, hleast u hu, h⟩⟩

theorem minimals_subset_iff_of_least : p.minimals s ⊆ t ↔ ∀ w ∈ s, p.le w b → w ∈ t :=
  ⟨fun h _ hw hwb ↦ h ⟨hw, fun ⦃_⦄ hx _ ↦ p.le_trans _ _ _ hwb (hleast _ hx)⟩,
    fun h m hm ↦ h m hm.1 (hm.2 hb (hleast m hm.1))⟩

theorem isGoodPossibility_iff_mem_necessityFilter_of_least :
    IsGoodPossibility p s t ↔ t ∈ necessityFilter p s :=
  (isGoodPossibility_iff_of_least hb hleast).trans (mem_necessityFilter_iff_of_least hb hleast).symm

end Least

/-! ### Changing the domain

The filters of one preorder over different domains obey the rules of preferential consequence,
with no Limit Assumption ([burgess-1981]). -/

/-- What is necessary over two domains is necessary over their union. -/
theorem necessityFilter_union_le :
    necessityFilter p (s ∪ s') ≤ necessityFilter p s ⊔ necessityFilter p s' := by
  have key {s s' t : Set W} (h : t ∈ necessityFilter p s) (h' : t ∈ necessityFilter p s')
      (u : W) (hu : u ∈ s) : ∃ v ∈ s ∪ s', p.le v u ∧ ∀ w ∈ s ∪ s', p.le w v → w ∈ t := by
    obtain ⟨v, hv, hvu, hvt⟩ := h u hu
    by_cases hx : ∃ x ∈ s', p.le x v
    · obtain ⟨x, hx, hxv⟩ := hx
      obtain ⟨y, hy, hyx, hyt⟩ := h' x hx
      have hyv := p.le_trans _ _ _ hyx hxv
      exact ⟨y, .inr hy, p.le_trans _ _ _ hyv hvu, fun w hw hwy ↦
        hw.elim (fun hw ↦ hvt w hw (p.le_trans _ _ _ hwy hyv)) (fun hw ↦ hyt w hw hwy)⟩
    · exact ⟨v, .inl hv, hvu, fun w hw hwv ↦
        hw.elim (fun hw ↦ hvt w hw hwv) (fun hw ↦ absurd ⟨w, hw, hwv⟩ hx)⟩
  intro t ht u hu
  obtain ⟨h, h'⟩ := mem_sup.1 ht
  exact hu.elim (key h h' u) fun hu ↦ Set.union_comm s' s ▸ key h' h u hu

/-- What is necessary over a domain restricted to `t` is necessary over the domain wherever `t`
holds. -/
theorem necessityFilter_inf_principal_le :
    necessityFilter p s ⊓ 𝓟 t ≤ necessityFilter p (s ∩ t) := fun a ha ↦
  mem_inf_principal.2 fun u hu ↦ by
    by_cases hx : ∃ x ∈ s ∩ t, p.le x u
    · obtain ⟨x, hx, hxu⟩ := hx
      obtain ⟨v, hv, hvx, hva⟩ := ha x hx
      exact ⟨v, hv.1, p.le_trans _ _ _ hvx hxu, fun w hw hwv hwt ↦ hva w ⟨hw, hwt⟩ hwv⟩
    · exact ⟨u, hu, p.le_refl u, fun w hw hwu hwt ↦ absurd ⟨w, ⟨hw, hwt⟩, hwu⟩ hx⟩

/-- Restricting a domain to one of its necessities leaves its filter unchanged: cautious
monotonicity and cut. -/
theorem necessityFilter_inter_of_mem (ht : t ∈ necessityFilter p s) :
    necessityFilter p (s ∩ t) = necessityFilter p s := by
  refine le_antisymm (fun a ha u hu ↦ ?_) fun a ha ↦ ?_
  · obtain ⟨v, hv, hvu, hvta⟩ := inter_mem ht ha u hu.1
    exact ⟨v, ⟨hv, (hvta v hv (p.le_refl v)).1⟩, hvu, fun w hw hwv ↦ (hvta w hw.1 hwv).2⟩
  · exact mem_of_superset (inter_mem ht (mem_inf_principal.1 (necessityFilter_inf_principal_le ha)))
      fun _ hx ↦ hx.2 hx.1

/-- On a total preorder, restricting a domain to a proposition possible over it restricts its
filter to that proposition: rational monotonicity. -/
theorem necessityFilter_inter_of_frequently (htot : Std.Total p.le)
    (ht : ∃ᶠ x in necessityFilter p s, x ∈ t) :
    necessityFilter p (s ∩ t) = necessityFilter p s ⊓ 𝓟 t := by
  refine le_antisymm (fun a ha ↦ ?_) necessityFilter_inf_principal_le
  have hb : {x | x ∈ t → x ∈ a} ∈ necessityFilter p s := mem_inf_principal.1 ha
  suffices hb' : {x | x ∈ t → x ∈ a} ∈ necessityFilter p (s ∩ t) from
    mem_of_superset (inter_mem hb' (mem_of_superset self_mem_necessityFilter
      Set.inter_subset_right)) fun _ hx ↦ hx.1 hx.2
  obtain ⟨x₀, hx₀, h₀⟩ : ∃ x₀ ∈ s, ∀ v ∈ s, p.le v x₀ → ∃ z ∈ s, p.le z v ∧ z ∈ t := by
    by_contra! hcon
    exact ht hcon
  intro u hu
  obtain ⟨y, hy, hyu, hyx₀, hyb⟩ : ∃ y ∈ s, p.le y u ∧ p.le y x₀ ∧
      ∀ w ∈ s, p.le w y → w ∈ {x | x ∈ t → x ∈ a} := by
    obtain ⟨y₁, hy₁, hy₁u, hy₁b⟩ := hb u hu.1
    rcases htot.total y₁ x₀ with h | h
    · exact ⟨y₁, hy₁, hy₁u, h, hy₁b⟩
    · obtain ⟨y₂, hy₂, hy₂x₀, hy₂b⟩ := hb x₀ hx₀
      exact ⟨y₂, hy₂, p.le_trans _ _ _ hy₂x₀ (p.le_trans _ _ _ h hy₁u), hy₂x₀, hy₂b⟩
  obtain ⟨z, hz, hzy, hzt⟩ := h₀ y hy hyx₀
  exact ⟨z, ⟨hz, hzt⟩, p.le_trans _ _ _ hzy hyu,
    fun w hw hwz ↦ hyb w hw.1 (p.le_trans _ _ _ hwz hzy)⟩

end OrderingSemantics
