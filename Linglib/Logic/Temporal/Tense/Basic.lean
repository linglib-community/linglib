module

public import Linglib.Core.Order.ForestOrder
public import Linglib.Logic.Modal.Defs
import Mathlib.Order.Nat

/-!
# Tense logic

A model of time is a type of instants with a precedence relation `<`. The operators of tense logic
are possibility and necessity along it and along its converse: `𝐅 p t` says that `p` holds at some
instant after `t`, `𝐏 p t` at some instant before it, and `𝐆` and `𝐇` that it holds at all of
them; `𝐄 p` is `𝐏 p ⊔ p ⊔ 𝐅 p` and `𝐀 p` is `𝐇 p ⊓ p ⊓ 𝐆 p`. Since the two relations are
converse, `𝐏` is left adjoint to `𝐆` and `𝐅` to `𝐇`, which is the minimal tense logic.

A schema *defines* a property of time when it holds of every proposition exactly on the models
with that property. This file proves the first-order correspondences of [goranko-2023], each for
the weakest structure that states it: no end, no beginning, density and transitivity for a bare
`<`, a beginning and an end for a preorder, and the linearity schemas for a bare `<`, with their
form on a partial order.

## Notation

* `𝐅`, `𝐏`, `𝐆`, `𝐇`, `𝐄`, `𝐀`: the tense operators, in the scope `TenseLogic`.

## Main results

* `TenseLogic.gc_P_G`, `TenseLogic.gc_F_H`: the adjunctions of the minimal tense logic.
* `TenseLogic.noEnd_iff`, `TenseLogic.noBeg_iff`: time without a last or a first instant.
* `TenseLogic.F_dense_iff`, `TenseLogic.F_tran_iff`: dense time and transitive precedence.
* `TenseLogic.beg_iff`, `TenseLogic.end_iff`: time with a beginning or an end.
* `TenseLogic.linF_iff`, `TenseLogic.linP_iff`, `TenseLogic.lin_iff`: time that does not branch.

## Implementation notes

The operators are notation for `ModalLogic.Diamond` and `ModalLogic.Box` along
`{x : T × T | x.1 < x.2}` and its converse, not definitions, so the lemmas of `Logic/Modal` apply
to them as they stand, and `to_dual` derives each statement about the past from the one about the
future. A schema is stated as an inequality for every proposition, `∀ p, 𝐆 p ≤ 𝐅 p`.

## References

* [goranko-2023]
* [prior-1967]
* [burgess-1984]
-/

@[expose] public section

namespace TenseLogic

open ModalLogic
open scoped SetRel

set_option quotPrecheck false in
/-- `𝐅 p` holds at an instant when `p` holds at some later instant. -/
scoped notation3 "𝐅" => ModalLogic.Diamond {x : _ × _ | x.1 < x.2}

set_option quotPrecheck false in
/-- `𝐏 p` holds at an instant when `p` holds at some earlier instant. -/
scoped notation3 "𝐏" => ModalLogic.Diamond {x : _ × _ | x.2 < x.1}

set_option quotPrecheck false in
/-- `𝐆 p` holds at an instant when `p` holds at every later instant. -/
scoped notation3 "𝐆" => ModalLogic.Box {x : _ × _ | x.1 < x.2}

set_option quotPrecheck false in
/-- `𝐇 p` holds at an instant when `p` holds at every earlier instant. -/
scoped notation3 "𝐇" => ModalLogic.Box {x : _ × _ | x.2 < x.1}

set_option quotPrecheck false in
/-- `𝐄 p` holds at an instant when `p` holds earlier, then or later. -/
scoped notation3 "𝐄" => ModalLogic.Diamond {x : _ × _ | x.2 < x.1 ∨ x.1 = x.2 ∨ x.1 < x.2}

set_option quotPrecheck false in
/-- `𝐀 p` holds at an instant when `p` holds earlier, then and later. -/
scoped notation3 "𝐀" => ModalLogic.Box {x : _ × _ | x.2 < x.1 ∨ x.1 = x.2 ∨ x.1 < x.2}

variable {T : Type*}

section LT

variable [LT T] {p : T → Prop} {t : T}

@[to_dual (attr := simp) P_apply]
theorem F_apply : 𝐅 p t ↔ ∃ s, t < s ∧ p s := .rfl

@[to_dual (attr := simp) H_apply]
theorem G_apply : 𝐆 p t ↔ ∀ s, t < s → p s := .rfl

theorem E_eq (p : T → Prop) : 𝐄 p = 𝐏 p ⊔ p ⊔ 𝐅 p := by
  ext t
  simp only [Diamond, Set.mem_ofPred_eq, or_and_right, exists_or, exists_eq_left', Pi.sup_apply,
    sup_Prop_eq, or_assoc]

theorem A_eq (p : T → Prop) : 𝐀 p = 𝐇 p ⊓ p ⊓ 𝐆 p := by
  ext t
  simp only [Box, Set.mem_ofPred_eq, or_imp, forall_and, forall_eq', Pi.inf_apply, inf_Prop_eq,
    and_assoc]

/-! ### The minimal tense logic -/

/-- Sometime in the past is left adjoint to always in the future. The unit is the schema
`p → 𝐆 (𝐏 p)` of the minimal tense logic. -/
@[to_dual gc_F_H /-- Sometime in the future is left adjoint to always in the past. The unit is the
schema `p → 𝐇 (𝐅 p)` of the minimal tense logic. -/]
theorem gc_P_G : GaloisConnection (𝐏 : (T → Prop) → T → Prop) 𝐆 := diamond_box_gc _

/-! ### The mirror image -/

/-- The mirror image: the future of reversed time is the past. -/
theorem F_toDual (p : T → Prop) (t : T) :
    𝐅 (p ∘ OrderDual.ofDual) (OrderDual.toDual t) ↔ 𝐏 p t := .rfl

theorem P_toDual (p : T → Prop) (t : T) :
    𝐏 (p ∘ OrderDual.ofDual) (OrderDual.toDual t) ↔ 𝐅 p t := .rfl

theorem G_toDual (p : T → Prop) (t : T) :
    𝐆 (p ∘ OrderDual.ofDual) (OrderDual.toDual t) ↔ 𝐇 p t := .rfl

theorem H_toDual (p : T → Prop) (t : T) :
    𝐇 (p ∘ OrderDual.ofDual) (OrderDual.toDual t) ↔ 𝐆 p t := .rfl

/-! ### Time without end or beginning -/

/-- (NOEND) `𝐆 p → 𝐅 p` defines time without a last instant. -/
@[to_dual noBeg_iff /-- (NOBEG) `𝐇 p → 𝐏 p` defines time without a first instant. -/]
theorem noEnd_iff : (∀ p : T → Prop, 𝐆 p ≤ 𝐅 p) ↔ NoMaxOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs, _⟩ := h (fun _ ↦ True) t fun _ _ ↦ trivial; ⟨s, hs⟩⟩,
    fun _ _ t hG ↦ let ⟨s, hs⟩ := exists_gt t; ⟨s, hs, hG s hs⟩⟩

/-- (NOEND) in its other form: `𝐅 ⊤` is valid exactly on time without a last instant. -/
@[to_dual top_le_P_top_iff
/-- (NOBEG) in its other form: `𝐏 ⊤` is valid exactly on time without a first instant. -/]
theorem top_le_F_top_iff : (⊤ : T → Prop) ≤ 𝐅 ⊤ ↔ NoMaxOrder T :=
  ⟨fun h ↦ ⟨fun t ↦ let ⟨s, hs, _⟩ := h t trivial; ⟨s, hs⟩⟩,
    fun _ t _ ↦ let ⟨s, hs⟩ := exists_gt t; ⟨s, hs, trivial⟩⟩

/-! ### Density -/

/-- (DENSE) `𝐅 p → 𝐅 (𝐅 p)` defines dense time. -/
@[to_dual P_dense_iff /-- (DENSE) `𝐏 p → 𝐏 (𝐏 p)` defines dense time. -/]
theorem F_dense_iff : (∀ p : T → Prop, 𝐅 p ≤ 𝐅 (𝐅 p)) ↔ DenselyOrdered T :=
  ⟨fun h ↦ ⟨fun a b hab ↦ let ⟨c, hac, _, hcb, rfl⟩ := h (· = b) a ⟨b, hab, rfl⟩; ⟨c, hac, hcb⟩⟩,
    fun _ _ _ ⟨s, hts, hs⟩ ↦ let ⟨c, htc, hcs⟩ := exists_between hts; ⟨c, htc, s, hcs, hs⟩⟩

/-- (DENSE) `𝐆 (𝐆 p) → 𝐆 p` defines dense time. -/
@[to_dual H_dense_iff /-- (DENSE) `𝐇 (𝐇 p) → 𝐇 p` defines dense time. -/]
theorem G_dense_iff : (∀ p : T → Prop, 𝐆 (𝐆 p) ≤ 𝐆 p) ↔ DenselyOrdered T :=
  ⟨fun h ↦ ⟨fun a b hab ↦ h (fun u ↦ ∃ c, a < c ∧ c < u) a (fun c hc _ hu ↦ ⟨c, hc, hu⟩) b hab⟩,
    fun _ _ _ h s hts ↦ let ⟨c, htc, hcs⟩ := exists_between hts; h c htc s hcs⟩

/-! ### Transitivity -/

/-- (TRAN) `𝐅 (𝐅 p) → 𝐅 p` defines transitive precedence. -/
theorem F_tran_iff : (∀ p : T → Prop, 𝐅 (𝐅 p) ≤ 𝐅 p) ↔ IsTrans T (· < ·) :=
  ⟨fun h ↦ ⟨fun a b c hab hbc ↦ let ⟨_, hac, rfl⟩ := h (· = c) a ⟨b, hab, c, hbc, rfl⟩; hac⟩,
    fun h _ _ ⟨_, hts, u, hsu, hu⟩ ↦ ⟨u, h.trans _ _ _ hts hsu, hu⟩⟩

/-- (TRAN) `𝐏 (𝐏 p) → 𝐏 p` defines transitive precedence. -/
theorem P_tran_iff : (∀ p : T → Prop, 𝐏 (𝐏 p) ≤ 𝐏 p) ↔ IsTrans T (· < ·) :=
  ⟨fun h ↦ ⟨fun a b c hab hbc ↦ let ⟨_, hac, rfl⟩ := h (· = a) c ⟨b, hbc, a, hab, rfl⟩; hac⟩,
    fun h _ _ ⟨_, hst, u, hus, hu⟩ ↦ ⟨u, h.trans _ _ _ hus hst, hu⟩⟩

/-- (TRAN) `𝐆 p → 𝐆 (𝐆 p)` defines transitive precedence. -/
theorem G_tran_iff : (∀ p : T → Prop, 𝐆 p ≤ 𝐆 (𝐆 p)) ↔ IsTrans T (· < ·) :=
  ⟨fun h ↦ ⟨fun a b c hab hbc ↦ h (a < ·) a (fun _ hs ↦ hs) b hab c hbc⟩,
    fun h _ _ hG _ hts u hsu ↦ hG u (h.trans _ _ _ hts hsu)⟩

/-- (TRAN) `𝐇 p → 𝐇 (𝐇 p)` defines transitive precedence. -/
theorem H_tran_iff : (∀ p : T → Prop, 𝐇 p ≤ 𝐇 (𝐇 p)) ↔ IsTrans T (· < ·) :=
  ⟨fun h ↦ ⟨fun a b c hab hbc ↦ h (· < c) c (fun _ hs ↦ hs) b hbc a hab⟩,
    fun h _ _ hH _ hst u hus ↦ hH u (h.trans _ _ _ hus hst)⟩

/-! ### Linearity -/

/-- (LIN-F) `𝐏 (𝐅 p) → 𝐄 p` defines forward-linear time: two instants preceded by the same
instant are comparable. -/
theorem linF_iff :
    (∀ p : T → Prop, 𝐏 (𝐅 p) ≤ 𝐄 p) ↔ ∀ ⦃a b c : T⦄, a < b → a < c → c < b ∨ b = c ∨ b < c :=
  ⟨fun h a b c hab hac ↦ let ⟨_, hbc, rfl⟩ := h (· = c) b ⟨a, hab, c, hac, rfl⟩; hbc,
    fun h _ _ ⟨_, hat, c, hac, hc⟩ ↦ ⟨c, h hat hac, hc⟩⟩

/-- (LIN-P) `𝐅 (𝐏 p) → 𝐄 p` defines backward-linear time: two instants preceding the same
instant are comparable. -/
theorem linP_iff :
    (∀ p : T → Prop, 𝐅 (𝐏 p) ≤ 𝐄 p) ↔ ∀ ⦃a b c : T⦄, b < a → c < a → c < b ∨ b = c ∨ b < c :=
  ⟨fun h a b c hba hca ↦ let ⟨_, hbc, rfl⟩ := h (· = c) b ⟨a, hba, c, hca, rfl⟩; hbc,
    fun h _ _ ⟨_, hta, c, hca, hc⟩ ↦ ⟨c, h hta hca, hc⟩⟩

/-- (LIN) `𝐏 (𝐅 p) ∨ 𝐅 (𝐏 p) → 𝐄 p` defines time that is linear in both directions. -/
theorem lin_iff :
    (∀ p : T → Prop, 𝐏 (𝐅 p) ⊔ 𝐅 (𝐏 p) ≤ 𝐄 p) ↔
      (∀ ⦃a b c : T⦄, a < b → a < c → c < b ∨ b = c ∨ b < c) ∧
        ∀ ⦃a b c : T⦄, b < a → c < a → c < b ∨ b = c ∨ b < c := by
  simp only [sup_le_iff, forall_and, linF_iff, linP_iff]

end LT

section Preorder

variable [Preorder T]

/-! ### Time with a beginning or an end -/

/-- (BEG) `𝐇 ⊥ ∨ 𝐏 (𝐇 ⊥)` is valid exactly when every instant is, or is preceded by, a first
instant. -/
@[to_dual end_iff /-- (END) `𝐆 ⊥ ∨ 𝐅 (𝐆 ⊥)` is valid exactly when every instant is, or is
followed by, a last instant. -/]
theorem beg_iff : (⊤ : T → Prop) ≤ 𝐇 ⊥ ⊔ 𝐏 (𝐇 ⊥) ↔ IsCoinitial {s : T | IsMin s} := by
  refine ⟨fun h t ↦ ?_, fun h t _ ↦ ?_⟩
  · rcases h t trivial with h | ⟨s, hs, hmin⟩
    · exact ⟨t, isMin_iff_forall_not_lt.2 fun s hs ↦ h s hs, le_rfl⟩
    · exact ⟨s, isMin_iff_forall_not_lt.2 fun u hu ↦ hmin u hu, hs.le⟩
  · obtain ⟨s, hs, hst⟩ := h t
    by_cases hlt : s < t
    · exact .inr ⟨s, hlt, fun u hu ↦ (hs.not_lt hu).elim⟩
    · exact .inl fun u hu ↦ hs.not_lt (hu.trans_le (not_lt_iff_le_imp_ge.1 hlt hst))

end Preorder

section PartialOrder

variable [PartialOrder T]

/-- (LIN-P) on a partial order: `𝐅 (𝐏 p) → 𝐄 p` holds exactly when the instants before any
instant are comparable, the tree-like models of branching time. -/
theorem linP_iff_isForestOrder : (∀ p : T → Prop, 𝐅 (𝐏 p) ≤ 𝐄 p) ↔ IsForestOrder T := by
  refine linP_iff.trans ⟨fun h ↦ ⟨fun a b c ha hb ↦ ?_⟩, fun h a b c hba hca ↦ ?_⟩
  · obtain rfl | ha := ha.eq_or_lt
    · exact .inr hb
    obtain rfl | hb := hb.eq_or_lt
    · exact .inl ha.le
    rcases h ha hb with h | rfl | h
    exacts [.inr h.le, .inl le_rfl, .inl h.le]
  · rcases h.le_total_of_le_of_le hba.le hca.le with h | h
    · exact .inr h.eq_or_lt
    · exact h.eq_or_lt.elim (fun h ↦ .inr (.inl h.symm)) .inl

/-- (LIN-F) on a partial order: `𝐏 (𝐅 p) → 𝐄 p` holds exactly when the instants after any
instant are comparable. -/
theorem linF_iff_isForestOrder : (∀ p : T → Prop, 𝐏 (𝐅 p) ≤ 𝐄 p) ↔ IsForestOrder Tᵒᵈ := by
  rw [isForestOrder_orderDual_iff]
  refine linF_iff.trans ⟨fun h a b c ha hb ↦ ?_, fun h a b c hab hac ↦ ?_⟩
  · obtain rfl | ha := ha.eq_or_lt
    · exact .inl hb
    obtain rfl | hb := hb.eq_or_lt
    · exact .inr ha.le
    rcases h ha hb with h | rfl | h
    exacts [.inr h.le, .inl le_rfl, .inl h.le]
  · rcases h hab.le hac.le with h | h
    · exact .inr h.eq_or_lt
    · exact h.eq_or_lt.elim (fun h ↦ .inr (.inl h.symm)) .inl

end PartialOrder

/-! ### The natural numbers

Time ordered as the natural numbers has a beginning and no end. -/

example : ∀ p : ℕ → Prop, 𝐆 p ≤ 𝐅 p := noEnd_iff.2 inferInstance

example : ¬ ∀ p : ℕ → Prop, 𝐇 p ≤ 𝐏 p := fun h ↦
  let ⟨_, hs⟩ := (noBeg_iff.1 h).exists_lt 0; Nat.not_lt_zero _ hs

example : (⊤ : ℕ → Prop) ≤ 𝐇 ⊥ ⊔ 𝐏 (𝐇 ⊥) := beg_iff.2 fun t ↦ ⟨0, fun _ _ ↦ Nat.zero_le _, t.zero_le⟩

example : ¬ ∀ p : ℕ → Prop, 𝐅 p ≤ 𝐅 (𝐅 p) := fun h ↦
  let ⟨_, h₁, h₂⟩ := (F_dense_iff.1 h).dense 0 1 Nat.zero_lt_one; by omega

end TenseLogic
