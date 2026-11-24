module

public import Linglib.Core.Order.Crossing
public import Linglib.Semantics.Space.Defs

/-!
# Shapes of paths

A *path* is a map `γ : ι → α` from a bounded linear order, and a *region* is a set `R : Set α`.
Each of the eight shapes of `Locative.Shape` is a condition on how a path passes through a
region. For example, a path is *cofinal* if it enters the region and *coinitial* if it leaves it.

This file defines `Locative.HasShape R γ d s`, which says that the path `γ` has the shape `s`
relative to the region `R`. The function `d` measures the distance to the region, and only the
approximative and recessive shapes use it. We prove that a path keeps its shape when it is
reparametrized, and we determine the shape of a reversed path and of a concatenation.

## Main definitions

* `Locative.HasShape`: a path has a shape relative to a region.

## Main results

* `Locative.exists_hasShape_iff`: a path that meets a region has some shape if and only if the
  positions it sends into the region form an order-connected set.
* `Locative.hasShape_reverse`: the reverse of a series has a shape if and only if the series has
  the reversed shape.
* `Locative.HasShape.concat`: if a shape is not bounded, the concatenation of two series of that
  shape has that shape.
* `Locative.HasShape.not_concat`: if a shape is bounded, the concatenation of two series of that
  shape does not have it.

## References

* [zwarts-2005]
* [pantcheva-2011]
-/

@[expose] public section

namespace Locative

open Order OrderDual Set
open scoped SetRel

section Shapes

variable {ι κ α β : Type*} [LinearOrder ι] [BoundedOrder ι] [LinearOrder κ] [BoundedOrder κ]
  (R : Set α) (γ : ι → α)

/-- `HasShape d R γ s` says that `γ` has shape `s` relative to `R`, `d` measuring nearness to
it. -/
def HasShape [Preorder β] (d : α → β) : Shape → Prop
  | .cofinal => Enters γ R
  | .coinitial => Leaves γ R
  | .transitive => Crosses γ R
  | .terminative => Reaches γ R
  | .egressive => Departs γ R
  | .approximative => Approaches γ R d
  | .recessive => Recedes γ R d
  | .prolative => StaysIn γ R

variable {R γ}

theorem HasShape.ordConnected [Preorder β] {d : α → β} {s : Shape} (h : HasShape R γ d s) :
    (γ ⁻¹' R).OrdConnected := by
  cases s with
  | cofinal | coinitial => exact h.1.ordConnected
  | transitive => exact h.1
  | terminative | egressive => rw [h.1]; exact ordConnected_singleton
  | prolative => rw [show γ ⁻¹' R = univ from eq_univ_of_forall h]; exact ordConnected_univ
  | approximative | recessive =>
    rw [show γ ⁻¹' R = ∅ from eq_empty_of_forall_notMem h.1]; exact ordConnected_empty

/-- A path that meets `R` has a shape exactly when its positions inside `R` are one stretch. -/
theorem exists_hasShape_iff [Preorder β] {d : α → β} (hne : (γ ⁻¹' R).Nonempty) :
    (∃ s, HasShape R γ d s) ↔ (γ ⁻¹' R).OrdConnected := by
  refine ⟨fun ⟨_, h⟩ ↦ h.ordConnected, fun h ↦ ?_⟩
  by_cases h₀ : γ ⊥ ∈ R <;> by_cases h₁ : γ ⊤ ∈ R
  · exact ⟨.prolative, fun _ ↦ h.out h₀ h₁ ⟨bot_le, le_top⟩⟩
  · exact ⟨.coinitial, leaves_iff_ordConnected.2 ⟨h, h₀, h₁⟩⟩
  · exact ⟨.cofinal, enters_iff_ordConnected.2 ⟨h, h₀, h₁⟩⟩
  · exact ⟨.transitive, h, hne, h₀, h₁⟩

private theorem HasShape.ends [Preorder β] {d : α → β} {s : Shape} (h : HasShape R γ d s) :
    (γ ⊥ ∈ R ↔ s ∈ [Shape.coinitial, .egressive, .prolative]) ∧
      (γ ⊤ ∈ R ↔ s ∈ [Shape.cofinal, .terminative, .prolative]) := by
  cases s with
  | cofinal | coinitial => simp [h.2.1, h.2.2]
  | terminative => have h := Reaches.enters h; simp [h.2.1, h.2.2]
  | egressive => have h := Departs.leaves h; simp [h.2.1, h.2.2]
  | transitive => simp [h.2.2.1, h.2.2.2]
  | prolative => simp [h ⊥, h ⊤]
  | approximative | recessive => simp [h.1 ⊥, h.1 ⊤]

/-- Two shapes of one path agree in direction and in being bounded, so they differ at most in
delimitation. -/
theorem HasShape.direction_eq [Preorder β] {d : α → β} {s t : Shape} (hs : HasShape R γ d s)
    (ht : HasShape R γ d t) : s.direction = t.direction ∧ (s.IsBounded ↔ t.IsBounded) := by
  have h₀ := hs.ends.1.symm.trans ht.ends.1
  have h₁ := hs.ends.2.symm.trans ht.ends.2
  have outside (hs : Crosses γ R) (ht : ∀ i, γ i ∉ R) : False :=
    hs.2.1.elim fun i hi ↦ ht i hi
  have opposite (ha : Approaches γ R d) (hr : Recedes γ R d) : False :=
    have hlt := lt_of_le_of_ne (bot_le (a := (⊤ : ι))) ha.2.2
    lt_asymm (ha.2.1 hlt) (hr.2.1 hlt)
  cases s <;> cases t <;> first
    | decide
    | (exfalso; revert h₀ h₁; decide)
    | exact (outside hs ht.1).elim
    | exact (outside ht hs.1).elim
    | exact (opposite hs ht).elim
    | exact (opposite ht hs).elim

theorem HasShape.comp [Preorder β] {d : α → β} {s : Shape} (h : HasShape R γ d s)
    (e : κ ≃o ι) : HasShape R (γ ∘ e) d s := by
  have hpre : (γ ∘ e) ⁻¹' R = e ⁻¹' (γ ⁻¹' R) := rfl
  have hne : ((⊥ : κ) ≠ ⊤ ↔ (⊥ : ι) ≠ ⊤) := by
    rw [ne_eq, ne_eq, ← e.injective.eq_iff, map_bot, map_top]
  cases s with
  | cofinal => exact ⟨hpre ▸ h.1.preimage e.monotone, by simpa using h.2.1, by simpa using h.2.2⟩
  | coinitial => exact ⟨hpre ▸ h.1.preimage e.monotone, by simpa using h.2.1, by simpa using h.2.2⟩
  | transitive =>
    obtain ⟨hc, ⟨i, hi⟩, h₀, h₁⟩ := h
    exact ⟨hpre ▸ hc.preimage_mono e.monotone, ⟨e.symm i, by simpa using hi⟩,
      by simpa using h₀, by simpa using h₁⟩
  | terminative =>
    refine ⟨?_, hne.2 h.2⟩
    ext k
    show e k ∈ γ ⁻¹' R ↔ k = ⊤
    rw [h.1, mem_singleton_iff, ← map_top e, e.injective.eq_iff]
  | egressive =>
    refine ⟨?_, hne.2 h.2⟩
    ext k
    show e k ∈ γ ⁻¹' R ↔ k = ⊥
    rw [h.1, mem_singleton_iff, ← map_bot e, e.injective.eq_iff]
  | prolative => exact fun k ↦ h (e k)
  | approximative => exact ⟨fun k ↦ h.1 (e k), h.2.1.comp_strictMono e.strictMono, hne.2 h.2.2⟩
  | recessive => exact ⟨fun k ↦ h.1 (e k), h.2.1.comp e.strictMono, hne.2 h.2.2⟩

/-- Reparametrizing a path by an order isomorphism keeps its shape. -/
theorem hasShape_comp [Preorder β] {d : α → β} (e : κ ≃o ι) {s : Shape} :
    HasShape R (γ ∘ e) d s ↔ HasShape R γ d s :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp e.symm, fun h ↦ h.comp e⟩

/-- Traversing a path the other way, on the dual order of positions, reverses its shape. -/
theorem hasShape_comp_ofDual [Preorder β] {d : α → β} {s : Shape} :
    HasShape R (γ ∘ ofDual) d s ↔ HasShape R γ d s.reverse := by
  have hpre : (γ ∘ ofDual) ⁻¹' R = ofDual ⁻¹' (γ ⁻¹' R) := rfl
  have hne : ((⊥ : ιᵒᵈ) ≠ ⊤ ↔ (⊥ : ι) ≠ ⊤) := by
    rw [ne_eq, ne_eq, ← toDual_top, ← toDual_bot, toDual_inj, eq_comm]
  cases s with
  | cofinal =>
    simp only [HasShape, Shape.reverse, Enters, Leaves, hpre,
      isUpperSet_preimage_ofDual_iff, Function.comp_apply, ofDual_bot, ofDual_top]
    tauto
  | coinitial =>
    simp only [HasShape, Shape.reverse, Enters, Leaves, hpre,
      isLowerSet_preimage_ofDual_iff, Function.comp_apply, ofDual_bot, ofDual_top]
    tauto
  | transitive =>
    simp only [HasShape, Shape.reverse, Crosses, hpre, ordConnected_dual,
      Function.comp_apply, ofDual_bot, ofDual_top, OrderDual.ofDual.surjective.nonempty_preimage]
    tauto
  | terminative =>
    refine and_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ hne
    · ext i
      have := congrArg (toDual i ∈ ·) h
      simpa [hpre, ← toDual_bot] using this
    · ext i
      rw [hpre, mem_preimage, h, mem_singleton_iff, mem_singleton_iff, ← toDual_bot]
      exact ⟨fun h' ↦ by rw [← h', toDual_ofDual], fun h' ↦ by rw [h', ofDual_toDual]⟩
  | egressive =>
    refine and_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ hne
    · ext i
      have := congrArg (toDual i ∈ ·) h
      simpa [hpre, ← toDual_top] using this
    · ext i
      rw [hpre, mem_preimage, h, mem_singleton_iff, mem_singleton_iff, ← toDual_top]
      exact ⟨fun h' ↦ by rw [← h', toDual_ofDual], fun h' ↦ by rw [h', ofDual_toDual]⟩
  | prolative => exact OrderDual.forall
  | approximative =>
    simp only [HasShape, Shape.reverse, Approaches, Recedes, OrderDual.forall,
      Function.comp_apply, ofDual_toDual, ← Function.comp_assoc, strictAnti_comp_ofDual_iff, hne]
  | recessive =>
    simp only [HasShape, Shape.reverse, Approaches, Recedes, OrderDual.forall,
      Function.comp_apply, ofDual_toDual, ← Function.comp_assoc, strictMono_comp_ofDual_iff, hne]

end Shapes

/-! ### Shapes of series -/

section Series

variable {α β : Type*} {r : SetRel α α} {p q : RelSeries r} {R : Set α} [Preorder β]
  {d : α → β} {s : Shape}

/-- Reversing a series reverses its shape. -/
theorem hasShape_reverse (p : RelSeries r) :
    HasShape R p.reverse d s ↔ HasShape R p d s.reverse :=
  (hasShape_comp (γ := p ∘ OrderDual.ofDual) Fin.revOrderIso.symm).trans hasShape_comp_ofDual

/-- A path with a shape that starts inside the region never enters it. -/
theorem HasShape.entries_eq_zero_of_head_mem
    (h : HasShape R p d s) (h0 : p.head ∈ R) : p.entries R = 0 := by
  cases s with
  | cofinal => exact absurd h0 h.2.1
  | coinitial => exact Leaves.entries_eq h
  | transitive => exact absurd h0 h.2.2.1
  | terminative => exact absurd h0 (Reaches.enters h).2.1
  | egressive => exact (Departs.leaves h).entries_eq
  | prolative => exact StaysIn.entries_eq h
  | approximative => exact absurd h0 (h.1 _)
  | recessive => exact absurd h0 (h.1 _)

/-- Concatenation keeps a shape without a transition. -/
theorem HasShape.concat (hs : ¬ s.IsBounded) (hp : HasShape R p d s) (hq : HasShape R q d s)
    (h : p.last = q.head) : HasShape R (p.smash q h) d s := by
  have hne (hne : (⊥ : Fin (p.length + 1)) ≠ ⊤) : (⊥ : Fin (p.length + q.length + 1)) ≠ ⊤ := by
    simp only [ne_eq, Fin.ext_iff, bot_eq_zero, Fin.top_eq_last, Fin.val_zero, Fin.val_last]
      at hne ⊢
    omega
  cases s with
  | prolative => exact (RelSeries.forall_smash_apply h).2 ⟨hp, hq⟩
  | approximative =>
    exact ⟨(RelSeries.forall_smash_apply h (P := (· ∉ R))).2 ⟨hp.1, hq.1⟩,
      RelSeries.strictAnti_comp_smash h hp.2.1 hq.2.1, hne hp.2.2⟩
  | recessive =>
    exact ⟨(RelSeries.forall_smash_apply h (P := (· ∉ R))).2 ⟨hp.1, hq.1⟩,
      RelSeries.strictMono_comp_smash h hp.2.1 hq.2.1, hne hp.2.2⟩
  | _ => exact absurd (by decide) hs

/-- Concatenation never keeps a shape with a transition: the ends of a cofinal or a coinitial path
lie on opposite sides of `R`, so no two of them concatenate, and a concatenation of two
transitive paths enters `R` twice. -/
theorem HasShape.not_concat (hs : s.IsBounded) (hp : HasShape R p d s) (hq : HasShape R q d s)
    (h : p.last = q.head) : ¬ HasShape R (p.smash q h) d s := by
  have cofinal (hp : Enters p R) (hq : Enters q R) : False :=
    hq.2.1 (by rw [RelSeries.apply_bot, ← h, ← RelSeries.apply_top]; exact hp.2.2)
  have coinitial (hp : Leaves p R) (hq : Leaves q R) : False :=
    hp.2.2 (by rw [RelSeries.apply_top, h, ← RelSeries.apply_bot]; exact hq.2.1)
  cases s with
  | cofinal => exact (cofinal hp hq).elim
  | terminative => exact (cofinal (Reaches.enters hp) (Reaches.enters hq)).elim
  | coinitial => exact (coinitial hp hq).elim
  | egressive => exact (coinitial (Departs.leaves hp) (Departs.leaves hq)).elim
  | transitive =>
    intro hr
    have := Crosses.entries_eq hr
    rw [RelSeries.entries_smash, Crosses.entries_eq hp, Crosses.entries_eq hq] at this
    exact absurd this (by decide)
  | _ => exact absurd hs (by decide)

end Series

end Locative
