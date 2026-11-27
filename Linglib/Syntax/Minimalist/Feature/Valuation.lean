/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Minimalist.Probe.Agree

/-!
# Valuation

This file defines valuation of feature bundles, the part of Agree that copies the value of a goal
into a probe ([chomsky-2000]), from the unification of a single slot (`FeatureSlot.unifyWith`)
in the slot order of its dimension. An absent slot is unchanged, since an item that lacks a
dimension is not a probe for it.

Valuing a bundle at a dimension it bears is unification with the bundle that bears only the
value (`Minimalist.FeatureBundle.valueAt_eq_coe_iff`). At an agreement dimension, person
included, unification followed by `FeatureBundle.agreement` is unification of agreement bundles
(`Minimalist.FeatureBundle.map_agreement_unifyAt`). Agree with a goal that has no value at
the dimension leaves the probe unchanged, so Agree can fail without causing a crash
([preminger-2014]). The goal a probe agrees with is found by search
(`Minimalist.PlanarSyntacticObject.goals`).

The items of a derivation carry their bundles in a `FeatureState`, and Agree over it is the one
Agree of `Probe/Agree.lean`, `Probe.agree`, with the probe of an item at a dimension and valuation
as its copying. Valuation values the probe and the goal each with the value of the other at the
dimension, so a valued probe, such as a case assigner, values an unvalued goal. A goal matches a
probe when it bears the dimension, since matching is identity of the dimension and not of the
value ([chomsky-2000]). The probe of an item at a dimension is satisfied by the goals that match
it and interacts with those that are also active. A matching goal that is not active therefore
halts the search without valuing: Chomsky's defective intervention is satisfaction without
interaction in the sense of [deal-2025a]. Valuation only adds features, so [a run of Agree
extends the state](##Minimalist.FeatureState.le_agree_state), and [a slot holding a maximal
element of its order, as a value of a flat slot is, keeps it
](##Minimalist.FeatureState.apply_eq_coe_of_le). A person slot can grow, as one holding the first
person comes to hold the first person inclusive.

## Main definitions

* `Minimalist.FeatureBundle.valueAt`: a bundle valued with `v` at a dimension.
* `Minimalist.FeatureBundle.valueFrom`: a bundle valued from another at a dimension.
* `Minimalist.FeatureState`: the feature bundles of the items of a derivation.
* `Minimalist.FeatureState.Matches`: a goal matches a probe at a dimension.
* `Minimalist.FeatureState.probe`: the probe of an item at a dimension.
* `Minimalist.FeatureState.value`: two items valued from each other at a dimension, the copying
  of Agree.

## Implementation notes

The leaves of a `SyntacticObject` are lexical-item tokens, and the tree records nothing else: in
[marcolli-chomsky-berwick-2025] the leaves are drawn from a set of lexical items and syntactic
features, and Merge attaches no label to an internal vertex. A lexical item carries the bundle it
has in the lexicon (`LexicalItem.features`). Agree changes the features of the items it relates,
producing what [chomsky-2000] calls modified lexical items. The bundles of a derivation are
therefore kept outside the tree: a `FeatureState` assigns a bundle to each item, and valuation
changes that assignment, not the tree.

## References

* [chomsky-2000]
* [marcolli-chomsky-berwick-2025]
* [deal-2025a]
* [preminger-2014]
* [amato-2025]
-/

@[expose] public section

namespace Minimalist

namespace FeatureBundle

variable (probe goal : FeatureBundle) (t : FeatureType)

/-- The bundle `b` unified with the slot `x` at `t`, or `⊤` if they are incompatible there. A
bundle that lacks the dimension is unchanged. -/
def unifyAt (b : FeatureBundle) (t : FeatureType) (x : t.Slot) : WithTop FeatureBundle :=
  ((b t).unifyWith (FeatureType.Slot.unify t) x).map (Function.update b t)

/-- The bundle `b` valued with `v` at `t`, or `⊤` if `b` is valued otherwise at `t`. -/
def valueAt (b : FeatureBundle) (t : FeatureType) (v : t.Value) : WithTop FeatureBundle :=
  b.unifyAt t (FeatureType.Slot.ofValue t v)

variable {t} {b b' : FeatureBundle} {x : t.Slot} {v : t.Value}

/-- Unifying a bundle at a dimension it bears is unifying it with the bundle that bears only the
slot. -/
theorem unifyAt_eq_coe_iff (hb : b t ≠ ⊥) :
    b.unifyAt t x = ↑b' ↔ IsLUB {b, Function.update (⊥ : FeatureBundle) t ↑x} b' := by
  rw [isLUB_pair_update_bot_iff, unifyAt, WithTop.map_eq_some_iff]
  have key {s' : FeatureSlot t.Slot} := FeatureSlot.unifyWith_eq_coe_iff (x := x) (s' := s')
    (FeatureType.Slot.isLUB_unify t) hb
  exact ⟨fun ⟨s, hs, hb'⟩ ↦ hb' ▸ ⟨by simpa using key.1 hs, by simp⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨b' t, key.2 h₁, h₂.symm⟩⟩

theorem le_of_unifyAt_eq_coe (h : b.unifyAt t x = ↑b') : b ≤ b' := by
  rcases eq_or_ne (b t) ⊥ with hb | hb
  · rw [unifyAt, hb, FeatureSlot.unifyWith_bot, WithTop.map_coe, WithTop.coe_inj] at h
    exact h ▸ le_update_self_iff.2 (hb ▸ le_rfl)
  · exact (isLUB_pair_iff_forall_le.1 ((unifyAt_eq_coe_iff hb).1 h)).1

theorem le_of_valueAt_eq_coe (h : b.valueAt t v = ↑b') : b ≤ b' := le_of_unifyAt_eq_coe h

/-- Valuing a bundle at a dimension it bears is unifying it with the bundle that bears only the
value. -/
theorem valueAt_eq_coe_iff (hb : b t ≠ ⊥) :
    b.valueAt t v = ↑b' ↔ IsLUB {b, single t v} b' :=
  unifyAt_eq_coe_iff hb

/-- Unifying a checking bundle at an agreement dimension it bears is unifying its agreement
bundle there. -/
theorem map_agreement_unifyAt {d : Agreement.Dimension} {x : d.Slot} {b : FeatureBundle}
    (hb : b (.agr d) ≠ ⊥) :
    (b.unifyAt (.agr d) x).map agreement =
      (b.agreement : WithTop Agreement.Bundle) ⊔ ↑(Function.update (⊥ : Agreement.Bundle) d x) := by
  rw [Agreement.Bundle.coe_sup_coe_update_bot, agreement_apply, unifyAt, WithTop.map_map,
    ← FeatureSlot.map_unbotD_unifyWith (u := Agreement.Dimension.Slot.unify d) hb,
    WithTop.map_map]
  exact congrArg (WithTop.map · _) (funext fun s' ↦ agreement_update_agr b d s')

variable (t)

/-- The bundle `probe` valued from `goal` at `t`: unified with what `goal` holds at `t`, so
unchanged if `goal` lacks the dimension or bears it unvalued. -/
def valueFrom : WithTop FeatureBundle := probe.unifyAt t ((goal t).unbotD ⊥)

variable {probe goal t}

theorem le_of_valueFrom_eq_coe {probe' : FeatureBundle}
    (h : probe.valueFrom goal t = ↑probe') : probe ≤ probe' :=
  le_of_unifyAt_eq_coe h

theorem le_untopD_valueFrom : probe ≤ (probe.valueFrom goal t).untopD probe := by
  cases h : probe.valueFrom goal t with
  | top => exact le_rfl
  | coe b => exact le_of_valueFrom_eq_coe h

@[simp] theorem unifyAt_bot (b : FeatureBundle) (t : FeatureType) : b.unifyAt t ⊥ = b := by
  rcases eq_or_ne (b t) ⊥ with hb | hb
  · rw [unifyAt, hb, FeatureSlot.unifyWith_bot, WithTop.map_coe, ← hb, Function.update_eq_self]
  · refine (unifyAt_eq_coe_iff hb).2 (isLUB_pair_iff_forall_le.2 ⟨le_rfl, ?_, fun _ h _ ↦ h⟩)
    obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.1 hb
    exact update_le_iff.2 ⟨hy ▸ WithBot.coe_le_coe.2 bot_le, fun _ _ ↦ bot_le⟩

/-- A bundle that bears a dimension unvalued takes the slot it is unified with there. -/
theorem unifyAt_of_eq_coe_bot (h : b t = ↑(⊥ : t.Slot)) :
    b.unifyAt t x = ↑(Function.update b t ↑x) := by
  have hb : b t ≠ ⊥ := h ▸ WithBot.coe_ne_bot
  refine (unifyAt_eq_coe_iff hb).2 (isLUB_pair_update_bot_iff.2 ⟨?_, by simp⟩)
  rw [h, Function.update_self]
  exact isLUB_pair_iff_forall_le.2 ⟨WithBot.coe_le_coe.2 bot_le, le_rfl, fun _ _ h ↦ h⟩

theorem valueFrom_of_unbotD_eq_bot (h : (goal t).unbotD ⊥ = ⊥) :
    probe.valueFrom goal t = probe := by
  rw [valueFrom, h, unifyAt_bot]

@[simp] theorem valueFrom_bot (probe : FeatureBundle) (t : FeatureType) :
    probe.valueFrom ⊥ t = probe :=
  valueFrom_of_unbotD_eq_bot rfl

end FeatureBundle

/-! ### Agree between items -/

/-- The feature bundles of the items of a derivation. -/
abbrev FeatureState (H : Type*) := H → FeatureBundle

namespace FeatureState

variable {H : Type*} (s : FeatureState H) (α : H) (t : FeatureType)

/-- The goal `g` matches the probe `α` at `t`. An unvalued probe matches a goal that bears `t`,
whether valued or not. A valued probe, such as a case assigner, matches a goal that bears `t`
unvalued ([amato-2025]). -/
def Matches (g : H) : Prop :=
  s α t ≠ ⊥ ∧ if (s α t).unbotD ⊥ = ⊥ then s g t ≠ ⊥ else s g t = ↑(⊥ : t.Slot)

instance : DecidablePred (s.Matches α t) := fun g ↦ by
  unfold Matches; infer_instance

/-- The probe of `α` at `t`, satisfied by the goals that match it and interacting with the matching
goals that are also active. -/
def probe (active : H → Prop) [DecidablePred active] : Probe H :=
  ⟨fun g ↦ s.Matches α t g ∧ active g, s.Matches α t⟩

section Agree

variable [DecidableEq H]

/-- The valuation of `α` and `g` at `t`, the copying of Agree between them: each is valued with the
value of the other at `t`, and a bundle whose value differs from the other's is unchanged. -/
def value (g : H) : FeatureState H :=
  Function.update (Function.update s α (((s α).valueFrom (s g) t).untopD (s α))) g
    (((s g).valueFrom (s α) t).untopD (s g))

theorem le_value (g : H) : s ≤ s.value α t g := by
  intro h
  rcases eq_or_ne h g with rfl | hg
  · simpa [value] using FeatureBundle.le_untopD_valueFrom
  · rcases eq_or_ne h α with rfl | hα
    · simpa [value, hg] using FeatureBundle.le_untopD_valueFrom
    · simp [value, hg, hα]

theorem le_agree_state (active : H → Prop) [DecidablePred active] (goals : List H) :
    s ≤ ((s.probe α t active).agree (fun g s ↦ s.value α t g) s goals).state :=
  Probe.le_agree_state fun g s ↦ s.le_value α t g

end Agree

variable {s} {s' : FeatureState H}

/-- A slot that holds a maximal element of its order, as a value of a flat slot is, keeps it. -/
theorem apply_eq_coe_of_le (h : s ≤ s') {x : H} {u : FeatureType} {y : u.Slot} (hy : IsMax y)
    (hv : s x u = ↑y) : s' x u = ↑y := by
  have hle := hv ▸ h x u
  obtain ⟨z, hz, hyz⟩ := WithBot.coe_le_iff.1 hle
  rw [hz, hy.eq_of_le hyz]

end FeatureState

end Minimalist
