module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Minimalist.Probe.Agree

/-!
# Valuation

This file defines valuation, the part of Agree that copies the value of a goal into a probe
([chomsky-2000]). Valuing a slot with `v` unifies it with `valued v`. An unvalued slot becomes
`valued v`, a slot valued `v` is unchanged, and a slot valued `w ≠ v` fails, which is `⊤`. An absent
slot is unchanged, since an item that lacks a dimension is not a probe for it.

Valuing a bundle at a dimension it bears is
[unification with the bundle that bears only the value](##Minimalist.FeatureBundle.valueAt_eq_unify).
At an agreement dimension, valuation followed by `FeatureBundle.agreement` is
[unification of agreement bundles](##Minimalist.FeatureBundle.map_agreement_valueAt).
Agree with a goal that has no value at the dimension leaves the probe unchanged, so Agree can fail
without causing a crash ([preminger-2014]). The goal a probe agrees with is found by search
(`Minimalist.LinearizedSyntacticObject.goals`).

The items of a derivation carry their bundles in a `FeatureState`. Agree between a probe and a goal
at a dimension values each with the value of the other there, so a valued probe, such as a case
assigner, values an unvalued goal. A goal matches a probe when it bears the dimension, since
matching is identity of the dimension and not of the value ([chomsky-2000]). The probe of an item
at a dimension is satisfied by the goals that match it and interacts with those that are also
active. A matching goal that is not active therefore halts the search without valuing: Chomsky's
defective intervention is satisfaction without interaction in the sense of [deal-2025a].
Valuation only adds features, so [a run of Agree extends the state](##Minimalist.FeatureState.le_agree_state),
and [a slot valued before Agree keeps its value](##Minimalist.FeatureState.apply_eq_valued_of_le).

## Main definitions

* `Minimalist.FeatureSlot.valueWith`: a slot valued with `v`.
* `Minimalist.FeatureBundle.valueAt`: a bundle valued with `v` at a dimension.
* `Minimalist.FeatureBundle.applyAgree`: a probe valued from a goal.
* `Minimalist.FeatureState`: the feature bundles of the items of a derivation.
* `Minimalist.FeatureState.Matches`: a goal matches a probe at a dimension.
* `Minimalist.FeatureState.probe`: the probe of an item at a dimension.
* `Minimalist.FeatureState.agree`: Agree between two items at a dimension.

## References

* [chomsky-2000]
* [deal-2025a]
* [preminger-2014]
* [amato-2025]
-/

@[expose] public section

namespace Minimalist

namespace FeatureSlot

variable {α : Type*} [DecidableEq α] {v w : α} {s s' : FeatureSlot α}

/-- The slot `s` valued with `v`, or `⊤` if `s` is valued otherwise. An absent slot is
unchanged. -/
def valueWith (v : α) (s : FeatureSlot α) : WithTop (FeatureSlot α) :=
  if s = absent then s else PartialUnify.unify s (valued v)

theorem valueWith_of_ne_absent (hs : s ≠ absent) :
    valueWith v s = PartialUnify.unify s (valued v) := by
  simp [valueWith, hs]

@[simp] theorem valueWith_absent (v : α) :
    valueWith v (absent : FeatureSlot α) = ↑(absent : FeatureSlot α) := by
  simp [valueWith]

@[simp] theorem valueWith_unvalued (v : α) :
    valueWith v (unvalued : FeatureSlot α) = valued v := by
  rw [valueWith_of_ne_absent unvalued_ne_absent]
  exact PartialUnify.unify_eq_right.2 (WithBot.coe_le_coe.2 bot_le)

@[simp] theorem valueWith_valued (v w : α) :
    valueWith v (valued w) = if w = v then ↑(valued w : FeatureSlot α) else ⊤ := by
  rw [valueWith_of_ne_absent (valued_ne_absent w)]
  split_ifs with h
  · exact h ▸ PartialUnify.unify_self _
  · simp [PartialUnify.unify_coe_coe,
      show PartialUnify.unify (w : Flat α) v = ⊤ from Flat.unify_eq_top_of_ne h]

theorem valueWith_eq_top_iff : valueWith v s = ⊤ ↔ ∃ w, w ≠ v ∧ s = valued w := by
  cases s with
  | absent => simp
  | unvalued => simp
  | valued w => by_cases h : w = v <;> simp [h]

theorem le_of_valueWith_eq_coe (h : valueWith v s = s') : s ≤ s' := by
  rcases eq_or_ne s absent with rfl | hs
  · exact bot_le
  · rw [valueWith_of_ne_absent hs, PartialUnify.unify_eq_coe_iff_isLUB] at h
    exact (mem_upperBounds_pair.1 h.1).1

theorem valueWith_mono (v : α) :
    Monotone (valueWith v : FeatureSlot α → WithTop (FeatureSlot α)) := by
  intro s s' h
  cases s with
  | absent => exact valueWith_absent v ▸ WithTop.coe_bot (α := FeatureSlot α) ▸ bot_le
  | unvalued =>
    cases s' with
    | absent => exact absurd h (WithBot.not_coe_le_bot _)
    | unvalued => exact le_rfl
    | valued w => by_cases hw : w = v <;> simp [hw]
  | valued u =>
    cases s' with
    | absent => exact absurd h (WithBot.not_coe_le_bot _)
    | unvalued => exact absurd (Flat.coe_le_iff.1 (WithBot.coe_le_coe.1 h)) (by simp)
    | valued w => obtain rfl : u = w := Flat.coe_le_coe.1 (WithBot.coe_le_coe.1 h); exact le_rfl

theorem map_toFlat_valueWith (hs : s ≠ absent) :
    (valueWith v s).map toFlat = PartialUnify.unify s.toFlat (v : Flat α) := by
  cases s with
  | absent => exact absurd rfl hs
  | unvalued =>
    rw [valueWith_unvalued, WithTop.map_coe, toFlat_valued, toFlat_unvalued, eq_comm]
    exact PartialUnify.unify_eq_right.2 bot_le
  | valued w =>
    rcases eq_or_ne w v with rfl | hwv
    · simp
    · rw [valueWith_eq_top_iff.2 ⟨w, hwv, rfl⟩, WithTop.map_top, toFlat_valued]
      exact (Flat.unify_eq_top_of_ne hwv).symm

end FeatureSlot

namespace FeatureBundle

variable (probe goal : FeatureBundle) (t : FeatureType)

/-- The bundle `b` valued with `v` at `t`, or `⊤` if `b` is valued otherwise at `t`. -/
def valueAt (b : FeatureBundle) (t : FeatureType) (v : t.Value) : WithTop FeatureBundle :=
  ((b t).valueWith v).map (Function.update b t)

variable {t} {b b' : FeatureBundle} {v : t.Value}

theorem le_of_valueAt_eq_coe (h : b.valueAt t v = ↑b') : b ≤ b' := by
  obtain ⟨s, hs, rfl⟩ := WithTop.map_eq_some_iff.1 h
  exact le_update_self_iff.2 (FeatureSlot.le_of_valueWith_eq_coe hs)

theorem valueAt_eq_unify (hb : b t ≠ .absent) :
    b.valueAt t v = PartialUnify.unify b (single t v) := by
  rw [valueAt, FeatureSlot.valueWith_of_ne_absent hb, single, PartialUnify.unify_update_bot]

theorem map_agreement_valueAt {d : Agreement.Dimension} {v : d.Value} {b : FeatureBundle}
    (hb : b (.agr d) ≠ .absent) :
    (b.valueAt (.agr d) v).map agreement = PartialUnify.unify b.agreement (.set d v ⊥) := by
  rw [show (Agreement.Bundle.set d v ⊥) = Function.update (⊥ : Agreement.Bundle) d ↑v from rfl,
    PartialUnify.unify_update_bot, agreement_apply,
    ← FeatureSlot.map_toFlat_valueWith (v := v) hb, valueAt]
  induction (b (.agr d)).valueWith v using WithTop.recTopCoe with
  | top => rfl
  | coe s' =>
    simp only [WithTop.map_coe]
    exact congrArg _ (agreement_update_agr b d s')

variable (t)

/-- The probe after Agree with the goal at `t`: valued with the value of the goal at `t`, or
unchanged if the goal has no value there. -/
def applyAgree : WithTop FeatureBundle :=
  match goal t with
  | .valued v => probe.valueAt t v
  | _ => probe

@[simp] theorem applyAgree_bot : probe.applyAgree ⊥ t = probe := rfl

variable {probe goal t}

theorem applyAgree_of_forall_ne_valued (h : ∀ v, goal t ≠ .valued v) :
    probe.applyAgree goal t = probe := by
  unfold applyAgree
  split
  · exact absurd ‹_› (h _)
  · rfl

theorem le_of_applyAgree_eq_coe {probe' : FeatureBundle}
    (h : probe.applyAgree goal t = ↑probe') : probe ≤ probe' := by
  unfold applyAgree at h
  split at h
  · exact le_of_valueAt_eq_coe h
  · exact (WithTop.coe_inj.1 h).le

theorem le_untopD_applyAgree : probe ≤ (probe.applyAgree goal t).untopD probe := by
  cases h : probe.applyAgree goal t with
  | top => exact le_rfl
  | coe b => exact le_of_applyAgree_eq_coe h

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
  match s α t with
  | .unvalued => s g t ≠ .absent
  | .valued _ => s g t = .unvalued
  | .absent => False

instance : DecidablePred (s.Matches α t) := fun g ↦ by
  unfold Matches; split <;> infer_instance

/-- The probe of `α` at `t`, satisfied by the goals that match it and interacting with the matching
goals that are also active. -/
def probe (active : H → Prop) [DecidablePred active] : Probe H :=
  ⟨fun g ↦ s.Matches α t g ∧ active g, s.Matches α t⟩

section Agree

variable [DecidableEq H]

/-- Agree between `α` and `g` at `t`, in which each is valued with the value of the other at `t`.
A bundle whose value differs from the other's is unchanged. -/
def agree (g : H) : FeatureState H :=
  Function.update (Function.update s α (((s α).applyAgree (s g) t).untopD (s α))) g
    (((s g).applyAgree (s α) t).untopD (s g))

theorem le_agree (g : H) : s ≤ s.agree α t g := by
  intro h
  rcases eq_or_ne h g with rfl | hg
  · simpa [agree] using FeatureBundle.le_untopD_applyAgree
  · rcases eq_or_ne h α with rfl | hα
    · simpa [agree, hg] using FeatureBundle.le_untopD_applyAgree
    · simp [agree, hg, hα]

theorem le_agree_state (active : H → Prop) [DecidablePred active] (goals : List H) :
    s ≤ ((s.probe α t active).agree (fun g s ↦ s.agree α t g) s goals).state :=
  Probe.le_agree_state fun g s ↦ s.le_agree α t g

end Agree

variable {s} {s' : FeatureState H}

theorem apply_eq_valued_of_le (h : s ≤ s') {x : H} {u : FeatureType} {v : u.Value}
    (hv : s x u = .valued v) : s' x u = .valued v :=
  FeatureSlot.valued_le_iff.1 (hv ▸ h x u)

end FeatureState

end Minimalist
