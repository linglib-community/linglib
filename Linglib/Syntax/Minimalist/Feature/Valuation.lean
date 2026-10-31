module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Minimalist.Probe.Agree

/-!
# Valuation

This file defines valuation of feature bundles, the part of Agree that copies the value of a goal
into a probe ([chomsky-2000]), from the valuation of a single slot (`FeatureSlot.valueWith`). An
absent slot is unchanged, since an item that lacks a dimension is not a probe for it.

Valuing a bundle at a dimension it bears is [unification with the bundle that bears only the
value](##Minimalist.FeatureBundle.valueAt_eq_unify). At an agreement dimension, valuation
followed by `FeatureBundle.agreement` is [unification of agreement
bundles](##Minimalist.FeatureBundle.map_agreement_valueAt). Agree with a goal that has no value at
the dimension leaves the probe unchanged, so Agree can fail without causing a crash
([preminger-2014]). The goal a probe agrees with is found by search
(`Minimalist.LinearizedSyntacticObject.goals`).

The items of a derivation carry their bundles in a `FeatureState`, and Agree over it is the one
Agree of `Probe/Agree.lean`, `Probe.agree`, with the probe of an item at a dimension and valuation
as its copying. Valuation values the probe and the goal each with the value of the other at the
dimension, so a valued probe, such as a case assigner, values an unvalued goal. A goal matches a
probe when it bears the dimension, since matching is identity of the dimension and not of the
value ([chomsky-2000]). The probe of an item at a dimension is satisfied by the goals that match
it and interacts with those that are also active. A matching goal that is not active therefore
halts the search without valuing: Chomsky's defective intervention is satisfaction without
interaction in the sense of [deal-2025a]. Valuation only adds features, so [a run of Agree
extends the state](##Minimalist.FeatureState.le_agree_state), and [a slot valued before Agree
keeps its value](##Minimalist.FeatureState.apply_eq_valued_of_le).

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

/-- The bundle `probe` valued from `goal` at `t`: valued with the value of `goal` at `t`, or
unchanged if `goal` has no value there. -/
def valueFrom : WithTop FeatureBundle :=
  match goal t with
  | .valued v => probe.valueAt t v
  | _ => probe

@[simp] theorem valueFrom_bot : probe.valueFrom ⊥ t = probe := rfl

variable {probe goal t}

theorem valueFrom_of_forall_ne_valued (h : ∀ v, goal t ≠ .valued v) :
    probe.valueFrom goal t = probe := by
  unfold valueFrom
  split
  · exact absurd ‹_› (h _)
  · rfl

theorem le_of_valueFrom_eq_coe {probe' : FeatureBundle}
    (h : probe.valueFrom goal t = ↑probe') : probe ≤ probe' := by
  unfold valueFrom at h
  split at h
  · exact le_of_valueAt_eq_coe h
  · exact (WithTop.coe_inj.1 h).le

theorem le_untopD_valueFrom : probe ≤ (probe.valueFrom goal t).untopD probe := by
  cases h : probe.valueFrom goal t with
  | top => exact le_rfl
  | coe b => exact le_of_valueFrom_eq_coe h

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

theorem apply_eq_valued_of_le (h : s ≤ s') {x : H} {u : FeatureType} {v : u.Value}
    (hv : s x u = .valued v) : s' x u = .valued v :=
  FeatureSlot.valued_le_iff.1 (hv ▸ h x u)

end FeatureState

end Minimalist
