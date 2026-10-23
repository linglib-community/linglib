module

public import Linglib.Syntax.Minimalist.Feature.Basic

/-!
# Valuation

Agree's effect on feature bundles: valuation copies a goal's value into an unvalued probe slot,
only adding information, and is unification with the bundle carrying only the value. What search
delivers the goal is `Minimalist.LinearizedSyntacticObject.goals`.

## Main definitions

* `Minimalist.FeatureBundle.valueAt`, `Minimalist.FeatureBundle.applyAgree`: valuation of a
  dimension, `⊤` on a clash, and the probe's bundle valued from a goal's.

## Main results

* `Minimalist.FeatureBundle.valueAt_eq_unify`: valuation is unification with the value.

## References

* [chomsky-2000]
-/

@[expose] public section

namespace Minimalist.FeatureBundle

variable (probe goal : FeatureBundle) (t : FeatureType)

/-- The bundle `b` with dimension `t` valued by `v`, `⊤` when its value there clashes with `v`; a
dimension the bundle lacks stays absent. -/
def valueAt (b : FeatureBundle) (t : FeatureType) (v : t.ValueOf) : WithTop FeatureBundle :=
  ((b t).valueWith v).map (Function.update b t)

variable {t} {b b' : FeatureBundle} {v : t.ValueOf}

/-- Valuation only adds information. -/
theorem le_of_valueAt_eq_coe (h : b.valueAt t v = ↑b') : b ≤ b' := by
  obtain ⟨s, hs, rfl⟩ := WithTop.map_eq_some_iff.1 h
  exact le_update_self_iff.2 (FeatureSlot.le_of_valueWith_eq_coe hs)

/-- Where the bundle bears the dimension, valuation is unification with the bundle carrying only
the value: Agree adds the goal's value to the probe as unification does, failing on a clash. -/
theorem valueAt_eq_unify (hb : b t ≠ .absent) :
    b.valueAt t v = PartialUnify.unify b (single t v) := by
  cases h : (b t).valueWith v with
  | top =>
    rw [valueAt, h, WithTop.map_top, eq_comm, PartialUnify.unify_eq_top_iff]
    rintro ⟨u, hu⟩
    obtain ⟨hbu, hsu⟩ := mem_upperBounds_pair.1 hu
    refine (FeatureSlot.valueWith_eq_top_iff_not_bddAbove hb).1 h ⟨u t, ?_⟩
    exact mem_upperBounds_pair.2 ⟨hbu t, by simpa using hsu t⟩
  | coe s' =>
    have hl := FeatureSlot.isLUB_of_valueWith_eq_coe hb h
    rw [valueAt, h, WithTop.map_coe, eq_comm, PartialUnify.unify_eq_coe_iff_isLUB]
    refine ⟨mem_upperBounds_pair.2 ⟨le_update_self_iff.2 (FeatureSlot.le_of_valueWith_eq_coe h),
      fun u ↦ ?_⟩, fun w hw ↦ fun u ↦ ?_⟩
    · rcases eq_or_ne u t with rfl | hu
      · simpa using (mem_upperBounds_pair.1 hl.1).2
      · simpa [single, hu] using (bot_le : ⊥ ≤ b u)
    · obtain ⟨hbw, hsw⟩ := mem_upperBounds_pair.1 hw
      rcases eq_or_ne u t with rfl | hu
      · simpa using hl.2 (mem_upperBounds_pair.2 ⟨hbw u, by simpa using hsw u⟩)
      · simpa [hu] using hbw u

variable (t)

/-- The probe's bundle after Agree with the goal at dimension `t`: valued by the goal's value
there, `⊤` on a clash, and unchanged when the goal has no value to transmit, Agree failing without
penalty. -/
def applyAgree : WithTop FeatureBundle :=
  (goal.getValuedFeature t).elim ↑probe (probe.valueAt t)

@[simp] theorem applyAgree_bot : probe.applyAgree ⊥ t = probe := rfl

variable {probe goal t}

theorem applyAgree_of_not_hasValuedFeature (h : ¬ goal.hasValuedFeature t) :
    probe.applyAgree goal t = probe := by
  cases hg : goal t <;> simp_all [applyAgree, getValuedFeature, hasValuedFeature,
    FeatureSlot.value?, FeatureSlot.isValued]

/-- A probe valued by Agree only gains information. -/
theorem le_of_applyAgree_eq_coe {probe' : FeatureBundle}
    (h : probe.applyAgree goal t = ↑probe') : probe ≤ probe' := by
  cases hg : goal.getValuedFeature t with
  | none => simp [applyAgree, hg] at h; exact h ▸ le_rfl
  | some v => exact le_of_valueAt_eq_coe (by simpa [applyAgree, hg] using h)

end Minimalist.FeatureBundle
