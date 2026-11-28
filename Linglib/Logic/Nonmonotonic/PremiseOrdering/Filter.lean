module

public import Linglib.Core.Order.Filter.AtBotOn
public import Linglib.Logic.Nonmonotonic.PremiseOrdering.Defs

/-!
# The bottom filter of the ordering a family of sets induces

Ranked by the members of a family that a point lies in, the filter of what holds toward the
bottom of a domain can be stated without points: the subfamilies with a common point of the domain
stand in for the points, and inclusion among them for the order.

## Main results

* `Filter.atBotOn_ofLowerSets`: the ordering of a family is the ranking by the members containing a
  point.
* `Filter.mem_atBotOn_satisfied_iff`: the bottom filter in terms of jointly satisfied criteria.

## References

* [kratzer-1981]
* [lewis-1981]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Preorder

variable {α : Type*} {a b : α}

private theorem sep_subset_sep_iff {C : Type*} {sat : α → C → Prop} {crit : Set C} :
    {c ∈ crit | sat b c} ⊆ {c ∈ crit | sat a c} ↔ ∀ c ∈ crit, sat b c → sat a c :=
  ⟨fun h _ hc hb ↦ (h ⟨hc, hb⟩).2, fun h _ hc ↦ ⟨hc.1, h _ hc.1 hc.2⟩⟩

end Preorder

namespace Filter

variable {W : Type*} {s t : Set W}

/-! ### Premise semantics

Ranked by the criteria a point satisfies, more being better, the filter can be stated without
points: the sets of criteria satisfied together at some point of the domain stand in for the
points, and inclusion among them for the order. -/

/-- The ordering of a family of sets is the ranking by the members containing a point. -/
theorem atBotOn_ofLowerSets (A : Set (Set W)) (s : Set W) :
    atBotOn[Preorder.ofLowerSets A] s =
      atBotOn (OrderDual.toDual ∘ (fun w ↦ {p ∈ A | w ∈ p})) s := by
  ext t
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    ← Preorder.ofLowerSets_le_iff_subset A, id]

/-- Ranked by the criteria satisfied, `t` holds toward the bottom of `s` exactly when every set of
criteria satisfied together at some point of `s` extends, within the criteria, to a set satisfied
together at some point of `s` and only at points of `t`. -/
theorem mem_atBotOn_satisfied_iff {C : Type*} {sat : W → C → Prop} {crit : Set C} :
    t ∈ atBotOn (OrderDual.toDual ∘ (fun w ↦ {c ∈ crit | sat w c})) s ↔
      ∀ B ⊆ crit, (∃ u ∈ s, ∀ c ∈ B, sat u c) → ∃ D ⊆ crit, (∃ v ∈ s, ∀ c ∈ D, sat v c) ∧
        B ⊆ D ∧ ∀ w ∈ s, (∀ c ∈ D, sat w c) → w ∈ t := by
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    Preorder.sep_subset_sep_iff]
  refine ⟨fun h B hB ⟨u, hu, huB⟩ ↦ ?_, fun h u hu ↦ ?_⟩
  · obtain ⟨v, hv, hvu, hvt⟩ := h u hu
    exact ⟨(fun w ↦ {c ∈ crit | sat w c}) v, Set.sep_subset _ _, ⟨v, hv, fun _ hc ↦ hc.2⟩,
      fun c hc ↦ ⟨hB hc, hvu c (hB hc) (huB c hc)⟩,
      fun w hw hwD ↦ hvt w hw fun c hc hvc ↦ hwD c ⟨hc, hvc⟩⟩
  · obtain ⟨D, hD, ⟨v, hv, hvD⟩, hBD, hDt⟩ :=
      h ((fun w ↦ {c ∈ crit | sat w c}) u) (Set.sep_subset _ _) ⟨u, hu, fun _ hc ↦ hc.2⟩
    exact ⟨v, hv, fun c hc huc ↦ hvD c (hBD ⟨hc, huc⟩),
      fun w hw hwv ↦ hDt w hw fun c hc ↦ hwv c (hD hc) (hvD c hc)⟩

end Filter
