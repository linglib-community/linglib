module

public import Linglib.Morphology.Exponence.Containment.Defs
public import Linglib.Morphology.Exponence.Decomposition
public import Linglib.Morphology.Exponence.Select
public import Linglib.Morphology.Paradigm.Basic
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Containment hierarchies: Elsewhere insertion and Superset spellout

This file defines the realization of a rule set over a containment hierarchy under each
reading as the shared core's score selection. Elsewhere insertion selects the applicable rule of
greatest threshold, the most specific; Superset spellout selects the matching entry of least
span, Minimize Junk. Both realize Elsewhere winners. Elsewhere insertion is the chain instance of
feature-decomposition exponence, reading a rule as the initial segment of grades up to its
threshold.

## Main definitions

* `realize`: Elsewhere insertion.
* `spellout`: Superset spellout.
* `SpanRule.toDecomposition`: a rule as a feature-decomposition rule over initial segments.

## Main results

* `realize_realizes`, `spellout_realizes`: both realize the exponent of an Elsewhere winner.
* `realize_eq_of_threshold_le`: the rule selected at a grade is realized at every lower grade it
  applies at.
* `spellout_eq_none_of_le`: spellout gaps propagate upward.
* `spellout_eq_some_of_filter_of_le`: the loss of entries extends a form downward only.
* `pattern_toDecomposition`: Elsewhere insertion is decomposition exponence over the chain.

## References

* [bobaljik-2012]
* [bubnov-2026]
* [caha-2009]
* [dekier-2021]
* [halle-1997]
-/

@[expose] public section

namespace Morphology.Containment

open Exponence

variable {n : ℕ} {F : Type*} {g g' : Fin n} {φ : F}

/-! ### Elsewhere insertion -/

/-- Elsewhere insertion realizes at each grade the exponent of the applicable rule of greatest
threshold, the most specific, the first listed on ties, and `none` where no rule applies. -/
abbrev realize (v : RuleSet (SpanRule n F)) : Paradigm n (Option F) :=
  v.realize SpanRule.threshold

section Realize

variable {v : RuleSet (SpanRule n F)} {it : SpanRule n F}

theorem realize_realizes (h : realize v g = some φ) : v.Realizes applySet g φ :=
  RuleSet.realize_realizes (fun _ _ _ _ h ↦ SpanRule.applySet_ssubset_iff.1 h) h

/-- The rule selected at a grade is realized at every lower grade its threshold reaches, so
Elsewhere insertion plateaus between thresholds. -/
theorem realize_eq_of_threshold_le (h : v.selectBy SpanRule.threshold g' = some it)
    (hit : it.threshold ≤ g) (hg : g ≤ g') : realize v g = realize v g' :=
  congrArg (Option.map _) <|
    (RuleSet.selectBy_eq_some_of_applies (fun _ _ hs ↦ le_trans hs hg) h hit).trans h.symm

end Realize

/-! ### Superset spellout -/

/-- Superset spellout realizes at each grade the exponent of the matching entry storing the least
structure, the first listed on ties, and `none` where no entry matches. -/
abbrev spellout (v : RuleSet (SupersetRule n F)) : Paradigm n (Option F) :=
  v.realize (fun e : SupersetRule n F ↦ OrderDual.toDual e.spans)

section Spellout

variable {v : RuleSet (SupersetRule n F)} {e : SupersetRule n F}

theorem spellout_realizes (h : spellout v g = some φ) : v.Realizes applySet g φ :=
  RuleSet.realize_realizes (f := fun e : SupersetRule n F ↦ OrderDual.toDual e.spans)
    (fun _ _ _ _ h ↦ OrderDual.toDual_lt_toDual.2 (SupersetRule.applySet_ssubset_iff.1 h)) h

/-- Spellout gaps propagate upward, since an entry matching a higher grade matches the lower one
too, [dekier-2021]'s paradigm-gap monotonicity for indefinites. -/
theorem spellout_eq_none_of_le (h : spellout v g = none) (hg : g ≤ g') : spellout v g' = none :=
  Option.map_eq_none_iff.mpr <| RuleSet.selectBy_eq_none_of_applies
    (fun _ _ hs ↦ le_trans hg hs) (Option.map_eq_none_iff.mp h)

/-- The entry selected at a grade is selected at every higher grade its constituent contains, so
Superset spellout plateaus up to the stored grade. -/
theorem spellout_eq_of_le_spans (h : v.selectBy (fun e ↦ OrderDual.toDual e.spans) g = some e)
    (hg : g ≤ g') (he : g' ≤ e.spans) : spellout v g' = spellout v g :=
  congrArg (Option.map _) <|
    (RuleSet.selectBy_eq_some_of_applies (fun _ _ hs ↦ le_trans hg hs) h he).trans h.symm

/-- The loss of entries extends a form downward only. If an antihomophonous lexicon spells out a
form at a grade and, after losing entries, still spells it out at a higher grade, it spelled it
out there before ([bubnov-2026]). -/
theorem spellout_eq_some_of_filter_of_le (hv : v.Antihomophonous) {p : SupersetRule n F → Bool}
    (h : spellout v g = some φ) (h' : spellout (v.filter p) g' = some φ) (hg : g ≤ g') :
    spellout v g' = some φ := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨e', he', hφ⟩ := Option.map_eq_some_iff.mp h'
  obtain rfl := hv (List.mem_filter.mp (RuleSet.selectBy_mem he')).1 (RuleSet.selectBy_mem he) hφ
  rw [spellout_eq_of_le_spans he hg (RuleSet.selectBy_applies he'), h]

end Spellout

/-! ### The chain decomposition

Feature-decomposition exponence (`Exponence/Decomposition.lean`) over the decomposition of each
grade into the initial segment below it: a rule specified for the grades up to its threshold
applies where its threshold does, and feature counting maximizes the threshold. -/

/-- A rule as a feature-decomposition rule specified for the grades up to its threshold. -/
def SpanRule.toDecomposition (it : SpanRule n F) : Decomposition.Rule (Fin n) Finset.Iic F :=
  ⟨Finset.Iic it.threshold, it.exponent⟩

/-- Elsewhere insertion is feature-decomposition exponence over the chain of initial segments. -/
theorem pattern_toDecomposition (v : RuleSet (SpanRule n F)) :
    Decomposition.pattern (v.map SpanRule.toDecomposition) = realize v := by
  funext g
  rw [Decomposition.pattern, RuleSet.selectBy_map (c := g) (f := SpanRule.threshold)
    (fun _ _ ↦ Finset.Iic_subset_Iic) fun _ _ _ _ ↦ by
      simp [SpanRule.toDecomposition, Fin.card_Iic], Option.map_map]
  rfl

end Morphology.Containment
