module

public import Mathlib.Algebra.Order.Ring.Rat
public import Studies.DaleReiter1995

/-!
# Westerbeek, Koolen & Maes (2015): Stored Object Knowledge and the Production of Referring Expressions

This file formalizes the computational claim of [westerbeek-koolen-maes-2015]. In two
production experiments, speakers referring to an object whose type alone distinguishes it from
the distractors mention its color more often the less typical that color is for the object,
and more so for objects whose shape is less diagnostic, which the paper attributes to a
contrast with the color stored with the object's category. The paper argues that models of
content determination without object knowledge cannot capture this: [dale-reiter-1995]'s
Incremental Algorithm, which considers attributes in a fixed preference order and keeps one
only when it rules out a remaining distractor, produces the bare head noun whenever the type
distinguishes the referent, whatever the colors in the scene
(`flat_makeReferringExpression_type`), so its output for a yellow and a red tomato is the same
(`makeReferringExpression_congr_type`) and its color-mention rate cannot vary with typicality
(`decision_rule_not_ia`).

## Implementation notes

The scenes are the flat domains of the Incremental Algorithm's user model, in which the user
knows a property exactly when the scene has it. The paper's decision rule, that the
probability of mentioning a property rises with its contrast to stored knowledge, is a
strictly decreasing rate in the typicality score; the experiments' rates and regression
coefficients are reported in the paper and not formalized.

## References

* [westerbeek-koolen-maes-2015]
* [dale-reiter-1995]
* [frank-goodman-2012]
-/

@[expose] public section

namespace WesterbeekKoolenMaes2015

open DaleReiter1995 DaleReiter1995.Domain

/-! ### The Incremental Algorithm on a type-distinguished referent -/

section IA

variable {E A V : Type*} [DecidableEq E] [DecidableEq A] [DecidableEq V]

/-- When the referent's type rules out every distractor and type heads the preference order,
the Incremental Algorithm returns the bare head noun, whatever the other attributes hold. -/
theorem flat_makeReferringExpression_type (kb : KB E A V) (t : A) (r : E) (C : Finset E)
    (rest : List A) {v : V} (hr : kb r t = some v)
    (hC : ∀ c ∈ C, ∃ w, kb c t = some w ∧ w ≠ v) :
    (flat kb t).makeReferringExpression r C (t :: rest) = some {(t, v)} := by
  have hbest : (flat kb t).findBestValue r C t 0 v = some v := by
    simp [findBestValue, flat, hr]
  have hrule : (flat kb t).rulesOut C t v = C :=
    Finset.filter_true_of_mem λ c hc => by
      obtain ⟨w, hw, hwv⟩ := hC c hc
      simp [flat, hw, hwv]
  have hstep : (flat kb t).step r t C ∅ =
      if C.Nonempty then (∅, {(t, v)}) else (C, ∅) := by
    simp only [step]
    rw [show (flat kb t).basicLevel r t = kb r t from rfl, hr,
      show (flat kb t).depth = 0 from rfl]
    simp [hbest, hrule]
  have htype : (flat kb t).withType r {(t, v)} = {(t, v)} := by
    simp [withType, show (flat kb t).type = t from rfl]
  have htype' : (flat kb t).withType r ∅ = {(t, v)} := by
    simp [withType, flat, hr]
  unfold makeReferringExpression loop
  rw [hstep]
  by_cases hCne : C.Nonempty
  · simp [hCne, htype]
  · simp [htype', Finset.not_nonempty_iff_eq_empty.mp hCne]

theorem makeReferringExpression_congr_type (kb₁ kb₂ : KB E A V) (t : A) (r : E) (C : Finset E)
    (rest : List A) (h : ∀ x, kb₁ x t = kb₂ x t) {v : V} (hr : kb₁ r t = some v)
    (hC : ∀ c ∈ C, ∃ w, kb₁ c t = some w ∧ w ≠ v) :
    (flat kb₁ t).makeReferringExpression r C (t :: rest) =
      (flat kb₂ t).makeReferringExpression r C (t :: rest) := by
  rw [flat_makeReferringExpression_type kb₁ t r C rest hr hC,
    flat_makeReferringExpression_type kb₂ t r C rest (h r ▸ hr)
      λ c hc => (hC c hc).imp λ w hw => ⟨h c ▸ hw.1, hw.2⟩]

end IA

/-! ### The scene of Figure 1 -/

/-- The objects of a scene: the tomato and the distractors of other types. -/
inductive Object
  | tomato | pineapple | cucumber
  deriving DecidableEq, Repr

/-- Types and colors. -/
inductive ObjectValue
  | tomato | pineapple | cucumber | red | yellow | green
  deriving DecidableEq, Repr

/-- The scene, with the tomato in a given color. -/
def scene (tomatoColor : ObjectValue) : KB Object Attr ObjectValue
  | .tomato, .type => some .tomato
  | .tomato, .property .color => some tomatoColor
  | .pineapple, .type => some .pineapple
  | .pineapple, .property .color => some .yellow
  | .cucumber, .type => some .cucumber
  | .cucumber, .property .color => some .green
  | _, _ => none

theorem tomato_bare (tomatoColor : ObjectValue) :
    (flat (scene tomatoColor) .type).makeReferringExpression .tomato {.pineapple, .cucumber}
        [.type, .property .color] = some {(.type, .tomato)} :=
  flat_makeReferringExpression_type _ _ _ _ _ rfl λ c hc => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl <;> exact ⟨_, rfl, by decide⟩

/-! ### The decision rule -/

/-- The paper's decision rule: the rate of mentioning a color falls strictly with the color's
typicality score for the object. -/
def DecisionRule (rate : ℚ → ℚ) : Prop := StrictAnti rate

theorem decision_rule_not_ia (c : ℚ) : ¬ DecisionRule λ _ => c :=
  λ h => lt_irrefl c (h zero_lt_one)

end WesterbeekKoolenMaes2015
