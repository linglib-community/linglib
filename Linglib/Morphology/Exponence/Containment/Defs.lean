module

public import Linglib.Morphology.Exponence.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Rule sets over containment hierarchies

The rules of the two realizational engines over an `n`-grade containment hierarchy, where grade
`g`'s structure contains every lower grade's. A `SpanRule` is a Distributed Morphology rule of
exponence realizing the initial span `[0, spans]`, optionally conditioned on a higher head; it
applies, by the Subset Principle, at every grade containing all it mentions, the up-set of its
`threshold`. A `SupersetRule` is a nanosyntax lexical entry storing the constituent `[0, spans]`;
it applies, by the Superset Principle, at every grade its constituent contains, the down-set of
`spans`. Specificity is threshold comparison for the first and span comparison for the second,
in opposite directions.

## Main definitions

* `SpanRule`, `SpanRule.threshold`: a rule of exponence and the least grade it applies at.
* `SupersetRule`: a lexical entry storing an initial span.
* `Terminal`, `Adjacent`, `Markedness`, `Grounded`: well-formedness conditions on rule sets of
  span rules.

## Main results

* `SpanRule.applySet_subset_iff`: a rule is more specific than another iff its threshold is
  higher.
* `SupersetRule.applySet_subset_iff`: an entry is more specific than another iff its span is
  smaller, the nanosyntax principle Minimize Junk.
* `markedness_iff_grounded`: under adjacency the markedness condition is the downward closure of
  thresholds.

## References

* [bobaljik-2012]
* [caha-2009]
* [kiparsky-1973]
* [starke-2009]
-/

@[expose] public section

namespace Morphology.Containment

open Morphology.Exponence

variable {n : ℕ} {F : Type*}

/-! ### The Subset reading: rules of exponence -/

/-- A rule of exponence ([bobaljik-2012]) over an `n`-grade containment hierarchy realizes the
initial span `[0, spans]`, the bare root when `spans = 0` and a portmanteau when `spans > 0`, and
applies only when its conditioning head `context`, if any, is present. In Latin `bon` is
`⟨bon, 0, none⟩`, `mel-` is `⟨mel, 0, some 1⟩` and the portmanteau `opt-` is `⟨opt, 1, some 2⟩`. -/
structure SpanRule (n : ℕ) (F : Type*) where
  /-- The exponent inserted for the span. -/
  exponent : F
  /-- The upper end of the exponed initial span `[0, spans]`. -/
  spans : Fin n
  /-- The head whose presence conditions the rule, if any. -/
  context : Option (Fin n)
  deriving DecidableEq, Repr

/-- The least grade at which the rule applies, the least containing both the exponed span and
the conditioning head. -/
def SpanRule.threshold (it : SpanRule n F) : Fin n :=
  max it.spans (it.context.getD it.spans)

/-- A rule applies at the grades from its threshold up. -/
instance : Rule (SpanRule n F) (Fin n) F :=
  ⟨SpanRule.exponent, fun it g ↦ it.threshold ≤ g⟩

instance : DecidableRel (Applies : SpanRule n F → Fin n → Prop) :=
  fun it g ↦ inferInstanceAs (Decidable (it.threshold ≤ g))

namespace SpanRule

variable {it jt : SpanRule n F} {g : Fin n}

@[simp] theorem applies_iff : Applies it g ↔ it.threshold ≤ g := Iff.rfl

@[simp] theorem exponent_eq : Rule.exponent it = it.exponent := rfl

/-- Over a linear hierarchy the applicability sets are nested, so specificity is the reverse of
threshold order and the Elsewhere ordering ([kiparsky-1973]) is total. -/
theorem applySet_subset_iff : applySet it ⊆ applySet jt ↔ jt.threshold ≤ it.threshold :=
  Set.Ici_subset_Ici

theorem applySet_ssubset_iff : applySet it ⊂ applySet jt ↔ jt.threshold < it.threshold :=
  Set.Ici_ssubset_Ici

end SpanRule

/-! ### Well-formedness conditions on rule sets

Each generalization hypothesizes exactly the conditions it needs, and rule sets violating a
condition witness the corresponding unattested pattern. -/

/-- Every rule expones the bare root, so the rule set has no portmanteaux. -/
def Terminal (v : RuleSet (SpanRule n F)) : Prop :=
  ∀ it ∈ v, (it.spans : ℕ) = 0

instance (v : RuleSet (SpanRule n F)) : Decidable (Terminal v) := by
  unfold Terminal; infer_instance

/-- Conditioning heads are adjacent to the exponed span, the adjacency condition on contextual
allomorphy that [bobaljik-2012] tentatively adopts. -/
def Adjacent (v : RuleSet (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ c : Fin n, it.context = some c → (c : ℕ) = (it.spans : ℕ) + 1

instance (v : RuleSet (SpanRule n F)) : Decidable (Adjacent v) := by
  unfold Adjacent; infer_instance

/-- [bobaljik-2012]'s markedness condition requires, for each context-sensitive rule involving a
node, a context-free rule involving that node. A rule involves the nodes `[0, k]` of its span,
context-sensitively below its threshold, and a context-free rule for `[0, k]` is one of
threshold `k`, so every threshold below a rule's and within its span is some rule's. -/
def Markedness (v : RuleSet (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ k : Fin n, k ≤ it.spans → k < it.threshold → ∃ jt ∈ v, jt.threshold = k

instance (v : RuleSet (SpanRule n F)) : Decidable (Markedness v) := by
  unfold Markedness; infer_instance

/-- A rule set is grounded when its thresholds are closed downward. This strengthens the
markedness condition to the thresholds between a rule's span and its context, which adjacency
leaves empty. -/
def Grounded (v : RuleSet (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ k : Fin n, k < it.threshold → ∃ jt ∈ v, jt.threshold = k

instance (v : RuleSet (SpanRule n F)) : Decidable (Grounded v) := by
  unfold Grounded; infer_instance

theorem Grounded.markedness {v : RuleSet (SpanRule n F)} (h : Grounded v) : Markedness v :=
  fun it hit k _ hk ↦ h it hit k hk

/-- Under adjacency the markedness condition is the downward closure of thresholds. -/
theorem markedness_iff_grounded {v : RuleSet (SpanRule n F)} (hA : Adjacent v) :
    Markedness v ↔ Grounded v := by
  refine ⟨fun hM it hit k hk ↦ hM it hit k ?_ hk, Grounded.markedness⟩
  rcases hc : it.context with - | c
  · rw [SpanRule.threshold, hc, Option.getD_none, max_self] at hk
    exact hk.le
  · rw [SpanRule.threshold, hc, Option.getD_some] at hk
    rcases lt_max_iff.mp hk with hk | hk
    · exact hk.le
    · have h := hA it hit c hc
      rw [Fin.lt_def] at hk
      rw [Fin.le_def]
      omega

/-! ### The Superset reading: lexical entries -/

/-- A nanosyntax lexical entry over an `n`-grade containment hierarchy stores the constituent
`[0, spans]`, with no contextual condition, in the pointer-free idealization of [caha-2009]. -/
structure SupersetRule (n : ℕ) (F : Type*) where
  /-- The exponent the entry spells out. -/
  exponent : F
  /-- The upper end of the stored constituent `[0, spans]`. -/
  spans : Fin n
  deriving DecidableEq, Repr

/-- An entry spells out every grade its stored constituent contains, the Superset Principle
([starke-2009]). -/
instance : Rule (SupersetRule n F) (Fin n) F :=
  ⟨SupersetRule.exponent, fun e g ↦ g ≤ e.spans⟩

instance : DecidableRel (Applies : SupersetRule n F → Fin n → Prop) :=
  fun e g ↦ inferInstanceAs (Decidable (g ≤ e.spans))

namespace SupersetRule

variable {e e' : SupersetRule n F} {g : Fin n}

@[simp] theorem applies_iff : Applies e g ↔ g ≤ e.spans := Iff.rfl

@[simp] theorem exponent_eq : Rule.exponent e = e.exponent := rfl

/-- An entry is more specific than another iff it stores the smaller constituent, the nanosyntax
principle Minimize Junk. -/
theorem applySet_subset_iff : applySet e ⊆ applySet e' ↔ e.spans ≤ e'.spans := Set.Iic_subset_Iic

theorem applySet_ssubset_iff : applySet e ⊂ applySet e' ↔ e.spans < e'.spans := Set.Iic_ssubset_Iic

end SupersetRule

end Morphology.Containment
