module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Morphology.Exponence.Select
public import Linglib.Morphology.Exponence.SubsetRule
public import Linglib.Morphology.Inflection.Paradigm.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Minimal
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Order.UpperLower.Basic

/-!
# Rules of exponence over a containment hierarchy

A `SpanRule` is a Distributed Morphology rule of exponence over an `n`-grade hierarchy in which
each grade's structure contains every lower grade's. It realizes an initial span, optionally
conditioned on a higher head, and applies from its `threshold` up; Elsewhere insertion
(`SpanRule.realize`) selects the applicable rule of greatest threshold. Over an antihomophonous rule
set it [realizes contiguous patterns](##SpanRule.isContiguous_realize). A grounded rule set that
realizes two grades alike [has no threshold above the lower](##SpanRule.threshold_le_of_realize_eq),
which excludes AAB over three grades as
[markedness with adjacency does](##SpanRule.realize_const_of_markedness).

## References

* [bobaljik-2012]
* [halle-1997]
* [kiparsky-1973]
-/

@[expose] public section

namespace Morphology

variable {n : ℕ} {F : Type*}

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
instance : ExponenceRule (SpanRule n F) (Fin n) F :=
  ⟨SpanRule.exponent, fun it g ↦ it.threshold ≤ g⟩

instance : DecidableRel (Applies : SpanRule n F → Fin n → Prop) :=
  fun it g ↦ inferInstanceAs (Decidable (it.threshold ≤ g))

namespace SpanRule

variable {it jt : SpanRule n F} {g g' : Fin n} {φ : F}

@[simp] theorem applies_iff : Applies it g ↔ it.threshold ≤ g := Iff.rfl

@[simp] theorem exponent_eq : ExponenceRule.exponent it = it.exponent := rfl

/-- Over a linear hierarchy the applicability sets are nested, so specificity is the reverse of
threshold order and the Elsewhere ordering ([kiparsky-1973]) is total. -/
theorem applySet_subset_iff : applySet it ⊆ applySet jt ↔ jt.threshold ≤ it.threshold :=
  Set.Ici_subset_Ici

theorem applySet_ssubset_iff : applySet it ⊂ applySet jt ↔ jt.threshold < it.threshold :=
  Set.Ici_ssubset_Ici

/-! ### Conditions on rule sets -/

/-- Every rule expones the bare root, so the rule set has no portmanteaux. -/
def Terminal (v : RuleSet (SpanRule n F)) : Prop :=
  ∀ it ∈ v, (it.spans : ℕ) = 0

instance (v : RuleSet (SpanRule n F)) : Decidable (Terminal v) := by
  unfold Terminal; infer_instance

/-- Conditioning heads cover the exponed span, the adjacency condition on contextual allomorphy
that [bobaljik-2012] tentatively adopts. -/
def Adjacent (v : RuleSet (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ c : Fin n, it.context = some c → it.spans ⋖ c

instance (v : RuleSet (SpanRule n F)) : Decidable (Adjacent v) :=
  decidable_of_iff (∀ it ∈ v, ∀ c : Fin n, it.context = some c → (it.spans : ℕ) + 1 = c) <| by
    simp [Adjacent]

/-- [bobaljik-2012]'s markedness condition requires, for each context-sensitive rule involving a
node, a context-free rule involving that node. A rule involves the nodes `[0, k]` of its span,
context-sensitively below its threshold, and a context-free rule for `[0, k]` is one of
threshold `k`, so every threshold below a rule's and within its span is some rule's. -/
def Markedness (v : RuleSet (SpanRule n F)) : Prop :=
  ∀ it ∈ v, ∀ k : Fin n, k ≤ it.spans → k < it.threshold → ∃ jt ∈ v, jt.threshold = k

instance (v : RuleSet (SpanRule n F)) : Decidable (Markedness v) := by
  unfold Markedness; infer_instance

/-- A rule set is grounded when its thresholds form a lower set (the name is ours). This
strengthens the markedness condition to the thresholds between a rule's span and its context,
which adjacency leaves empty. -/
def Grounded (v : RuleSet (SpanRule n F)) : Prop :=
  IsLowerSet (threshold '' {it | it ∈ v})

theorem grounded_iff {v : RuleSet (SpanRule n F)} :
    Grounded v ↔ ∀ it ∈ v, ∀ k < it.threshold, ∃ jt ∈ v, jt.threshold = k := by
  simp only [Grounded, isLowerSet_iff_forall_lt, Set.mem_image]
  exact ⟨fun h it hit k hk ↦ h hk ⟨it, hit, rfl⟩, fun h _ k hk ⟨it, hit, he⟩ ↦ h it hit k (he ▸ hk)⟩

instance (v : RuleSet (SpanRule n F)) : Decidable (Grounded v) :=
  decidable_of_iff _ grounded_iff.symm

theorem Grounded.markedness {v : RuleSet (SpanRule n F)} (h : Grounded v) : Markedness v :=
  fun it hit k _ hk ↦ grounded_iff.1 h it hit k hk

/-- Under adjacency the markedness condition is grounding. -/
theorem markedness_iff_grounded {v : RuleSet (SpanRule n F)} (hA : Adjacent v) :
    Markedness v ↔ Grounded v := by
  refine ⟨fun hM ↦ grounded_iff.2 fun it hit k hk ↦ hM it hit k ?_ hk, Grounded.markedness⟩
  rcases hc : it.context with - | c
  · simp only [threshold, hc, Option.getD_none, max_self] at hk
    exact hk.le
  · rw [threshold, hc, Option.getD_some] at hk
    exact (lt_max_iff.mp hk).elim le_of_lt (hA it hit c hc).le_of_lt

/-! ### Elsewhere insertion -/

/-- Elsewhere insertion realizes at each grade the exponent of the applicable rule of greatest
threshold, the most specific, the first listed on ties, and `none` where no rule applies. -/
abbrev realize (v : RuleSet (SpanRule n F)) : Paradigm n (Option F) :=
  v.realize threshold

variable {v : RuleSet (SpanRule n F)}

/-- Elsewhere gaps propagate downward, since a rule applying at a grade applies at every higher
one; spellout gaps propagate the other way (`SupersetRule.spellout_eq_none_of_le`). -/
theorem realize_eq_none_of_le (h : realize v g' = none) (hg : g ≤ g') : realize v g = none :=
  Option.map_eq_none_iff.mpr <| RuleSet.selectBy_eq_none_of_applies
    (fun _ _ hs ↦ le_trans hs hg) (Option.map_eq_none_iff.mp h)

/-- The rule selected at a grade is realized at every lower grade its threshold reaches, so
Elsewhere insertion plateaus between thresholds. -/
theorem realize_eq_of_threshold_le (h : v.selectBy threshold g' = some it)
    (hit : it.threshold ≤ g) (hg : g ≤ g') : realize v g = realize v g' :=
  congrArg (Option.map _) <|
    (RuleSet.selectBy_eq_some_of_applies (fun _ _ hs ↦ le_trans hs hg) h hit).trans h.symm

/-! ### *ABA and the plateau -/

/-- Elsewhere insertion over an antihomophonous rule set is contiguous ([bobaljik-2012]
§2.2). -/
theorem isContiguous_realize (hv : v.Antihomophonous) : IsContiguous (realize v) :=
  RuleSet.isContiguous_realize_of_monotone hv fun _ _ _ _ hg hs ↦ le_trans hs hg

theorem realize_const_of_cap {m : Fin n} (hcap : ∀ it ∈ v, it.threshold ≤ m) (hg : m ≤ g)
    (hg' : m ≤ g') : realize v g = realize v g' :=
  RuleSet.realize_congr <| List.filter_congr fun it hit ↦ by
    simp [le_trans (hcap it hit) hg, le_trans (hcap it hit) hg']

private theorem threshold_le_one {it : SpanRule 3 F} (h0 : (it.spans : ℕ) = 0)
    (hc : ∀ c : Fin 3, it.context = some c → it.spans ⋖ c) : it.threshold ≤ 1 := by
  rcases hcx : it.context with - | c
  · simp [threshold, hcx, Fin.le_def, h0]
  · have h := hc c hcx
    simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq, h0] at h
    simp [threshold, hcx, Fin.le_def, h0, ← h]

/-- Terminal rules with adjacent contexts have thresholds at most the first head, so the
comparative and superlative cells coincide and only AAA and ABB root patterns are generable. -/
theorem realize_const_of_terminal_adjacent {v : RuleSet (SpanRule 3 F)}
    (hT : Terminal v) (hA : Adjacent v) : realize v 1 = realize v 2 :=
  realize_const_of_cap (fun it hit ↦ threshold_le_one (hT it hit) (hA it hit)) le_rfl
    (by decide)

/-- Under adjacency a superlative distinct from the comparative is realized by a portmanteau, as
Latin *opt-* and Welsh *gor-* are ([bobaljik-2012] §5.3.1). -/
theorem exists_portmanteau_of_ne {v : RuleSet (SpanRule 3 F)} (hA : Adjacent v)
    (h12 : realize v 1 ≠ realize v 2) :
    ∃ it, v.selectBy threshold 2 = some it ∧ 0 < (it.spans : ℕ) := by
  rcases hw : v.selectBy threshold 2 with - | w
  · refine absurd ?_ h12
    simp [RuleSet.realize, hw, RuleSet.selectBy_eq_none_of_applies
      (fun _ _ hs ↦ le_trans hs (by decide : (1 : Fin 3) ≤ 2)) hw]
  · refine ⟨w, rfl, Nat.pos_of_ne_zero fun h0 ↦ h12 ?_⟩
    exact realize_eq_of_threshold_le hw
      (threshold_le_one h0 (hA w (RuleSet.selectBy_mem hw))) (by decide)

/-! ### Grounded rule sets -/

/-- In a grounded rule set, the rule selected at a grade that some threshold reaches has that
grade as its threshold. -/
theorem exists_selectBy_threshold_eq (hG : Grounded v) (hit : it ∈ v) (hg : g ≤ it.threshold) :
    ∃ w, v.selectBy threshold g = some w ∧ w.threshold = g := by
  obtain ⟨jt, hjt, rfl⟩ := hG hg ⟨it, hit, rfl⟩
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
    (RuleSet.selectBy_isSome_iff (f := threshold).mpr ⟨jt, hjt, le_rfl⟩)
  exact ⟨w, hw, le_antisymm (RuleSet.selectBy_applies hw)
    (RuleSet.le_of_selectBy_eq_some hw hjt le_rfl)⟩

theorem realize_ne_of_grounded (hv : v.Antihomophonous) (hG : Grounded v) (hit : it ∈ v)
    (hg : g < g') (hg' : g' ≤ it.threshold) : realize v g ≠ realize v g' := by
  obtain ⟨w, hw, rfl⟩ := exists_selectBy_threshold_eq hG hit (hg.le.trans hg')
  obtain ⟨w', hw', rfl⟩ := exists_selectBy_threshold_eq hG hit hg'
  intro h
  simp only [RuleSet.realize, hw, hw', Option.map_some, Option.some.injEq] at h
  exact hg.ne (congrArg _ (hv (RuleSet.selectBy_mem hw) (RuleSet.selectBy_mem hw') h))

/-- A grounded antihomophonous rule set that realizes two grades alike has no threshold above the
lower one. -/
theorem threshold_le_of_realize_eq (hv : v.Antihomophonous) (hG : Grounded v) (hg : g < g')
    (h : realize v g = realize v g') (hit : it ∈ v) : it.threshold ≤ g := by
  refine not_lt.mp fun hlt ↦ ?_
  rcases le_total g' it.threshold with h' | h'
  · exact realize_ne_of_grounded hv hG hit hg h' h
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
      (RuleSet.selectBy_isSome_iff (f := threshold).mpr ⟨it, hit, h'⟩)
    exact realize_ne_of_grounded hv hG (RuleSet.selectBy_mem hw)
      (hlt.trans_le (RuleSet.le_of_selectBy_eq_some hw hit h')) le_rfl
      (h.trans (realize_eq_of_threshold_le hw le_rfl (RuleSet.selectBy_applies hw)).symm)

/-- *AAB ([bobaljik-2012] §5.3.1): over three grades, an antihomophonous rule set meeting the
markedness condition with adjacent contexts that realizes the positive and the comparative alike
realizes the comparative and the superlative alike. Under adjacency the markedness condition is
grounding, which excludes AAB without adjacency. -/
theorem realize_const_of_markedness {v : RuleSet (SpanRule 3 F)}
    (hv : v.Antihomophonous) (hM : Markedness v) (hA : Adjacent v)
    (h01 : realize v 0 = realize v 1) : realize v 1 = realize v 2 :=
  realize_const_of_cap
    (fun _ ↦ threshold_le_of_realize_eq hv ((markedness_iff_grounded hA).1 hM) (by decide) h01)
    (by decide) (by decide)

end SpanRule

end Morphology
