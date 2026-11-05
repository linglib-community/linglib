module

public import Linglib.Morphology.Exponence.Containment.Selection
public import Linglib.Morphology.Paradigm.Contiguity
public import Mathlib.Order.Minimal

/-!
# Containment hierarchies: contiguity and the suppletion generalizations

Over an antihomophonous rule set, Elsewhere insertion and Superset spellout realize contiguous
patterns, since applicability is closed upward for rules of exponence and downward for lexical
entries. Each engine generates every contiguous pattern, so the two
[generate the same fully realized patterns](##SupersetRule.generable_iff_spanRule_generable). A
grounded rule set realizes a form that recurs
[at every grade from its first one up](##SpanRule.groundedGenerable_iff), which over three grades
leaves AAA, ABB and ABC and excludes AAB as
[the markedness condition with adjacency does](##SpanRule.realize_const_of_markedness); under
adjacency, a superlative distinct from the comparative
[needs a portmanteau](##SpanRule.exists_portmanteau_of_ne).

## Implementation notes

The canonical rule set of a pattern has one rule per form, at the grade where the form is
`Minimal` in its fiber for rules of exponence and `Maximal` for lexical entries.

## References

* [bobaljik-2012]
* [caha-2009]
-/

@[expose] public section

namespace Morphology

variable {n : ℕ} {F : Type*}

private theorem isContiguous_of_eq_some {q : Paradigm n (Option F)} {p : Paradigm n F}
    (hq : IsContiguous q) (h : ∀ g, q g = some (p g)) : IsContiguous p :=
  (isContiguous_comp_iff (Option.some_injective F)).1 <| (funext h : q = some ∘ p) ▸ hq

namespace SpanRule

/-! ### *ABA -/

/-- Elsewhere insertion over an antihomophonous rule set is contiguous ([bobaljik-2012]
§2.2). -/
theorem isContiguous_realize {v : RuleSet (SpanRule n F)} (hv : v.Antihomophonous) :
    IsContiguous (realize v) :=
  RuleSet.isContiguous_realize_of_monotone hv fun _ _ _ _ hg hs ↦ le_trans hs hg

/-! ### The plateau -/

theorem realize_const_of_cap {v : RuleSet (SpanRule n F)} {m g g' : Fin n}
    (hcap : ∀ it ∈ v, it.threshold ≤ m) (hg : m ≤ g) (hg' : m ≤ g') :
    realize v g = realize v g' :=
  RuleSet.realize_congr <| List.filter_congr fun it hit ↦ by
    simp [le_trans (hcap it hit) hg, le_trans (hcap it hit) hg']

private theorem threshold_le_one {it : SpanRule 3 F} (h0 : (it.spans : ℕ) = 0)
    (hc : ∀ c : Fin 3, it.context = some c → (c : ℕ) = (it.spans : ℕ) + 1) :
    it.threshold ≤ 1 := by
  rcases hcx : it.context with - | c
  · simp [threshold, hcx, Fin.le_def, h0]
  · simp [threshold, hcx, Fin.le_def, h0, hc c hcx]

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

section Grounded

variable {v : RuleSet (SpanRule n F)} {it : SpanRule n F} {g g' : Fin n}

/-- In a grounded rule set, the rule selected at a grade that some threshold reaches has that
grade as its threshold. -/
theorem exists_selectBy_threshold_eq (hG : Grounded v) (hit : it ∈ v) (hg : g ≤ it.threshold) :
    ∃ w, v.selectBy threshold g = some w ∧ w.threshold = g := by
  obtain ⟨jt, hjt, rfl⟩ : ∃ jt ∈ v, jt.threshold = g :=
    hg.lt_or_eq.elim (hG it hit g) fun h ↦ ⟨it, hit, h.symm⟩
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

end Grounded

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

/-! ### Generative capacity -/

theorem threshold_ofPattern {p : Paradigm n F} {s : Fin n} :
    (⟨p s, ⟨0, s.pos⟩, some s⟩ : SpanRule n F).threshold = s :=
  max_eq_right (Fin.le_def.mpr (Nat.zero_le _))

section OfPattern

variable [DecidableEq F] {p : Paradigm n F}

variable (p) in
/-- The canonical rule set of a pattern has one terminal rule per form, conditioned on the least
grade of the form. -/
def ofPattern : RuleSet (SpanRule n F) :=
  ((List.finRange n).filter fun s ↦ ∀ j < s, p j ≠ p s).map fun s ↦ ⟨p s, ⟨0, s.pos⟩, some s⟩

theorem mem_ofPattern {it : SpanRule n F} :
    it ∈ ofPattern p ↔ ∃ s, Minimal (p · = p s) s ∧ it = ⟨p s, ⟨0, s.pos⟩, some s⟩ := by
  simp [ofPattern, minimal_iff_forall_lt, eq_comm]

variable (p) in
theorem terminal_ofPattern : Terminal (ofPattern p) := by
  intro it hit
  obtain ⟨s, -, rfl⟩ := mem_ofPattern.mp hit
  rfl

variable (p) in
theorem antihomophonous_ofPattern : RuleSet.Antihomophonous (ofPattern p) := by
  intro it hit jt hjt hexp
  obtain ⟨s, hs, rfl⟩ := mem_ofPattern.mp hit
  obtain ⟨t, ht, rfl⟩ := mem_ofPattern.mp hjt
  replace hexp : p s = p t := hexp
  obtain rfl : s = t := le_antisymm (hs.le hexp.symm) (ht.le hexp)
  rfl

theorem realize_ofPattern (hp : IsContiguous p) (g : Fin n) :
    realize (ofPattern p) g = some (p g) := by
  obtain ⟨s, hsg, hs⟩ := exists_minimal_le_of_wellFoundedLT (p · = p g) g rfl
  have hsg' : p s = p g := hs.prop
  rw [← hsg']
  replace hs : Minimal (p · = p s) s := hsg' ▸ hs
  refine RuleSet.realize_eq_of_forall_le (mem_ofPattern.mpr ⟨s, hs, rfl⟩)
    (threshold_ofPattern.trans_le hsg) (fun jt hjt hjg ↦ ?_) fun jt hjt _ hτ ↦ ?_
  · obtain ⟨t, ht, rfl⟩ := mem_ofPattern.mp hjt
    have htg : t ≤ g := threshold_ofPattern.symm.trans_le hjg
    rw [threshold_ofPattern, threshold_ofPattern]
    exact (le_total t s).elim id fun hst ↦ ht.le (hp hst htg hsg')
  · obtain ⟨t, -, rfl⟩ := mem_ofPattern.mp hjt
    obtain rfl : t = s := by simpa only [threshold_ofPattern] using hτ
    rfl

end OfPattern

/-- A pattern is **generable** when some terminal antihomophonous rule set realizes it in full. -/
def Generable (p : Paradigm n F) : Prop :=
  ∃ v : RuleSet (SpanRule n F), Terminal v ∧ v.Antihomophonous ∧ ∀ g, realize v g = some (p g)

/-- A fully realized pattern arises from Elsewhere insertion over a terminal antihomophonous
rule set iff it is contiguous. -/
theorem isContiguous_iff_generable (p : Paradigm n F) : IsContiguous p ↔ Generable p := by
  classical
  exact ⟨fun hp ↦ ⟨ofPattern p, terminal_ofPattern p, antihomophonous_ofPattern p,
    realize_ofPattern hp⟩,
    fun ⟨_, _, hv, hreal⟩ ↦ isContiguous_of_eq_some (isContiguous_realize hv) hreal⟩

instance [DecidableEq F] : DecidablePred (Generable : Paradigm n F → Prop) :=
  fun p ↦ decidable_of_iff _ (isContiguous_iff_generable p)

/-- A pattern is **groundedly generable** when some grounded antihomophonous rule set realizes it
in full. -/
def GroundedGenerable (p : Paradigm n F) : Prop :=
  ∃ v : RuleSet (SpanRule n F), v.Antihomophonous ∧ Grounded v ∧ ∀ g, realize v g = some (p g)

/-- A pattern is groundedly generable iff a form that recurs holds at every grade from its first
one up, a suppletive stretch followed by a plateau: over three grades AAA, ABB and ABC. Grounding
alone does the work that [bobaljik-2012] §5.3.1 assigns to the markedness condition and adjacency
together. -/
theorem groundedGenerable_iff [DecidableEq F] (p : Paradigm n F) :
    GroundedGenerable p ↔ ∀ ⦃i j⦄, i < j → p i = p j → ∀ ⦃k⦄, i ≤ k → p k = p i := by
  refine ⟨fun ⟨v, hv, hG, hreal⟩ i j hij h k hik ↦ Option.some_injective _ ?_, fun hp ↦ ?_⟩
  · rw [← hreal, ← hreal]
    exact realize_const_of_cap
      (fun _ ↦ threshold_le_of_realize_eq hv hG hij (by rw [hreal, hreal, h])) hik le_rfl
  have hc : IsContiguous p := fun i j k hij hjk hik ↦ by
    rcases hij.lt_or_eq with hlt | rfl
    · exact (hp (hlt.trans_le hjk) hik hij).symm
    · rfl
  refine ⟨ofPattern p, antihomophonous_ofPattern p, fun it hit k hk ↦ ?_, realize_ofPattern hc⟩
  obtain ⟨s, hs, rfl⟩ := mem_ofPattern.mp hit
  rw [threshold_ofPattern] at hk
  refine ⟨_, mem_ofPattern.mpr ⟨k, minimal_iff_forall_lt.mpr ⟨rfl, fun j hjk hj ↦ ?_⟩, rfl⟩,
    threshold_ofPattern⟩
  exact (hjk.trans hk).not_ge (hs.le (hp hjk hj (hjk.trans hk).le).symm)

instance [DecidableEq F] : DecidablePred (GroundedGenerable : Paradigm n F → Prop) :=
  fun p ↦ decidable_of_iff _ (groundedGenerable_iff p).symm

end SpanRule

namespace SupersetRule

/-- Superset spellout over an antihomophonous lexicon is contiguous ([caha-2009]). -/
theorem isContiguous_spellout {v : RuleSet (SupersetRule n F)} (hv : v.Antihomophonous) :
    IsContiguous (spellout v) :=
  RuleSet.isContiguous_realize_of_antitone hv fun _ _ _ _ hg hs ↦ le_trans hg hs

section OfPattern

variable [DecidableEq F] {p : Paradigm n F}

variable (p) in
/-- The canonical lexicon of a pattern has one entry per form, storing the greatest grade of the
form. -/
def ofPattern : RuleSet (SupersetRule n F) :=
  ((List.finRange n).filter fun s ↦ ∀ j, s < j → p j ≠ p s).map fun s ↦ ⟨p s, s⟩

theorem mem_ofPattern {e : SupersetRule n F} :
    e ∈ ofPattern p ↔ ∃ s, Maximal (p · = p s) s ∧ e = ⟨p s, s⟩ := by
  simp [ofPattern, maximal_iff_forall_gt, eq_comm]

variable (p) in
theorem antihomophonous_ofPattern : RuleSet.Antihomophonous (ofPattern p) := by
  intro e he e' he' hexp
  obtain ⟨s, hs, rfl⟩ := mem_ofPattern.mp he
  obtain ⟨t, ht, rfl⟩ := mem_ofPattern.mp he'
  replace hexp : p s = p t := hexp
  obtain rfl : s = t := le_antisymm (ht.le hexp) (hs.le hexp.symm)
  rfl

theorem spellout_ofPattern (hp : IsContiguous p) (g : Fin n) :
    spellout (ofPattern p) g = some (p g) := by
  obtain ⟨s, hgs, hs⟩ := exists_maximal_ge_of_wellFoundedGT (p · = p g) g rfl
  have hsg' : p s = p g := hs.prop
  rw [← hsg']
  replace hs : Maximal (p · = p s) s := hsg' ▸ hs
  refine RuleSet.realize_eq_of_forall_le (mem_ofPattern.mpr ⟨s, hs, rfl⟩) hgs
    (fun e he hge ↦ ?_) fun e he _ hτ ↦ ?_
  · obtain ⟨t, ht, rfl⟩ := mem_ofPattern.mp he
    refine OrderDual.toDual_le_toDual.mpr ((le_total s t).elim id fun hts ↦ ht.le ?_)
    exact hsg'.trans (hp hge hts hsg'.symm)
  · obtain ⟨t, -, rfl⟩ := mem_ofPattern.mp he
    obtain rfl : t = s := OrderDual.toDual_inj.mp hτ
    rfl

end OfPattern

/-- A pattern is **generable** when some antihomophonous lexicon spells it out in full. -/
def Generable (p : Paradigm n F) : Prop :=
  ∃ v : RuleSet (SupersetRule n F), v.Antihomophonous ∧ ∀ g, spellout v g = some (p g)

/-- A fully realized pattern arises from Superset spellout over an antihomophonous lexicon iff it
is contiguous, [caha-2009]'s Universal Contiguity sharpened to exact generative capacity. -/
theorem isContiguous_iff_generable (p : Paradigm n F) : IsContiguous p ↔ Generable p := by
  classical
  exact ⟨fun hp ↦ ⟨ofPattern p, antihomophonous_ofPattern p, spellout_ofPattern hp⟩,
    fun ⟨_, hv, hreal⟩ ↦ isContiguous_of_eq_some (isContiguous_spellout hv) hreal⟩

instance [DecidableEq F] : DecidablePred (Generable : Paradigm n F → Prop) :=
  fun p ↦ decidable_of_iff _ (isContiguous_iff_generable p)

/-- Superset spellout and Elsewhere insertion from terminal rule sets generate the same fully
realized patterns, the contiguous ones. On partial patterns they part: spellout gaps propagate
upward (`spellout_eq_none_of_le`), Elsewhere gaps downward (`SpanRule.realize_eq_none_of_le`). -/
theorem generable_iff_spanRule_generable (p : Paradigm n F) :
    Generable p ↔ SpanRule.Generable p :=
  (isContiguous_iff_generable p).symm.trans (SpanRule.isContiguous_iff_generable p)

end SupersetRule

end Morphology
