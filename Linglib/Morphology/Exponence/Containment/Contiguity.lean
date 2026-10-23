module

public import Linglib.Morphology.Exponence.Containment.Selection
public import Linglib.Morphology.Paradigm.Contiguity
public import Mathlib.Data.Finset.Max

/-!
# Containment hierarchies: contiguity and the suppletion generalizations

This file proves the *ABA generalization and its refinements for the two realizational engines
over a containment hierarchy. Over antihomophonous rule sets both engines realize contiguous
patterns, since applicability is closed upward for rules of exponence and downward for lexical
entries, and each engine generates every contiguous pattern, so Elsewhere insertion from terminal
rule sets and Superset spellout generate the same fully realized patterns. Over the
three-grade degree hierarchy, terminal adjacent rule sets realize the comparative and the
superlative alike, grounded rule sets exclude AAB, and a superlative root distinct from the
comparative one needs a portmanteau.

## Main definitions

* `ElsewhereGenerable`, `SupersetSpellable`: the patterns each engine realizes in full.
* `GroundedGenerable`: the patterns a grounded antihomophonous rule set realizes in full.

## Main results

* `isContiguous_realize`, `isContiguous_spellout`: *ABA for both engines.
* `isContiguous_iff_generable`, `isContiguous_iff_spelloutGenerable`,
  `spelloutGenerable_iff_generable`: both engines generate exactly the contiguous patterns.
* `realize_const_of_terminal_adjacent`, `realize_const_of_grounded`, `exists_portmanteau_of_ne`:
  the AAA/ABB plateau, *AAB, and the portmanteau prediction.
* `groundedGenerable_iff`: grounded rule sets generate exactly AAA, ABB and ABC.

## References

* [bobaljik-2012]
* [caha-2009]
* [declercq-vandenwyngaerd-2017]
-/

@[expose] public section

namespace Morphology.Containment

open Exponence

variable {n : ℕ} {F : Type*}

/-! ### *ABA -/

theorem isContiguous_realize {v : RuleSet (SpanRule n F)} (hv : v.Antihomophonous) :
    IsContiguous (realize v) :=
  RuleSet.isContiguous_realize_of_monotone hv fun _ _ _ _ hg hs ↦ le_trans hs hg

theorem isContiguous_spellout {v : RuleSet (SupersetRule n F)} (hv : v.Antihomophonous) :
    IsContiguous (spellout v) :=
  RuleSet.isContiguous_realize_of_antitone hv fun _ _ _ _ hg hs ↦ le_trans hg hs

/-! ### The plateau: terminal adjacency generates only AAA and ABB -/

theorem realize_const_of_cap {v : RuleSet (SpanRule n F)} {m g g' : Fin n}
    (hcap : ∀ it ∈ v, it.threshold ≤ m) (hg : m ≤ g) (hg' : m ≤ g') :
    realize v g = realize v g' :=
  RuleSet.realize_congr <| List.filter_congr fun it hit ↦ by
    simp [le_trans (hcap it hit) hg, le_trans (hcap it hit) hg']

private theorem threshold_le_one {it : SpanRule 3 F} (h0 : (it.spans : ℕ) = 0)
    (hc : ∀ c : Fin 3, it.context = some c → (c : ℕ) = (it.spans : ℕ) + 1) :
    it.threshold ≤ 1 := by
  rcases hcx : it.context with - | c
  · simp [SpanRule.threshold, hcx, Fin.le_def, h0]
  · simp [SpanRule.threshold, hcx, Fin.le_def, h0, hc c hcx]

theorem realize_const_of_terminal_adjacent {v : RuleSet (SpanRule 3 F)}
    (hT : Terminal v) (hA : Adjacent v) : realize v 1 = realize v 2 :=
  realize_const_of_cap (fun it hit ↦ threshold_le_one (hT it hit) (hA it hit)) le_rfl
    (by decide)

/-! ### Completeness: Elsewhere-generable = contiguous -/

theorem threshold_ofPattern {p : Paradigm n F} {s : Fin n} :
    (⟨p s, ⟨0, s.pos⟩, some s⟩ : SpanRule n F).threshold = s :=
  max_eq_right (Fin.le_def.mpr (Nat.zero_le _))

section Completeness

variable [DecidableEq F]

/-- The earliest grade sharing `g`'s form. -/
def firstOcc (p : Paradigm n F) (g : Fin n) : Fin n :=
  (Finset.univ.filter (fun j ↦ p j = p g)).min' ⟨g, by simp⟩

theorem apply_firstOcc (p : Paradigm n F) (g : Fin n) : p (firstOcc p g) = p g :=
  (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun j ↦ p j = p g)) _)).2

theorem firstOcc_le (p : Paradigm n F) (g : Fin n) : firstOcc p g ≤ g :=
  Finset.min'_le _ g (by simp)

theorem firstOcc_congr {p : Paradigm n F} {g g' : Fin n} (h : p g = p g') :
    firstOcc p g = firstOcc p g' := by
  unfold firstOcc
  congr 1
  simp [h]

/-- The canonical rule set of a pattern has one terminal rule per form, conditioned on the
form's first grade. -/
def ofPattern (p : Paradigm n F) : RuleSet (SpanRule n F) :=
  (List.finRange n).filterMap fun s ↦
    if firstOcc p s = s then some ⟨p s, ⟨0, s.pos⟩, some s⟩ else none

theorem mem_ofPattern {p : Paradigm n F} {it : SpanRule n F} :
    it ∈ ofPattern p ↔ ∃ s : Fin n, firstOcc p s = s ∧ it = ⟨p s, ⟨0, s.pos⟩, some s⟩ := by
  simp [ofPattern, eq_comm]

theorem terminal_ofPattern (p : Paradigm n F) : Terminal (ofPattern p) := by
  intro it hit
  obtain ⟨s, -, rfl⟩ := mem_ofPattern.mp hit
  rfl

theorem antihomophonous_ofPattern (p : Paradigm n F) :
    RuleSet.Antihomophonous (ofPattern p) := by
  intro it hit jt hjt hexp
  obtain ⟨s, hs, rfl⟩ := mem_ofPattern.mp hit
  obtain ⟨t, ht, rfl⟩ := mem_ofPattern.mp hjt
  obtain rfl : s = t := hs.symm.trans ((firstOcc_congr hexp).trans ht)
  rfl

theorem realize_ofPattern {p : Paradigm n F} (hp : IsContiguous p) (g : Fin n) :
    realize (ofPattern p) g = some (p g) := by
  have hff : firstOcc p (firstOcc p g) = firstOcc p g := firstOcc_congr (apply_firstOcc p g)
  rw [← apply_firstOcc p g]
  refine RuleSet.realize_eq_of_forall_le (mem_ofPattern.mpr ⟨_, hff, rfl⟩)
    (threshold_ofPattern.trans_le (firstOcc_le p g)) (fun jt hjt hjg ↦ ?_) fun jt hjt _ hτ ↦ ?_
  · obtain ⟨t, htfo, rfl⟩ := mem_ofPattern.mp hjt
    have htg : t ≤ g := threshold_ofPattern.symm.trans_le hjg
    rw [threshold_ofPattern, threshold_ofPattern]
    refine not_lt.mp fun hlt ↦ ne_of_gt hlt ?_
    exact htfo.symm.trans ((firstOcc_congr (hp hlt.le htg (apply_firstOcc p g)).symm).trans hff)
  · obtain ⟨t, -, rfl⟩ := mem_ofPattern.mp hjt
    obtain rfl : t = firstOcc p g := by simpa only [threshold_ofPattern] using hτ
    rfl

end Completeness

/-- A pattern is **Elsewhere-generable** when some terminal antihomophonous rule set realizes
it in full. -/
def ElsewhereGenerable (p : Paradigm n F) : Prop :=
  ∃ v : RuleSet (SpanRule n F), Terminal v ∧ v.Antihomophonous ∧
    ∀ g, realize v g = some (p g)

/-- A fully realized pattern arises from Elsewhere insertion over a terminal antihomophonous
rule set iff it is contiguous. -/
theorem isContiguous_iff_generable (p : Paradigm n F) :
    IsContiguous p ↔ ElsewhereGenerable p := by
  classical
  refine ⟨fun hp ↦ ⟨ofPattern p, terminal_ofPattern p, antihomophonous_ofPattern p,
    realize_ofPattern hp⟩, fun ⟨v, _, hv, hreal⟩ ↦ ?_⟩
  have h : realize v = some ∘ p := funext hreal
  rw [← isContiguous_comp_iff (Option.some_injective F), ← h]
  exact isContiguous_realize hv

/-! ### Three-grade hierarchies: *AAB and the portmanteau prediction -/

theorem realize_const_of_grounded {v : RuleSet (SpanRule 3 F)}
    (hv : v.Antihomophonous) (hG : Grounded v)
    (h01 : realize v 0 = realize v 1) (h2 : (realize v 2).isSome) :
    realize v 1 = realize v 2 := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (by simpa [RuleSet.realize] using h2)
  by_cases hτ : w.threshold ≤ 1
  · exact realize_eq_of_threshold_le hw hτ (by decide)
  obtain ⟨jt, hjt, hj1⟩ := hG w (RuleSet.selectBy_mem hw) 1 (not_le.mp hτ)
  obtain ⟨w₁, hw₁⟩ := Option.isSome_iff_exists.mp
    (RuleSet.selectBy_isSome_iff (f := SpanRule.threshold).mpr ⟨jt, hjt, hj1.le⟩)
  have hw₁τ : w₁.threshold = 1 := le_antisymm (RuleSet.selectBy_applies hw₁)
    (hj1.symm.le.trans (RuleSet.le_of_selectBy_eq_some hw₁ hjt hj1.le))
  obtain ⟨w₀, hw₀, he⟩ : ∃ w₀, v.selectBy SpanRule.threshold 0 = some w₀ ∧
      w₀.exponent = w₁.exponent := by
    simpa [RuleSet.realize, hw₁] using h01
  obtain rfl := hv (RuleSet.selectBy_mem hw₀) (RuleSet.selectBy_mem hw₁) he
  have h0 : w₀.threshold ≤ 0 := RuleSet.selectBy_applies hw₀
  rw [hw₁τ] at h0
  exact absurd h0 (by decide)

/-- ABC requires a portmanteau ([bobaljik-2012] §5.3.1). Under adjacency, a superlative root
distinct from the comparative one is realized by a rule exponing more than the root, as Latin
*opt-* and Welsh *gor-* are. -/
theorem exists_portmanteau_of_ne {v : RuleSet (SpanRule 3 F)} (hA : Adjacent v)
    (h12 : realize v 1 ≠ realize v 2) :
    ∃ it ∈ v, v.selectBy SpanRule.threshold 2 = some it ∧ 0 < (it.spans : ℕ) := by
  rcases hw : v.selectBy SpanRule.threshold 2 with - | w
  · refine absurd ?_ h12
    simp [RuleSet.realize, hw, RuleSet.selectBy_eq_none_of_applies
      (fun _ _ hs ↦ le_trans hs (by decide : (1 : Fin 3) ≤ 2)) hw]
  · refine ⟨w, RuleSet.selectBy_mem hw, rfl, Nat.pos_of_ne_zero fun h0 ↦ h12 ?_⟩
    exact realize_eq_of_threshold_le hw
      (threshold_le_one h0 (hA w (RuleSet.selectBy_mem hw))) (by decide)

/-- A pattern is **groundedly generable** when some antihomophonous rule set satisfying
[bobaljik-2012]'s markedness condition realizes it in full. -/
def GroundedGenerable (p : Paradigm n F) : Prop :=
  ∃ v : RuleSet (SpanRule n F), v.Antihomophonous ∧ Grounded v ∧ ∀ g, realize v g = some (p g)

/-- Over the three-grade hierarchy the groundedly generable patterns are the contiguous ones but
AAB, that is AAA, ABB and ABC: the canonical rule set of such a pattern is grounded. -/
theorem groundedGenerable_iff [DecidableEq F] (p : Paradigm 3 F) :
    GroundedGenerable p ↔ IsContiguous p ∧ ¬ (p 0 = p 1 ∧ p 1 ≠ p 2) := by
  constructor
  · rintro ⟨v, hv, hG, hreal⟩
    refine ⟨?_, fun ⟨h01, h12⟩ ↦ h12 ?_⟩
    · have h : realize v = some ∘ p := funext hreal
      rw [← isContiguous_comp_iff (Option.some_injective F), ← h]
      exact isContiguous_realize hv
    · simpa [hreal] using
        realize_const_of_grounded hv hG (by rw [hreal, hreal, h01]) (by simp [hreal])
  · rintro ⟨hc, hab⟩
    refine ⟨ofPattern p, antihomophonous_ofPattern p, fun it hit k hk ↦ ?_, realize_ofPattern hc⟩
    obtain ⟨s, hs, rfl⟩ := mem_ofPattern.mp hit
    rw [threshold_ofPattern] at hk
    refine ⟨_, mem_ofPattern.mpr ⟨k, ?_, rfl⟩, threshold_ofPattern⟩
    have h0 : firstOcc p 0 = 0 := le_antisymm (firstOcc_le p 0) (Fin.zero_le _)
    fin_cases s <;> fin_cases k <;> simp at hk
    · exact h0
    · exact h0
    · dsimp only at hs
      have h2 : ∀ j : Fin 3, j < 2 → p j ≠ p 2 := fun j hj hpj ↦ by
        have h' := firstOcc_le p j
        rw [(firstOcc_congr hpj).trans hs] at h'
        exact not_le.mpr hj h'
      have h01 : p 0 ≠ p 1 := fun h ↦ hab ⟨h, h2 1 (by decide)⟩
      have hle := firstOcc_le p 1
      have hne : firstOcc p 1 ≠ 0 := fun h ↦ h01 (h ▸ apply_firstOcc p 1)
      exact le_antisymm hle (Fin.one_le_of_ne_zero hne)

/-! ### Completeness: Superset-spellable = contiguous -/

section Completeness

variable [DecidableEq F]

/-- The latest grade sharing `g`'s form. -/
def lastOcc (p : Paradigm n F) (g : Fin n) : Fin n :=
  (Finset.univ.filter (fun j ↦ p j = p g)).max' ⟨g, by simp⟩

theorem apply_lastOcc (p : Paradigm n F) (g : Fin n) : p (lastOcc p g) = p g :=
  (Finset.mem_filter.mp (Finset.max'_mem (Finset.univ.filter (fun j ↦ p j = p g)) _)).2

theorem le_lastOcc (p : Paradigm n F) (g : Fin n) : g ≤ lastOcc p g :=
  Finset.le_max' _ g (by simp)

theorem lastOcc_congr {p : Paradigm n F} {g g' : Fin n} (h : p g = p g') :
    lastOcc p g = lastOcc p g' := by
  unfold lastOcc
  congr 1
  simp [h]

/-- The canonical lexicon of a pattern has one entry per form, storing the form's last grade. -/
def spelloutOfPattern (p : Paradigm n F) : RuleSet (SupersetRule n F) :=
  (List.finRange n).filterMap fun s ↦ if lastOcc p s = s then some ⟨p s, s⟩ else none

theorem mem_spelloutOfPattern {p : Paradigm n F} {e : SupersetRule n F} :
    e ∈ spelloutOfPattern p ↔ ∃ s : Fin n, lastOcc p s = s ∧ e = ⟨p s, s⟩ := by
  simp [spelloutOfPattern, eq_comm]

theorem antihomophonous_spelloutOfPattern (p : Paradigm n F) :
    RuleSet.Antihomophonous (spelloutOfPattern p) := by
  intro e he e' he' hexp
  obtain ⟨s, hs, rfl⟩ := mem_spelloutOfPattern.mp he
  obtain ⟨t, ht, rfl⟩ := mem_spelloutOfPattern.mp he'
  obtain rfl : s = t := hs.symm.trans ((lastOcc_congr hexp).trans ht)
  rfl

theorem spellout_spelloutOfPattern {p : Paradigm n F} (hp : IsContiguous p) (g : Fin n) :
    spellout (spelloutOfPattern p) g = some (p g) := by
  have hll : lastOcc p (lastOcc p g) = lastOcc p g := lastOcc_congr (apply_lastOcc p g)
  rw [← apply_lastOcc p g]
  refine RuleSet.realize_eq_of_forall_le (mem_spelloutOfPattern.mpr ⟨_, hll, rfl⟩)
    (le_lastOcc p g) (fun e he hge ↦ ?_) fun e he _ hτ ↦ ?_
  · obtain ⟨t, htlo, rfl⟩ := mem_spelloutOfPattern.mp he
    refine OrderDual.toDual_le_toDual.mpr (not_lt.mp fun hlt ↦ ne_of_lt hlt ?_)
    exact htlo.symm.trans (lastOcc_congr (hp hge hlt.le (apply_lastOcc p g).symm).symm)
  · obtain ⟨t, -, rfl⟩ := mem_spelloutOfPattern.mp he
    obtain rfl : t = lastOcc p g := OrderDual.toDual_inj.mp hτ
    rfl

end Completeness

/-- A pattern is **Superset-spellable** when some antihomophonous lexicon spells it out in
full. -/
def SupersetSpellable (p : Paradigm n F) : Prop :=
  ∃ v : RuleSet (SupersetRule n F), v.Antihomophonous ∧ ∀ g, spellout v g = some (p g)

theorem isContiguous_iff_spelloutGenerable (p : Paradigm n F) :
    IsContiguous p ↔ SupersetSpellable p := by
  classical
  refine ⟨fun hp ↦ ⟨spelloutOfPattern p, antihomophonous_spelloutOfPattern p,
    spellout_spelloutOfPattern hp⟩, fun ⟨v, hv, hreal⟩ ↦ ?_⟩
  have h : spellout v = some ∘ p := funext hreal
  rw [← isContiguous_comp_iff (Option.some_injective F), ← h]
  exact isContiguous_spellout hv

theorem spelloutGenerable_iff_generable (p : Paradigm n F) :
    SupersetSpellable p ↔ ElsewhereGenerable p :=
  (isContiguous_iff_spelloutGenerable p).symm.trans (isContiguous_iff_generable p)

/-! ### Where the engines diverge

On partial rule sets the selection directions come apart: an entry storing more structure
spells out smaller structures under the Superset Principle, while the corresponding rule leaves a
gap under Elsewhere insertion, nanosyntax's characteristic prediction
([declercq-vandenwyngaerd-2017]). -/

example : spellout [(⟨"gwell", 1⟩ : SupersetRule 3 String)] 0 = some "gwell" := by decide

example : realize [(⟨"gwell", 1, none⟩ : SpanRule 3 String)] 0 = none := by decide

/-! ### Antihomophony is necessary for *ABA

Two entries sharing an exponent generate ABA. [caha-2009] separates such accidental homophony
from syncretism, one entry over a contiguous span, and `RuleSet.Antihomophonous` is that
separation. -/

private def homophonous : RuleSet (SupersetRule 3 String) := [⟨"A", 0⟩, ⟨"B", 1⟩, ⟨"A", 2⟩]

example : ¬ homophonous.Antihomophonous := by decide

example : spellout homophonous 0 = some "A" ∧ spellout homophonous 1 = some "B" ∧
    spellout homophonous 2 = some "A" := by decide

end Morphology.Containment
