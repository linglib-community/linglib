module

public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Agree: closest goals and valuation

This file states the structural conditions of Agree over syntactic objects and its valuation step
over feature bundles. A probe on the head at a position of a linearized object searches the
positions the head c-commands, closest by the branching positions above them, and so finds a goal
that no other satisfier asymmetrically c-commands: the Minimal Link Condition, with mutually
c-commanding candidates equidistant. Positions closed to the search, by the PIC or by a horizon,
cut its domain, and valuation copies a goal's value into an unvalued probe slot, only adding
information.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.goals`, `goalsUnder`: the terms a probe on a head finds,
  and those it finds with some positions closed to it.
* `Minimalist.LinearizedSyntacticObject.leafProbe`, `phraseProbe`: the probes satisfied by the
  leaves of a category, and by the phrases its heads form.
* `Minimalist.FeatureBundle.valueAt`, `Minimalist.FeatureBundle.applyAgree`: valuation of a
  dimension, `⊤` on a clash, and the probe's bundle valued from a goal's.

## Main results

* `Minimalist.LinearizedSyntacticObject.not_finds_of_cCommands`: a satisfier that asymmetrically
  c-commands a position blocks the goal there.
* `Minimalist.LinearizedSyntacticObject.finds_above_branching_iff`: among satisfiers none of which
  dominates another, a probe finds those that no satisfier asymmetrically c-commands.
* `Minimalist.FeatureBundle.valueAt_eq_unify`: valuation is unification with the value.

## References

* [chomsky-1995], [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

/-! ### Closest goals

A probe on the head at a position searches the positions the head c-commands, keyed by the
branching positions above each (`LinearizedSyntacticObject.above`), and finds a goal minimal under
the key, the Minimal Link Condition of [chomsky-1995]. -/

namespace LinearizedSyntacticObject

variable {t : LinearizedSyntacticObject} {p : Probe t.val.Positions} {s : Set t.val.Positions}
  {q g : t.val.Positions}

/-- A satisfier that asymmetrically c-commands a position blocks the goal there, whatever else the
probe's domain holds. -/
theorem not_finds_of_cCommands (hq : q ∈ s) (hsq : p.sat q) (hqg : t.val.CCommands q g)
    (hgq : ¬ t.val.CCommands g q) : ¬ p.Finds s (t.above t.branching) g := fun h ↦
  h.inspects.2 hq hsq (above_branching_lt_of_cCommands hqg hgq)

/-- Among satisfiers none of which dominates another, a probe finds those that no satisfier
asymmetrically c-commands: mutually c-commanding candidates are equidistant. -/
theorem finds_above_branching_iff (hs : IsAntichain (· ≤ ·) {q | q ∈ s ∧ p.sat q}) :
    p.Finds s (t.above t.branching) g ↔ (g ∈ s ∧ p.sat g) ∧
      ∀ ⦃q⦄, q ∈ s → p.sat q → ¬ (t.val.CCommands q g ∧ ¬ t.val.CCommands g q) := by
  simpa only [Probe.Finds, and_imp] using minimalFor_iff_of_isAntichain hs (fun _ h ↦ h.2 h.1)
    fun _ _ ↦ above_branching_lt_iff

variable (t) in
/-- The terms a probe on the head `h` finds: those at the closest satisfying positions that an
occurrence of `h` c-commands. -/
def goals (p : Probe t.val.Positions) (h : SyntacticObject) : Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.val.CCommands a q} (t.above t.branching) g).image t.termAt

theorem mem_goals {h x : SyntacticObject} : x ∈ t.goals p h ↔
    ∃ a, t.termAt a = h ∧ ∃ g, p.Finds {q | t.val.CCommands a q} (t.above t.branching) g ∧
      t.termAt g = x := by
  simp only [goals, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨g, ⟨a, ha, hg⟩, hx⟩ ↦ ⟨a, ha, g, hg, hx⟩,
    fun ⟨a, ha, g, hg, hx⟩ ↦ ⟨g, ⟨a, ha, hg⟩, hx⟩⟩

variable (t) in
/-- The terms a probe on the head `h` finds when, at each occurrence `a` of `h`, the positions
`cut a` are closed to its search, by the PIC or by a horizon. -/
def goalsUnder (p : Probe t.val.Positions) (h : SyntacticObject)
    (cut : Core.Order.TreePath → Set Core.Order.TreePath) [∀ a, DecidablePred (· ∈ cut a)] :
    Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.val.CCommands a q ∧ q.val ∉ cut a.val} (t.above t.branching) g).image t.termAt

/-- With nothing closed, the search is unrestricted. -/
@[simp] theorem goalsUnder_empty {h : SyntacticObject} :
    t.goalsUnder p h (fun _ ↦ ∅) = t.goals p h := by
  simp only [goalsUnder, goals, Set.mem_empty_iff_false, not_false_eq_true, and_true]

/-- A goal found outside the closed positions is still found: closing part of the domain removes
only the goals inside it, though it can expose goals they shielded. -/
theorem mem_goalsUnder_of_finds {h : SyntacticObject}
    {cut : Core.Order.TreePath → Set Core.Order.TreePath}
    [∀ a, DecidablePred (· ∈ cut a)] {a : t.val.Positions} (ha : t.termAt a = h)
    (hg : p.Finds {q | t.val.CCommands a q} (t.above t.branching) g) (hgc : g.val ∉ cut a.val) :
    t.termAt g ∈ t.goalsUnder p h cut := by
  simp only [goalsUnder, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨g, ⟨a, ha, hg.of_subset (fun _ hq ↦ hq.1) ⟨hg.mem, hgc⟩⟩, rfl⟩

variable (t) in
/-- The probe satisfied by the leaves of category `c`. -/
def leafProbe (c : Cat) : Probe t.val.Positions :=
  .relativized fun q ↦ decide (SyntacticObject.isLeafOf c (t.termAt q))

variable (t) in
/-- The probe satisfied by the phrases a head of category `c` forms with its sister, so that a
phrase in a specifier is closer than whatever its sister contains. -/
def phraseProbe (c : Cat) : Probe t.val.Positions :=
  .relativized fun q ↦
    decide (∃ e : t.val.Positions, e ≠ ⊥ ∧ e.val.parent = q.val ∧
      SyntacticObject.isLeafOf c (t.termAt e))

end LinearizedSyntacticObject

namespace FeatureBundle

variable (probe goal : FeatureBundle) (t : FeatureType)

/-! ### Valuation -/

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

end FeatureBundle

end Minimalist
