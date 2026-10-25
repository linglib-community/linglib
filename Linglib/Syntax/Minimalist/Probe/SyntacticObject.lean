module

public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Minimal search over syntactic objects

This file instantiates probe search at the tree: a probe on the head at a position of a
linearized object searches the positions the head c-commands in some order, a key on positions.
Closest by the branching positions above them, it finds a goal that no other satisfier
asymmetrically c-commands: the Minimal Link Condition, with mutually c-commanding candidates
equidistant. Procedural search orders are in `Probe/Search.lean`. Positions closed to the search,
by the PIC or by a horizon, cut its domain. Agree and labeling are both this search; what Agree
then does to the goal's features is `Minimalist.FeatureBundle.applyAgree`.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.goalsBy`, `goals`, `goalsUnder`: the terms a probe on a
  head finds under a search order, under closeness, and with some positions closed to it.
* `Minimalist.LinearizedSyntacticObject.leafProbe`, `phraseProbe`: the probes satisfied by the
  leaves of a category, and by the phrases its heads form.

## Main results

* `Minimalist.LinearizedSyntacticObject.not_finds_of_cCommands`: a satisfier that asymmetrically
  c-commands a position blocks the goal there.
* `Minimalist.LinearizedSyntacticObject.finds_above_branching_iff`: among satisfiers none of which
  dominates another, a probe finds those that no satisfier asymmetrically c-commands.

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

section Search

variable {β : Type*} [Preorder β] [DecidableRel ((· < ·) : β → β → Prop)]

variable (t) in
/-- The terms a probe on the head `h` finds when its search orders positions by `key`: those at
the first satisfying positions that an occurrence of `h` c-commands. -/
def goalsBy (p : Probe t.val.Positions) (h : SyntacticObject) (key : t.val.Positions → β) :
    Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.val.CCommands a q} key g).image t.termAt

theorem mem_goalsBy {h x : SyntacticObject} {key : t.val.Positions → β} :
    x ∈ t.goalsBy p h key ↔
      ∃ a, t.termAt a = h ∧ ∃ g, p.Finds {q | t.val.CCommands a q} key g ∧ t.termAt g = x := by
  simp only [goalsBy, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨g, ⟨a, ha, hg⟩, hx⟩ ↦ ⟨a, ha, g, hg, hx⟩,
    fun ⟨a, ha, g, hg, hx⟩ ↦ ⟨g, ⟨a, ha, hg⟩, hx⟩⟩

end Search

variable (t) in
/-- The terms a probe on the head `h` finds: those at the closest satisfying positions that an
occurrence of `h` c-commands. -/
def goals (p : Probe t.val.Positions) (h : SyntacticObject) : Finset SyntacticObject :=
  t.goalsBy p h (t.above t.branching)

theorem mem_goals {h x : SyntacticObject} : x ∈ t.goals p h ↔
    ∃ a, t.termAt a = h ∧ ∃ g, p.Finds {q | t.val.CCommands a q} (t.above t.branching) g ∧
      t.termAt g = x :=
  mem_goalsBy

variable (t) in
/-- The terms a probe on the head `h` finds when, at each occurrence `a` of `h`, the positions
`cut a` are closed to its search, by the PIC or by a horizon. -/
def goalsUnder (p : Probe t.val.Positions) (h : SyntacticObject)
    (cut : Core.Order.TreePath → Set Core.Order.TreePath) [∀ a, DecidablePred (· ∈ cut a)] :
    Finset SyntacticObject :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.val.CCommands a q ∧ q.val ∉ cut a.val} (t.above t.branching) g).image t.termAt

@[simp] theorem goalsUnder_empty {h : SyntacticObject} :
    t.goalsUnder p h (fun _ ↦ ∅) = t.goals p h := by
  simp only [goalsUnder, goals, goalsBy, Set.mem_empty_iff_false, not_false_eq_true, and_true]

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

end Minimalist
