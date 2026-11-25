/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Syntax.Minimalist.SyntacticObject.Token

/-!
# Minimal search over syntactic objects

This file instantiates probe search at the tree: a probe on the head at a position of a
planar object searches the positions the head c-commands in some order, a key on positions.
Closest by the branching positions above them, it finds a goal that no other satisfier
asymmetrically c-commands: the Minimal Link Condition, with mutually c-commanding candidates
equidistant. What Agree then does to the features of the probe and the goal is
`Minimalist.FeatureState.value`.

## Main definitions

* `Minimalist.PlanarSyntacticObject.goalsBy`, `goals`: the terms a probe on a head finds under a
  search order, and under closeness.
* `Minimalist.PlanarSyntacticObject.leafProbe`: the probe satisfied by the leaves of a category.

## Main results

* `Minimalist.PlanarSyntacticObject.not_finds_of_cCommands`: a satisfier that asymmetrically
  c-commands a position blocks the goal there.
* `Minimalist.PlanarSyntacticObject.finds_above_branching_iff`: among satisfiers none of which
  dominates another, a probe finds those that no satisfier asymmetrically c-commands.

## References

* [chomsky-1995], [chomsky-2000]
-/

@[expose] public section

namespace Minimalist

/-! ### Closest goals

A probe on the head at a position searches the positions the head c-commands, keyed by the
branching positions above each (`PlanarSyntacticObject.above`), and finds a goal minimal under
the key, the Minimal Link Condition of [chomsky-1995]. -/

namespace PlanarSyntacticObject

variable {t : PlanarSyntacticObject TokenLeaf} {p : Probe t.toRoseTree.Positions} {s : Set
    t.toRoseTree.Positions}
  {q g : t.toRoseTree.Positions}

/-- A satisfier that asymmetrically c-commands a position blocks the goal there, whatever else the
probe's domain holds. -/
theorem not_finds_of_cCommands (hq : q ∈ s) (hsq : p.sat q) (hqg : t.toRoseTree.CCommands q g)
    (hgq : ¬ t.toRoseTree.CCommands g q) : ¬ p.Finds s (t.above t.toRoseTree.branching) g := fun h ↦
  h.inspects.2 hq hsq (above_branching_lt_of_cCommands hqg hgq)

/-- Among satisfiers none of which dominates another, a probe finds those that no satisfier
asymmetrically c-commands: mutually c-commanding candidates are equidistant. -/
theorem finds_above_branching_iff (hs : IsAntichain (· ≤ ·) {q | q ∈ s ∧ p.sat q}) :
    p.Finds s (t.above t.toRoseTree.branching) g ↔ (g ∈ s ∧ p.sat g) ∧
      ∀ ⦃q⦄, q ∈ s → p.sat q → ¬ (t.toRoseTree.CCommands q g ∧ ¬ t.toRoseTree.CCommands g q) := by
  simpa only [Probe.Finds, and_imp] using minimalFor_iff_of_isAntichain hs (fun _ h ↦ h.2 h.1)
    fun _ _ ↦ above_branching_lt_iff

section Search

variable {β : Type*} [Preorder β] [DecidableRel ((· < ·) : β → β → Prop)]

variable (t) in
/-- The terms a probe on the head `h` finds when its search orders positions by `key`: those at
the first satisfying positions that an occurrence of `h` c-commands. -/
def goalsBy (p : Probe t.toRoseTree.Positions) (h : SyntacticObject TokenLeaf)
    (key : t.toRoseTree.Positions →
    β) :
    Finset (SyntacticObject TokenLeaf) :=
  (Finset.univ.filter fun g ↦ ∃ a, t.termAt a = h ∧
    p.Finds {q | t.toRoseTree.CCommands a q} key g).image t.termAt

theorem mem_goalsBy {h x : SyntacticObject TokenLeaf} {key : t.toRoseTree.Positions → β} :
    x ∈ t.goalsBy p h key ↔
      ∃ a, t.termAt a = h ∧ ∃ g, p.Finds {q | t.toRoseTree.CCommands a q} key g ∧ t.termAt g = x :=
          by
  simp only [goalsBy, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨g, ⟨a, ha, hg⟩, hx⟩ ↦ ⟨a, ha, g, hg, hx⟩,
    fun ⟨a, ha, g, hg, hx⟩ ↦ ⟨g, ⟨a, ha, hg⟩, hx⟩⟩

end Search

variable (t) in
/-- The terms a probe on the head `h` finds: those at the closest satisfying positions that an
occurrence of `h` c-commands. -/
def goals (p : Probe t.toRoseTree.Positions) (h : SyntacticObject TokenLeaf) : Finset
    (SyntacticObject TokenLeaf) :=
  t.goalsBy p h (t.above t.toRoseTree.branching)

theorem mem_goals {h x : SyntacticObject TokenLeaf} : x ∈ t.goals p h ↔
    ∃ a, t.termAt a = h ∧ ∃ g,
      p.Finds {q | t.toRoseTree.CCommands a q} (t.above t.toRoseTree.branching) g ∧
        t.termAt g = x :=
  mem_goalsBy

variable (t) in
/-- The probe satisfied by the leaves of category `c`. -/
def leafProbe (c : Cat) : Probe t.toRoseTree.Positions :=
  .relativized fun q ↦ decide (SyntacticObject.isLeafOf c (t.termAt q))

end PlanarSyntacticObject

end Minimalist
