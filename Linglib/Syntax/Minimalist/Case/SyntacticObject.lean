/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Case.Dependent
public import Linglib.Syntax.Minimalist.Locality.Transfer

/-!
# Case on syntactic objects

Case is read off an object with traces, phase by phase. The domain of a phase head sees the NPs
with a copy in what it transfers on its own (`transferSlice`), ordered by asymmetric c-command
between those copies; its probes are the heads with an Agree case whose complement it transfers,
each reaching the copies it c-commands there; and its elsewhere case goes to the NPs whose
pronounced copy it transfers. An NP that shifts to the edge of a phase is thus seen by the phase
through its lower copy and by the next phase through its higher one, and `PhasedNP`, the order of
the NPs and the probes of a derivation are all read off the object. Assignment is
`assignBy` over the phase heads innermost first, of which the calculus over NPs placed by hand is
another instance by definition (`CaseAssigners.assign`).

## Main definitions

* `Minimalist.copiesAt`: the copies of an NP in what a phase transfers on its own.
* `Minimalist.VisibleAt`, `Minimalist.SpelledOutAt`: an NP seen by a phase, and spelled out there.
* `Minimalist.CCommandsAt`, `Minimalist.ReachesAt`: c-command among the NPs of a phase, and the
  NPs a head reaches there.
* `Minimalist.projectingHeads`, `Minimalist.phaseHeads`: the heads that project, and the phase
  heads, deepest first.
* `Minimalist.CaseAssigners.probesAt`: the probes of a phase.
* `Minimalist.CaseAssigners.assignOn`: case for the NPs of an object.

## Implementation notes

* Copies count wherever they stand, the representational reading Baker and Vinokurova mention in
  their note 6. They note that it needs copies in A-bar positions not to count (note 7): an
  object scrambled above the subject within one phase ((16), (17)) would otherwise make each the
  other's competitor. No such proviso is modelled.

## References

* [baker-vinokurova-2010]
* [baker-2015]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Minimalist

open Core.Order Case

variable (hd : HeadFunction) (t : LinearizedSyntacticObject) (Φ : Finset TreePath)
  (D : TreePath → Set TreePath) [∀ h, DecidablePred (· ∈ D h)] (h : TreePath)

/-- The copies of an NP standing in what the phase head at `h` transfers on its own, each at the
projection of its token. -/
def copiesAt (tok : LexicalItem.Token) : List TreePath :=
  ((chain t tok).map (projectionAt hd t)).filter (· ∈ transferSlice Φ D h)

/-- An NP is seen by the phase head at `h` when a copy of it stands in what `h` transfers. -/
def VisibleAt (tok : LexicalItem.Token) : Prop := copiesAt hd t Φ D h tok ≠ []

/-- An NP is spelled out by the phase head at `h` when its pronounced copy stands in what `h`
transfers. -/
def SpelledOutAt (tok : LexicalItem.Token) : Prop :=
  ∃ p ∈ occurrences t tok, projectionAt hd t p ∈ transferSlice Φ D h

/-- In what `h` transfers, `x` c-commands `y` when a copy of `x` there asymmetrically c-commands a
copy of `y` there. -/
def CCommandsAt (x y : LexicalItem.Token) : Prop :=
  ∃ p ∈ copiesAt hd t Φ D h x, ∃ q ∈ copiesAt hd t Φ D h y,
    t.val.CCommands p q ∧ ¬ t.val.CCommands q p

/-- The head at `a` reaches an NP when it c-commands a copy of it standing in what `h`
transfers. -/
def ReachesAt (a : TreePath) (tok : LexicalItem.Token) : Prop :=
  ∃ p ∈ copiesAt hd t Φ D h tok, t.val.CCommands a p

instance (tok : LexicalItem.Token) : Decidable (VisibleAt hd t Φ D h tok) :=
  inferInstanceAs (Decidable (_ ≠ _))

instance (tok : LexicalItem.Token) : Decidable (SpelledOutAt hd t Φ D h tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : DecidableRel (CCommandsAt hd t Φ D h) :=
  fun _ _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (a : TreePath) (tok : LexicalItem.Token) : Decidable (ReachesAt hd t Φ D h a tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The heads of `t` that project, deepest first: the pronounced tokens heading their mothers. -/
def projectingHeads : List (TreePath × LexicalItem.Token) :=
  -- Sorted by bucketing on depth: `List.insertionSort` does not unfold under `decide +kernel` in
  -- a module file, which the studies' checks run in.
  (List.range t.val.numNodes).reverse.flatMap fun n ↦
    (tokenList t.val).filter fun x ↦ x.1.toList.length == n && projectionAt hd t x.1 != x.1

/-- The probes of the phase head at `h`: the heads with an Agree case whose complement it
transfers, deepest first, each with its case and the NPs it reaches. -/
def CaseAssigners.probesAt (g : CaseAssigners) : List (Case × (LexicalItem.Token → Bool)) :=
  (projectingHeads hd t).filterMap fun x ↦ (g.agreeCase x.2.item.cat).bind fun k ↦
    if complement x.1 ∈ transferSlice Φ D h then
      some (k, fun tok ↦ decide (ReachesAt hd t Φ D h x.1 tok))
    else none

/-- The phase heads of `t` with their positions, innermost first. -/
def phaseHeads (IsPhaseHead : LexicalItem.Token → Prop) [DecidablePred IsPhaseHead] :
    List (TreePath × LexicalItem.Token) :=
  (projectingHeads hd t).filter fun x ↦ decide (IsPhaseHead x.2)

/-- Case for the NPs `xs` of `t`, phase by phase innermost first, `D` giving the domain of each
phase head and `case` the case slot each NP enters with. -/
def CaseAssigners.assignOn (g : CaseAssigners) (D : TreePath → Set TreePath)
    [∀ h, DecidablePred (· ∈ D h)] (IsPhaseHead : LexicalItem.Token → Prop)
    [DecidablePred IsPhaseHead] (case : LexicalItem.Token → FeatureSlot Case)
    (xs : List LexicalItem.Token) : Valuation LexicalItem.Token (Case × Mechanism) :=
  let ph := phaseHeads hd t IsPhaseHead
  let Φ := (ph.map (·.1)).toFinset
  assignBy (fun x ↦ g.rules x.2.item.cat) (fun x tok ↦ VisibleAt hd t Φ D x.1 tok)
    (fun x p q ↦ CCommandsAt hd t Φ D x.1 p.2 q.2) (fun x ↦ CCommandsAt hd t Φ D x.1)
    (fun x ↦ g.probesAt hd t Φ D x.1) (fun x tok ↦ SpelledOutAt hd t Φ D x.1 tok) ph
    (slotValuation case xs)

end Minimalist
