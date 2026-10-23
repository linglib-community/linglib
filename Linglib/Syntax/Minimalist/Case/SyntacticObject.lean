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
`CaseAssigners.assignBy` over the phase heads innermost first, of which the list calculus is
another instance (`CaseAssigners.assign_eq_assignBy`).

## Main definitions

* `Minimalist.VisibleAt`, `Minimalist.SpelledOutAt`: an NP seen by a phase, and spelled out there.
* `Minimalist.CCommandsAt`, `Minimalist.ReachesAt`: c-command among the NPs of a phase, and the
  NPs a head reaches there.
* `Minimalist.projectingHeads`, `Minimalist.phaseHeads`: the heads that project, and the phase
  heads, deepest first.
* `Minimalist.CaseAssigners.probesAt`: the probes of a phase.
* `Minimalist.CaseAssigners.assignOn`: case for the NPs of an object.

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

/-- An NP is seen by the phase head at `h` when a copy of it stands in what `h` transfers. -/
def VisibleAt (tok : LexicalItem.Token) : Prop :=
  ∃ p ∈ chain t tok, projectionAt hd t p ∈ transferSlice Φ D h

/-- An NP is spelled out by the phase head at `h` when its pronounced copy stands in what `h`
transfers. -/
def SpelledOutAt (tok : LexicalItem.Token) : Prop :=
  ∃ p ∈ occurrences t tok, projectionAt hd t p ∈ transferSlice Φ D h

/-- In what `h` transfers, `x` c-commands `y` when a copy of `x` there asymmetrically c-commands a
copy of `y` there. -/
def CCommandsAt (x y : LexicalItem.Token) : Prop :=
  ∃ p ∈ chain t x, ∃ q ∈ chain t y,
    projectionAt hd t p ∈ transferSlice Φ D h ∧ projectionAt hd t q ∈ transferSlice Φ D h ∧
      t.val.CCommands (projectionAt hd t p) (projectionAt hd t q) ∧
      ¬ t.val.CCommands (projectionAt hd t q) (projectionAt hd t p)

/-- The head at `a` reaches an NP when it c-commands a copy of it standing in what `h`
transfers. -/
def ReachesAt (a : TreePath) (tok : LexicalItem.Token) : Prop :=
  ∃ p ∈ chain t tok,
    projectionAt hd t p ∈ transferSlice Φ D h ∧ t.val.CCommands a (projectionAt hd t p)

instance (tok : LexicalItem.Token) : Decidable (VisibleAt hd t Φ D h tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (tok : LexicalItem.Token) : Decidable (SpelledOutAt hd t Φ D h tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : DecidableRel (CCommandsAt hd t Φ D h) :=
  fun _ _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance (a : TreePath) (tok : LexicalItem.Token) : Decidable (ReachesAt hd t Φ D h a tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The heads of `t` that project, deepest first: the pronounced tokens heading their mothers. -/
def projectingHeads : List (TreePath × LexicalItem.Token) :=
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
phase head and `lex` the case lexical heads value. -/
def CaseAssigners.assignOn (g : CaseAssigners) (D : TreePath → Set TreePath)
    [∀ h, DecidablePred (· ∈ D h)] (IsPhaseHead : LexicalItem.Token → Prop)
    [DecidablePred IsPhaseHead] (lex : LexicalItem.Token → Option Case)
    (xs : List LexicalItem.Token) : Valuation LexicalItem.Token (Case × Mechanism) :=
  let Φ := ((phaseHeads hd t IsPhaseHead).map (·.1)).toFinset
  g.assignBy (fun x ↦ x.2.item.cat) (fun x tok ↦ decide (VisibleAt hd t Φ D x.1 tok))
    (fun x ↦ CCommandsAt hd t Φ D x.1) (fun x ↦ g.probesAt hd t Φ D x.1)
    (fun x tok ↦ decide (SpelledOutAt hd t Φ D x.1 tok)) (phaseHeads hd t IsPhaseHead)
    (lexicalValuation lex xs)

end Minimalist
