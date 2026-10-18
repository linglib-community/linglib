/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole

/-!
# Larson (1988): On the Double Object Construction

This file formalizes the analysis of [larson-1988]: a ditransitive verb projects a VP shell, the
oblique dative *send a letter to Mary* is built by merging the *to*-phrase as the complement
and the theme as the inner specifier, and the double object construction is derived from it by
the operation of Passive applied within the VP, an internal merge of the indirect object above
the theme. The derivations are `Derivation`s whose movement steps are the same
internal-merge step as the clausal passive, and the c-command relations of the resulting trees
give the asymmetries of [barss-lasnik-1986]: in the oblique dative the theme c-commands the goal
(`oblique_do_ccommands_goal`), in the double object construction the indirect object
c-commands the theme and not conversely (`doc_io_ccommands_do`, `doc_do_not_ccommands_io`),
as the promoted object c-commands the demoted subject of a passive. Dative shift is subject to
recoverability: the content of *to* must be recoverable from the verb's own assignment of a goal
role (`recoverable`), which separates *give* and *send* from *donate* and *contribute*. The
indirect passive *Mary was sent a letter* is derived by dative shift followed by passive.

## Implementation notes

The oblique dative and dative shift are the paper's second and third sections, the indirect
passive its fourth, and recoverability the second part of its fifth. The head movement of the verb
from the inner to the outer shell is not modelled, since the c-command facts depend only on the
positions of the arguments; each derivation is paired with the planar tree it produces, on which
c-command is decided. The recoverability entries record the roles the paper assigns to each
verb's indirect object.

## References

* [larson-1988]
* [barss-lasnik-1986]
-/

@[expose] public section

open ArgumentStructure

namespace Larson1988

open Minimalist SyntacticObject
open RoseTree UnorderedTree

/-! ### Lexical items -/

def V_send    := mkLeafPhon .V [.D]  "send"     300
def P_to      := mkLeafPhon .P [.D]  "to"       301
def DP_john   := mkLeafPhon .D []    "John"     302
def DP_mary   := mkLeafPhon .D []    "Mary"     303
def DP_letter := mkLeafPhon .D []    "a letter" 304

def V_kick    := mkLeafPhon .V [.D]  "kicked"   310
def DP_ball   := mkLeafPhon .D []    "the ball" 311

/-! The planar tokens of the result trees on which c-command is decided. -/

def tok_send   : LexicalItem.Token := ⟨.of .V [.D] (phonForm := "send"), 300⟩
def tok_to     : LexicalItem.Token := ⟨.of .P [.D] (phonForm := "to"), 301⟩
def tok_john   : LexicalItem.Token := ⟨.of .D [] (phonForm := "John"), 302⟩
def tok_mary   : LexicalItem.Token := ⟨.of .D [] (phonForm := "Mary"), 303⟩
def tok_letter : LexicalItem.Token := ⟨.of .D [] (phonForm := "a letter"), 304⟩
def tok_kick   : LexicalItem.Token := ⟨.of .V [.D] (phonForm := "kicked"), 310⟩
def tok_ball   : LexicalItem.Token := ⟨.of .D [] (phonForm := "the ball"), 311⟩

/-- The constituent *to Mary*. -/
def ppToMaryP : PlanarSyntacticObject := tok_to * tok_mary

/-! ### The oblique dative

*John sent a letter to Mary*: the *to*-phrase is merged as the complement, the theme as the
inner specifier, and the agent as the outer specifier, so the theme c-commands the goal, which
is buried in the prepositional phrase. -/

def obliqueDative : Derivation :=
  { initial := V_send
    steps := [
      .em .right ppToMaryP,
      .em .left DP_letter,
      .em .left DP_john
    ] }

/-- The oblique dative's tree, `[John [a letter [send [to Mary]]]]`. -/
def obliqueDativeTree : PlanarSyntacticObject :=
  tok_john * (tok_letter * (tok_send * ppToMaryP))

theorem oblique_do_ccommands_goal :
    CCommands obliqueDativeTree DP_letter DP_mary := by decide

theorem oblique_goal_not_ccommands_do :
    ¬ CCommands obliqueDativeTree DP_mary DP_letter := by decide

/-! ### Dative shift

*John sent Mary a letter* extends the oblique dative by one step, the internal merge of the
indirect object from inside the *to*-phrase to the edge of the inner shell, the operation of
Passive within the VP. The indirect object thereby comes to c-command the theme, which gives the
six asymmetries of [barss-lasnik-1986]: anaphor binding, quantifier–pronoun binding, weak
crossover, superiority, *each … the other*, and negative polarity licensing. -/

def docDativeShift : Derivation :=
  { initial := V_send
    steps := [
      .em .right ppToMaryP,
      .em .left DP_letter,
      .im DP_mary,
      .em .left DP_john
    ] }

/-- The double object construction's tree, `[John [Mary [a letter [send [to t]]]]]`. -/
def docDativeShiftTree : PlanarSyntacticObject :=
  tok_john * (tok_mary * (tok_letter * (tok_send * (tok_to * PlanarSyntacticObject.trace))))

/-- In the double object construction the indirect object c-commands the theme. -/
theorem doc_io_ccommands_do :
    CCommands docDativeShiftTree DP_mary DP_letter := by decide

/-- And the theme does not c-command the indirect object. -/
theorem doc_do_not_ccommands_io :
    ¬ CCommands docDativeShiftTree DP_letter DP_mary := by decide

/-- Dative shift is one internal merge, of the indirect object. -/
theorem dativeShift_has_one_im :
    docDativeShift.movedItems = [DP_mary] := by decide

/-! ### Passive

*The ball was kicked by John* is the same internal-merge step applied in the clausal domain:
the object is promoted above the subject. -/

def standardPassive : Derivation :=
  { initial := V_kick
    steps := [
      .em .right DP_ball,
      .em .left DP_john,
      .im DP_ball
    ] }

/-- The passive's tree, `[the ball [John [kicked t]]]`. -/
def standardPassiveTree : PlanarSyntacticObject :=
  tok_ball * (tok_john * (tok_kick * PlanarSyntacticObject.trace))

theorem passive_object_ccommands_subject :
    CCommands standardPassiveTree DP_ball DP_john := by decide

theorem passive_subject_not_ccommands_object :
    ¬ CCommands standardPassiveTree DP_john DP_ball := by decide

/-- Passive is one internal merge, of the object. -/
theorem passive_has_one_im :
    standardPassive.movedItems = [DP_ball] := by decide

/-! ### Recoverability (§5.2)

Dative shift requires the content of *to* to be recoverable from the verb: both the verb and
*to* assign a role to the indirect object, and when the verb's roles include the goal role that
*to* contributes, *to* reduces to a case marker that Passive can absorb; a verb that assigns
only a beneficiary role leaves *to*'s contribution unrecoverable, and dative shift is blocked.
-/

/-- A dative verb with the roles it assigns to its indirect object. -/
structure DativeVerbEntry where
  verb : String
  ioRoles : List ThetaRole
  deriving Repr, BEq

/-- The role *to* contributes. -/
def toRole : ThetaRole := .goal

/-- The verb's roles subsume the contribution of *to*. -/
def recoverable (e : DativeVerbEntry) : Bool := e.ioRoles.contains toRole

def give_entry : DativeVerbEntry := { verb := "give", ioRoles := [.goal] }
def send_entry : DativeVerbEntry := { verb := "send", ioRoles := [.goal] }
def promise_entry : DativeVerbEntry := { verb := "promise", ioRoles := [.goal] }
/-- *I donated money to charity*, not *I donated charity money*. -/
def donate_entry : DativeVerbEntry := { verb := "donate", ioRoles := [] }
def distribute_entry : DativeVerbEntry := { verb := "distribute", ioRoles := [] }
def contribute_entry : DativeVerbEntry := { verb := "contribute", ioRoles := [] }

def allDativeVerbs : List DativeVerbEntry :=
  [give_entry, send_entry, promise_entry, donate_entry, distribute_entry, contribute_entry]

/-- *give*, *send*, and *promise* assign a goal and shift; *donate*, *distribute*, and
*contribute* do not. -/
theorem recoverability :
    recoverable give_entry = true ∧ recoverable send_entry = true ∧
      recoverable promise_entry = true ∧ recoverable donate_entry = false ∧
      recoverable distribute_entry = false ∧ recoverable contribute_entry = false := by
  decide

/-! ### The indirect passive (§4)

*Mary was sent a letter* promotes the indirect object to subject: dative shift followed by
passive, each an internal merge leaving a trace, so the promoted indirect object c-commands the
stranded theme. -/

def V_sent     := mkLeafPhon .V [.D]  "was-sent" 320
def DP_mary2   := mkLeafPhon .D []    "Mary"     321
def DP_letter2 := mkLeafPhon .D []    "a letter" 322
def P_to2      := mkLeafPhon .P [.D]  "to"       323

def tok_sent    : LexicalItem.Token := ⟨.of .V [.D] (phonForm := "was-sent"), 320⟩
def tok_mary2   : LexicalItem.Token := ⟨.of .D [] (phonForm := "Mary"), 321⟩
def tok_letter2 : LexicalItem.Token := ⟨.of .D [] (phonForm := "a letter"), 322⟩
def tok_to2     : LexicalItem.Token := ⟨.of .P [.D] (phonForm := "to"), 323⟩

def indirectPassive : Derivation :=
  { initial := V_sent
    steps := [
      .em .right (tok_to2 * tok_mary2 : PlanarSyntacticObject),
      .em .left DP_letter2,
      .im DP_mary2,
      .im DP_mary2
    ] }

/-- The indirect passive's tree, `[Mary [t [a letter [sent [to t]]]]]`, with a trace at each
extraction site. -/
def indirectPassiveTree : PlanarSyntacticObject :=
  tok_mary2 * (PlanarSyntacticObject.trace * (tok_letter2 * (tok_sent * (tok_to2 *
    PlanarSyntacticObject.trace))))

theorem indirect_passive_io_ccommands_do :
    CCommands indirectPassiveTree DP_mary2 DP_letter2 := by decide

/-- The indirect passive is two internal merges. -/
theorem indirect_passive_two_im :
    indirectPassive.movedItems.length = 2 := by decide

end Larson1988
