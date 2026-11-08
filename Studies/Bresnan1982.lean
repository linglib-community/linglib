module

public import Linglib.Fragments.English.Verbs.Inventory

/-!
# Bresnan (1982): Control and complementation

Bresnan distinguishes the open complements, whose subject is that of a function of the matrix
under functional control, from the closed complements, which have a subject of their own. Which
function controls an open complement is predictable: by her Lexical Rule of Functional Control it
is the second object if there is one, else the object, else the subject, and [every control and
raising verb of the English fragment follows the rule but *promise*](##lexicalRule_verbs). Only
the semantically unrestricted functions control, or go unfilled under raising, [as every diathesis
of the fragment bears out](##controllerSlot_mem_coreSlots).

## Implementation notes

* A diathesis records the slot a complement's subject depends on (`Diathesis.control`) and
  whether a participant fills it, under equi, or none does, under raising. The subject, object and
  second object are the frame's core slots (`ArgumentFrame.coreSlots`), its objects in the order of
  its complements. That the dependent is unpronounced in an open complement, as English's are, is
  the fragment's record of its subject (`English.Verbs.toInfinitive`).
* The control of adjuncts, which c-structure induces, and anaphoric control, of a closed
  complement's own unexpressed subject, are not encoded: the fragment's open complements are all
  lexically controlled.

## References

* [bresnan-1982]
-/

@[expose] public section

namespace Bresnan1982

open ArgumentFrame (Slot)
open English.Verbs (verbs promise)

/-- The controller the Lexical Rule of Functional Control, (20) on p. 376, predicts for an open
complement: the frame's second object if it has one, else its object, else its subject. -/
def unmarkedController (fr : ArgumentFrame) : Slot :=
  (fr.coreObjects[1]?.orElse fun _ ↦ fr.coreObjects[0]?).getD .external

/-- A diathesis follows the rule when the slot controlling its open complement, if it has one, is
the slot the rule predicts. -/
def FollowsLexicalRule {n : ℕ} (d : Diathesis n) : Prop :=
  ∀ s ∈ d.controllerSlot?, s = unmarkedController d.toArgumentFrame

instance {n : ℕ} (d : Diathesis n) : Decidable (FollowsLexicalRule d) :=
  inferInstanceAs (Decidable (∀ s ∈ d.controllerSlot?, _))

/-- The Lexical Rule of Functional Control holds of every verb of the English fragment but
*promise*, whose subject controls the infinitive across its object. -/
theorem lexicalRule_verbs :
    (∀ v ∈ verbs, (∀ d ∈ v.valency.diatheses, FollowsLexicalRule d) ∨
        v.morphs = promise.morphs) ∧
      ¬ ∀ d ∈ promise.valency.diatheses, FollowsLexicalRule d := by
  decide +kernel

/-- Only the semantically unrestricted functions, subject, object and second object, are
functional controllers (p. 376) or go unpaired with an argument (p. 352): the slot controlling an
open complement of the fragment is always a core one. -/
theorem controllerSlot_mem_coreSlots :
    ∀ v ∈ verbs, ∀ d ∈ v.valency.diatheses, ∀ s ∈ d.controllerSlot?, s ∈ d.coreSlots := by
  decide +kernel

end Bresnan1982
