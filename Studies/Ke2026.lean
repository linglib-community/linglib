module

public import Linglib.Data.Examples.Ke2026
public import Linglib.Syntax.Minimalist.Linearization.SpelloutDomain
public import Linglib.Syntax.Minimalist.Locality.Transfer

/-!
# Ke (2026): The domain of transfer

Ke argues that Transfer applies to whole phases, edge included, once they are complete, rather
than to the complement of a phase head, and that a phase may wait to be transferred until the next
phase is complete, by which time what it contains with unvalued features has moved out. Full-phase
transfer at completion would trap a phrase at the edge of vP (`edge_trapped_at_completion`), but
with the delay it does not (`transfer_after_next_phase`). The edge effects of successive-cyclic
movement then come not from Transfer, which a phrase skipping the edge of vP obeys
(`skip_obeys_transfer`), but from Fox and Pesetsky's preservation of spell-out order, which only
movement through every edge satisfies (`ex13`), and only when whole phases are spelled out
(`complement_spellout_fails`).

## Implementation notes

* The phase heads are v and C. The clause of (13) is built without T-to-C movement, and nominals
  and the wh-phrase are single heads.
* Spell-out order preservation is the consistency of the derivation's spell-outs
  (`Minimalist.Derivation.Linearizes`). A whole phase is spelled out when it is complete
  (`Minimalist.Derivation.phaseSchedule`), a complement when its phase head merges.
* Transfer is read off the chains of the derived object, a link failing when its lower copy lies in
  a domain transferred by the stage it lands at.

## TODO

* The feature criterion (8), under which a transferred phase crashes if it contains an unvalued
  feature other than on a lower copy, and which makes the delay the only route for a successful
  derivation.
* Head movement across a phase boundary (14)–(15), and the problems of Table 35.1 beyond the
  domain and timing of transfer and the edge effects.

## References

* [ke-2026]
* [fox-pesetsky-2005]
* [chomsky-2000]
* [chomsky-2001]
-/

@[expose] public section

namespace Ke2026

open Core.Order Minimalist

/-! ### The derivation of (13) -/

def toWhom : LexicalItem.Token := ⟨.of .P [] "to whom", 1⟩
def gave : LexicalItem.Token := ⟨.of .V [.D, .P] "gave", 2⟩
def book : LexicalItem.Token := ⟨.of .D [] "the book", 3⟩
def v₁ : LexicalItem.Token := ⟨.of .v [.V], 4⟩
def mary : LexicalItem.Token := ⟨.of .D [] "Mary", 5⟩
def t₁ : LexicalItem.Token := ⟨.of .T [.v], 6⟩
def that : LexicalItem.Token := ⟨.of .C [.T] "that", 7⟩
def say : LexicalItem.Token := ⟨.of .V [.C] "say", 8⟩
def v₂ : LexicalItem.Token := ⟨.of .v [.V], 9⟩
def he : LexicalItem.Token := ⟨.of .D [] "he", 10⟩
def will : LexicalItem.Token := ⟨.of .T [.v] "will", 11⟩
def cQ : LexicalItem.Token := ⟨.of .C [.T], 12⟩

/-- Whether *to whom* stops at the edge of vP₁ on its way to the edge of CP₁. -/
inductive Route
  | edge | skip
  deriving DecidableEq, Fintype

/-- The derivation of (13): *to whom*, raised through the edges of the phases, the edge of vP₁
only on the first route. -/
def derivation (r : Route) : Derivation :=
  ⟨gave, [.em .right book, .em .right toWhom, .em .left v₁, .em .left mary] ++
    (match r with | .edge => [.im toWhom] | .skip => []) ++
    [.em .left t₁, .im mary, .em .left that, .im toWhom, .em .left say, .em .left v₂,
      .em .left he, .im toWhom, .em .left will, .im he, .em .left cQ, .im toWhom]⟩

/-- The phase heads, v and C. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop := a.item.cat = .v ∨ a.item.cat = .C

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-! ### Spell-out order preservation -/

/-- The schedule that spells a complement out when its phase head merges, the complement being the
object built just before. -/
def complementSchedule (d : Derivation) : List (ℕ × ℕ) :=
  (List.range d.length).filterMap fun i ↦ match (d.steps[i]? : Option Step) with
    | some (.em _ x) =>
      if (tokenList x.val).any fun y ↦ decide (y.1 = ⊥ ∧ IsPhaseHead y.2) then some (i, i + 1)
      else none
    | _ => none

/-- (13): spelling whole phases out when they are complete, the derivation through the edge of vP₁
preserves its spell-out order, and the one that skips it, which spells *gave* out before *to whom*
in vP₁ and after it in CP₁, does not. -/
theorem ex13 : (derivation .edge).Linearizes ((derivation .edge).phaseSchedule IsPhaseHead) ∧
    ¬ (derivation .skip).Linearizes ((derivation .skip).phaseSchedule IsPhaseHead) ∧
    (Examples.ex13.judgment = .acceptable ↔
      ∃ r, (derivation r).Linearizes ((derivation r).phaseSchedule IsPhaseHead)) := by
  decide +kernel

/-- Spelling complements out instead, even the derivation through every edge reverses an order:
the complement of v₁ spells *the book* out before *to whom*, that of C₁ after it. -/
theorem complement_spellout_fails :
    ¬ (derivation .edge).Linearizes (complementSchedule (derivation .edge)) := by
  decide +kernel

/-! ### The domain and timing of Transfer -/

/-- Ke's schedule: the domain of `h` is transferred once a phase containing the phase of `h` in its
complement is complete. -/
def AfterNextPhase (t : LinearizedSyntacticObject) : Schedule :=
  fun Φ h s ↦ ∃ z ∈ Φ, complement z ≤ projectionAt t h ∧ s < projectionAt t z

instance (t : LinearizedSyntacticObject) (Φ : Finset TreePath) (h s : TreePath) :
    Decidable (AfterNextPhase t Φ h s) :=
  inferInstanceAs (Decidable (∃ _ ∈ Φ, _))

/-- No link of a chain in the object a derivation derives leaves a domain `D` of its phase heads
transferred under the schedule `σ`. -/
def ObeysTransfer (d : Derivation) (D : LinearizedSyntacticObject → TreePath → Set TreePath)
    [∀ t h, DecidablePred (· ∈ D t h)] (σ : LinearizedSyntacticObject → Schedule)
    [∀ t Φ h s, Decidable (σ t Φ h s)] : Prop :=
  ∀ t ∈ d.externalize?, ∀ y ∈ tokenList t.val,
    ¬ LinkLeaves t y.2 (sealed (occurrencesWith t IsPhaseHead).toFinset (D t) (σ t))

instance (d : Derivation) (D : LinearizedSyntacticObject → TreePath → Set TreePath)
    [∀ t h, DecidablePred (· ∈ D t h)] (σ : LinearizedSyntacticObject → Schedule)
    [∀ t Φ h s, Decidable (σ t Φ h s)] : Decidable (ObeysTransfer d D σ) := by
  unfold ObeysTransfer; infer_instance

/-- Transferred whole as soon as it is complete, vP₁ traps *to whom* and *Mary* at its edge (2b). -/
theorem edge_trapped_at_completion :
    ¬ ObeysTransfer (derivation .edge) wholePhaseDomain Pic1 := by
  decide +kernel

/-- Transferred whole once the next phase is complete, the phases let what moves through their
edges out, as the transfer of complements does. -/
theorem transfer_after_next_phase :
    ObeysTransfer (derivation .edge) wholePhaseDomain AfterNextPhase ∧
      ObeysTransfer (derivation .edge) (complementDomain · ∅) Pic1 := by
  decide +kernel

/-- Skipping the edge of vP₁ is no violation of full-phase transfer, though it is one of the
transfer of complements: under full-phase transfer the edge effects are spell-out order's alone. -/
theorem skip_obeys_transfer :
    ObeysTransfer (derivation .skip) wholePhaseDomain AfterNextPhase ∧
      ¬ ObeysTransfer (derivation .skip) (complementDomain · ∅) Pic1 := by
  decide +kernel

end Ke2026
