module

public import Linglib.Syntax.Voice.Basic

/-!
# The action of a voice on a diathesis

A voice relates an initial and a derived diathesis of its own participants
(`Syntax/Voice/Basic.lean`). Read as a map of slots, `Voice.image`, it acts on any diathesis of
any verb: `d.relink τ gr` is the diathesis of frame `gr` in which a participant at slot `s` is at
`τ s`, and leaves the construction if `τ` sends `s` nowhere, and `v.apply d` relinks `d` along
`v.image` into the derived frame of `v`. The three ways a relinking can change a diathesis are
the three modifications of [melcuk-1993]: a permutation of slots, the suppression of a slot, and
the identification of two. `d.restrict Open` suppresses the slots whose position is not `Open`,
the frame unchanged: which positions hold arguments of the verb's relation, as against modifiers
and understood participants, is a choice theories make differently.

## Implementation notes

A control dependency names its complement by index, so `relink` moves the slot depended on and
the complement together and drops the dependency when the complement stops being a complement,
as when a passive makes a clause the subject.

## References

* [melcuk-1993]
* [creissels-2024]
-/

@[expose] public section

open ArgumentFrame (Slot)

/-- The diathesis of frame `gr` whose participants are moved along `τ`, a participant at a slot
`τ` sends nowhere leaving the construction. -/
def Diathesis.relink {n : ℕ} (τ : Slot → Option Slot) (gr : ArgumentFrame) (d : Diathesis n) :
    Diathesis n :=
  { gr with
    links := d.links.map (·.bind τ)
    control := d.control.filterMap fun p ↦
      (τ p.1).bind fun s ↦ match τ (.complement p.2) with
        | some (.complement j) => some (s, j)
        | _ => none
    form := d.form }

@[simp] theorem Diathesis.get_links_relink {n : ℕ} (τ : Slot → Option Slot) (gr : ArgumentFrame)
    (d : Diathesis n) (i : Fin n) : (d.relink τ gr).links.get i = (d.links.get i).bind τ := by
  simp [Diathesis.relink, Vector.get]

/-- The diathesis of the same frame in which only the participants at positions that are `Open`
are linked. -/
def Diathesis.restrict {n : ℕ} (Open : ArgumentFrame.Position → Prop) [DecidablePred Open]
    (d : Diathesis n) : Diathesis n :=
  d.relink (fun s ↦ if ∃ p ∈ d.get? s, Open p then some s else none) d.toArgumentFrame

/-- The diathesis a voice derives from `d`: `d` relinked along the voice's image of each slot. -/
def Voice.apply (v : Voice) {n : ℕ} (d : Diathesis n) : Diathesis n :=
  d.relink v.image v.derived.toArgumentFrame
