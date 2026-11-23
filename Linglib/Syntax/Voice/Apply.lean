module

public import Linglib.Syntax.Voice.Basic

/-!
# The action of a voice on a diathesis

A diathesis links the participants of a verb to the slots of a frame. This file defines how a map
of slots changes a diathesis.

For `τ : Slot → Option Slot` and a frame `gr`, we define `d.relink τ gr`. It is the diathesis of
frame `gr` in which a participant that `d` puts at slot `s` is at slot `τ s`. If `τ s = none`, the
participant is at no slot. A map `τ` can permute slots, send a slot to `none`, or send two slots to
one. These are the three modifications of a diathesis in [melcuk-1993].

We define two special cases.

* `v.apply d` relinks `d` along `v.image`, the map of slots of the voice `v`, into the derived
  frame of `v`.
* `d.restrict Open` keeps the frame of `d` and unlinks every participant whose position does not
  satisfy `Open`.

## Implementation notes

* A control dependency in a `Diathesis` names its clausal complement by index. So `relink` maps
  both the slot depended on and the complement. It drops the dependency when the complement is
  no longer a complement, as when a passive makes a clause the subject.
* `restrict` takes `Open` as an argument because theories differ on which positions hold
  arguments of the verb's relation.

## References

* [melcuk-1993]
* [creissels-2024]
-/

@[expose] public section

open ArgumentFrame (Slot)

/-- The diathesis of frame `gr` in which a participant that `d` puts at slot `s` is at slot
`τ s`, and at no slot if `τ s = none`. -/
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

/-- The diathesis with the frame of `d` in which a participant keeps its slot only if its
position satisfies `Open`. -/
def Diathesis.restrict {n : ℕ} (Open : ArgumentFrame.Position → Prop) [DecidablePred Open]
    (d : Diathesis n) : Diathesis n :=
  d.relink (fun s ↦ if ∃ p ∈ d.get? s, Open p then some s else none) d.toArgumentFrame

/-- The diathesis that the voice `v` derives from `d`. -/
def Voice.apply (v : Voice) {n : ℕ} (d : Diathesis n) : Diathesis n :=
  d.relink v.image v.derived.toArgumentFrame
