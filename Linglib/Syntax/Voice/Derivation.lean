module

public import Linglib.Syntax.Voice.Basic

/-!
# Voice derivations

A derivation applies voices one after another to a clause's participants. A `Stage` records
where each participant sits in the current frame, the referential dependencies established and
the agreements registered so far; applying a voice moves each participant to the slot its own
corresponds to (`Voice.image`), suppresses those without one, lets a fresh participant into the
slot the voice adds (`Voice.newSlots`) and links a subject the voice cumulates
(`Voice.fate`) to each participant cumulated with it. Agreement registers the participants in
the subject slot, the pivot of the frame.

The single-process architecture of [baker-1985] §6 reads a word's morphology and its
grammatical functions off one such sequence, and [hyman-2003] separates the two again for
Bantu, where the syntactic derivation is read off scope while the affix order is templatic.

## Main definitions

* `Voice.Stage` — participants at the slots of a frame, with links and registrations.
* `Voice.Stage.subjects`, `Stage.apply`, `Stage.agree` — the subject participants, the stage a
  voice derives, and agreement registration.

## Main results

* `Voice.Stage.registered_agree_apply`, `registered_apply_agree` — agreement before a voice
  registers the subject before it applied, agreement after it the subject after.

## References

* [baker-1985]
* [hyman-2003]
-/

@[expose] public section

namespace Voice

open ArgumentFrame (Slot)

/-- A derivational stage over participants `α` records the current frame, the slot each
participant occupies, the referential dependencies established and the agreements registered so
far. -/
structure Stage (α : Type*) where
  /-- The current frame. -/
  frame : ArgumentFrame
  /-- The slot each participant occupies. -/
  slots : List (α × Slot)
  /-- The referential dependencies established, a subject with each participant bound to it. -/
  links : List (α × α) := []
  /-- The participants agreement has registered, in order. -/
  registered : List α := []
  deriving DecidableEq, Repr

namespace Stage

variable {α : Type*} (s : Stage α)

/-- The participants in the subject slot, the pivot of the frame. -/
def subjects : List α :=
  (s.slots.filter fun p ↦ some p.2 = s.frame.coreSlots.head?).map (·.1)

/-- In the stage a voice derives, each participant moves to the slot its own corresponds to or
is suppressed if none, a fresh participant enters the first slot the voice adds, and a subject
the voice cumulates is linked to each participant cumulated with it. -/
def apply (v : Voice) (fresh : Option α) : Stage α where
  frame := v.derived.toArgumentFrame
  slots := (fresh.bind fun a ↦ v.newSlots.head?.map (a, ·)).toList ++
    s.slots.filterMap fun p ↦ (v.image p.2).map (p.1, ·)
  links := s.links ++ s.slots.flatMap fun p ↦
    if some p.2 = s.frame.coreSlots.head? ∧ v.fate p.2 = .cumulated then
      s.slots.filterMap fun q ↦
        if q.2 ≠ p.2 ∧ v.image q.2 = v.image p.2 then some (p.1, q.1) else none
    else []
  registered := s.registered

/-- Agreement registers the subject. -/
def agree : Stage α := { s with registered := s.registered ++ s.subjects }

@[simp] theorem frame_apply (v : Voice) (a : Option α) :
    (s.apply v a).frame = v.derived.toArgumentFrame := rfl

@[simp] theorem registered_apply (v : Voice) (a : Option α) :
    (s.apply v a).registered = s.registered := rfl

@[simp] theorem frame_agree : s.agree.frame = s.frame := rfl

@[simp] theorem slots_agree : s.agree.slots = s.slots := rfl

@[simp] theorem registered_agree : s.agree.registered = s.registered ++ s.subjects := rfl

@[simp] theorem subjects_agree : s.agree.subjects = s.subjects := rfl

theorem registered_agree_apply (v : Voice) (a : Option α) :
    (s.agree.apply v a).registered = s.registered ++ s.subjects := rfl

theorem registered_apply_agree (v : Voice) (a : Option α) :
    (s.apply v a).agree.registered = s.registered ++ (s.apply v a).subjects := rfl

end Stage

end Voice
