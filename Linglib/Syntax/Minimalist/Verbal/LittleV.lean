/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Chain

/-!
# Little v

[cuervo-2003]'s event introducers: the three flavors of little v that verbalize a root and fix
its event type. `vDO` builds activities, `vGO` events of change, movement and happening, `vBE`
states. A sentence's event structure is the list of its verbal heads from the highest down, and a
complex structure embeds one vP under another.

Causatives and inchoatives are the two complex structures: an event or state embedded under
`vDO`, and a state embedded under `vGO`. There is no CAUSE head: "being causative is the
property of the configuration as a whole", and the two alternants of *cerrar* share the lower
stative event and differ in the dynamic head that embeds it, `[vDO, vBE]` against `[vGO, vBE]`.
Only a `vDO`-headed structure combines with Voice and so licenses an external argument.

## Main definitions

* `LittleV`
* `LittleV.Causative`, `LittleV.Inchoative`, `LittleV.LicensesVoice`

## Main results

* `LittleV.Causative.not_inchoative`: causatives do not include inchoatives
* `LittleV.causative_cons`, `LittleV.inchoative_cons`: the alternation over a shared lower event

## Implementation notes

The head-driven rivals, [pylkkanen-2008]'s Cause head and the v_CAUSE that
[alexiadou-anagnostopoulou-schaefer-2006] and [wood-2015] keep in both alternants so that Voice
alone distinguishes them, are not encodable here: every `Causative` is `BiEventive`, and the
alternation changes the higher head rather than Voice (`Causative.not_inchoative`). A study of
those programs states its claims about `Minimalist.Voice` directly.

## References

* [cuervo-2003]
* [alexiadou-anagnostopoulou-schaefer-2006]
* [pylkkanen-2008]
* [wood-2015]
-/

@[expose] public section

namespace Minimalist

/-- [cuervo-2003]'s flavors of v, the event introducers that verbalize a root. -/
inductive LittleV where
  /-- Dynamic activity: the root names a manner of acting; the only head Voice combines with. -/
  | vDO
  /-- Dynamic change, movement or happening; unaccusative. -/
  | vGO
  /-- State; unaccusative. -/
  | vBE
  deriving DecidableEq, Repr

namespace LittleV

variable {l lower : List LittleV} {v w : LittleV}

/-- Dynamic heads, `vDO` and `vGO`, against stative `vBE`. -/
def Dynamic (v : LittleV) : Prop := v ≠ .vBE

instance : DecidablePred Dynamic := fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-! ### Event types ([cuervo-2003] §1.3) -/

/-- A complex, bi-eventive event: at least two sub-events. -/
def BiEventive (l : List LittleV) : Prop := 2 ≤ l.length

/-- A causative: an event or result embedded under `vDO`; the causative reading is the
    interpretation of this configuration, not of a CAUSE head. -/
def Causative (l : List LittleV) : Prop := l.head? = some .vDO ∧ BiEventive l

/-- An inchoative: a result embedded under `vGO`. -/
def Inchoative (l : List LittleV) : Prop := l.head? = some .vGO ∧ BiEventive l

/-- Combines with Voice, and so licenses an external argument: `vDO`-headed structures only,
    predicates of change and states being unaccusative. -/
def LicensesVoice (l : List LittleV) : Prop := l.head? = some .vDO

instance : DecidablePred BiEventive := fun _ => inferInstanceAs (Decidable (_ ≤ _))
instance : DecidablePred Causative := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred Inchoative := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred LicensesVoice := fun _ => inferInstanceAs (Decidable (_ = _))

theorem Causative.biEventive (h : Causative l) : BiEventive l := h.2

theorem Inchoative.biEventive (h : Inchoative l) : BiEventive l := h.2

theorem Causative.licensesVoice (h : Causative l) : LicensesVoice l := h.1

theorem Inchoative.not_licensesVoice (h : Inchoative l) : ¬ LicensesVoice l :=
  fun h' => by simp [LicensesVoice, h.1] at h'

/-- Causatives do not include inchoatives: the two differ in the higher head. -/
theorem Causative.not_inchoative (h : Causative l) : ¬ Inchoative l :=
  fun h' => by simp [Inchoative, h.1] at h'

/-! ### The causative alternation ([cuervo-2003] §§1.3.4–1.3.5)

Over a shared lower event, `vDO` gives the causative and `vGO` the inchoative: *Vicki cerró la
puerta* is `[vDO, vBE]` under Voice, *se cerró la puerta* is `[vGO, vBE]` with *se* spelling
out `vGO`. -/

theorem causative_cons (h : lower ≠ []) : Causative (.vDO :: lower) :=
  ⟨rfl, Nat.succ_le_succ (List.length_pos_iff.2 h)⟩

theorem inchoative_cons (h : lower ≠ []) : Inchoative (.vGO :: lower) :=
  ⟨rfl, Nat.succ_le_succ (List.length_pos_iff.2 h)⟩

end LittleV

end Minimalist
