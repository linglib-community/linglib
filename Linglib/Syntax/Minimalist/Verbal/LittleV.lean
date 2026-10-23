module

public import Mathlib.Data.List.Chain

/-!
# Little v

[cuervo-2003]'s event introducers: the three flavors of little v that verbalize a root and fix
its event type. `vDO` builds activities, `vGO` events of change, movement and happening, `vBE`
states. A sentence's event structure is the list of its verbal heads from the highest down; a
complex structure embeds one vP under another, and the possible combinations of the
dissertation's table (17) and its footnote are the chains of `LittleV.Embeds`: `vDO` embeds any
event, `vGO` only a state, `vBE` nothing.

Causatives and inchoatives are the two complex structures: an event or state embedded under
`vDO`, and a state embedded under `vGO`. There is no CAUSE head: "being causative is the
property of the configuration as a whole", and the two alternants of *cerrar* share the lower
stative event and differ in the dynamic head that embeds it, `[vDO, vBE]` against `[vGO, vBE]`.
Only a `vDO`-headed structure combines with Voice and so licenses an external argument.

## Main definitions

* `LittleV`, `LittleV.Embeds`, `LittleV.IsWellFormed`
* `LittleV.Activity`, `LittleV.Change`, `LittleV.State`, `LittleV.Causative`,
  `LittleV.Inchoative`, `LittleV.LicensesVoice`

## Main results

* `LittleV.Inchoative.eq_of_isWellFormed`: a well-formed inchoative is exactly `[vGO, vBE]`
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

/-- Which event a head may embed, [cuervo-2003]'s table (17) with its footnote: `vDO` embeds any
    event, `vGO` only a state, and `vBE` nothing, since events have to "become" states before they
    combine with `vBE`. -/
def Embeds (v w : LittleV) : Prop := v = .vDO ∨ (v = .vGO ∧ w = .vBE)

instance : DecidableRel Embeds := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem Embeds.dynamic (h : Embeds v w) : v.Dynamic := by
  rcases h with rfl | ⟨rfl, -⟩ <;> decide

@[simp] theorem not_vBE_embeds (w : LittleV) : ¬ Embeds .vBE w := by simp [Embeds]

@[simp] theorem vGO_embeds_iff : Embeds .vGO w ↔ w = .vBE := by simp [Embeds]

@[simp] theorem vDO_embeds (w : LittleV) : Embeds .vDO w := .inl rfl

/-- A well-formed event structure: a nonempty top-down chain of heads, each embedding the next. -/
def IsWellFormed (l : List LittleV) : Prop := l ≠ [] ∧ l.IsChain Embeds

instance : DecidablePred IsWellFormed := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem IsWellFormed.not_infix_vBE (hw : IsWellFormed l) (w : LittleV) : ¬ [.vBE, w] <:+: l :=
  fun h => not_vBE_embeds w (List.isChain_pair.1 (hw.2.infix h))

theorem IsWellFormed.eq_vBE_of_infix_vGO (hw : IsWellFormed l) (h : [.vGO, w] <:+: l) :
    w = .vBE :=
  vGO_embeds_iff.1 (List.isChain_pair.1 (hw.2.infix h))

/-! ### Event types ([cuervo-2003] §1.3) -/

/-- A simple activity: a root verbalized by `vDO` alone. -/
def Activity (l : List LittleV) : Prop := l = [.vDO]

/-- A simple predicate of change, movement or happening: `vGO` alone. -/
def Change (l : List LittleV) : Prop := l = [.vGO]

/-- A simple state, existential or predicational: `vBE` alone. -/
def State (l : List LittleV) : Prop := l = [.vBE]

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

instance : DecidablePred Activity := fun _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Change := fun _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred State := fun _ => inferInstanceAs (Decidable (_ = _))
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

theorem Change.not_licensesVoice (h : Change l) : ¬ LicensesVoice l := by
  subst h; decide

theorem State.not_licensesVoice (h : State l) : ¬ LicensesVoice l := by
  subst h; decide

/-- A well-formed inchoative is exactly `[vGO, vBE]`: `vGO` embeds only a state, under which
    nothing is embedded. -/
theorem Inchoative.eq_of_isWellFormed (hi : Inchoative l) (hw : IsWellFormed l) :
    l = [.vGO, .vBE] := by
  obtain ⟨hd, hl⟩ := hi
  rcases l with _ | ⟨v, _ | ⟨w, _ | ⟨u, t⟩⟩⟩
  · simp at hd
  · simp [BiEventive] at hl
  · obtain rfl := Option.some.inj hd
    obtain rfl := vGO_embeds_iff.1 (List.isChain_pair.1 hw.2)
    rfl
  · obtain rfl := Option.some.inj hd
    obtain ⟨hvw, hc⟩ := List.isChain_cons_cons.1 hw.2
    obtain rfl := vGO_embeds_iff.1 hvw
    exact absurd (List.isChain_cons_cons.1 hc).1 (not_vBE_embeds u)

/-! ### The causative alternation ([cuervo-2003] §§1.3.4–1.3.5)

Over a shared lower event, `vDO` gives the causative and `vGO` the inchoative: *Vicki cerró la
puerta* is `[vDO, vBE]` under Voice, *se cerró la puerta* is `[vGO, vBE]` with *se* spelling
out `vGO`. -/

theorem causative_cons (h : lower ≠ []) : Causative (.vDO :: lower) :=
  ⟨rfl, Nat.succ_le_succ (List.length_pos_iff.2 h)⟩

theorem inchoative_cons (h : lower ≠ []) : Inchoative (.vGO :: lower) :=
  ⟨rfl, Nat.succ_le_succ (List.length_pos_iff.2 h)⟩

/-- The four possible combinations of table (17) are well formed, the three under `vDO`
    causative and the one under `vGO` inchoative. -/
theorem possible_combinations :
    IsWellFormed [.vDO, .vDO] ∧ IsWellFormed [.vDO, .vGO] ∧ IsWellFormed [.vDO, .vBE] ∧
      IsWellFormed [.vGO, .vBE] ∧
    Causative [.vDO, .vDO] ∧ Causative [.vDO, .vGO] ∧ Causative [.vDO, .vBE] ∧
      Inchoative [.vGO, .vBE] := by
  decide

/-- The combinations the footnote to (17) excludes: nothing under `vBE`, nothing dynamic under
    `vGO`. -/
theorem impossible_combinations :
    ¬ IsWellFormed [.vBE, .vDO] ∧ ¬ IsWellFormed [.vBE, .vGO] ∧
      ¬ IsWellFormed [.vGO, .vGO] ∧ ¬ IsWellFormed [.vGO, .vDO] := by
  decide

end LittleV

end Minimalist
