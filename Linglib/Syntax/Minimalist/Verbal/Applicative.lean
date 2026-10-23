/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Minimalist.Category.Basic
public import Linglib.Syntax.Minimalist.Verbal.LittleV
public import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Applicative heads

Applicative heads introduce applied arguments such as benefactives, goals, sources and affected
datives. [pylkkanen-2008] distinguishes a high applicative, which Merges with the event and
relates the applied argument to it, from a low applicative, which Merges with the theme and
relates the applied argument to it by transfer to or from it; [cuervo-2003] adds the static
possession a low applicative can express and a third type, the affected applicative, which
Merges between two events, taking the result state as its complement under the dynamic head
that embeds it. The type is where the head Merges: `ApplSite`, a cut of the little-v chain of
`Minimalist.LittleV`, is low when no head is below it, so that its complement is the theme DP,
high when no head is above it, so that Voice selects it, and affected between. `ApplSite.applType`
reads the type off the site, and the complement category of the type agrees with that of the site
(`ApplSite.applType_complement`), so the typology follows from attachment height by construction.

## Main definitions

* `LowRelation`, `ApplType`, `ApplType.complement`, `ApplType.IsLow`: the types and the category
  each Merges with.
* `ApplSite`, `ApplSite.Low`, `ApplSite.Affected`, `ApplSite.High`, `ApplSite.complement`,
  `ApplSite.selector`, `ApplSite.applType`, `ApplSite.all`: the merge site and its type.
* `ApplHead`, `ApplHead.Licensed`, `ApplHead.SpecCanBearCase`: the head, its licensing by Voice
  and the case-based blocking of its specifier.

## Main results

* `ApplSite.low_or_affected_or_high`, `ApplSite.applType_complement`, `ApplSite.mem_all_iff`.
* `ApplSite.Affected.biEventive`, `ApplSite.Affected.selector_dynamic`,
  `ApplSite.not_affected_of_state`: an affected applicative needs two events and a dynamic head
  above it, so none is applied under a state.
* `low_licensed_with_any`, `affected_licensed_with_any`, `high_licensed_of_assignsTheta`.

## Implementation notes

`ApplHead.Licensed` states the licensing of a high applicative by a Voice with event semantics
([pylkkanen-2008], [schaefer-2008]), which blocks the ethical dative in middles; [cuervo-2003]'s
high applicative over a state has no Voice above it at all, a disagreement a predicate over Voice
heads cannot state, and `Studies/Cuervo2003` states her licensing over sites instead.

## References

* [pylkkanen-2008]
* [cuervo-2003]
* [schaefer-2008]
* [wood-2015]
-/

@[expose] public section

namespace Minimalist

/-! ### Applicative types -/

/-- A low applicative relates the applied argument and the theme by the dynamic transfer to a
recipient or from a source of [pylkkanen-2008], or by the static possession of [cuervo-2003]'s low
applicative AT. -/
inductive LowRelation where
  | recipient
  | source
  | possessor
  deriving DecidableEq, Repr

/-- An applicative is high, relating the applied argument to the event; affected, relating it to a
result state under the dynamic event that embeds it; or low, relating it to the theme. -/
inductive ApplType where
  | high
  | affected
  | low (relation : LowRelation)
  deriving DecidableEq, Repr

/-- An applicative Merges with a vP when it is high or affected, and with the theme `D` when it is
low. -/
def ApplType.complement : ApplType → Cat
  | .high | .affected => .v
  | .low _ => .D

/-- An applicative is low when its complement is the theme. -/
def ApplType.IsLow (t : ApplType) : Prop := t.complement = .D

instance : DecidablePred ApplType.IsLow := fun _ ↦ inferInstanceAs (Decidable (_ = _))

theorem ApplType.isLow_iff (t : ApplType) : t.IsLow ↔ ∃ r, t = .low r := by
  cases t <;> simp [IsLow, complement]

/-! ### The merge site -/

/-- The site of an applicative head in an event structure records the verbal heads above ApplP and
the heads of its complement, highest first. -/
structure ApplSite where
  above : List LittleV
  below : List LittleV
  deriving DecidableEq, Repr

namespace ApplSite

variable (s : ApplSite)

/-- The event structure the applicative sits in. -/
def heads : List LittleV := s.above ++ s.below

/-- A site is low when Appl takes the theme DP as its complement, below every verbal head, and ApplP
is the complement of the root. -/
def Low : Prop := s.below = []

/-- A site is high when ApplP is the complement of no verbal head, Voice or Tense taking it. -/
def High : Prop := s.above = []

/-- A site is affected when Appl takes a vP as its complement and ApplP is the complement of the
verbal head above, so the applied argument participates in two events. -/
def Affected : Prop := s.above ≠ [] ∧ s.below ≠ []

instance : DecidablePred Low := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred High := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Affected := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The category of Appl's complement, the theme DP of a low applicative and a vP otherwise. -/
def complement : Cat := if s.below = [] then .D else .v

/-- ApplP is the complement of the lowest verbal head above it, whose root takes ApplP when the
applicative is low, and of no verbal head when it is high. -/
def selector : Option LittleV := s.above.getLast?

/-- The type of the applicative at the site, given the relation a low one reads. -/
def applType (r : LowRelation) : ApplType :=
  if s.below = [] then .low r else if s.above = [] then .high else .affected

theorem complement_eq_D_iff : s.complement = .D ↔ s.Low := by
  simp [complement, Low]

theorem selector_eq_none_iff : s.selector = none ↔ s.High := by
  simp [selector, High]

/-- The type read off the site Merges with the category the site gives it. -/
theorem applType_complement (r : LowRelation) : (s.applType r).complement = s.complement := by
  unfold applType complement
  split_ifs <;> rfl

theorem applType_eq_low_iff (r : LowRelation) : s.applType r = .low r ↔ s.Low := by
  unfold applType Low; split_ifs <;> simp_all

theorem applType_eq_affected_iff (r : LowRelation) : s.applType r = .affected ↔ s.Affected := by
  unfold applType Affected; split_ifs <;> simp_all

/-- The three types partition the sites in a nonempty structure. -/
theorem low_or_affected_or_high (h : s.heads ≠ []) : s.Low ∨ s.Affected ∨ s.High := by
  by_cases hb : s.below = [] <;> by_cases ha : s.above = [] <;>
    simp_all [heads, Low, Affected, High]

theorem Affected.not_low (h : s.Affected) : ¬ s.Low := h.2

theorem Affected.not_high (h : s.Affected) : ¬ s.High := h.1

/-- An affected applicative requires two events. -/
theorem Affected.biEventive (h : s.Affected) : LittleV.BiEventive s.heads := by
  obtain ⟨ha, hb⟩ := h
  unfold LittleV.BiEventive heads
  rw [List.length_append]
  have := List.length_pos_iff.2 ha
  have := List.length_pos_iff.2 hb
  omega

/-- The head an affected applicative is the complement of is dynamic: it embeds the eventuality
below the applicative. -/
theorem Affected.selector_dynamic (hw : LittleV.IsWellFormed s.heads) (h : s.Affected) :
    ∀ v ∈ s.selector, v.Dynamic := by
  intro v hv
  obtain ⟨ha, hb⟩ := h
  rw [selector, Option.mem_def, List.getLast?_eq_some_iff] at hv
  obtain ⟨l, hl⟩ := hv
  obtain ⟨w, t, hb'⟩ := List.exists_cons_of_ne_nil hb
  refine LittleV.Embeds.dynamic (w := w) (List.isChain_pair.1 (hw.2.infix ⟨l, t, ?_⟩))
  simp [heads, hl, hb']

/-- No affected applicative is applied under a state. -/
theorem not_affected_of_state (hw : LittleV.IsWellFormed s.heads)
    (h : s.selector = some .vBE) : ¬ s.Affected :=
  fun ha ↦ (ha.selector_dynamic s hw _ h) rfl

/-- The sites of an applicative in the structure `l` are the cuts of the list. -/
def all (l : List LittleV) : List ApplSite :=
  (List.range (l.length + 1)).map fun i ↦ ⟨l.take i, l.drop i⟩

theorem mem_all_iff {l : List LittleV} {s : ApplSite} : s ∈ all l ↔ s.heads = l := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    exact List.take_append_drop i l
  · rintro rfl
    exact List.mem_map.2 ⟨s.above.length,
      List.mem_range.2 (by simp only [heads, List.length_append]; omega), by simp [heads]⟩

end ApplSite

/-! ### The applicative head -/

/-- An applicative head carries its type and whether it assigns dative case to its specifier. -/
structure ApplHead where
  /-- High, affected or low. -/
  applType : ApplType
  /-- Whether the applied argument receives dative case. -/
  assignsDative : Bool := true
  deriving DecidableEq, Repr

/-- Canonical high applicative (ethical dative). -/
def applHigh : ApplHead := { applType := .high }

/-- Canonical affected applicative (the dative of a causative or an inchoative). -/
def applAffected : ApplHead := { applType := .affected }

/-- Canonical low recipient applicative (DOC). -/
def applLowRecipient : ApplHead := { applType := .low .recipient }

/-- Canonical low source applicative. -/
def applLowSource : ApplHead := { applType := .low .source }

/-- Canonical low possessor applicative (possessive dative). -/
def applLowPossessor : ApplHead := { applType := .low .possessor }

/-! ### Voice–applicative licensing ([pylkkanen-2008], [schaefer-2008]) -/

/-- `appl.Licensed voice` holds when `voice` is thematic and so supplies the event semantics a high
applicative, the complement of Voice, requires; a low or an affected applicative requires
nothing of Voice. -/
def ApplHead.Licensed (appl : ApplHead) (voice : Voice.Head) : Prop :=
  appl.applType = .high → voice.IsThematic

instance (appl : ApplHead) (voice : Voice.Head) : Decidable (appl.Licensed voice) :=
  inferInstanceAs (Decidable (_ → _))

variable (v : Voice.Head)

/-- Low applicatives are licensed under any Voice head ([pylkkanen-2008]). -/
theorem low_licensed_with_any (r : LowRelation) : ApplHead.Licensed { applType := .low r } v :=
  fun h ↦ absurd h (by simp)

/-- Affected applicatives are licensed under any Voice head: the head that selects them is the
dynamic v below Voice ([cuervo-2003]). -/
theorem affected_licensed_with_any : applAffected.Licensed v := fun h ↦ absurd h (by decide)

/-- θ-assigning Voice licenses high applicatives (θ-assignment entails event semantics). -/
theorem high_licensed_of_assignsTheta (h : v.AssignsTheta) : applHigh.Licensed v :=
  fun _ ↦ h.isThematic

theorem ethical_possessive_middle_asymmetry :
    ¬ applHigh.Licensed Voice.middle ∧ applLowPossessor.Licensed Voice.middle := by decide

/-! ### Case-based blocking of SpecApplP ([wood-2015]) -/

/-- If `appl` assigns dative, its specifier, bearing the case `c`, must bear one
([wood-2015]). -/
def ApplHead.SpecCanBearCase (appl : ApplHead) (c : Option Case) : Prop :=
  appl.assignsDative = true → c.isSome = true

instance (appl : ApplHead) (c : Option Case) : Decidable (appl.SpecCanBearCase c) :=
  inferInstanceAs (Decidable (_ → _))

end Minimalist
