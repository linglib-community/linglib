module

public import Linglib.Syntax.Minimalist.Probe.Phi
public import Linglib.Fragments.Mayan.Kaqchikel.Agreement
public import Linglib.Fragments.Mayan.Kiche.Agreement
public import Studies.BejarRezac2003

/-!
# Preminger (2014): Agreement and Its Failures

Preminger accounts for φ-agreement in the Kichean Agent-Focus construction (chapters 3 to 5 and
7), whose single agreement slot follows the hierarchy *1st/2nd person > 3rd plural > 3rd singular*
in subject and object alike (22), (23). Two feature-relativized probes derive the hierarchy, a
person probe seeking [participant], merged first, whose goal is clitic-doubled, and a number probe
seeking [plural], whose exponent surfaces only when no clitic fills the slot (65), (71), (74).
Béjar and Rezac's Person Licensing Condition makes the person restriction, at most one 1st/2nd
person core argument, the consequence of a single person probe (75), (76), and under the
obligatory-operations model of chapter 5 a probe that finds no goal ends unvalued (112), (113).
The probes read agreement features, not salience, so the K'ichee' formal addressee, which agrees as
a third person singular, does not outrank the third person (§7.1).

## Main results

* `Preminger2014.afTarget_eq`, `Preminger2014.afTarget_eq_rank`: the slot reflects the
  participant if there is one, otherwise the plural argument.
* `Preminger2014.af_paradigm`, `Preminger2014.afMarker_comm`: the probes deliver the hierarchy's
  marker, symmetrically in subject and object.
* `Preminger2014.personRestriction_iff_plc`: the person restriction is the Person Licensing
  Condition.
* `Preminger2014.participant_marker`: the clitic carries its goal's whole φ-set (68), (69).
* `Preminger2014.afTarget_eq_none_iff`, `Preminger2014.failed_agree_tolerated`: failed Agree
  converges with the null exponent.
* `Preminger2014.plural_marker`: an available plural goal must be agreed with (114).
* `Preminger2014.relativization_contrast`: relativization separates the pattern from the Person
  Case Constraint (§4.2).
* `Preminger2014.hierarchy_silent_on_restriction`: a hierarchy cannot state the person
  restriction (§7.1).
* `Preminger2014.formal_addressee`: the K'ichee' formal addressee patterns as a third person
  singular (§7.1).

## Implementation notes

The probes are the substrate's `Probe.Target.participant` and `.plural`, and their competition
for the slot (71) is their `Probe.cascade`; the marker is the fragment's Set B exponent of the
cascade's goal. The paradigm (22) enters as the hierarchy (23) read as `rank`. The
morphophonology (§3.4), §4.5–§4.6, and the Zulu and Basque studies of chapter 6 are prose; the
Zulu analysis is `Studies/Halpert2012.lean`.

## References

* [preminger-2014]
* [bejar-rezac-2003]
* [harley-ritter-2002]
* [nevins-2011]
* [halpert-2012]
-/

@[expose] public section

namespace Preminger2014

open Kaqchikel Minimalist Agreement

/-! ### The probes and the slot (§4.4) -/

/-- π⁰, the person probe, relativized to [participant]. -/
def piProbe : Probe Bundle := Probe.Target.participant.toProbe

/-- #⁰, the number probe, relativized to [plural]. -/
def numProbe : Probe Bundle := Probe.Target.plural.toProbe

/-- The Agent-Focus slot reflects the person probe's goal, else the number probe's, else none,
the competition for the single slot (71) run as a cascade over the subject's and object's cells. -/
def afTarget (subj obj : Bundle) : Option Bundle := Probe.cascade [piProbe, numProbe] [subj, obj]

/-- The Person Licensing Condition holds of the clause's two core arguments when the person
probe's search licenses each argument bearing [participant]. -/
def Plc (subj obj : Bundle) : Prop :=
  piProbe.AllLicensed (·.visibleTo .participant) [subj, obj]

instance (subj obj : Bundle) : Decidable (Plc subj obj) :=
  inferInstanceAs (Decidable (Probe.AllLicensed _ _ _))

/-- The absolutive exponent of a cell, empty where the paradigm has none. -/
def exponent (c : Bundle) : List Morphology.Morph := (setBExponent.realize c).getD []

/-- The Agent-Focus marker is the exponent of the slot's goal, the empty exponent when both probes
fail, and undefined when the Person Licensing Condition fails. -/
def afMarker (subj obj : Bundle) : Option (List Morphology.Morph) :=
  if Plc subj obj then some (((afTarget subj obj).map exponent).getD []) else none

/-- The person restriction (25) allows at most one core argument to bear [participant]. -/
def PersonRestriction (subj obj : Bundle) : Prop := ¬ (subj.IsSAP ∧ obj.IsSAP)

instance : DecidableRel PersonRestriction := fun s o ↦
  inferInstanceAs (Decidable ¬ (s.IsSAP ∧ o.IsSAP))

/-! ### Relativized probing (§4.2, §4.4) -/

/-- Under skipping the slot reflects a participant if either argument is one, the subject first,
otherwise a plural argument, and otherwise nothing (66), (73). -/
theorem afTarget_eq (s o : Bundle) :
    afTarget s o = if s.IsSAP then some s else if o.IsSAP then some o
      else if s.IsPlural then some s else if o.IsPlural then some o else none := by
  by_cases h1 : s.IsSAP <;> by_cases h2 : o.IsSAP <;>
    by_cases h3 : s.IsPlural <;> by_cases h4 : o.IsPlural <;>
    simp [afTarget, piProbe, numProbe, Probe.Target.toProbe, Bundle.visibleTo, Probe.cascade,
      Probe.search, Probe.relativized, List.find?_cons, h1, h2, h3, h4]

/-- The rank of a cell on the hierarchy (23) puts [participant] above [plural] above the rest. -/
def rank (c : Bundle) : ℕ := if c.IsSAP then 2 else if c.IsPlural then 1 else 0

theorem afTarget_eq_rank (s o : Bundle) :
    afTarget s o = if rank s = 0 ∧ rank o = 0 then none
      else if rank o ≤ rank s then some s else some o := by
  rw [afTarget_eq]
  by_cases h1 : s.IsSAP <;> by_cases h2 : o.IsSAP <;>
    by_cases h3 : s.IsPlural <;> by_cases h4 : o.IsPlural <;>
    simp [rank, h1, h2, h3, h4]

/-- The hierarchy (23) as an account is the morphological competition of §3.3.2, in which the slot
shows the higher-ranked argument's absolutive marker. -/
def hierarchyMarker (subj obj : Bundle) : List Morphology.Morph :=
  exponent (if rank obj ≤ rank subj then subj else obj)

/-- On every licit pair of person–number cells of the paradigm (22), (74), the probes deliver the
hierarchy's marker. -/
theorem af_paradigm :
    ∀ s ∈ Bundle.personNumberCells, ∀ o ∈ Bundle.personNumberCells,
      PersonRestriction s o → afMarker s o = some (hierarchyMarker s o) := by
  decide

/-- The marker is symmetric in subject and object (22, note a), (74), a consequence of skipping,
since the probe finds its goal in either position. -/
theorem afMarker_comm :
    ∀ s ∈ Bundle.personNumberCells, ∀ o ∈ Bundle.personNumberCells,
      afMarker s o = afMarker o s := by
  decide

/-! ### Licensing (§4.4.2) -/

/-- The person restriction is the Person Licensing Condition on the clause's two core
arguments (76), since a single person probe licenses at most one [participant] feature. -/
theorem personRestriction_iff_plc (s o : Bundle) : PersonRestriction s o ↔ Plc s o := by
  unfold PersonRestriction Plc piProbe Probe.Target.toProbe
  rw [Probe.relativized_allLicensed_iff]
  by_cases hs : s.IsSAP <;> by_cases ho : o.IsSAP <;>
    simp [Bundle.visibleTo, hs, ho]

/-- The marker is undefined exactly when the person restriction is violated; two plural
arguments in particular are never excluded (77). -/
theorem afMarker_eq_none_iff (s o : Bundle) : afMarker s o = none ↔ ¬ PersonRestriction s o := by
  rw [afMarker, personRestriction_iff_plc]
  split_ifs with h <;> simp [h]

/-- The clitic is featurally coarse (68), (69). With one participant argument, the marker is
that argument's whole exponent, its number included, whether it is the subject or the object
and whatever the other argument's number. -/
theorem participant_marker (s o : Bundle) (h : ¬ (s.IsSAP ∧ o.IsSAP)) :
    (s.IsSAP → afMarker s o = some (exponent s)) ∧
      (o.IsSAP → afMarker s o = some (exponent o)) := by
  have hplc : Plc s o := (personRestriction_iff_plc s o).1 h
  rw [afMarker, ite_eq_left hplc, afTarget_eq]
  refine ⟨fun hs ↦ by simp [hs], fun ho ↦ ?_⟩
  have hs : ¬ s.IsSAP := fun hs ↦ h ⟨hs, ho⟩
  simp [hs, ho]

/-! ### Obligatory operations (chapter 5) -/

theorem afTarget_eq_none_iff (s o : Bundle) :
    afTarget s o = none ↔ piProbe.search [s, o] = none ∧ numProbe.search [s, o] = none := by
  rw [afTarget, Probe.cascade_eq_none_iff, Probe.search_eq_none_iff, Probe.search_eq_none_iff]
  simp

/-- Failed Agree is tolerated (112), (113). With no participant and no plural argument, both
probes end unvalued, the derivation converges, and the slot carries the null exponent. -/
theorem failed_agree_tolerated (s o : Bundle) (hs : ¬ s.IsSAP) (ho : ¬ o.IsSAP)
    (hsp : ¬ s.IsPlural) (hop : ¬ o.IsPlural) :
    afTarget s o = none ∧ afMarker s o = some [] := by
  have hplc : Plc s o := (personRestriction_iff_plc s o).1 fun h ↦ hs h.1
  rw [afMarker, ite_eq_left hplc, afTarget_eq]
  simp [hs, ho, hsp, hop]

/-- There is no gratuitous nonagreement (114). With no participant argument, a plural argument
must be agreed with, and the slot carries its exponent, the subject's first. -/
theorem plural_marker (s o : Bundle) (hs : ¬ s.IsSAP) (ho : ¬ o.IsSAP) :
    (s.IsPlural → afMarker s o = some (exponent s)) ∧
      (¬ s.IsPlural → o.IsPlural → afMarker s o = some (exponent o)) := by
  have hplc : Plc s o := (personRestriction_iff_plc s o).1 fun h ↦ hs h.1
  rw [afMarker, ite_eq_left hplc, afTarget_eq]
  exact ⟨fun hsp ↦ by simp [hs, ho, hsp], fun hsp hop ↦ by simp [hs, ho, hsp, hop]⟩

/-! ### Against the alternatives (§4.2, chapter 7) -/

/-- A relativized probe escapes the Person Case Constraint (§4.2). The unrelativized person probe
of [bejar-rezac-2003] is absorbed by a Case-licensed third-person dative above a participant, the
PCC, whereas the Kichean probe, relativized to [participant], skips the third-person argument and
licenses the participant below it. -/
theorem relativization_contrast :
    ¬ BejarRezac2003.PLC (BejarRezac2003.v.derive
        [.dat (.personNumber .third .singular), .caseless (.personNumber .first .singular)]) ∧
      Plc (.personNumber .third .singular) (.personNumber .first .singular) := by
  decide

/-- There is an asymmetry a hierarchy cannot state (§7.1). It assigns a marker to two participant
arguments, which the probes exclude, while two plural arguments are admitted by both. -/
theorem hierarchy_silent_on_restriction :
    afMarker (.personNumber .first .singular) (.personNumber .second .singular) = none ∧
      hierarchyMarker (.personNumber .first .singular) (.personNumber .second .singular) =
        exponent (.personNumber .first .singular) ∧
      afMarker (.personNumber .third .plural) (.personNumber .third .plural) =
        some (exponent (.personNumber .third .plural)) := by
  decide

/-- The K'ichee' formal addressee *laal* does not outrank the third person (§7.1, quoting
Stiebels). It denotes the hearer, as *at* does, but agrees as a third person singular, and the
probes read agreement: beside a first person singular argument the slot reflects the first
person, where *at* violates the person restriction, and beside a third person plural it reflects
the plural. -/
theorem formal_addressee :
    afTarget (phi Kiche.laal) (.personNumber .first .singular) =
        some (.personNumber .first .singular) ∧
      ¬ PersonRestriction (phi Kiche.at_) (.personNumber .first .singular) ∧
      afTarget (phi Kiche.laal) (.personNumber .third .plural) =
        some (.personNumber .third .plural) := by
  decide

end Preminger2014
