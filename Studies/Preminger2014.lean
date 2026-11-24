module

public import Linglib.Syntax.Minimalist.Probe.Agree
public import Linglib.Syntax.Feature.Geometry
public import Linglib.Languages.Mayan.Kaqchikel.Agreement
public import Linglib.Languages.Mayan.Kaqchikel.Pronouns
public import Linglib.Languages.Mayan.Kiche.Pronouns
public import Linglib.Morphology.Word.Leipzig
public import Linglib.Data.Examples.Preminger2014
public import Linglib.Data.Examples.Readers
public import Studies.BejarRezac2003

/-!
# Preminger 2014: Agreement and Its Failures

The verb of the Kichean Agent-Focus construction has one agreement slot, filled from the absolutive
paradigm, for two core arguments. Preminger derives what fills it from two probes relativized to
nodes of a φ-feature geometry, a person probe π⁰ seeking [participant] and a number probe #⁰
seeking [plural]. A probe relativized to a feature `f` is satisfied by the goals that bear `f` and
skips the rest, and it copies from its goal the features `f` dominates. The goal of π⁰ is doubled
by a clitic, which bears the goal's whole φ-set. The slot shows that clitic if there is one, and
otherwise the exponent of #⁰, that of a third person in the number #⁰ copied.

We prove that the slot shows the cell of a participant argument if there is one, otherwise the
third person plural if an argument bears [plural], and otherwise the third person singular, and that
it does not depend on which argument is the subject when at most one argument is a participant.
Béjar and Rezac's Person Licensing Condition, on which the search of π⁰ reaches every argument
that bears [participant], holds of the two arguments exactly when at most one of them does. A
probe relativized to a feature is satisfied by every goal that satisfies a probe relativized below
it, so that a probe relativized to the root, as English Infl⁰ is, finds the subject. Each of the
paper's Kaqchikel examples is acceptable exactly when its arguments obey the condition and its
verb shows the cell the probes give.

## Implementation notes

The geometry is Harley and Ritter's, of which the paper's keeps four nodes: its root [φ] is the
Referring Expression node, and its [participant], [author] and [plural] are Participant, Speaker
and Group. A nominal bears the lower set of nodes of its φ-cell, `Agreement.Bundle.nodes`.

The slot is a total function of the two arguments and licensing is a separate condition on them,
since a probe that finds no goal leaves a form, the null third person singular, while a
participant the person probe does not reach leaves none. The exponent of #⁰ is read off the third
person cells of the Set B table, a privative geometry having no feature for the third person.

An argument that is not a pronoun is read as a third person, plural if its gloss says so. The
rows record each marker the paper prints in a slot as a row of its own, and the model is compared
with the cell a marker is glossed as, not with its shape, which varies with the following segment.

The morphophonology of the markers, agreement in regular transitives and intransitives, the
alternative analyses, and the Zulu and Basque chapters are not formalized; the Zulu analysis is
`Studies/Halpert2012.lean`.

## References

* [preminger-2014]
* [bejar-rezac-2003]
* [harley-ritter-2002]
* [halpert-2012]
-/

@[expose] public section

namespace Preminger2014

open Kaqchikel Minimalist Agreement
open Morphology.FeatureGeometry (Node)

variable {c s o : Bundle} {f g : Node}

/-! ### Relativized probes -/

/-- The probe relativized to the node `f`, which the cells that bear `f` satisfy. -/
def probe (f : Node) : Probe Bundle := (Probe.Spec.relativized f).toProbe Bundle.nodeFinset

@[simp] theorem probe_sat : (probe f).sat c ↔ f ∈ c.nodes := Probe.Spec.ofGeometry_toProbe_sat

/-- A probe relativized to a node is satisfied by every cell that satisfies a probe relativized
to a node it dominates. -/
theorem probe_sat_anti (h : f ≤ g) (hg : (probe g).sat c) : (probe f).sat c :=
  Probe.Spec.relativized_toProbe_sat_anti c.nodes.lower h hg

-- a probe finds a goal wherever a probe relativized below it does
theorem search_isSome_of_le (h : f ≤ g) {goals : List Bundle}
    (hg : ((probe g).search goals).isSome) : ((probe f).search goals).isSome :=
  Probe.search_isSome_mono (fun _ _ ↦ probe_sat_anti h) hg

-- a probe relativized to the root, as English Infl⁰ is, finds the closest goal
theorem probe_bot_search (c : Bundle) (l : List Bundle) : (probe ⊥).search (c :: l) = some c := by
  simp [Probe.search]

/-- π⁰, the person probe, relativized to [participant]. -/
abbrev piProbe : Probe Bundle := probe .participant

/-- #⁰, the number probe, relativized to [plural], the Group node. -/
abbrev numProbe : Probe Bundle := probe .group

/-- (112): the nodes that the obligatory operation copies to a head relativized to `f` from the
subject and the object. -/
def find (f : Node) (s o : Bundle) : Finset Node :=
  ((Probe.Spec.relativized f).agree Bundle.nodeFinset ∅ [s, o]).state.copied

/-- The operation copies from the goal of the probe the nodes that `f` dominates, and nothing when
the probe finds no goal. -/
theorem find_eq (f : Node) (s o : Bundle) :
    find f s o = ((probe f).search [s, o]).elim ∅ fun c ↦ c.nodeFinset ∩ Finset.Ici f := by
  have h (a : Bundle) : (probe f).int a ↔ (probe f).sat a :=
    (Probe.Spec.ofGeometry_toProbe_int_iff a.nodes.lower).trans
      Probe.Spec.ofGeometry_toProbe_sat.symm
  rw [find, Probe.Spec.agree_empty]
  exact (Probe.agree_state_eq_elim h).trans (by simp [probe])

/-! ### The agreement slot -/

/-- (66): the clitic that doubles the goal of π⁰, which bears the goal's whole φ-set. -/
def clitic (s o : Bundle) : Option Bundle := piProbe.search [s, o]

/-- (71): the cell the agreement slot shows, the clitic's, and without a clitic the third person
in the number #⁰ copies. -/
def slot (s o : Bundle) : Bundle :=
  (clitic s o).getD
    (.personNumber .third (if (numProbe.search [s, o]).isSome then .plural else .singular))

/-- The marker in the slot, the Set B exponent of the cell it shows. -/
def marker (s o : Bundle) : List Morphology.Morph := (setBExponent.realize (slot s o)).getD []

/-- (75): the Person Licensing Condition holds of the two core arguments when the search of π⁰
reaches each of them that bears [participant], the feature π⁰ seeks. -/
def PLC (s o : Bundle) : Prop := piProbe.AllLicensed piProbe.sat [s, o]

instance (s o : Bundle) : Decidable (PLC s o) :=
  inferInstanceAs (Decidable (Probe.AllLicensed _ _ _))

-- (66)
theorem clitic_eq (s o : Bundle) :
    clitic s o = if s.IsSAP then some s else if o.IsSAP then some o else none := by
  by_cases hs : s.IsSAP <;> by_cases ho : o.IsSAP <;> simp [clitic, Probe.search, hs, ho]

/-- The slot shows the cell of a participant argument, the subject's first; without one it shows
the third person plural if an argument bears [plural], and the third person singular otherwise. -/
theorem slot_eq (s o : Bundle) :
    slot s o = if s.IsSAP then s else if o.IsSAP then o
      else .personNumber .third
        (if .group ∈ s.nodes ∨ .group ∈ o.nodes then .plural else .singular) := by
  by_cases hs : s.IsSAP <;> by_cases ho : o.IsSAP <;>
    by_cases hsp : Node.group ∈ s.nodes <;> by_cases hop : Node.group ∈ o.nodes <;>
    simp [slot, clitic_eq, Probe.search, hs, ho, hsp, hop]

/-- The Person Licensing Condition holds of the two core arguments exactly when at most one of
them bears [participant]. -/
theorem plc_iff (s o : Bundle) : PLC s o ↔ ¬ (s.IsSAP ∧ o.IsSAP) := by
  rw [PLC, Probe.allLicensed_sat_iff]
  by_cases hs : s.IsSAP <;> by_cases ho : o.IsSAP <;> simp [hs, ho]

-- (22): when at most one argument bears [participant], the slot does not depend on which
-- argument is the subject
theorem slot_comm (h : ¬ (s.IsSAP ∧ o.IsSAP)) : slot s o = slot o s := by
  rw [slot_eq, slot_eq]
  by_cases hs : s.IsSAP <;> by_cases ho : o.IsSAP <;> simp_all [or_comm]

-- (113): with no participant and no plural argument both probes fail and the marker is null
theorem marker_eq_nil (hs : ¬ s.IsSAP) (ho : ¬ o.IsSAP) (hsp : .group ∉ s.nodes)
    (hop : .group ∉ o.nodes) :
    piProbe.search [s, o] = none ∧ numProbe.search [s, o] = none ∧ marker s o = [] := by
  refine ⟨by simp [hs, ho], by simp [hsp, hop], ?_⟩
  rw [marker, slot_eq]
  simp only [hs, ho, hsp, hop, ite_false, or_self]
  decide

-- (60): π⁰ copies the same features from a first person singular and a first person plural
-- goal, whose clitics differ
theorem find_participant_coarse :
    find .participant (.personNumber .first .singular) (.personNumber .third .singular) =
        {.participant, .speaker} ∧
      find .participant (.personNumber .first .plural) (.personNumber .third .singular) =
        {.participant, .speaker} ∧
      marker (.personNumber .first .singular) (.personNumber .third .singular) ≠
        marker (.personNumber .first .plural) (.personNumber .third .singular) := by
  decide

/-! ### The examples -/

open Examples (all)

/-- The pronoun of the Kaqchikel language file that a lexeme of the rows is. -/
def Examples.Lexeme.pronoun : Examples.Lexeme → PersonalPronoun
  | .yin => Pronouns.yin
  | .rat => Pronouns.rat
  | .rja => Pronouns.rja'
  | .roj => Pronouns.roj
  | .rje => Pronouns.rje'

/-- The φ-cell of the argument of a row marked `l`, a pronoun's agreement, and for another noun
phrase the third person, plural if a word of it is glossed so. -/
def argument? (e : Datum) (l : Examples.SpanLabel) : Option Bundle :=
  (e.spans.find? fun x ↦ Examples.label? x = some l).map fun x ↦
    match Examples.lexeme? x with
    | some p => p.pronoun.agreement
    | none => .personNumber .third
        (if ∃ w ∈ x.words e, w.features .number = some .plural then .plural else .singular)

/-- The cell the absolutive marker of a row's verb is glossed as. -/
def shown? (e : Datum) : Option Bundle :=
  (e.glossedWords.flatMap (·.glossedMorphemes)).findSome? fun m ↦
    if "ABS".toList ∈ Gloss.elements m.gloss then
      some (.ofFeatures (.ofLabels (Gloss.elements m.gloss)))
    else none

-- each lexeme of the rows is a strong pronoun of the language file
theorem pronoun_mem_personal : ∀ l : Examples.Lexeme, l.pronoun ∈ Pronouns.personal := by decide

-- each marked pronoun is printed as the language file writes it
theorem printed :
    ∀ e ∈ all, ∀ x ∈ e.spans, ∀ l ∈ Examples.lexeme? x,
      (x.words e).map (·.word) = [l.pronoun.form.toList] := by
  decide

/-- Each example is acceptable exactly when its arguments obey the Person Licensing Condition and
its verb shows the person and number the probes give. -/
theorem examples_fit :
    ∀ e ∈ all, ∃ s ∈ argument? e .subject, ∃ o ∈ argument? e .object, ∃ c ∈ shown? e,
      (e.judgment = .acceptable ↔
        PLC s o ∧ slot s o .person = c .person ∧ slot s o .number = c .number) := by
  decide

/-! ### The hierarchy and the Person Case Constraint -/

/-- (23): the rank of a cell on the hierarchy 1st/2nd person > 3rd plural > 3rd singular. -/
def rank (c : Bundle) : ℕ := if c.IsSAP then 2 else if c.IsPlural then 1 else 0

-- (22), (74): on the cells of the paradigm the slot shows the higher-ranked argument, the
-- subject at a tie
theorem slot_eq_of_rank :
    ∀ s ∈ Bundle.personNumberCells, ∀ o ∈ Bundle.personNumberCells,
      slot s o = if rank o ≤ rank s then s else o := by
  decide

-- §4.2: the person probe of [bejar-rezac-2003], which every nominal halts, leaves a participant
-- below a third person dative unlicensed, and π⁰ skips a third person subject to license it
theorem relativization_contrast :
    ¬ BejarRezac2003.PLC (BejarRezac2003.v.derive
        [.dat (.personNumber .third .singular), .caseless (.personNumber .first .singular)]) ∧
      PLC (.personNumber .third .singular) (.personNumber .first .singular) := by
  decide

-- §7.1: the K'ichee' formal addressee *laal* agrees as a third person singular, so that it
-- occurs with a first person and does not outrank a third person plural
theorem formal_addressee :
    ¬ PLC Kiche.Pronouns.at_.agreement (.personNumber .first .singular) ∧
      PLC Kiche.Pronouns.laal.agreement (.personNumber .first .singular) ∧
      slot Kiche.Pronouns.laal.agreement (.personNumber .first .singular) =
        .personNumber .first .singular ∧
      slot Kiche.Pronouns.laal.agreement (.personNumber .third .plural) =
        .personNumber .third .plural := by
  decide

end Preminger2014
