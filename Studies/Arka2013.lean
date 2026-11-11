/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Fragments.Indonesian.Aspect
public import Linglib.Fragments.Indonesian.Complementation
public import Linglib.Semantics.Tense.Reichenbach
public import Linglib.Data.Examples.Arka2013
public import Linglib.Data.Examples.Readers

/-!
# Arka (2013): On the typology and syntax of TAM in Indonesian

Arka argues that Indonesian has no grammatical tense or aspect and yet has finiteness. A bare
verb is anchored in time by context or by an adjunct, and the auxiliaries only add a relation
between the event and the reference time, which [the printed E, R and S of each example
bear out](##rows_annotations): *sudah* puts the event before a reference time that is free, so
[the puzzle of the English present perfect does not arise](##klein_puzzle_dissolved). The
auxiliaries occupy I, and a clause whose subject must be controlled is a bare VP, so that [a TAM
particle is accepted exactly where the clause projects I](##particle_iff_projectsI). A
nominalisation in *=nya* is past unless an adjunct says otherwise, where [a bare verb is open to
any time](##readings_iff_admits), and it enters an equational structure, which [the copula
*adalah*](##adalah_iff) and [the negators *bukan* and *tidak*](##negation) show.

## Implementation notes

* An annotation such as `E-R<S` is read as the temporal group of each primitive. The auxiliaries
  of a sentence are those of the aspect fragment whose gloss is in its gloss line, and its
  temporal adjunct is found by its gloss.
* The paper's fifth auxiliary, the volitive *mau* 'want', is not an aspect marker and is left
  out. In (15) the particle tested is the modal *bisa* 'able'.
* Which clause of a sentence is at issue, what selects it, and which sentences have a
  nominalisation are entered here, each sentence cited by its row; the judgments are the rows'.
  A row's alternatives are the sentences the paper prints with the particle, the copula or
  *tidak* added.
* The phrase structures of the two analyses of the equational structure are not modelled.

## References

* [arka-2013]
* [klein-1992]
* [kibort-2009]
* [sneddon-1996]
-/

@[expose] public section

namespace Arka2013

open Tense Indonesian Indonesian.Aspect Indonesian.Complementation Arka2013.Examples

/-! ### Temporal frames -/

/-- An E/R/S annotation as the paper prints it — `E-R<S`, `S<E-R`, `E<S,R` — read as the
temporal group each primitive falls in, later groups later in time. -/
structure Annotation where
  e : ℕ
  r : ℕ
  s : ℕ
  deriving DecidableEq, Repr

/-- An annotation is read left to right, `<` opening a later group and `-` and `,` keeping the
current one. -/
def Annotation.parse? (str : String) : Option Annotation :=
  let step : Option (Annotation × ℕ) → Char → Option (Annotation × ℕ)
    | some (a, g), 'E' => some ({ a with e := g }, g)
    | some (a, g), 'R' => some ({ a with r := g }, g)
    | some (a, g), 'S' => some ({ a with s := g }, g)
    | some (a, g), '<' => some (a, g + 1)
    | some (a, g), '-' => some (a, g)
    | some (a, g), ',' => some (a, g)
    | some (a, g), ' ' => some (a, g)
    | _, _ => none
  (str.toList.foldl step (some (⟨0, 0, 0⟩, 0))).map (·.1)

/-- The frame an annotation describes, with the perspective at speech time. -/
def Annotation.frame (a : Annotation) : ReichenbachFrame ℤ := .root a.s a.r a.e

/-- The TAM auxiliaries among the fragment's aspect markers, *sudah* and *telah* 'PERF', *sedang*
'PROG' and *akan* 'FUT', which occupy I (16). -/
def auxiliaries : List Aspect.Marker := [sudah, telah, sedang, akan]

/-- The auxiliaries of a sentence, those whose gloss is in its gloss line. -/
def auxiliariesOf (e : Datum) : List Aspect.Marker :=
  auxiliaries.filter (·.gloss ∈ e.glossLine)

/-- Where a temporal adjunct puts the reference time relative to the moment of speech, by its
gloss: *kemarin* 'yesterday', *sekarang* 'now', *besok* 'tomorrow' and *nanti* 'later'. -/
def adjunctReference (gloss : String) : Option Ordering :=
  [("yesterday", Ordering.lt), ("now", .eq), ("tomorrow", .gt), ("later", .gt)].lookup gloss

/-- The reference position that the temporal adjunct of a sentence names. -/
def referenceOf (e : Datum) : Option Ordering := e.glossLine.findSome? adjunctReference

/-- `frame v f` is the frame relation the paper reads off the viewpoint `v`, which is E < R with
R free for the perfect (5), E = R for the progressive (18), and S < E-R for the prospective *akan*,
read as a future tense (10). No auxiliary marks another viewpoint. -/
def frame {T : Type*} [LinearOrder T] : Aspect.ViewpointType → ReichenbachFrame T → Prop
  | .perfect, f => f.eventPosition = .lt
  | .imperfective, f => f.eventPosition = .eq
  | .prospective, f => f.referencePosition = .gt ∧ f.eventPosition = .eq
  | _, _ => False

instance {T : Type*} [LinearOrder T] (v : Aspect.ViewpointType) (f : ReichenbachFrame T) :
    Decidable (frame v f) := by
  cases v <;> dsimp only [frame] <;> infer_instance

-- (4), (5), (10): each printed annotation has the relation of the sentence's auxiliary and
-- the reference position of its adjunct
theorem rows_annotations :
    ∀ e ∈ all, ∀ ann ∈ e.feature? "frame" >>= Annotation.parse?,
      (∀ m ∈ auxiliariesOf e, frame m.viewpoint ann.frame) ∧
        ∀ o ∈ referenceOf e, ann.frame.referencePosition = o := by
  decide +kernel

theorem readCount_annotations :
    Datum.ReadCount (fun e ↦ e.feature? "frame" >>= Annotation.parse?) all 6 := by
  decide +kernel

/-- The annotations of the sentences with a perfect auxiliary, the *sudah* sentences of (5). -/
def sudahAnnotations : List Annotation :=
  all.filterMap fun e ↦
    if ∃ m ∈ auxiliariesOf e, m.viewpoint = .perfect then
      e.feature? "frame" >>= Annotation.parse?
    else none

-- (5): the event precedes the reference time, which is at the moment of speech or before it
theorem sudah_reference_free :
    (∃ a ∈ sudahAnnotations, a.r = a.s) ∧ (∃ a ∈ sudahAnnotations, a.r < a.s) ∧
      ∀ a ∈ sudahAnnotations, a.e < a.r := by
  decide +kernel

/-- The English present perfect grammaticalises E < R together with R at the deictic
centre. -/
def englishPresentPerfect {T : Type*} [LinearOrder T] (f : ReichenbachFrame T) : Prop :=
  f.eventPosition = .lt ∧ f.referencePosition = .eq

instance {T : Type*} [LinearOrder T] (f : ReichenbachFrame T) :
    Decidable (englishPresentPerfect f) := by
  unfold englishPresentPerfect; infer_instance

/-- The English present perfect keeps the reference time at the moment of speech, so a past
adjunct clashes with it, and *sudah* admits a frame with a past reference time, as in (5b). -/
theorem klein_puzzle_dissolved :
    (∀ f : ReichenbachFrame ℤ, englishPresentPerfect f → f.referencePosition ≠ .lt) ∧
      ∃ f : ReichenbachFrame ℤ, frame sudah.viewpoint f ∧ f.referencePosition = .lt :=
  ⟨fun _ h ↦ h.2 ▸ by decide, ⟨.root 2 1 0, by decide⟩⟩

theorem english_pp_strictly_stronger {T : Type*} [LinearOrder T] :
    (∀ f : ReichenbachFrame T, englishPresentPerfect f → frame sudah.viewpoint f) ∧
      ∃ f : ReichenbachFrame ℤ, frame sudah.viewpoint f ∧ ¬ englishPresentPerfect f :=
  ⟨fun _ h ↦ h.1, ⟨.root 2 1 0, by decide⟩⟩

/-! ### Finiteness -/

/-- The place of a clause in its sentence: a root clause, a clause that a verb or a subordinator
selects, or a nominalisation in *=nya* standing as predicate. -/
inductive Site where
  | root
  | complement (v : Verb)
  | subordinate (c : Complementizer)
  | nominal

namespace Site

/-- The subject of the clause is not expressed and is controlled from outside it. -/
def IsControlled : Site → Prop
  | complement v => ∃ fr ∈ v.valency.frames, ∃ pos ∈ fr.complements, pos.subject? = some .null
  | subordinate c => c.subject = some .null
  | _ => False

instance : DecidablePred IsControlled := fun s ↦ by
  cases s <;> unfold IsControlled <;> infer_instance

/-- A clause projects I, the position of the TAM auxiliaries (16), unless its subject is
controlled, when it is a bare VP (17), or it is a nominal predicate. -/
def ProjectsI : Site → Prop
  | root => True
  | nominal => False
  | s => ¬ s.IsControlled

instance : DecidablePred ProjectsI := fun s ↦ by
  cases s <;> unfold ProjectsI <;> infer_instance

end Site

/-- The sentences with a TAM particle, or *bisa* in (15c), in the clause at issue. -/
def withParticle : List (Datum × Site) :=
  [(ex_10, .root), (ex_12a, .root), (ex_34d, .root), (ex_35c, .root), (ex_36c, .root),
    (ex_11c, .subordinate bahwa), (ex_15c, .subordinate agar)]

/-- The sentences without one in the clause at issue, whose alternatives add it. -/
def withoutParticle : List (Datum × Site) :=
  [(ex_11a, .complement ingin), (ex_12b, .complement menyuruh),
    (ex_13a, .complement mendorong), (ex_14a, .subordinate sambil),
    (ex_15a, .complement belajar), (ex_34a, .nominal), (ex_35a, .nominal), (ex_36a, .nominal),
    (ex_40a, .nominal)]

/-- A TAM particle is accepted in a clause exactly when the clause projects I: in a root clause
and after *bahwa* and *agar*, and not in the controlled complements of *ingin*, *menyuruh*,
*mendorong* and *belajar*, after *sambil*, or on a nominalisation in *=nya* ((10) to (15),
(34) to (36), (40)). -/
theorem particle_iff_projectsI :
    (∀ x ∈ withParticle, x.1.judgment.band = .ofProp x.2.ProjectsI ∧
      ∀ alt ∈ x.1.alternatives, alt.2.band = .ofProp x.2.ProjectsI) ∧
      ∀ x ∈ withoutParticle, x.1.alternatives ≠ [] ∧
        ∀ alt ∈ x.1.alternatives, alt.2.band = .ofProp x.2.ProjectsI := by
  decide +kernel

/-! ### Nominalisation in *=nya* -/

/-- The sentences in which a verb of saying or feeling, a modal or an evidential root is
nominalised by *=nya*. -/
def nominalisations : List Datum :=
  [ex_34a, ex_34b, ex_35a, ex_36a, ex_37b, ex_38b, ex_39b, ex_40a, ex_42b, ex_43a, ex_43b,
    ex_46a, ex_46b, ex_48a, ex_48b, ex_52a, ex_52b, ex_53]

/-- The position relative to the moment of speech that a reading or an annotation names. -/
def axisOf (name : String) : Option Ordering :=
  [("past", Ordering.lt), ("present", .eq), ("future", .gt)].lookup name

/-- The times open to a state of affairs expressed with no TAM particle: the one its temporal
adjunct names, and without an adjunct any time for a verb and the past for a nominalisation in
*=nya*. -/
def Admits (nominalised : Prop) (adjunct : Option Ordering) (o : Ordering) : Prop :=
  match adjunct with
  | some a => o = a
  | none => nominalised → o = .lt

instance (nominalised : Prop) [Decidable nominalised] (adjunct : Option Ordering)
    (o : Ordering) : Decidable (Admits nominalised adjunct o) := by
  cases adjunct <;> unfold Admits <;> infer_instance

/-- The bare verb of (3) is read as past, present or future. The nominalisations of (34a),
(35a) and (36a) are read as past and not as future, and that of (34b), with *nanti* 'later',
as future. -/
theorem readings_iff_admits :
    ∀ e ∈ [ex_3, ex_34a, ex_34b, ex_35a, ex_36a], e.readings ≠ [] ∧
      ∀ rd ∈ e.readings, ∃ o ∈ axisOf rd.1,
        (rd.2 = .acceptable ↔ Admits (e ∈ nominalisations) (referenceOf e) o) := by
  decide +kernel

/-- The times of the state of affairs under a modal: the future under a bare modal, and the
past or the present under one nominalised by *=nya*, which evaluates it counterfactually. -/
def modalAxes (nominalised : Prop) [Decidable nominalised] : List Ordering :=
  if nominalised then [.lt, .eq] else [.gt]

-- (37) to (39): the printed time of each state of affairs
theorem soa_mem_modalAxes :
    ∀ e ∈ [ex_37a, ex_37b, ex_38a, ex_38b, ex_39a, ex_39b], e.features "soa" ≠ [] ∧
      ∀ s ∈ e.features "soa", ∃ o ∈ axisOf s, o ∈ modalAxes (e ∈ nominalisations) := by
  decide +kernel

/-! ### The equational structure -/

/-- What stands after the copula or the negator: a verb, a noun, a nominalisation in *=nya*, or
a verb heading a clause in a nominal slot, as *tidur* in (46b). -/
inductive Predicate where
  | verb
  | noun
  | nominalisation
  | clause
  deriving DecidableEq, Repr

/-- The predicate occupies a nominal slot. -/
def Predicate.IsNominal (p : Predicate) : Prop := p ≠ .verb

instance : DecidablePred Predicate.IsNominal := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The predicate is headed by a verb. -/
def Predicate.IsVerbal (p : Predicate) : Prop := p = .verb ∨ p = .clause

instance : DecidablePred Predicate.IsVerbal := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The sentences printed with *adalah* before the predicate. -/
def copular : List (Datum × Option Predicate) :=
  [(ex_45a, some .noun), (ex_45b, some .noun), (ex_46a, some .nominalisation),
    (ex_46b, some .clause)]

/-- The sentences whose alternatives add *adalah*: before a verb in (44), and between *katanya*
and the clause it goes with in (52), where *katanya* is an adjunct and there is no predicate
after the copula. -/
def copularAlternatives : List (Datum × Option Predicate) :=
  [(ex_44a, some .verb), (ex_52a, none), (ex_52b, none)]

/-- The copula *adalah* is accepted exactly before a nominal predicate: a noun, a
nominalisation in *=nya* or a clause in a nominal slot, and not a verb, nor beside the adjunct
*katanya* ((44) to (46), (52)). -/
theorem adalah_iff :
    (∀ x ∈ copular, x.1.judgment.band = .ofProp (∃ p ∈ x.2, p.IsNominal)) ∧
      ∀ x ∈ copularAlternatives, x.1.alternatives ≠ [] ∧
        ∀ alt ∈ x.1.alternatives, alt.2.band = .ofProp (∃ p ∈ x.2, p.IsNominal) := by
  decide +kernel

/-- The sentences negated by *bukan*, whose alternatives have *tidak*. -/
def negated : List (Datum × Predicate) :=
  [(ex_47a, .noun), (ex_47b, .noun), (ex_48a, .nominalisation), (ex_48b, .clause)]

/-- *Bukan* negates a nominal predicate and *tidak* one headed by a verb, so the *tidur* of
(48b), a verb heading a clause in a nominal slot, takes either ((47), (48)). -/
theorem negation :
    ∀ x ∈ negated, x.1.judgment.band = .ofProp x.2.IsNominal ∧ x.1.alternatives ≠ [] ∧
      ∀ alt ∈ x.1.alternatives, alt.2.band = .ofProp x.2.IsVerbal := by
  decide +kernel

end Arka2013
