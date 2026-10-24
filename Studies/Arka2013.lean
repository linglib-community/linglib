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

/-!
# Arka 2013: the typology and syntax of TAM in Indonesian

Indonesian has no grammatical TAM: there is no obligatory morphosyntactic opposition, a bare
verb is anchored in time by context or by an optional adjunct, and the perfect auxiliary
*sudah/telah* expresses only that the event precedes the reference time, which is free to sit
at the moment of speech or in the past — so Klein's puzzle about the English present perfect,
which pins the reference time to the present, does not arise. The language nonetheless
shows finiteness: the TAM auxiliaries occupy I, a finite clause projects IP whether or not an
auxiliary is present, and truncated or controlled complements, resultatives, and *sambil*
adjuncts are bare VPs that admit none of them, while nominal predicates project no I at all.
The clitic *=nya* nominalises verbs of saying and feeling, modals, and evidential roots; a
nominalisation carries a default past temporal axis that an adjunct like *nanti* cancels, a
nominalised modal reports a past or present state of affairs counterfactually where the bare
modal points to a future one, and the copula *adalah* and the negator *bukan* show that these
structures are equational.

## Main definitions

* `Annotation`: the paper's E/R/S annotations, with `Annotation.frame` the Reichenbach
  frame they describe.
* `auxiliaries`, `frame`: the auxiliaries of I among the fragment's aspect markers, and the frame
  relation the paper reads off the viewpoint of each; `englishPresentPerfect` the English
  contrast.
* `ProjectsI`: a clause projects I exactly when its complement coding is not reduced; the
  selecting verbs and subordinators are fragment entries.

## References

* [arka-2013]
* [klein-1992] — the present perfect puzzle
* [kibort-2009] — languages grammaticalise different E, R, S configurations
* [sneddon-1996] — the aspect markers of the fragment
-/

@[expose] public section

namespace Arka2013


open Tense Indonesian Indonesian.Aspect

/-! ### Tense theory and the status of Indonesian TAM (§2) -/

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

/-- The TAM auxiliaries among the fragment's aspect markers, *sudah/telah* 'PERF', *sedang* 'PROG'
and *akan* 'FUT', which occupy I (16). The paper's fifth auxiliary, the volitive *mau* 'want', is
not an aspect marker. -/
def auxiliaries : List Aspect.Marker := [sudah, telah, sedang, akan]

/-- The auxiliary written as a form. -/
def auxiliary? (s : String) : Option Aspect.Marker :=
  auxiliaries.find? (·.morphs = [.free s])

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

theorem rows_annotations :
    ∀ r ∈ Examples.all, ∀ m ∈ (r.feature? "aux" >>= auxiliary?).toList,
      ∀ ann ∈ (r.feature? "frame" >>= Annotation.parse?).toList, frame m.viewpoint ann.frame := by
  decide +kernel

/-- The annotations of the sentences with a perfect auxiliary, the *sudah* sentences of (5). -/
def sudahAnnotations : List Annotation :=
  Examples.all.filterMap fun r => do
    let m ← r.feature? "aux" >>= auxiliary?
    guard (m.viewpoint = .perfect)
    r.feature? "frame" >>= Annotation.parse?

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

/-- With a past reference time, the English present perfect is contradictory while *sudah* is
satisfiable, as in (5b). -/
theorem klein_puzzle_dissolved :
    (∀ f : ReichenbachFrame ℤ, englishPresentPerfect f → f.referencePosition ≠ .lt) ∧
      ∃ f : ReichenbachFrame ℤ, frame sudah.viewpoint f ∧ f.referencePosition = .lt :=
  ⟨fun _ h ↦ h.2 ▸ by decide, ⟨.root 2 1 0, by decide⟩⟩

theorem english_pp_strictly_stronger {T : Type*} [LinearOrder T] :
    (∀ f : ReichenbachFrame T, englishPresentPerfect f → frame sudah.viewpoint f) ∧
      ∃ f : ReichenbachFrame ℤ, frame sudah.viewpoint f ∧ ¬ englishPresentPerfect f :=
  ⟨fun _ h ↦ h.1, ⟨.root 2 1 0, by decide⟩⟩

/-! ### Finiteness (§3) -/

/-- The verb selecting a row's complement clause, from the fragment. -/
def matrixVerb : String → Option Verb
  | "ingin" => some Complementation.ingin
  | "belajar" => some Complementation.belajar
  | "menyuruh" => some Complementation.menyuruh
  | "mendorong" => some Complementation.mendorong
  | "tahu" => some Complementation.tahu
  | _ => none

/-- The subordinator typing a row's dependent clause, from the fragment. -/
def subordinator : String → Option Complementizer
  | "bahwa" => some Complementation.bahwa
  | "agar" => some Complementation.agar
  | _ => none

/-- A clause projects I — the position of the TAM auxiliaries (16) — exactly when its coding is
finite: a full clause anchors its own temporal axis, a reduced complement is a bare VP (17). -/
def ProjectsI (c : Clause.ComplementType) : Prop := c.IsFinite

instance : DecidablePred ProjectsI := fun c ↦ inferInstanceAs (Decidable c.IsFinite)

/-- The coding of the clause a verb's basic frame selects. -/
def complementCoding (v : Verb) : Option Clause.ComplementType :=
  v.valency.frames.head?.bind fun fr => fr.codings.head?

theorem rows_finiteness :
    ∀ r ∈ Examples.all,
      (∀ v ∈ (r.feature? "matrix" >>= matrixVerb).toList, ∀ c ∈ (complementCoding v).toList,
        (ProjectsI c ↔ r.feature? "withAux" = some "acceptable")) ∧
      (∀ s ∈ (r.feature? "subordinator" >>= subordinator).toList, ∀ c ∈ s.coding.toList,
        (ProjectsI c ↔ r.feature? "withAux" = some "acceptable")) ∧
      (r.feature? "clause" = some "root" → r.feature? "withAux" = some "acceptable") ∧
      (r.feature? "predicate" = some "nominal" →
        ∀ j ∈ (r.feature? "withAux").toList, j ≠ "acceptable") := by
  decide +kernel

/-! ### Morphosemantic TAM: *=nya* nominalisation (§4) -/

/-- The default past axis of a nominalisation is cancelled exactly by a future adjunct
(34)–(36). -/
theorem rows_nya_default_past :
    ∀ r ∈ Examples.all, r.feature? "nominalised" = some "true" →
      ∀ axis ∈ (r.feature? "axis").toList,
        (axis = "future" ↔ r.feature? "adjunct" = some "nanti") := by
  decide +kernel

/-- A bare modal evaluates a future state of affairs; its nominalisation a past or present
one (37)–(39). -/
theorem rows_modal_nominalisation :
    ∀ r ∈ Examples.all, ∀ soa ∈ (r.feature? "soa").toList,
      (soa = "future" ↔ r.feature? "nominalised" = some "false") := by
  decide +kernel

/-- The copula *adalah* and the negator *bukan* take nominal predicates only, the
nominalisations among them (44)–(48). -/
theorem rows_equational :
    ∀ r ∈ Examples.all, ∀ key ∈ ["adalah", "bukan"], ∀ j ∈ (r.feature? key).toList,
      (j = "acceptable" ↔ r.feature? "predicate" = some "nominal") := by
  decide +kernel

end Arka2013
