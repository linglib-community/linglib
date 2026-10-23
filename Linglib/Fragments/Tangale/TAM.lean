/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

module

/-!
# Tangale tense–aspect morphology

The six tense–aspect categories of Tangale (Kaltungo dialect) and
their exponence, from [kidda-1985]'s summary diagram: the perfective
and imperative are verb-final suffixes; the four imperfective
non-imperatives share the suffix *-é* and are distinguished by a
preposed particle (*wa* future, *né* continuous), the subject clitic
*-n* (habitual), or nothing (subjunctive). Suffix alternants are
conditioned by voicing of the preceding segment and tense–lax vowel
harmony (§1.19–1.20).

The `subjectVE` field records the (23)–(24) generalization: the
subject's final vowel elides unless *wa*, *né*, or *-n* intervenes —
the morphological ground for the focus-marking asymmetry between
perfective and progressive clauses in [hartmann-zimmermann-2004].
[jungraithmayr-1991] is the lexical companion source.
-/

@[expose] public section

namespace Tangale

/-- The six tense–aspect categories ([kidda-1985] §1.20). -/
inductive TAM where
  | perfective | imperative | future | continuous | habitual | subjunctive
  deriving DecidableEq, Repr

/-- The distinctive marker accompanying an aspect beyond the verb-final
suffix ([kidda-1985] §1.20). -/
inductive Marker where
  | none
  | preposed (form : String)
  | subjectClitic (form : String)
  deriving DecidableEq, Repr

/-- One row of [kidda-1985]'s tense–aspect paradigm: the verb-final
suffix alternants and the distinctive marker. `subjectVE` is the
(23)–(24) generalization: the preceding subject's final vowel elides
iff no marker intervenes. -/
structure TAMEntry where
  tam : TAM
  suffixAlternants : List String
  marker : Marker
  subjectVE : Bool
  deriving DecidableEq, Repr

/-- Perfective, singular-object suffix set (voicing × harmony
alternants). -/
def perfectiveSg : TAMEntry :=
  ⟨.perfective, ["kó", "kọ́", "gó", "gọ́"], .none, true⟩

/-- Perfective, plural-object suffix set — the *o → u* raising variant
of the singular. -/
def perfectivePl : TAMEntry :=
  ⟨.perfective, ["kú", "kụ́", "gú", "gụ́"], .none, true⟩

/-- Perfective for action performed at a location different from the
speaker's. -/
def perfectiveDistal : TAMEntry := ⟨.perfective, ["ná"], .none, true⟩

/-- Imperfective imperative. -/
def imperative : TAMEntry := ⟨.imperative, ["u", "ụ"], .none, true⟩

/-- Future: *-é* plus preposed *wa*. -/
def future : TAMEntry := ⟨.future, ["é", "ẹ́"], .preposed "wa", false⟩

/-- Continuous: *-é* plus preposed *né* — the progressive of
[hartmann-zimmermann-2004]'s focus examples. -/
def continuous : TAMEntry := ⟨.continuous, ["é", "ẹ́"], .preposed "né", false⟩

/-- Habitual: *-é* plus *-n* cliticized to the subject. -/
def habitual : TAMEntry := ⟨.habitual, ["é", "ẹ́"], .subjectClitic "n", false⟩

/-- Subjunctive: *-é* with no distinctive marker. -/
def subjunctive : TAMEntry := ⟨.subjunctive, ["é", "ẹ́"], .none, true⟩

/-- The full tense–aspect paradigm. -/
def tamEntries : List TAMEntry :=
  [perfectiveSg, perfectivePl, perfectiveDistal, imperative,
   future, continuous, habitual, subjunctive]

theorem imperfectives_share_suffix :
    ∀ e ∈ tamEntries,
      (e.tam = .future ∨ e.tam = .continuous ∨ e.tam = .habitual ∨
       e.tam = .subjunctive) →
      e.suffixAlternants = ["é", "ẹ́"] := by decide

/-- Subject-final vowel elision is blocked exactly by an intervening
marker ((23)–(24)): *wa*, *né*, and *-n* protect the subject's final
vowel; bare-suffix aspects elide it. -/
theorem subjectVE_iff_no_marker :
    ∀ e ∈ tamEntries, e.subjectVE ↔ e.marker = .none := by decide

end Tangale
