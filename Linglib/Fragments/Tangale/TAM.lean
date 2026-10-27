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

The `subjectVE` field records whether Kidda's examples show the subject's final vowel eliding
before the verb. It elides in the perfective and not where *wa*, *né* or *-n* intervenes
(`subjectVE_iff_no_marker`), the morphological ground for the focus-marking asymmetry between
perfective and progressive clauses in [hartmann-zimmermann-2004]. [jungraithmayr-1991] is the
lexical companion source.
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

/-- One row of [kidda-1985]'s tense–aspect paradigm: the verb-final suffix alternants, the
distinctive marker, and whether the preceding subject's final vowel elides where an example shows
it, (23) and (24a–c). -/
structure TAMEntry where
  tam : TAM
  suffixAlternants : List String
  marker : Marker
  subjectVE : Option Bool
  deriving DecidableEq, Repr

/-- Perfective, singular-object suffix set (voicing × harmony
alternants). -/
def perfectiveSg : TAMEntry :=
  ⟨.perfective, ["kó", "kọ́", "gó", "gọ́"], .none, some true⟩

/-- Perfective, plural-object suffix set — the *o → u* raising variant
of the singular. -/
def perfectivePl : TAMEntry :=
  ⟨.perfective, ["kú", "kụ́", "gú", "gụ́"], .none, some true⟩

/-- Perfective for action performed at a location different from the
speaker's. -/
def perfectiveDistal : TAMEntry := ⟨.perfective, ["ná"], .none, none⟩

/-- Imperfective imperative, which has no overt subject. -/
def imperative : TAMEntry := ⟨.imperative, ["u", "ụ"], .none, none⟩

/-- Future: *-é* plus preposed *wa*. -/
def future : TAMEntry := ⟨.future, ["é", "ẹ́"], .preposed "wa", some false⟩

/-- Continuous: *-é* plus preposed *né* — the progressive of
[hartmann-zimmermann-2004]'s focus examples. -/
def continuous : TAMEntry := ⟨.continuous, ["é", "ẹ́"], .preposed "né", some false⟩

/-- Habitual: *-é* plus *-n* cliticized to the subject. -/
def habitual : TAMEntry := ⟨.habitual, ["é", "ẹ́"], .subjectClitic "n", some false⟩

/-- Subjunctive: *-é* with no distinctive marker. Its example (24d) has no overt subject of its
own, the elided *Lak* standing before the matrix verb. -/
def subjunctive : TAMEntry := ⟨.subjunctive, ["é", "ẹ́"], .none, none⟩

/-- The full tense–aspect paradigm. -/
def tamEntries : List TAMEntry :=
  [perfectiveSg, perfectivePl, perfectiveDistal, imperative,
   future, continuous, habitual, subjunctive]

theorem imperfectives_share_suffix :
    ∀ e ∈ tamEntries,
      (e.tam = .future ∨ e.tam = .continuous ∨ e.tam = .habitual ∨
       e.tam = .subjunctive) →
      e.suffixAlternants = ["é", "ẹ́"] := by decide

/-- Where an example shows it, the subject's final vowel elides exactly when no marker
intervenes: it elides in the perfective (23) and not before *wa*, *né* or *-n* (24a–c), p. 37. -/
theorem subjectVE_iff_no_marker :
    ∀ e ∈ tamEntries, ∀ b ∈ e.subjectVE, b = true ↔ e.marker = .none := by decide

end Tangale
