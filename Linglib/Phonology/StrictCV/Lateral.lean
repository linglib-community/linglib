/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Order.WithBot

/-!
# Lateral relations

In Strict CV syllable structure is a network of two lateral forces that nuclei discharge
leftwards. Government diminishes the melody of its target and licensing supports it. A nucleus
governs the nucleus before it when that nucleus is unexpressed and no more complex than the
governor is strong, and it governs its own onset otherwise; it licenses whichever of the two it
does not govern. Government between nuclei is [local](##StrictCV.Lateral.Governs.covBy), each
governor has [one target](##StrictCV.Lateral.Governs.eq_left), and a governed nucleus
[governs nothing](##StrictCV.Lateral.Governs.not_governs), so the governing pairs of a domain
are disjoint pairs of neighbours. How strong each nucleus is varies with the language and is
the theory's parameter. A consonant is weak when governed, strong when licensed and a coda when
its nucleus discharges nothing; a syllable is open when its nucleus is licensed. The Empty
Category Principle lets a nucleus stay unexpressed when it is governed, enclosed in a domain of
infrasegmental government, or final.

## Implementation notes

A domain is the list of its nuclei, each with its melody and whether it is phonetically
expressed, so that domains concatenate as lists. All relations are local, between a nucleus and
its own onset or the nucleus before it, as the handbook states the theory. Scheer's book lets
government apply over a domain of infrasegmental government instead, and the two agree on which
nuclei are unexpressed when the enclosed nucleus is as strong as a full one. What may support a
domain of infrasegmental government is open in the sources and is a field of the parameter.
Melody is ordered by complexity, and the strength of a nucleus is the most complex melody it
can govern, so that government obeys the complexity condition by definition.

## TODO

Every theorem is stated and unproved. Not stated: long vowels, whose empty complement calls for
licensing; degrees of licensing strength, by which a final empty nucleus may act and yet fail
to license length; stress; and a second, autosegmental licensing that every nucleus discharges.
Whether two consonants may contract infrasegmental government is a flag on the nucleus between
them and is not derived from their elements.

## References

* [scheer-2004]
* [scheer-zikova-2010]
* [cavirani-2022]
-/

@[expose] public section

namespace StrictCV.Lateral

/-! ### Nuclei -/

/-- The melody of a nucleus: none, melody that alternates with zero, or melody that is always
expressed. -/
inductive Melody
  /-- No melody. -/
  | empty
  /-- Melody that is expressed unless the nucleus is governed. -/
  | floating
  /-- Associated melody. -/
  | associated
  deriving DecidableEq, Repr

/-- The complexity of a melody. -/
def Melody.complexity : Melody → ℕ
  | .empty => 0
  | .floating => 1
  | .associated => 2

theorem Melody.complexity_injective : Function.Injective Melody.complexity := by
  rintro (_ | _ | _) (_ | _ | _) h <;> first | rfl | cases h

/-- Melodies are ordered by complexity. -/
instance : LinearOrder Melody := LinearOrder.lift' Melody.complexity Melody.complexity_injective

/-- A nucleus of a domain. -/
structure Nucleus where
  /-- The melody of the nucleus. -/
  melody : Melody
  /-- The nucleus is phonetically expressed. -/
  expressed : Bool := false
  /-- The consonants flanking the nucleus may contract infrasegmental government. -/
  cluster : Bool := false
  deriving DecidableEq, Repr

/-- The lateral actorship of a language: what each nucleus can do when it is not governed,
according to its melody, whether it is expressed, and whether it is final in its domain. -/
structure Actorship where
  /-- The most complex melody the nucleus can govern, `⊥` when it cannot govern. -/
  strength : Nucleus → Bool → WithBot Melody
  /-- The nucleus can license. -/
  licenses : Nucleus → Bool → Bool
  /-- The nucleus supports a domain of infrasegmental government whose governing consonant is
  its onset. -/
  supports : Nucleus → Bool → Bool

/-- The actorship of the Lateral Theory of Phonology. A full nucleus governs anything and
licenses. An empty nucleus that is unexpressed and not final, which is ungoverned only when it is
enclosed, does the same. Schwa, a nucleus expressed without associated melody, and the
unexpressed final nucleus have the strengths `schwa` and `final` and license as
`schwaLicenses` and `finalLicenses` say. Expressed nuclei support a domain of infrasegmental
government, and the unexpressed final nucleus does where `finalSupports`. -/
def Actorship.ltp (schwa final : WithBot Melody)
    (schwaLicenses finalLicenses finalSupports : Bool) : Actorship where
  strength x isFinal :=
    if x.expressed then (if x.melody = .associated then ↑Melody.associated else schwa)
    else if isFinal then final
    else if x.melody = .empty then ↑Melody.associated else ⊥
  licenses x isFinal :=
    if x.expressed then (decide (x.melody = .associated) || schwaLicenses)
    else if isFinal then finalLicenses else decide (x.melody = .empty)
  supports x isFinal := x.expressed || (isFinal && finalSupports)

variable (A : Actorship) (l : List Nucleus) {i j k : ℕ}

/-! ### Government between nuclei -/

/-- The first nucleus of a stretch is enclosed in a domain of infrasegmental government: it is
unexpressed and empty, its flanking consonants may contract government, and the next nucleus
supports the domain. -/
def EnclosedHead : List Nucleus → Prop
  | x :: y :: r => x.expressed = false ∧ x.melody = .empty ∧ x.cluster = true ∧
      A.supports y (decide (r = [])) = true
  | _ => False

instance : DecidablePred (EnclosedHead A)
  | [] | [_] => isFalse fun h ↦ h
  | _ :: _ :: _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The first nucleus of a stretch is governed by the next: it is unexpressed and not enclosed,
and the next nucleus is not itself governed and is strong enough for its melody. -/
def GovernedHead : List Nucleus → Prop
  | [] => False
  | x :: r => x.expressed = false ∧ ¬ EnclosedHead A (x :: r) ∧ ¬ GovernedHead r ∧
      ∃ y ∈ r.head?, (x.melody : WithBot Melody) ≤ A.strength y (decide (r.tail = []))

instance instDecidablePredGovernedHead : DecidablePred (GovernedHead A)
  | [] => isFalse fun h ↦ h
  | _ :: r =>
    have := instDecidablePredGovernedHead r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Nucleus `i` is enclosed in a domain of infrasegmental government. -/
def Enclosed (i : ℕ) : Prop := EnclosedHead A (l.drop i)

/-- Nucleus `i` is governed. -/
def Governed (i : ℕ) : Prop := GovernedHead A (l.drop i)

/-- Nucleus `j` governs nucleus `i`. -/
def Governs (j i : ℕ) : Prop := i + 1 = j ∧ Governed A l i

/-- Nucleus `j` is a governor: it is not governed and has some strength. -/
def IsGovernor (j : ℕ) : Prop :=
  ¬ Governed A l j ∧ ∃ x ∈ l[j]?, A.strength x (decide (j + 1 = l.length)) ≠ ⊥

/-- Nucleus `j` is a licensor: it is not governed and can license. -/
def IsLicensor (j : ℕ) : Prop :=
  ¬ Governed A l j ∧ ∃ x ∈ l[j]?, A.licenses x (decide (j + 1 = l.length)) = true

/-- Nucleus `j` governs its own onset, which it does when it governs no nucleus. -/
def GovernsOnset (j : ℕ) : Prop := IsGovernor A l j ∧ ∀ i, ¬ Governs A l j i

/-- Nucleus `j` licenses its own onset, which it does when it does not govern it. -/
def LicensesOnset (j : ℕ) : Prop := IsLicensor A l j ∧ ¬ GovernsOnset A l j

/-- Nucleus `j` licenses nucleus `i`, the nucleus before it, which it does when it governs its
own onset. -/
def Licenses (j i : ℕ) : Prop := i + 1 = j ∧ IsLicensor A l j ∧ GovernsOnset A l j

instance : DecidablePred (Enclosed A l) := fun _ ↦ inferInstanceAs (Decidable (EnclosedHead A _))

instance : DecidablePred (Governed A l) := fun _ ↦ inferInstanceAs (Decidable (GovernedHead A _))

instance : Decidable (Governs A l j i) := inferInstanceAs (Decidable (_ ∧ _))

variable {A l}

theorem governed_iff : Governed A l i ↔ ¬ Enclosed A l i ∧ ¬ Governed A l (i + 1) ∧
    ∃ x ∈ l[i]?, x.expressed = false ∧ ∃ y ∈ l[i + 1]?,
      (x.melody : WithBot Melody) ≤ A.strength y (decide (i + 2 = l.length)) := by
  sorry

/-- The lateral relations of a stretch are those it has at the end of any longer domain. -/
theorem governed_append (l₁ l₂ : List Nucleus) :
    Governed A (l₁ ++ l₂) (i + l₁.length) ↔ Governed A l₂ i := by
  sorry

namespace Governs

/-- Government is local: the governed nucleus is the one before the governor. -/
theorem covBy (h : Governs A l j i) : i ⋖ j := by
  sorry

/-- A governor governs one nucleus. -/
theorem eq_left (h : Governs A l j i) (h' : Governs A l j k) : i = k := by
  sorry

/-- A nucleus is governed by one governor. -/
theorem eq_right (h : Governs A l j i) (h' : Governs A l k i) : j = k := by
  sorry

/-- A governed nucleus governs nothing. -/
theorem not_governs (h : Governs A l j i) : ¬ Governs A l i k := by
  sorry

/-- The governed nucleus is unexpressed. -/
theorem not_expressed (h : Governs A l j i) : ∃ x ∈ l[i]?, x.expressed = false := by
  sorry

protected theorem isGovernor (h : Governs A l j i) : IsGovernor A l j := by
  sorry

end Governs

/-! ### The distribution of the two forces -/

/-- A governor discharges its government, on the nucleus before it or on its own onset. -/
theorem isGovernor_iff : IsGovernor A l j ↔ GovernsOnset A l j ∨ ∃ i, Governs A l j i := by
  sorry

/-- A licensor discharges its licensing, on its own onset or on the nucleus before it, unless
it is the first nucleus and governs its onset. -/
theorem isLicensor_iff : IsLicensor A l j ↔ LicensesOnset A l j ∨ (∃ i, Licenses A l j i) ∨
    j = 0 ∧ IsLicensor A l 0 ∧ GovernsOnset A l 0 := by
  sorry

/-- No onset is both governed and licensed. -/
theorem not_governsOnset_and_licensesOnset : ¬ (GovernsOnset A l j ∧ LicensesOnset A l j) := by
  sorry

/-- No nucleus is both governed and licensed. -/
theorem not_governs_and_licenses : ¬ (Governs A l j i ∧ Licenses A l k i) := by
  sorry

/-- The Coda Mirror: where a governor licenses, a consonant is licensed exactly when its
nucleus governs the nucleus before it, or licenses without governing. -/
theorem licensesOnset_iff (h : IsGovernor A l (i + 1) → IsLicensor A l (i + 1)) :
    LicensesOnset A l (i + 1) ↔
      Governs A l (i + 1) i ∨ IsLicensor A l (i + 1) ∧ ¬ IsGovernor A l (i + 1) := by
  sorry

/-- A consonant is a coda, neither governed nor licensed, exactly when its nucleus neither
governs nor licenses, as a governed nucleus does not. -/
theorem not_governsOnset_and_not_licensesOnset_iff :
    ¬ GovernsOnset A l j ∧ ¬ LicensesOnset A l j ↔ ¬ IsGovernor A l j ∧ ¬ IsLicensor A l j := by
  sorry

/-- A nucleus is licensed exactly when the next nucleus licenses, governs, and does not govern
it. -/
theorem licenses_iff : Licenses A l (i + 1) i ↔
    IsLicensor A l (i + 1) ∧ IsGovernor A l (i + 1) ∧ ¬ Governed A l i := by
  sorry

/-! ### The Empty Category Principle -/

variable (A l) in
/-- The Empty Category Principle: associated melody is expressed, and a nucleus is unexpressed
only if it is governed, enclosed in a domain of infrasegmental government, or final. -/
structure SatisfiesECP : Prop where
  /-- Associated melody is expressed. -/
  expressed_of_associated : ∀ x ∈ l, x.melody = .associated → x.expressed = true
  /-- The silence of an unexpressed nucleus is licensed. -/
  licensed : ∀ i, (∃ x ∈ l[i]?, x.expressed = false) →
    Governed A l i ∨ Enclosed A l i ∨ i + 1 = l.length

/-- Of two successive unexpressed nuclei before the last, one is enclosed. -/
theorem SatisfiesECP.enclosed_or_enclosed (h : SatisfiesECP A l) {x y : Nucleus}
    (hx : l[i]? = some x) (hy : l[i + 1]? = some y) (hxe : x.expressed = false)
    (hye : y.expressed = false) (hl : i + 2 < l.length) :
    Enclosed A l i ∨ Enclosed A l (i + 1) := by
  sorry

/-! ### The obligatory realization -/

variable (A) in
/-- The obligatory realization of a stretch whose first nucleus is nucleus `i` of its domain:
from the right, a nucleus is left unexpressed exactly when its silence is licensed, unless it
has associated melody or is one of `R`, the nuclei required to be expressed. -/
def obligatoryFrom (R : Finset ℕ) : ℕ → List Nucleus → List Nucleus
  | _, [] => []
  | i, x :: r =>
    let r' := obligatoryFrom R (i + 1) r
    let silent : Nucleus := { x with expressed := false }
    if x.melody ≠ .associated ∧ i ∉ R ∧
        (GovernedHead A (silent :: r') ∨ EnclosedHead A (silent :: r') ∨ r = []) then
      silent :: r'
    else { x with expressed := true } :: r'

variable (A) in
/-- The obligatory realization of a domain, in which every nucleus that may be unexpressed is,
except those of `R`. -/
def obligatory (R : Finset ℕ) (l : List Nucleus) : List Nucleus := obligatoryFrom A R 0 l

variable {R : Finset ℕ}

@[simp] theorem length_obligatory : (obligatory A R l).length = l.length := by
  sorry

/-- The obligatory realization changes only which nuclei are expressed. -/
theorem map_obligatory : (obligatory A R l).map ({ · with expressed := false }) =
    l.map ({ · with expressed := false }) := by
  sorry

theorem satisfiesECP_obligatory : SatisfiesECP A (obligatory A R l) := by
  sorry

/-- A domain is its own obligatory realization exactly when it satisfies the Empty Category
Principle, expresses the required nuclei, and expresses no other nucleus without associated
melody whose silence would be licensed. -/
theorem obligatory_eq_self_iff : obligatory A R l = l ↔ SatisfiesECP A l ∧
    ∀ i x, l[i]? = some x → (x.expressed = true ↔ x.melody = .associated ∨ i ∈ R ∨
      ¬ (Governed A (l.set i { x with expressed := false }) i ∨
        Enclosed A (l.set i { x with expressed := false }) i ∨ i + 1 = l.length)) := by
  sorry

/-- Havlík's Law: where an expressed alternating vowel governs another and an unexpressed final
one does not, a word of alternating vowels expresses those at an even distance from its end,
the last standing at distance one. -/
theorem expressed_obligatory_of_governs (hl : ∀ x ∈ l, x.melody = .floating)
    (hs : ∀ x b, x.melody = .floating → x.expressed = true →
      (Melody.floating : WithBot Melody) ≤ A.strength x b)
    (hf : ∀ x, x.melody = .floating → x.expressed = false →
      A.strength x true < (Melody.floating : WithBot Melody)) :
    (∃ x ∈ (obligatory A ∅ l)[i]?, x.expressed = true) ↔ i < l.length ∧ Even (l.length - i) := by
  sorry

/-- Lower: where no alternating vowel governs another, a word of alternating vowels expresses
all but the last. -/
theorem expressed_obligatory_of_not_governs (hl : ∀ x ∈ l, x.melody = .floating)
    (hs : ∀ x b, x.melody = .floating → A.strength x b < (Melody.floating : WithBot Melody)) :
    (∃ x ∈ (obligatory A ∅ l)[i]?, x.expressed = true) ↔ i + 1 < l.length := by
  sorry

end StrictCV.Lateral
