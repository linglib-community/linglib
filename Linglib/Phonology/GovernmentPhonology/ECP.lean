/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.GovernmentPhonology.Basic
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Finset.Basic

/-!
# The Empty Category Principle

A nucleus may stay unexpressed when it is governed, when it is enclosed in a domain of
infrasegmental government, or when it is final in a language whose final nuclei may be empty.
Since a governed nucleus governs nothing, of two successive unexpressed nuclei
[one is enclosed](##GovernmentPhonology.SatisfiesECP.enclosed_or_enclosed). Where alternation with zero is
obligatory, the realization of a domain is fixed from the right, each nucleus unexpressed
exactly when its silence is licensed, and the principle [holds of it](##GovernmentPhonology.satisfiesECP_obligatory).
In a word of alternating vowels the outcome depends on whether such a vowel, once expressed,
is strong enough to govern another: where it is, [every other one](##GovernmentPhonology.expressed_obligatory_iff_even)
is expressed, counting from the end, and where it is not, [all but the last](##GovernmentPhonology.expressed_obligatory_iff_succ_lt)
are.

## Implementation notes

The realization takes the set of nuclei that are required to be expressed on grounds the
lateral relations do not give. Alternation is optional in some languages, and the realization
here is the obligatory one.

## TODO

Every theorem is stated and unproved.

## References

* [kaye-lowenstamm-vergnaud-1990]
* [scheer-2004]
* [scheer-cyran-2018]
-/

@[expose] public section

namespace GovernmentPhonology

variable (A : Actorship) (l : List Nucleus) {i : ℕ}

/-- The Empty Category Principle ([scheer-2004] (53)): associated melody is expressed, and a
nucleus is unexpressed only if it is governed, enclosed in a domain of infrasegmental
government, or final where final nuclei may be empty. -/
structure SatisfiesECP : Prop where
  /-- Associated melody is expressed. -/
  expressed_of_associated : ∀ x ∈ l, x.melody = .associated → x.expressed = true
  /-- The silence of an unexpressed nucleus is licensed. -/
  licensed : ∀ i, (∃ x ∈ l[i]?, x.expressed = false) →
    Governed A l i ∨ Enclosed A l i ∨ i + 1 = l.length ∧ A.finalEmpty = true

variable {A l}

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
    if x.melody ≠ .associated ∧ i ∉ R ∧ (GovernedHead A (silent :: r') ∨
        EnclosedHead A (silent :: r') ∨ r = [] ∧ A.finalEmpty = true) then
      silent :: r'
    else { x with expressed := true } :: r'

variable (A) in
/-- The obligatory realization of a domain, in which every nucleus that may be unexpressed is,
except those of `R`. -/
def obligatory (R : Finset ℕ) (l : List Nucleus) : List Nucleus := obligatoryFrom A R 0 l

variable {R : Finset ℕ}

theorem length_obligatory : (obligatory A R l).length = l.length := by
  sorry

/-- The obligatory realization changes only which nuclei are expressed. -/
theorem map_obligatory : (obligatory A R l).map ({ · with expressed := false }) =
    l.map ({ · with expressed := false }) := by
  sorry

theorem satisfiesECP_obligatory : SatisfiesECP A (obligatory A R l) := by
  sorry

/-- A domain is its own obligatory realization exactly when each nucleus is expressed just in
case it has associated melody, is required to be expressed, or would not have its silence
licensed. -/
theorem obligatory_eq_self_iff : obligatory A R l = l ↔
    ∀ i x, l[i]? = some x → (x.expressed = true ↔ x.melody = .associated ∨ i ∈ R ∨
      ¬ (Governed A (l.set i { x with expressed := false }) i ∨
        Enclosed A (l.set i { x with expressed := false }) i ∨
        i + 1 = l.length ∧ A.finalEmpty = true)) := by
  sorry

variable (A) in
/-- An unexpressed final alternating vowel is too weak to govern another. -/
def FinalFloatingInert : Prop := ∀ x : Nucleus, x.melody = .floating → x.expressed = false →
  A.strength x true < (Melody.floating : WithBot Melody)

/-- Havlík's Law ([scheer-2004] (304)): where an expressed alternating vowel governs another, a
word of alternating vowels expresses those at an even distance from its end, the last standing
at distance one. -/
theorem expressed_obligatory_iff_even (hl : ∀ x ∈ l, x.melody = .floating)
    (he : A.finalEmpty = true) (hf : FinalFloatingInert A)
    (hs : ∀ x : Nucleus, x.melody = .floating → x.expressed = true →
      (Melody.floating : WithBot Melody) ≤ A.strength x false) :
    (∃ x ∈ (obligatory A ∅ l)[i]?, x.expressed = true) ↔ i < l.length ∧ Even (l.length - i) := by
  sorry

/-- Lower: where an expressed alternating vowel does not govern another, a word of alternating
vowels expresses all but the last. -/
theorem expressed_obligatory_iff_succ_lt (hl : ∀ x ∈ l, x.melody = .floating)
    (he : A.finalEmpty = true) (hf : FinalFloatingInert A)
    (hs : ∀ x : Nucleus, x.melody = .floating → x.expressed = true →
      A.strength x false < (Melody.floating : WithBot Melody)) :
    (∃ x ∈ (obligatory A ∅ l)[i]?, x.expressed = true) ↔ i + 1 < l.length := by
  sorry

end GovernmentPhonology
