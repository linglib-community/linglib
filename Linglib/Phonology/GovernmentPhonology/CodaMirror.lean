/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.GovernmentPhonology.Basic

/-!
# The Coda Mirror

A nucleus that can govern does, and a nucleus that can license does. Government goes to the
preceding nucleus when the governor governs it and to the governor's own onset otherwise.
Licensing goes to the licensor's own onset unless that onset is governed, and then to the
preceding nucleus, so that [no position](##GovernmentPhonology.not_governsOnset_and_licensesOnset) is both
governed and licensed. A consonant is weak when governed, as between two vowels,
[strong](##GovernmentPhonology.licensesOnset_iff) when licensed, as after a governed nucleus, and
[a coda](##GovernmentPhonology.not_governsOnset_and_not_licensesOnset_iff) when its nucleus discharges
nothing; a syllable is open when its nucleus [is licensed](##GovernmentPhonology.licenses_iff).

## Implementation notes

The first nucleus of a domain has no nucleus before it, so when it governs its onset its
licensing lands nowhere. A licensor that cannot govern licenses its own onset and never the
preceding nucleus.

## TODO

Every theorem is stated and unproved. Long vowels are not represented: their empty complement
calls for licensing, which would take the licensing of a nucleus that cannot govern. Stress is
not represented, nor a second, autosegmental licensing that every nucleus discharges.

## References

* [segeral-scheer-2001]
* [scheer-zikova-2010]
* [scheer-cyran-2018]
-/

@[expose] public section

namespace GovernmentPhonology

variable (A : Actorship) (l : List Nucleus) {i j k : ℕ}

/-- Nucleus `j` governs its own onset, which it does when it governs no nucleus. -/
def GovernsOnset (j : ℕ) : Prop := IsGovernor A l j ∧ ∀ i, i + 1 = j → ¬ Governed A l i

/-- Nucleus `j` licenses its own onset, which it does when it does not govern it. -/
def LicensesOnset (j : ℕ) : Prop := IsLicensor A l j ∧ ¬ GovernsOnset A l j

/-- Nucleus `j` licenses nucleus `i`, the nucleus before it, which it does when it governs its
own onset. -/
def Licenses (j i : ℕ) : Prop := i + 1 = j ∧ IsLicensor A l j ∧ GovernsOnset A l j

instance : DecidablePred (GovernsOnset A l)
  | 0 => decidable_of_iff (IsGovernor A l 0) (by simp [GovernsOnset])
  | j + 1 => decidable_of_iff (IsGovernor A l (j + 1) ∧ ¬ Governed A l j) (by simp [GovernsOnset])

instance : DecidablePred (LicensesOnset A l) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (Licenses A l j i) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {A l}

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

/-- Where a governor licenses, a consonant is licensed exactly when its nucleus governs the
nucleus before it, or licenses without governing. -/
theorem licensesOnset_iff (h : IsGovernor A l (i + 1) → IsLicensor A l (i + 1)) :
    LicensesOnset A l (i + 1) ↔
      Governs A l (i + 1) i ∨ IsLicensor A l (i + 1) ∧ ¬ IsGovernor A l (i + 1) := by
  sorry

/-- A consonant is neither governed nor licensed exactly when its nucleus neither governs nor
licenses, as a governed nucleus does not. -/
theorem not_governsOnset_and_not_licensesOnset_iff :
    ¬ GovernsOnset A l j ∧ ¬ LicensesOnset A l j ↔ ¬ IsGovernor A l j ∧ ¬ IsLicensor A l j := by
  sorry

/-- A nucleus is licensed exactly when the next nucleus licenses, governs, and does not govern
it. -/
theorem licenses_iff : Licenses A l (i + 1) i ↔
    IsLicensor A l (i + 1) ∧ IsGovernor A l (i + 1) ∧ ¬ Governed A l i := by
  sorry

end GovernmentPhonology
