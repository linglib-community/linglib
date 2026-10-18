/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morphotactics.CVTemplate
public import Linglib.Phonology.Autosegmental.Floating
public import Linglib.Phonology.StrictCV.Basic

/-!
# Strict CV skeletons

A strict-CV skeleton is a sequence of CV units, consonantal and vocalic slots in strict
alternation. The units of a form are numbered from the left, unit `j` having its onset at slot
`2j` and its nucleus at slot `2j + 1`. A candidate presents the profile that the lateral
computation reads: the nuclei that host melody, and the units whose onset may be governed by the
next onset, as two consonants that contract infrasegmental government.

## Main definitions

* `StrictCV.IsStrict`: the skeleton is a sequence of CV units.
* `StrictCV.units`, `StrictCV.onset`, `StrictCV.nucleus`: the CV units and their slots.
* `StrictCV.hosting`, `StrictCV.clusters`: the nuclei of a candidate that host melody, and the
  units whose onsets may contract infrasegmental government.

## References

* [lowenstamm-1996]
* [scheer-2004]
-/

@[expose] public section

namespace StrictCV

open Autosegmental
open Morphology (CVSlot)

variable {T M : Type*} (u : Autosegmental.Form CVSlot T M)

/-- A skeleton is strict when it is a sequence of CV units. -/
def IsStrict : Prop :=
  u.lower.map (·.value) = (List.replicate (u.lower.length / 2) [.C, .V]).flatten

instance : Decidable (IsStrict u) := inferInstanceAs (Decidable (_ = _))

/-- The number of CV units. -/
def units : ℕ := u.lower.length / 2

/-- The onset of CV unit `j`. -/
def onset (j : Fin (units u)) : Fin u.lower.length :=
  ⟨2 * j, by have := j.isLt; unfold units at this; omega⟩

/-- The nucleus of CV unit `j`. -/
def nucleus (j : Fin (units u)) : Fin u.lower.length :=
  ⟨2 * j + 1, by have := j.isLt; unfold units at this; omega⟩

variable {u} (c : Candidate u)

/-- The nuclei that host an object satisfying `P` on the surface. -/
def hosting (P : T → Prop) [DecidablePred P] : Finset (Fin (units u)) :=
  Finset.univ.filter fun j ↦ ∃ t ∈ c.tierValues (nucleus u j), P t

/-- The units whose onset may be governed by the next onset, given which melodies `MayGovern`
allows to contract infrasegmental government ([scheer-2004] (49a)). -/
def clusters (MayGovern : List T → List T → Prop) [∀ a b, Decidable (MayGovern a b)] :
    Finset (Fin (units u)) :=
  Finset.univ.filter fun j ↦ ∃ k : Fin (units u), k.val = j.val + 1 ∧
    MayGovern (c.tierValues (onset u k)) (c.tierValues (onset u j))

variable {c} {P : T → Prop} [DecidablePred P] {j : Fin (units u)}

theorem mem_hosting : j ∈ hosting c P ↔ ∃ k, (k, nucleus u j) ∈ c.links ∧ P u.upper[k].value := by
  simp [hosting, Candidate.mem_tierValues]

end StrictCV
