module

public import Linglib.Syntax.Voice.Basic
public import Mathlib.Data.Finset.Image

/-!
# Voice systems

A language's voices are a finite set of `Voice`s. The symmetrical voices of
Western Austronesian and of a few languages elsewhere code which participant is
the pivot, the syntactically privileged term, without affecting the transitivity
of the construction, and a system is symmetrical when every voice does so
([creissels-2024] §8.1.7); it is multiple rather than binary when some voice
selects an oblique as pivot (§8.5.1, §8.5.2). Of the four characteristics of
an Austronesian-type voice system in [erlewine-levin-van-urk-2017], the
privileged argument realized in one form or position whatever its function
(4a) is `Voice.pivot`, and verb morphology varying with its choice, obliques
included (4b), is `Voice.marker` and `Multiple`; the extraction restriction to
the pivot (4c) and the marking of non-pivot subjects (4d) are recorded where a
fragment states them.

## Main definitions

* `Voice.Symmetrical`, `Voice.Multiple`, `Voice.Equipollent` — properties of a
  set of voices

## Main results

* `Voice.Symmetrical.not_isValencyIncreasing`, `Symmetrical.not_isValencyDecreasing`
  — no voice of a symmetrical system changes valency
* `Voice.symmetrical_image`, `multiple_image`, `equipollent_image` — the
  properties over a system indexed by a language's voice names

## Implementation notes

* [creissels-2024] §8.1.7 reports two rival criteria for symmetry: equipollent
  marking (Himmelmann) and equal transitivity of all voices (Riesberg), and
  adopts the second. `Symmetrical` is the book's criterion and `Equipollent`,
  every voice coded and so none derived from an unmarked one, the first;
  Balinese separates them (`Studies/Creissels2024.lean`).
* A language whose names outrun the frames, two passives or two oblique voices
  of one relation, keeps its own name type and states the properties of the
  image of its map into `Voice`.

## References

* [creissels-2024]
* [erlewine-levin-van-urk-2017]
-/

@[expose] public section

namespace Voice

variable (S : Finset Voice)

/-- Every voice selects a pivot without affecting transitivity: the book's criterion for a
symmetrical voice system ([creissels-2024] §8.1.7). -/
def Symmetrical : Prop := ∀ v ∈ S, v.IsSymmetrical

/-- Some voice selects an oblique as pivot: a multiple system, as against a binary one whose
pivot is always a nuclear participant ([creissels-2024] §8.5.1, §8.5.2). -/
def Multiple : Prop := ∃ v ∈ S, v.SelectsOblique

/-- Every voice is coded, none derived from an unmarked one by adding marking: the criterion
for symmetry [creissels-2024] §8.1.7 attributes to Himmelmann and does not adopt. -/
def Equipollent : Prop := ∀ v ∈ S, v.IsCoded

instance : Decidable (Symmetrical S) := inferInstanceAs (Decidable (∀ _ ∈ _, _))
instance : Decidable (Multiple S) := inferInstanceAs (Decidable (∃ _ ∈ _, _))
instance : Decidable (Equipollent S) := inferInstanceAs (Decidable (∀ _ ∈ _, _))

variable {S}

theorem Symmetrical.not_isValencyIncreasing (h : Symmetrical S) {v : Voice} (hv : v ∈ S) :
    ¬ v.IsValencyIncreasing := fun h' ↦ h'.not_isSymmetrical (h v hv)

theorem Symmetrical.not_isValencyDecreasing (h : Symmetrical S) {v : Voice} (hv : v ∈ S) :
    ¬ v.IsValencyDecreasing := fun h' ↦ h'.not_isSymmetrical (h v hv)

/-! ### Systems indexed by a language's names -/

variable {V : Type*} [Fintype V] {f : V → Voice}

@[simp] theorem symmetrical_image :
    Symmetrical (Finset.univ.image f) ↔ ∀ i, (f i).IsSymmetrical := by
  simp [Symmetrical]

@[simp] theorem multiple_image :
    Multiple (Finset.univ.image f) ↔ ∃ i, (f i).SelectsOblique := by
  simp [Multiple]

@[simp] theorem equipollent_image :
    Equipollent (Finset.univ.image f) ↔ ∀ i, (f i).IsCoded := by
  simp [Equipollent]

end Voice
