module

public import Linglib.Phonology.Segmental.Defs
public import Mathlib.Data.List.Chain

/-!
# Vowel hiatus

This file defines vowel hiatus, the adjacency of two vowels, and its repair at a morpheme
juncture by eliding one of the vowels, by merging the two into one, or by inserting a consonant
between them.

Many languages do not tolerate hiatus. Where a vowel-final morpheme meets a vowel-initial one,
they elide one of the two vowels, turn the first into a glide, merge the two into a third
vowel, syllabify them together as a diphthong, or insert a consonant, and Casali surveys the
variation. Which vowel elides is not free. The first vowel is the usual target, and elision of
the second is well attested only before a function word and at the boundary between a stem and
a suffix, which is the question of Casali's earlier article.

Like `OCP.IsClean`, `Hiatus.Free` is a thin layer over `List.IsChain`, but over two segments
both being vowels, not their being identical, and over adjacency in the string, not on a tier.
So neither constraint is an instance of the other.

## Main definitions

* `Hiatus.Free`, `Hiatus.count`: a form has no two adjacent vowels; the number of adjacent
  vowel pairs.
* `Hiatus.Juncture`: hiatus at a morpheme boundary, where a vowel-final stem meets a
  vowel-initial suffix.
* `Juncture.epenthesize`, `Juncture.elideV1`, `Juncture.elideV2`, `Juncture.coalesce`: the
  repairs by insertion of a consonant, by elision of either vowel, and by merger of the two
  into a given vowel.

## Main results

* `Hiatus.free_iff_count_eq_zero`: the ban and the count agree.
* `Juncture.not_free_input`: the unrepaired concatenation has a hiatus.
* `Juncture.free_epenthesize`, `Juncture.free_elideV1`, `Juncture.free_elideV2`,
  `Juncture.free_coalesce`: a repaired form is free of hiatus exactly when the material on each
  side of the juncture is.
* `Juncture.coalesce_v2`, `Juncture.coalesce_v1`: elision is merger into the surviving vowel.
* `Juncture.elideV1_eq_eraseIdx`, `Juncture.elideV2_eq_eraseIdx`,
  `Juncture.epenthesize_eq_insertIdx`: the repairs as the deletion of one position of the
  unrepaired concatenation and the insertion of one segment into it.
* `Juncture.elideV2_eq_stem_iff`: elision of the second vowel merges the suffixed form with
  the bare stem exactly for a suffix of one segment.

## Implementation notes

Which vowel a merger yields turns on the quality of the two, so `Juncture.coalesce` takes the
result as an argument. Glide formation and diphthong formation are not defined, since they turn
on the syllabification of the two vowels and no study yet consumes them.

## References

* [casali-1997]
* [casali-2011]
-/

@[expose] public section

namespace Phonology.Hiatus

/-- A form is free of hiatus when no two adjacent segments are both vowels. -/
def Free (fm : List Segment) : Prop :=
  List.IsChain (fun a b ↦ ¬(a.IsVowel ∧ b.IsVowel)) fm

instance : DecidablePred Free := fun fm ↦
  inferInstanceAs (Decidable (List.IsChain _ fm))

/-- `count fm` is the number of adjacent vowel pairs in the form, the violation count of the
markedness constraint against hiatus. -/
def count (fm : List Segment) : ℕ :=
  (fm.zip fm.tail).countP fun p ↦ decide (p.1.IsVowel ∧ p.2.IsVowel)

@[simp] theorem count_nil : count [] = 0 := rfl

@[simp] theorem count_singleton (a : Segment) : count [a] = 0 := rfl

theorem count_cons_cons (a b : Segment) (fm : List Segment) :
    count (a :: b :: fm) =
      count (b :: fm) + if a.IsVowel ∧ b.IsVowel then 1 else 0 := by
  simp [count, List.countP_cons]

/-- The categorical ban and the violation count agree. -/
theorem free_iff_count_eq_zero (fm : List Segment) : Free fm ↔ count fm = 0 := by
  induction fm with
  | nil => simp [Free]
  | cons a t ih =>
      cases t with
      | nil => simp [Free]
      | cons b t' =>
          rw [Free, List.isChain_cons_cons, count_cons_cons, ← Free, ih]
          by_cases h : a.IsVowel ∧ b.IsVowel <;> simp [h]

/-! ### Hiatus at a morpheme juncture -/

/-- A juncture is a vowel-final stem `stemBody ++ [v1]` followed by a vowel-initial suffix
`v2 :: suffixBody`. The repairs below resolve the adjacency of `v1` and `v2`, and apply only
here, since a consonant-final stem or a consonant-initial suffix never presents it. -/
structure Juncture where
  /-- The stem without its final vowel. -/
  stemBody : List Segment
  /-- The stem-final vowel. -/
  v1 : Segment
  /-- The suffix-initial vowel. -/
  v2 : Segment
  /-- The suffix without its initial vowel. -/
  suffixBody : List Segment
  /-- The stem-final segment is a vowel. -/
  v1_isVowel : v1.IsVowel
  /-- The suffix-initial segment is a vowel. -/
  v2_isVowel : v2.IsVowel

namespace Juncture

variable (j : Juncture)

/-- `j.stem` is the stem. -/
def stem : List Segment := j.stemBody ++ [j.v1]

/-- `j.suffix` is the suffix. -/
def suffix : List Segment := j.v2 :: j.suffixBody

/-- `j.input` is the unrepaired concatenation, with `v1` and `v2` in hiatus. -/
def input : List Segment := j.stemBody ++ j.v1 :: j.v2 :: j.suffixBody

theorem stem_append_suffix : j.stem ++ j.suffix = j.input := by
  simp [stem, suffix, input]

/-- `j.epenthesize c` inserts the consonant `c` between the two vowels. -/
def epenthesize (c : Segment) : List Segment :=
  j.stemBody ++ j.v1 :: c :: j.v2 :: j.suffixBody

/-- `j.elideV1` elides the stem-final vowel. -/
def elideV1 : List Segment := j.stemBody ++ j.suffix

/-- `j.elideV2` elides the suffix-initial vowel. -/
def elideV2 : List Segment := j.stem ++ j.suffixBody

/-- `j.coalesce v` merges the two vowels into `v`. -/
def coalesce (v : Segment) : List Segment := j.stemBody ++ v :: j.suffixBody

@[simp] theorem length_stem : j.stem.length = j.stemBody.length + 1 := by simp [stem]

@[simp] theorem length_input : j.input.length = j.stemBody.length + j.suffixBody.length + 2 := by
  simp [input]; omega

@[simp] theorem length_epenthesize (c : Segment) :
    (j.epenthesize c).length = j.stemBody.length + j.suffixBody.length + 3 := by
  simp [epenthesize]; omega

@[simp] theorem length_elideV1 :
    j.elideV1.length = j.stemBody.length + j.suffixBody.length + 1 := by
  simp [elideV1, suffix]; omega

@[simp] theorem length_elideV2 :
    j.elideV2.length = j.stemBody.length + j.suffixBody.length + 1 := by
  simp [elideV2, stem]; omega

@[simp] theorem length_coalesce (v : Segment) :
    (j.coalesce v).length = j.stemBody.length + j.suffixBody.length + 1 := by
  simp [coalesce]; omega

/-- Merger into the second vowel is elision of the first. -/
theorem coalesce_v2 : j.coalesce j.v2 = j.elideV1 := rfl

/-- Merger into the first vowel is elision of the second. -/
theorem coalesce_v1 : j.coalesce j.v1 = j.elideV2 := by simp [coalesce, elideV2, stem]

theorem input_ne_stem : j.input ≠ j.stem := fun h ↦ by
  have := congrArg List.length h
  simp at this
  omega

theorem epenthesize_ne_stem (c : Segment) : j.epenthesize c ≠ j.stem := fun h ↦ by
  have := congrArg List.length h
  simp at this
  omega

/-- Elision of the second vowel merges the suffixed form with the bare stem exactly when the
suffix has one segment. -/
@[simp] theorem elideV2_eq_stem_iff : j.elideV2 = j.stem ↔ j.suffixBody = [] := by
  simp [elideV2]

@[simp] theorem elideV1_eq_suffix_iff : j.elideV1 = j.suffix ↔ j.stemBody = [] := by
  simp [elideV1]

/-! ### The repairs as deletion and insertion -/

/-- `j.v1Idx` is the position of the first vowel in the unrepaired concatenation. -/
def v1Idx : ℕ := j.stemBody.length

/-- `j.v2Idx` is the position of the second vowel in the unrepaired concatenation. -/
def v2Idx : ℕ := j.stemBody.length + 1

theorem v1Idx_lt_length_input : j.v1Idx < j.input.length := by
  simp only [v1Idx, length_input]; omega

theorem v2Idx_lt_length_input : j.v2Idx < j.input.length := by
  simp only [v2Idx, length_input]; omega

/-- Elision of the first vowel deletes its position from the unrepaired concatenation. -/
theorem elideV1_eq_eraseIdx : j.elideV1 = j.input.eraseIdx j.v1Idx := by
  simp [elideV1, suffix, input, v1Idx, List.eraseIdx_append_of_length_le]

/-- Elision of the second vowel deletes its position from the unrepaired concatenation. -/
theorem elideV2_eq_eraseIdx : j.elideV2 = j.input.eraseIdx j.v2Idx := by
  simp [elideV2, stem, input, v2Idx, List.eraseIdx_append_of_length_le]

private theorem insertIdx_append_cons {α : Type*} (l : List α) (x c : α) (r : List α) :
    (l ++ x :: r).insertIdx (l.length + 1) c = l ++ x :: c :: r := by
  induction l with
  | nil => simp [List.insertIdx_succ_cons]
  | cons a l ih => simp [List.insertIdx_succ_cons, ih]

/-- Insertion of a consonant puts it at the position of the second vowel. -/
theorem epenthesize_eq_insertIdx (c : Segment) :
    j.epenthesize c = j.input.insertIdx j.v2Idx c :=
  (insertIdx_append_cons _ _ _ _).symm

/-! ### The repairs remove the hiatus -/

/-- The unrepaired concatenation has a hiatus. -/
theorem not_free_input : ¬ Free j.input := fun h ↦
  (List.isChain_append_cons_cons.1 h).2.1 ⟨j.v1_isVowel, j.v2_isVowel⟩

/-- The form with an inserted consonant is free of hiatus exactly when the stem and the suffix
are. -/
theorem free_epenthesize {c : Segment} (hc : ¬ c.IsVowel) :
    Free (j.epenthesize c) ↔ Free j.stem ∧ Free j.suffix := by
  simp only [Free, epenthesize, stem, suffix, List.isChain_append_cons_cons,
    List.isChain_cons_cons]
  tauto

/-- The form without the first vowel is free of hiatus exactly when the stem body followed by
the second vowel is, and the suffix is. -/
theorem free_elideV1 : Free j.elideV1 ↔ Free (j.stemBody ++ [j.v2]) ∧ Free j.suffix :=
  List.isChain_split

/-- The form without the second vowel is free of hiatus exactly when the stem is, and the first
vowel followed by the suffix body is. -/
theorem free_elideV2 : Free j.elideV2 ↔ Free j.stem ∧ Free (j.v1 :: j.suffixBody) := by
  simp only [Free, elideV2, stem, List.append_assoc, List.singleton_append]
  exact List.isChain_split

/-- The form with the two vowels merged into `v` is free of hiatus exactly when the stem body
followed by `v` is, and `v` followed by the suffix body is. -/
theorem free_coalesce (v : Segment) :
    Free (j.coalesce v) ↔ Free (j.stemBody ++ [v]) ∧ Free (v :: j.suffixBody) :=
  List.isChain_split

end Juncture

end Phonology.Hiatus
