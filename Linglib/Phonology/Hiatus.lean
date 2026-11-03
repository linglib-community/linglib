module

public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenPairs
public import Linglib.Phonology.Segmental.Defs
public import Mathlib.Data.List.Chain

/-!
# Vowel hiatus

Vowel hiatus is the adjacency of two vowels in separate syllables. Many languages do not tolerate
it, and where a vowel-final morph meets a vowel-initial one they elide one of the vowels, turn the
first into a glide, merge the two, syllabify them as a diphthong, or insert a consonant.

On strings of segments, a form is [free of hiatus](##Free) when no two adjacent segments are both
vowels, and `Hiatus.count` is the constraint against such pairs. A `Hiatus.Juncture` is a seam at
which two vowels meet, and
[a form has a hiatus exactly when it has one](##not_free_iff_exists_input). Merger, elision and
epenthesis [all leave the same count](##count_coalesce), one below the unrepaired form's, so the
constraint cannot choose among them and the choice falls to the other constraints each violates.

## Implementation notes

Forms carry no syllable boundaries, so `Hiatus.count` also counts a vowel sequence within one
syllable, and glide formation and diphthong formation, which turn on the syllabification of the two
vowels, are not defined.

## References

* [casali-1997]
* [casali-2011]
-/

@[expose] public section

namespace Phonology.Hiatus

open OptimalityTheory

/-- A form is free of hiatus when no two adjacent segments are both vowels. Like `OCP.IsClean`, it
is a reducible alias of `List.IsChain`, so that API applies. -/
abbrev Free (fm : List Segment) : Prop :=
  fm.IsChain fun a b ↦ ¬(a.IsVowel ∧ b.IsVowel)

/-- `count fm` is the number of adjacent vowel pairs in the form, the violations of the markedness
constraint against hiatus. Since a form has no syllable boundaries, this is not quite NOHIATUS in
tableau (30) of [casali-2011], which the diphthong candidate [.kua.bo.] does not violate. -/
abbrev count : Constraint (List Segment) :=
  Constraint.forbidPairs fun a b ↦ a.IsVowel ∧ b.IsVowel

/-- The categorical ban and the violation count agree. -/
theorem free_iff_count_eq_zero (fm : List Segment) : Free fm ↔ count fm = 0 :=
  (Constraint.forbidPairs_eq_zero_iff _ fm).symm

/-! ### Hiatus at a juncture -/

/-- A juncture is a seam at which a vowel-final form `leftBody ++ [v1]` meets a vowel-initial form
`v2 :: rightBody`, whether a stem and a suffix, a prefix and a root, or two words. The repairs
below resolve the adjacency of `v1` and `v2`. -/
structure Juncture where
  /-- The form on the left without its final vowel. -/
  leftBody : List Segment
  /-- The final vowel of the form on the left. -/
  v1 : Segment
  /-- The initial vowel of the form on the right. -/
  v2 : Segment
  /-- The form on the right without its initial vowel. -/
  rightBody : List Segment
  /-- The final segment of the form on the left is a vowel. -/
  v1_isVowel : v1.IsVowel
  /-- The initial segment of the form on the right is a vowel. -/
  v2_isVowel : v2.IsVowel

namespace Juncture

variable (j : Juncture)

/-- `j.left` is the form on the left of the juncture. -/
def left : List Segment := j.leftBody ++ [j.v1]

/-- `j.right` is the form on the right of the juncture. -/
def right : List Segment := j.v2 :: j.rightBody

/-- `j.input` is the unrepaired concatenation, with `v1` and `v2` in hiatus. -/
def input : List Segment := j.leftBody ++ j.v1 :: j.v2 :: j.rightBody

theorem left_append_right : j.left ++ j.right = j.input := by
  simp [left, right, input]

/-- `j.epenthesize c` inserts the consonant `c` between the two vowels. -/
def epenthesize (c : Segment) : List Segment :=
  j.leftBody ++ j.v1 :: c :: j.v2 :: j.rightBody

/-- `j.elideV1` elides the first vowel. -/
def elideV1 : List Segment := j.leftBody ++ j.right

/-- `j.elideV2` elides the second vowel. -/
def elideV2 : List Segment := j.left ++ j.rightBody

/-- `j.coalesce v` merges the two vowels into `v`. -/
def coalesce (v : Segment) : List Segment := j.leftBody ++ v :: j.rightBody

/-- Merger into the second vowel has the form of elision of the first. The two remain different
correspondences, which violate UNIFORMITY and MAX respectively ([casali-2011]). -/
theorem coalesce_v2 : j.coalesce j.v2 = j.elideV1 := rfl

/-- Merger into the first vowel has the form of elision of the second. -/
theorem coalesce_v1 : j.coalesce j.v1 = j.elideV2 := by simp [coalesce, elideV2, left]

theorem input_ne_left : j.input ≠ j.left := by simp [input, left]

theorem epenthesize_ne_left (c : Segment) : j.epenthesize c ≠ j.left := by
  simp [epenthesize, left]

/-- Elision of the second vowel merges the form with the one on the left exactly when the form on
the right has one segment. -/
@[simp] theorem elideV2_eq_left_iff : j.elideV2 = j.left ↔ j.rightBody = [] := by
  simp [elideV2]

/-- The juncture of two forms, if the first ends and the second begins with a vowel. -/
def ofForms? (l r : List Segment) : Option Juncture :=
  match l.reverse, r with
  | v₁ :: lb, v₂ :: rb =>
    if h : v₁.IsVowel ∧ v₂.IsVowel then some ⟨lb.reverse, v₁, v₂, rb, h.1, h.2⟩ else none
  | _, _ => none

theorem ofForms?_left_right : ofForms? j.left j.right = some j := by
  simp [ofForms?, left, right, j.v1_isVowel, j.v2_isVowel]

theorem mem_ofForms?_iff {l r : List Segment} {j : Juncture} :
    j ∈ ofForms? l r ↔ j.left = l ∧ j.right = r := by
  refine ⟨fun h ↦ ?_, fun ⟨hl, hr⟩ ↦ hl ▸ hr ▸ j.ofForms?_left_right⟩
  unfold ofForms? at h
  split at h
  · rename_i v₁ lb v₂ rb hl
    split_ifs at h
    · obtain rfl := Option.mem_some_iff.1 h
      exact ⟨by simpa [left] using (congrArg List.reverse hl).symm, rfl⟩
    · simp at h
  · simp at h

/-! ### The repairs as deletion and insertion -/

@[simp] theorem length_input : j.input.length = j.leftBody.length + j.rightBody.length + 2 := by
  simp [input]; omega

/-- `j.v1Idx` is the position of the first vowel in the unrepaired concatenation. -/
def v1Idx : ℕ := j.leftBody.length

/-- `j.v2Idx` is the position of the second vowel in the unrepaired concatenation. -/
def v2Idx : ℕ := j.leftBody.length + 1

theorem v1Idx_lt_length_input : j.v1Idx < j.input.length := by
  simp only [v1Idx, length_input]; omega

theorem v2Idx_lt_length_input : j.v2Idx < j.input.length := by
  simp only [v2Idx, length_input]; omega

/-- Elision of the first vowel deletes its position from the unrepaired concatenation. -/
theorem elideV1_eq_eraseIdx : j.elideV1 = j.input.eraseIdx j.v1Idx := by
  simp [elideV1, right, input, v1Idx, List.eraseIdx_append_of_length_le]

/-- Elision of the second vowel deletes its position from the unrepaired concatenation. -/
theorem elideV2_eq_eraseIdx : j.elideV2 = j.input.eraseIdx j.v2Idx := by
  simp [elideV2, left, input, v2Idx, List.eraseIdx_append_of_length_le]

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

/-- The juncture adds one hiatus to those of the two forms. -/
theorem count_input : count j.input = count j.left + 1 + count j.right := by
  simp [input, left, right, Constraint.forbidPairs_append_cons_cons, j.v1_isVowel, j.v2_isVowel]

/-- Merger into a vowel removes the hiatus at the juncture and no other. Each elision and epenthesis
leave the same count, so the constraint against hiatus does not choose among these repairs: in
tableau (30) of [casali-2011] each passes NOHIATUS and violates a constraint of its own. -/
theorem count_coalesce {v : Segment} (hv : v.IsVowel) :
    count (j.coalesce v) = count j.left + count j.right := by
  unfold coalesce left right count
  rw [Constraint.forbidPairs_split,
    Constraint.forbidPairs_congr_last _ (a := v) (b := j.v1) (by simp [hv, j.v1_isVowel]),
    Constraint.forbidPairs_congr_head _ (a := v) (b := j.v2) (by simp [hv, j.v2_isVowel])]

theorem count_elideV1 : count j.elideV1 = count j.left + count j.right :=
  j.coalesce_v2 ▸ j.count_coalesce j.v2_isVowel

theorem count_elideV2 : count j.elideV2 = count j.left + count j.right :=
  j.coalesce_v1 ▸ j.count_coalesce j.v1_isVowel

theorem count_epenthesize {c : Segment} (hc : ¬ c.IsVowel) :
    count (j.epenthesize c) = count j.left + count j.right := by
  simp [epenthesize, left, right, Constraint.forbidPairs_append_cons_cons, hc]

end Juncture

/-- A form has a hiatus exactly when it is the unrepaired concatenation at a juncture. -/
theorem not_free_iff_exists_input {fm : List Segment} :
    ¬ Free fm ↔ ∃ j : Juncture, j.input = fm := by
  rw [Free, List.isChain_iff_forall_rel_of_append_cons_cons]
  constructor
  · intro h
    push Not at h
    obtain ⟨a, b, l₁, l₂, rfl, ha, hb⟩ := h
    exact ⟨⟨l₁, a, b, l₂, ha, hb⟩, rfl⟩
  · rintro ⟨j, rfl⟩ h
    exact h rfl ⟨j.v1_isVowel, j.v2_isVowel⟩

end Phonology.Hiatus
