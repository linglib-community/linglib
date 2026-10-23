module

public import Studies.Casali1997
public import Linglib.Fragments.Hungarian.Phonology
public import Linglib.Data.Wordlist.Vago2017

/-!
# Vago (2017): \*VV in Hungarian

Vago analyses the vowel sequences that suffixation creates in Hungarian with Casali's
position-sensitive MAX constraints and a ban on vowel sequences, \*VV. Between a root and a suffix
the second vowel usually deletes, under the hierarchy MAX LEX ≫ \*VV ≫ MAX MI, and a handful of
suffixes are indexed to rerankings that delete the first vowel instead or keep both. Between two
suffixes the second vowel deletes after a long vowel or a suffix of one vowel, which high-ranked
MAX constraints on long vowels and on morphs of one segment protect, and the first vowel deletes
after the infinitival suffix -ni. Vago concludes that Casali's constraints make the right
predictions for Hungarian.

## Main results

* `optimal_regular`: between a morph and a suffix that are not roots, the regular hierarchy
  deletes the second vowel when the first is long or alone in its morph, and the first otherwise.
* `corr_form_rhs`, `maxAt_deleted_eq_maxViolAt`: a candidate is the deletion of its vowels from
  the unrepaired concatenation, and each MAX constraint counts the protected input segments that
  have no correspondent in its output.
* `tableaux`: for every example, the tableau of its four candidates (no deletion, either vowel,
  both) under the hierarchy of its suffix selects the attested deletion, and its output spells the
  attested form.
* `starVV_dominates_of_erdesz`: a ranking that deletes the first vowel of erdő-ész ranks \*VV above
  MAX on long vowels and MAX LEX, since the deleted root vowel is long.

## Implementation notes

* Each example is a row of `Data/Wordlist/Vago2017` giving its two morphs, their kinds, the morph
  before them, the attested deletion and the hierarchy its suffix is indexed to. Long vowels are
  read off the accents of the spelling, length being prosodic in the Hungarian fragment.
* The hierarchy that deletes the first vowel is taken as Table 2 prints it, without the
  constraints on long vowels and morphs of one segment, which the paper ranks above the regular
  hierarchy; with MAX on long vowels on top it would keep the long vowel of erdő
  (`starVV_dominates_of_erdesz`).
* Vago derives the deletion after -ni in Table 4 from the reranking (8b), and the row follows
  him; the regular hierarchy derives it too (`optimal_regular`), since MAX LEX does not bear on
  two suffixes.

## References

* [vago-2017]
* [casali-1997]
-/

@[expose] public section

namespace Vago2017

open Phonology Phonology.Hiatus OptimalityTheory Morphology
open Data.Hiatus (ElidedVowel)

/-- Vago's constraints are MAX on long vowels (22), MAX on morphs of one segment (24), MAX on
lexical material (4), the ban on vowel sequences (5), and MAX on morpheme-initial segments (6). -/
inductive Con where
  | maxLong
  | maxMS
  | maxLex
  | starVV
  | maxMI
  deriving DecidableEq, Fintype, Repr

variable (c : Context) (long : Finset ℕ)

/-- A candidate is the set of vowels it deletes, and `deleted c D` the positions they occupy. -/
def deleted (D : Finset ElidedVowel) : Finset ℕ := D.image (Casali1997.position c)

/-- The form a candidate gives. -/
def resolve (D : Finset ElidedVowel) : List Segment :=
  c.stemBody ++ (if .first ∈ D then [] else [c.v1]) ++ (if .second ∈ D then [] else [c.v2]) ++
    c.suffixBody

/-- `corr c D` is the correspondence between the unrepaired concatenation and the form that the
candidate `D` gives, the deletion of the positions of its vowels. -/
def corr (D : Finset ElidedVowel) : Correspondence BinaryRole Segment :=
  Correspondence.eraseIdxs c.input (deleted c D)

theorem corr_form_rhs (D : Finset ElidedVowel) : (corr c D).form .rhs = resolve c D := by
  have hmem (k : ℕ) : k ∈ deleted c D ↔
      .first ∈ D ∧ k = c.stemBody.length ∨ .second ∈ D ∧ k = c.stemBody.length + 1 := by
    simp only [deleted, Finset.mem_image]
    refine ⟨?_, by rintro (⟨h, rfl⟩ | ⟨h, rfl⟩) <;> exact ⟨_, h, rfl⟩⟩
    rintro ⟨_ | _, h, rfl⟩ <;> simp [h, Casali1997.position, Juncture.v1Idx, Juncture.v2Idx]
  have hkeep (l : List Segment) (k : ℕ) (hk : ∀ p ∈ l.zipIdx k, p.2 ∉ deleted c D) :
      (l.zipIdx k).filter (fun p ↦ p.2 ∉ deleted c D) = l.zipIdx k :=
    List.filter_eq_self.2 fun p hp ↦ decide_eq_true (hk p hp)
  rw [corr, Correspondence.eraseIdxs_form_rhs, Juncture.input, List.zipIdx_append,
    List.zipIdx_cons, List.zipIdx_cons, List.filter_append,
    hkeep _ _ fun p hp ↦ ?stem, List.filter_cons, List.filter_cons,
    hkeep _ _ fun p hp ↦ ?suffix]
  · by_cases h₁ : ElidedVowel.first ∈ D <;> by_cases h₂ : ElidedVowel.second ∈ D <;>
      simp [hmem, h₁, h₂, resolve, List.zipIdx_map_fst]
  case stem =>
    have := List.snd_lt_of_mem_zipIdx hp
    rw [hmem]
    rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega
  case suffix =>
    have := List.le_snd_of_mem_zipIdx hp
    rw [hmem]
    rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega

theorem maxAt_deleted_eq_maxViolAt (P : ℕ → Prop) [DecidablePred P] (D : Finset ElidedVowel) :
    maxAt P (deleted c D) = (corr c D).maxViolAt P .lhs .rhs :=
  maxAt_eq_maxViolAt P fun k hk ↦ by
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 hk
    exact Casali1997.position_lt_length_input c e

/-- The violations of a candidate, with the long vowels at the positions `long`. -/
def marks (D : Finset ElidedVowel) : Con → ℕ
  | .maxLong => maxAt (· ∈ long) (deleted c D)
  | .maxMS => maxAt (c.Protects .soleSegment) (deleted c D)
  | .maxLex => maxAt (c.Protects .lexical) (deleted c D)
  | .starVV => Hiatus.count (resolve c D)
  | .maxMI => maxAt (c.Protects .morphemeInitial) (deleted c D)

/-- The tableau of the four candidates under a constraint order, most dominant first. -/
abbrev tableau (order : List Con) : Tableau (Finset ElidedVowel) order.length :=
  Tableau.ofOrder order (marks c long)

/-- The constraint order of the hierarchy a suffix is indexed to, most dominant first: the
regular hierarchy (8a), MAX LEX ≫ \*VV ≫ MAX MI, below MAX on long vowels and on morphs of one
segment; the reranking (8b) that deletes the first vowel, \*VV ≫ MAX MI ≫ MAX LEX; and the
reranking (9b) that deletes neither vowel, MAX LEX ≫ MAX MI ≫ \*VV. -/
def Wordlist.Hierarchy.order : Wordlist.Hierarchy → List Con
  | .regular => [.maxLong, .maxMS, .maxLex, .starVV, .maxMI]
  | .v1Deletion => [.starVV, .maxMI, .maxLex]
  | .noDeletion => [.maxLex, .maxMI, .starVV]

/-! ### Between two suffixes -/

section Profiles

variable {c long}

@[simp] theorem deleted_empty : deleted c ∅ = ∅ := rfl

@[simp] theorem deleted_first : deleted c {.first} = {c.v1Idx} := rfl

@[simp] theorem deleted_second : deleted c {.second} = {c.v2Idx} := rfl

@[simp] theorem deleted_pair : deleted c {.first, .second} = insert c.v1Idx {c.v2Idx} := by
  simp [deleted, Casali1997.position]

theorem resolve_empty : resolve c ∅ = c.input := by simp [resolve, Juncture.input]

private theorem v1Idx_ne_v2Idx : c.v1Idx ≠ c.v2Idx := by
  simp [Juncture.v1Idx, Juncture.v2Idx]

private theorem regular_lt {D D' : Finset ElidedVowel} (k : ℕ)
    (hk : k < Wordlist.Hierarchy.regular.order.length)
    (h : ∀ j (hj : j < k), marks c long D (Wordlist.Hierarchy.regular.order.get ⟨j, by omega⟩) =
      marks c long D' (Wordlist.Hierarchy.regular.order.get ⟨j, by omega⟩))
    (hi : marks c long D (Wordlist.Hierarchy.regular.order.get ⟨k, hk⟩) <
      marks c long D' (Wordlist.Hierarchy.regular.order.get ⟨k, hk⟩)) :
    (tableau c long Wordlist.Hierarchy.regular.order).profile D <
      (tableau c long Wordlist.Hierarchy.regular.order).profile D' :=
  ⟨⟨k, hk⟩, fun j hj ↦ h j.1 hj, hi⟩

private theorem finset_cases (D : Finset ElidedVowel) :
    D = ∅ ∨ D = {.first} ∨ D = {.second} ∨ D = {.first, .second} := by
  revert D; decide

end Profiles

/-- Closes a comparison under the regular hierarchy that the constraint at position `k`
decides. -/
local macro "regular_beats " k:num : tactic =>
  `(tactic| (refine regular_lt $k (by decide) (fun j hj ↦ ?_) ?_ <;>
    [(rcases j with _ | _ | _ | _ | j <;>
      first | omega | simp_all [Wordlist.Hierarchy.order, marks, maxAt_insert]);
      simp_all [Wordlist.Hierarchy.order, marks, maxAt_insert, Nat.pos_iff_ne_zero]]))

theorem optimal_regular (hl : c.left ≠ .root) (hr : c.right ≠ .root) (hv₂ : c.v2Idx ∉ long)
    (hs : c.suffixBody ≠ []) (hfree : ∀ D : Finset ElidedVowel, D.Nonempty →
      Hiatus.count (resolve c D) = 0) :
    (tableau c long Wordlist.Hierarchy.regular.order).optimal =
      {if c.v1Idx ∈ long ∨ c.stemBody = [] then {.second} else {.first}} := by
  have hne := v1Idx_ne_v2Idx (c := c)
  have h₀ : Hiatus.count (resolve c ∅) ≠ 0 := fun h ↦
    c.not_free_input ((Hiatus.free_iff_count_eq_zero _).2 (resolve_empty ▸ h))
  have h₁ := hfree {.first} (by simp)
  have h₂ := hfree {.second} (by simp)
  have h₃ := hfree {.first, .second} (by simp)
  refine Tableau.optimal_eq_singleton_iff.2 ⟨Finset.mem_univ _, fun D _ hD ↦ ?_⟩
  split_ifs at hD ⊢ with hlong
  · rcases finset_cases D with rfl | rfl | rfl | rfl
    · regular_beats 3
    · by_cases hv₁ : c.v1Idx ∈ long
      · regular_beats 0
      · regular_beats 1
    · exact absurd rfl hD
    · by_cases hv₁ : c.v1Idx ∈ long
      · regular_beats 0
      · regular_beats 1
  · rcases finset_cases D with rfl | rfl | rfl | rfl
    · regular_beats 3
    · exact absurd rfl hD
    · regular_beats 4
    · regular_beats 4

/-! ### The examples -/

/-- The context of two spelled morphs of the given kinds, if the first ends and the second begins
with a vowel. -/
def context? (before : Option Morph.Kind) (left right : Morph.Kind) (l r : List Segment) :
    Option Context :=
  match l.reverse, r with
  | v₁ :: stem, v₂ :: suffix =>
    if h : v₁.IsVowel ∧ v₂.IsVowel then
      some ⟨⟨stem.reverse, v₁, v₂, suffix, h.1, h.2⟩, before, left, right⟩
    else none
  | _, _ => none

/-- An example records its context, the positions of its long vowels, the segments of the morph
before the context, the hierarchy of its suffix and the attested deletion. -/
structure Example where
  context : Context
  long : Finset ℕ
  before : List Segment
  hierarchy : Wordlist.Hierarchy
  deletion : Finset ElidedVowel

/-- The morph kind of the paper's label. -/
def kindOf : Wordlist.Kind → Morph.Kind
  | .root => .root
  | .suffix => .bound .after .affix

/-- The deleted vowels of the paper's label. -/
def deletionOf : Wordlist.Deleted → Finset ElidedVowel
  | .neither => ∅
  | .first => {.first}
  | .second => {.second}

/-- The example the paper's analysis of a form records. -/
def example? (a : Wordlist.Analysis) : Option Example := do
  let l ← Hungarian.transcribe? a.left
  let r ← Hungarian.transcribe? a.right
  let c ← context? (a.beforeKind.map kindOf) (kindOf a.leftKind) (kindOf a.rightKind) l r
  pure ⟨c, Hungarian.longPositions a.left ∪ (Hungarian.longPositions a.right).image (· + l.length),
    ← Hungarian.transcribe? (a.before.getD ""), a.hierarchy, deletionOf a.deleted⟩

theorem tableaux :
    ∀ a ∈ Wordlist.analyses, ∃ x ∈ example? a,
      (tableau x.context x.long x.hierarchy.order).optimal = {x.deletion} ∧
        some (x.before ++ resolve x.context x.deletion) = Hungarian.transcribe? a.form.form := by
  decide +kernel

/-! ### The ranking that deletes the first vowel -/

/-- Vago's constraints on the candidates of an example. -/
def con (x : Example) : ConstraintSet (Finset ElidedVowel) Con :=
  fun i D ↦ marks x.context x.long D i

/-- The example erdő-ész of Table 2. -/
def erdesz : Example := (example? Wordlist.erdesz.analysis).get (by decide +kernel)

private theorem con_erdesz_lt_iff (i : Con) :
    con erdesz i {.first} < con erdesz i ∅ ↔ i = .starVV := by
  revert i; decide +kernel

theorem starVV_dominates_of_erdesz {r : Ranking Con 5}
    (h : {.first} ∈
      (Tableau.ofRanking (con erdesz) r {∅, {.first}, {.second}, {.first, .second}}).optimal) :
    r.Dominates .starVV .maxLong ∧ r.Dominates .starVV .maxLex := by
  have hle := Tableau.le_of_mem_optimal h (d := (∅ : Finset ElidedVowel)) (by simp)
  have hlt := hle.lt_of_ne fun heq ↦ by
    have := congrArg (· (r.symm .starVV)) heq
    simp only [Tableau.profile_apply, Tableau.ofRanking_constraints, Function.comp_apply,
      Equiv.apply_symm_apply] at this
    exact (con_erdesz_lt_iff .starVV).2 rfl |>.ne this
  obtain ⟨i, hi, hr⟩ := Tableau.ofRanking_profile_lt_iff_exists_dominates.1 hlt
  obtain rfl := (con_erdesz_lt_iff i).1 hi
  exact ⟨hr _ (by decide +kernel), hr _ (by decide +kernel)⟩

end Vago2017
