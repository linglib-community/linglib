module

public import Studies.Casali1997
public import Linglib.Data.Hiatus.Mkochi2021

/-!
# Mkochi (2021): V2 elision in root-suffix hiatus contexts in Malawian CiTonga

Mkochi reports that Malawian CiTonga, a Bantu language of Malawi, resolves hiatus within the verb
stem by eliding the second vowel. It does so between a verb root that ends in a non-high vowel and
a suffix, where Casali derives the elision from the prominence of the root, and also between two
suffixes and between two enclitics, where neither vowel is in a root. Mkochi argues that Casali's
account does not extend to these junctures, and attributes the pattern instead to the prosodic
stem, within which hiatus is resolved by eliding the second vowel; the paper leaves the formal
statement of that proposal open.

Against Casali's constraints the reports
[divide by the kind of juncture](##exists_mem_optimal_iff_rootSuffix): some ranking elides the
second vowel between a root and a suffix, and none does between two suffixes or two enclitics
whose first vowel begins no morph. Between two suffixes or enclitics the ranking in fact plays no
part, since [every ranking selects the same elisions](##optimal_of_bound_after), read off the
shapes of the two morphs. The first vowel elides where the first morph has more than its vowel,
as between two final-vowel suffixes and between two enclitics, so that the second vowel can elide
[only after a morph of one vowel](##exists_mem_optimal_second_iff_leftBody_eq_nil).
That is the shape of the applicative before a final vowel once its liquid has deleted, where both
morphs are a single vowel: the two elisions then violate the same constraints, and no ranking
chooses between them.

## Implementation notes

* A `Context` records the two morphs as they stand where the vowels meet. Before a final vowel
  the hiatus arises once the liquid of the applicative *el* has deleted, and the applicative is
  read as the vowel that remains, as the paper's intermediate forms segment it.
* The rows record the junctures by the kinds of Casali's survey, at which the first vowel begins
  no morph, so the applicative before a final vowel is of none of them.
* A root that ends in a high vowel resolves the hiatus by turning that vowel into a glide, a
  repair the substrate does not define.

## TODO

* The paper's forms are not rows. PHOIBLE has no inventory of Malawian CiTonga from which to
  transcribe them, so the contexts of the examples are given by their shapes alone.
* Read on its underlying form, the vowel of the applicative begins its morph without being the
  whole of it, which a `Context` cannot express: its left morph ends in the first vowel.

## References

* [mkochi-2021]
* [casali-1997]
-/

public section

namespace Mkochi2021

open Casali1997 Phonology.Hiatus OptimalityTheory Morphology
open Data.Hiatus (ElidedVowel)

/-- Some ranking of Casali's constraints elides the vowel a row reports exactly at the junctures
between a root and a suffix, and none does between two suffixes or two enclitics. -/
theorem exists_mem_optimal_iff_rootSuffix :
    ∀ row ∈ Data.Hiatus.Mkochi2021.rows, ∀ c, IsOfKind c row.juncture →
      ((∃ r, row.elided ∈ (tableau c r).optimal) ↔ row.juncture = .rootSuffix) := by
  have key : ∀ row ∈ Data.Hiatus.Mkochi2021.rows, (row.elided = .first ∨
      (kinds row.juncture).1 = .root ∧ (kinds row.juncture).2 ≠ .root) ↔
        row.juncture = .rootSuffix := by
    decide
  exact fun row hrow _ hc ↦ (exists_mem_optimal_iff_of_isOfKind hc).trans (key row hrow)

/-! ### Between two suffixes or enclitics -/

variable {c : Context} {a a' : Morph.Attachment}

/-- Between two suffixes or enclitics every ranking of Casali's constraints selects the same
elisions. The first vowel elides where the first morph has more than its vowel, the second where
the first morph is a single vowel and the second morph is not, and both where each morph is a
single vowel. -/
theorem optimal_of_bound_after (hl : c.leftKind = .bound .after a)
    (hr : c.rightKind = .bound .after a') (hb : c.beforeKind.isSome)
    (r : Ranking (Option Prominence) 5) :
    (tableau c r).optimal =
      if c.leftBody = [] then if c.rightBody = [] then {.first, .second} else {.second}
      else {.first} := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb
  split_ifs with h₁ h₂
  · rw [optimal_eq_pair_iff]
    ext (_ | _ | _ | _ | _) <;> simp [h₁, h₂, hl, hr, hb, Morph.Kind.JoinsAt]
  · refine optimal_eq_singleton_of_ssubset (e' := .first) (by decide) ⟨?_, fun h ↦ h₂ ?_⟩ r
    · rintro (_ | _ | _ | _ | _) hi <;> simp_all [Morph.Kind.JoinsAt]
    · simpa [h₁] using h (show some .soleSegment ∈ violations c .first by simpa using h₁)
  · refine optimal_eq_singleton_of_ssubset (e' := .second) (by decide) ⟨?_, fun h ↦ h₁ ?_⟩ r
    · rintro (_ | _ | _ | _ | _) hi <;> simp_all
    · simpa using h (show some .morphemeInitial ∈ violations c .second by simp)

/-- Between two suffixes or enclitics some ranking of Casali's constraints elides the second
vowel exactly when the first morph is a single vowel. -/
theorem exists_mem_optimal_second_iff_leftBody_eq_nil (hl : c.leftKind = .bound .after a)
    (hr : c.rightKind = .bound .after a') :
    (∃ r, .second ∈ (tableau c r).optimal) ↔ c.leftBody = [] := by
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun h ↦ ?_⟩
  · simpa [hl] using (exists_mem_optimal_second_iff hne).1 h
  · refine (exists_mem_optimal_iff (e' := .first) (by decide)).2 fun hlt ↦ hlt.2 ?_
    rintro (_ | _ | _ | _ | _) hi <;> simp_all [Morph.Kind.JoinsAt]

/-- Two final-vowel suffixes after a root, as in (10): the first is a vowel, a consonant and a
vowel, and its last vowel elides under every ranking. -/
example (r : Ranking (Option Prominence) 5) :
    (tableau { schematic .suffixSuffix with beforeKind := some .root } r).optimal = {.first} :=
  optimal_of_bound_after rfl rfl rfl r

/-- The vowel of the applicative before a final vowel after a root, as in (11): each morph is a
single vowel, and both elisions are optimal under every ranking. -/
example (r : Ranking (Option Prominence) 5) :
    (tableau { schematic .suffixSuffix with
      leftBody := [], rightBody := [], beforeKind := some .root } r).optimal =
        {.first, .second} :=
  optimal_of_bound_after rfl rfl rfl r

end Mkochi2021
