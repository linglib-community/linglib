module

public import Studies.Casali1997
public import Linglib.Data.Hiatus.Mkochi2021

/-!
# Mkochi (2021): V2 elision in root-suffix hiatus contexts in Malawian CiTonga

Mkochi reports that Malawian CiTonga, a Bantu language of Malawi, resolves hiatus by eliding the
second vowel between a verb root and a suffix, where Casali derives the elision from the
prominence of the root, and also between two suffixes and between two enclitics, where neither
vowel is in a root. Mkochi argues that Casali's account does not extend to these junctures, and
attributes the pattern instead to the prosodic stem, within which hiatus is resolved by eliding
the second vowel; the paper leaves the formal statement of that proposal open.

Against Casali's constraints the reports divide by the kind of juncture. Some ranking elides the
second vowel between a root and a suffix, but none does between two suffixes or two enclitics,
since there the constraints violated by eliding the first vowel are a proper subset of those
violated by eliding the second. This holds even where the second suffix is a single vowel, as
with the final vowel of the paper's (11), which the constraint on morphs of one segment then
protects as well.

## References

* [mkochi-2021]
* [casali-1997]
-/

@[expose] public section

namespace Mkochi2021

open Casali1997

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

/-- At a schematic juncture of two suffixes no ranking of Casali's constraints elides the second
vowel. -/
theorem schematic_suffixSuffix :
    ¬ ∃ r, .second ∈ (tableau (schematic .suffixSuffix) r).optimal := by
  rw [exists_mem_optimal_iff_of_isOfKind (isOfKind_schematic _)]
  decide

end Mkochi2021
