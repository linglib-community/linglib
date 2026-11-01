module

public import Linglib.Data.Statistics.Schema

/-!
# Jacobs2026: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Jacobs2026.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Counts of Latialis/Latiaris and linealis/linearis in the Library of Latin Texts, from the combined
searches *latiali/*latiale, *latiari/*latiare, *lineale/*lineali and *lineari/*lineare, per period.

## References

* [jacobs-2026]
-/

@[expose] public section

namespace Jacobs2026

open Data.Statistics

/-- The period of a row. -/
inductive Period where
  /-- <200: before 200 AD -/
  | before200
  /-- <500: between 200 AD and 500 AD, as the text glosses the row -/
  | from200To500
  deriving DecidableEq, Repr, Fintype

/-- A row of (23), p. 138: the occurrences of Latialis, Latiaris, linealis and linearis per
period. -/
structure HiatusCounts where
  /-- Occurrences of Latialis. -/
  latialis : ℕ
  /-- Occurrences of Latiaris. -/
  latiaris : ℕ
  /-- Occurrences of linealis. -/
  linealis : ℕ
  /-- Occurrences of linearis. -/
  linearis : ℕ
  deriving DecidableEq, Repr

/-- The cells of (23), p. 138, by period; counted in a corpus; checked against the page images. -/
def table23 : Period → HiatusCounts
  | .before200 => ⟨3, 15, 0, 7⟩
  | .from200To500 => ⟨3, 21, 1, 7⟩

end Jacobs2026
