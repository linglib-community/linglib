/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Judgments

A paper marks an example to report how speakers judge it, as `*` marks an ungrammatical sentence. A
**judgment** is one of the seven marks the library records: none, `?`, `??`, `#`, `?*`, `*`, and `%`
where speakers differ. The Cross-Linguistic Data Formats, version 1.3, hold it in the column
`grammaticalityJudgement`.
## Implementation notes

* CLDF leaves the value of the column free. The seven marks are the library's inventory.
* The type carries no order and no grouping of its marks. Which marks a paper counts as accepted,
  and whether it reads them as a scale, is that paper's link between its account and its data, so
a study states it; `Datum.Fits` reads a mark through `Judgment.band`.
* A split mark a paper prints, such as `*/??`, is several marks for one sentence. A row records the
  first as `Datum.judgment` and the rest as `Datum.alsoJudged`. Gradient ratings are results,
recorded in `Data/Statistics/`.
* The file imports nothing, since every module of example data imports it.

## References

* [forkel-etal-2024]
-/

@[expose] public section

/-- A **judgment** is the mark a paper puts before an example. -/
inductive Judgment where
  /-- The paper accepts the example and leaves it unmarked. -/
  | acceptable
  /-- The mark `?` calls the example marginal. -/
  | marginal
  /-- The mark `??` calls the example questionable. -/
  | questionable
  /-- The mark `#` calls the example well formed but infelicitous or semantically anomalous. -/
  | unacceptable
  /-- The mark `?*`, also printed `*?`, calls the example nearly ungrammatical. -/
  | nearlyUngrammatical
  /-- The mark `*` calls the example ungrammatical. -/
  | ungrammatical
  /-- The mark `%` says that speakers differ, some accepting the example and others rejecting
  it. -/
  | variable
  deriving DecidableEq, Repr, Inhabited
