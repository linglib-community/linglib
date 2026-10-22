/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Schema

/-!
# Language samples

This file defines the rows of a paper's language sample, after the CLDF StructureDataset: the
languages of the sample, and the codes a language takes for a parameter the paper records. The
parameters, their codes and the rows of a sample are generated per paper.

## Main definitions

* `Data.Structures.Language`: a row of the `LanguageTable`.
* `Data.Structures.Coded`: a value of the `ValueTable`, a code with the marks a source puts on it.

## Implementation notes

* Per-paper data lives in `Linglib/Data/Structures/{AuthorYear}.json`, an object holding the
  CLDF tables `ContributionTable`, `LanguageTable`, `ParameterTable`, `CodeTable` and
  `ValueTable` under CLDF column names, and is compiled by `scripts/gen_structures.py` into
  `{AuthorYear}.lean`, declaring `namespace {AuthorYear}.Structures`.
* Each parameter becomes an inductive type with a constructor for each code, except that a
  parameter may take the codes of another, as the semantic types of a sample may share their
  parts of speech; a parameter whose codes others take and which has no values of its own is a
  type and no field. The values, long
  in the JSON as CLDF has them, are emitted as one row per language with a field for each
  parameter, so a theorem about the sample reads each language once.
* Each table of a paper is a contribution with its own list of rows. Languages, parameters and
  codes are shared, so a language two tables list is one `Language` with a row in each.
* A language may take several codes for a parameter, or none: a row's field is a list.
* A language without a Glottocode is one the source names without saying which Glottolog
  language it means; the JSON records why.
* Comments, footnotes and the lineage a source prints are its record: the generator validates
  them and does not emit them.
-/

@[expose] public section

namespace Data.Structures

/-- A `Language` is a row of a CLDF `LanguageTable`, a language of the sample. -/
structure Language where
  /-- The `ID` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The `Name` column holds the language's name as the source prints it; where its tables print
  several, the JSON records the others. -/
  name : String
  /-- The `Glottocode` column holds the Glottocode, when the source's name determines one. -/
  glottocode : Option Glottocode
  deriving DecidableEq, Repr

/-- A `Coded C` is a value of a CLDF `ValueTable`: a code of the parameter `C`, with the marks a
source may put on it. -/
structure Coded (C : Type*) where
  /-- The code. -/
  code : C
  /-- The source marks the code as questionable. -/
  questionable : Bool := false
  /-- The source marks the strategy the code names as optional. -/
  optional : Bool := false
  /-- The source marks the code as holding of only a few of the language's items, as *some*,
  *one* or *few* do. -/
  minor : Bool := false
  deriving DecidableEq, Repr

end Data.Structures
