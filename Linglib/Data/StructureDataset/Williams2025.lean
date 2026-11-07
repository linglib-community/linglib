module

public import Linglib.Data.StructureDataset.Schema

/-!
# `Williams2025`: language samples

Auto-generated from `Linglib/Data/StructureDataset/Williams2025.json` by
`scripts/gen_structure_dataset.py`. Do not edit by hand; edit the JSON and re-run the generator.
Declarations live in `namespace Williams2025.StructureDataset`.
-/

@[expose] public section

namespace Williams2025.StructureDataset

open CLDF.StructureDataset

/-- modalization: Whether the factive presupposition of forget with a complement is modalized, as the presupposition that the subject was supposed to perform the action is (5a). -/
inductive Modalization where
  /-- `✓`: The factive presupposition is modalized. -/
  | modalized
  /-- `×`: The factive presupposition is not modalized. -/
  | notModalized
  deriving DecidableEq, Repr

/-- A row of a sample: a language with its codes for each parameter. -/
structure Row where
  /-- The language. -/
  language : Language
  /-- The codes for plain infinitive. -/
  plainInfinitive : List (Coded Modalization)
  /-- The codes for perfect infinitive. -/
  perfectInfinitive : List (Coded Modalization)
  /-- The codes for clausal gerund. -/
  clausalGerund : List (Coded Modalization)
  deriving DecidableEq, Repr

def english : Language :=
  { id := "english", name := "English", glottocode := some "stan1293" }

def spanish : Language :=
  { id := "spanish", name := "Spanish", glottocode := some "stan1288" }

def italian : Language :=
  { id := "italian", name := "Italian", glottocode := some "ital1282" }

def german : Language :=
  { id := "german", name := "German", glottocode := some "stan1295" }

def hungarian : Language :=
  { id := "hungarian", name := "Hungarian", glottocode := some "hung1274" }

/-- Modalization of factive presupposition with non-finite complements. The rows of Table 1, in the order of the source (williams-2025, Table 1, p. 8). -/
def table1 : List Row := [
  { language := english,
    plainInfinitive := [⟨.modalized, false, false, false⟩],
    perfectInfinitive := [],
    clausalGerund := [⟨.notModalized, false, false, false⟩] },
  { language := spanish,
    plainInfinitive := [⟨.modalized, false, false, false⟩],
    perfectInfinitive := [⟨.notModalized, false, false, false⟩],
    clausalGerund := [] },
  { language := italian,
    plainInfinitive := [⟨.modalized, false, false, false⟩],
    perfectInfinitive := [⟨.notModalized, false, false, false⟩],
    clausalGerund := [] },
  { language := german,
    plainInfinitive := [⟨.modalized, false, false, false⟩],
    perfectInfinitive := [⟨.notModalized, false, false, false⟩],
    clausalGerund := [] },
  { language := hungarian,
    plainInfinitive := [⟨.modalized, false, false, false⟩],
    perfectInfinitive := [],
    clausalGerund := [] }]

end Williams2025.StructureDataset
