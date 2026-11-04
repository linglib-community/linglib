module

public import Linglib.Data.StructureDataset.Schema

/-!
# `Ochs1992`: language samples

Auto-generated from `Linglib/Data/StructureDataset/Ochs1992.json` by
`scripts/gen_structure_dataset.py`. Do not edit by hand; edit the JSON and re-run the generator.
Declarations live in `namespace Ochs1992.StructureDataset`.
-/

@[expose] public section

namespace Ochs1992.StructureDataset

open CLDF.StructureDataset

/-- verbal strategy: The strategies of Figure 14.3, whose three rows are three verbal practices (p. 347). -/
inductive Strategy where
  /-- `Extensive simplification`: Extensive simplification -/
  | extensiveSimplification
  /-- `Little simplification`: Little simplification -/
  | littleSimplification
  /-- `Express guess and negotiate meaning`: Express guess and negotiate meaning -/
  | expressGuess
  /-- `Display minimal grasp`: Display minimal grasp -/
  | displayMinimalGrasp
  /-- `Unidirectional`: Unidirectional -/
  | unidirectional
  /-- `Bidirectional`: Bidirectional -/
  | bidirectional
  deriving DecidableEq, Repr

/-- orientation: The orientation printed in parentheses in the column heads of Figure 14.3. -/
inductive Orientation where
  /-- `child-centered`: child-centered -/
  | childCentered
  /-- `other-centered`: other-centered -/
  | otherCentered
  deriving DecidableEq, Repr

/-- A row of a sample: a language with its codes for each parameter. -/
structure Row where
  /-- The language. -/
  language : Language
  /-- The codes for orientation. -/
  orientation : List (Coded Orientation)
  /-- The codes for Production strategies. -/
  production : List (Coded Strategy)
  /-- The codes for Interpretive strategies. -/
  interpretive : List (Coded Strategy)
  /-- The codes for Praising. -/
  praising : List (Coded Strategy)
  deriving DecidableEq, Repr

def american : Language :=
  { id := "american", name := "Mainstream American", glottocode := some "stan1293" }

def samoan : Language :=
  { id := "samoan", name := "Samoan", glottocode := some "samo1305" }

/-- Verbal strategies that constitute mothering. The rows of Figure 14.3, in the order of the source (ochs-1992, Figure 14.3, p. 347). -/
def figure143 : List Row := [
  { language := american,
    orientation := [⟨.childCentered, false, false, false⟩],
    production := [⟨.extensiveSimplification, false, false, false⟩],
    interpretive := [⟨.expressGuess, false, false, false⟩],
    praising := [⟨.unidirectional, false, false, false⟩] },
  { language := samoan,
    orientation := [⟨.otherCentered, false, false, false⟩],
    production := [⟨.littleSimplification, false, false, false⟩],
    interpretive := [⟨.displayMinimalGrasp, false, false, false⟩],
    praising := [⟨.bidirectional, false, false, false⟩] }]

end Ochs1992.StructureDataset
