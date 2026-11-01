module

public import Linglib.Data.Statistics.Schema

/-!
# Creissels2024: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/Creissels2024.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The survey figures Creissels reports from Bahrt (2021: 144): the percentage of the languages of a
222-language sample, all of different genera, in which synthetic marking of each of seven types of
voice alternation is attested, analytic marking excluded.

## References

* [creissels-2024]
-/

@[expose] public section

namespace Creissels2024

open Data.Statistics

/-- A type of voice alternation in Bahrt's survey, whose applicativization pools the book's
applicativization with non-causative A/S-nucleativization. -/
inductive BahrtType where
  /-- causativization: a causer nucleativized -/
  | causativization
  /-- reciprocalization: A and P cumulated in a group S -/
  | reciprocalization
  /-- applicativization: an applied phrase added, or a non-causer nucleativized as A or S -/
  | applicativization
  /-- reflexivization: A and P cumulated in an individual S -/
  | reflexivization
  /-- decausativization: the initial A suppressed -/
  | decausativization
  /-- passivization: the initial A denucleativized -/
  | passivization
  /-- antipassivization: the initial P denucleativized -/
  | antipassivization
  deriving DecidableEq, Repr, Fintype

/-- The languages of Bahrt's sample. (§8.3.8, p. 348; checked against the page images.) -/
def bahrtSampleSize : ℕ := 222

/-- A row of §8.3.8, p. 348: the percentage of the sample with synthetic marking of each type. -/
structure BahrtShare where
  /-- The percentage of the sample with synthetic marking of it. -/
  share : Decimal
  deriving DecidableEq, Repr

/-- The cells of §8.3.8, p. 348, by type; from a sample of languages coded from their
descriptions; checked against the page images. -/
def bahrtShares : BahrtType → BahrtShare
  | .causativization => ⟨⟨739, 1⟩⟩
  | .reciprocalization => ⟨⟨604, 1⟩⟩
  | .applicativization => ⟨⟨459, 1⟩⟩
  | .reflexivization => ⟨⟨419, 1⟩⟩
  | .decausativization => ⟨⟨360, 1⟩⟩
  | .passivization => ⟨⟨360, 1⟩⟩
  | .antipassivization => ⟨⟨185, 1⟩⟩

end Creissels2024
