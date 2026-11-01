module

public import Linglib.Data.Experiments.Schema

/-!
# ODonnell2015: corpus counts (generated)

Auto-generated from `Linglib/Data/Corpus/ODonnell2015.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

O'Donnell's counts for the nominalizers *-ness*:Adj>N and *-ion*:V>N in the CELEX-derived training
corpus of Chapter 7: word types, word tokens and hapax legomena. Page numbers are those of the 2015
MIT Press edition.

## References

* [odonnell-2015]
-/

@[expose] public section

namespace ODonnell2015

open Data.Experiments

/-- The two nominalizers whose frequency spectra Figure 7.4 compares. -/
inductive Suffix where
  /-- -ness: *-ness*:Adj>N, abstract nouns from adjectives, as in *pine-scentedness* -/
  | ness
  /-- -ion: *-ion*:V>N, nouns from verbs, as in *regression* -/
  | ion
  deriving DecidableEq, Repr, Fintype

/-- A row of pp. 267–268: The word types, word tokens and hapax legomena of a nominalizer in the
training corpus. -/
structure SpectrumRow where
  /-- The number of word types containing the nominalizer. -/
  wordTypes : ℕ
  /-- The number of word tokens containing the nominalizer. -/
  wordTokens : ℕ
  /-- The number of word types containing the nominalizer that occur once. -/
  hapaxes : ℕ
  deriving DecidableEq, Repr

/-- The cells of pp. 267–268, by suffix; checked against the page images. -/
def spectrum : Suffix → SpectrumRow
  | .ness =>  -- p. 268 misprints -ion for -ness here; Figure 7.4 and the next sentence settle it
    ⟨1024,
     15568,
     350⟩
  | .ion => ⟨1117, 162573, 83⟩

end ODonnell2015
