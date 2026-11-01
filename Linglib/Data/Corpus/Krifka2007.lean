module

public import Linglib.Data.Experiments.Schema

/-!
# Krifka2007: corpus counts (generated)

Auto-generated from `Linglib/Data/Corpus/Krifka2007.json` by `scripts/gen_experiments.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Krifka's own corpus counts behind the alignment of expression simplicity with representation
simplicity. Average syllable counts of English number words on scales of different granularity, and
Google occurrence counts of March 4, 2005 for the words for the multiples of ten from 20 to 90 in
decimal Norwegian and vigesimal Danish.

## References

* [krifka-2007]
-/

@[expose] public section

namespace Krifka2007

open Data.Experiments

/-- A scale whose number words are counted for syllables. -/
inductive SyllableScale where
  /-- ones: *one, two, three, four, ... one hundred* -/
  | ones
  /-- fives: *one, five, ten, fifteen, ... one hundred* -/
  | fives
  /-- tens: *one, ten, twenty, thirty, ... one hundred* -/
  | tens
  /-- threes: *three, six, nine, twelve, ... ninety-nine*, the odd scale no decimal granularity
  motivates -/
  | threes
  /-- months by one: ages of young children in months, 1 to 24 -/
  | monthsByOne
  /-- months coarse: ages of young children at 1, 3, 6, 9, 12, 15, 18, 21 and 24 months -/
  | monthsCoarse
  deriving DecidableEq, Repr, Fintype

/-- The two Scandinavian languages compared. -/
inductive Language where
  /-- Norwegian: decimal number system -/
  | norwegian
  /-- Danish: vigesimal number system from 50 up -/
  | danish
  deriving DecidableEq, Repr, Fintype

/-- A Norwegian or Danish word for a multiple of ten. -/
inductive Word where
  /-- tjue: Norwegian 20 -/
  | tjue
  /-- tretti: Norwegian 30 -/
  | tretti
  /-- førti: Norwegian 40 -/
  | foerti
  /-- femti: Norwegian 50 -/
  | femti
  /-- seksti: Norwegian 60 -/
  | seksti
  /-- sytti: Norwegian 70 -/
  | sytti
  /-- åtti: Norwegian 80 -/
  | aatti
  /-- nitti: Norwegian 90 -/
  | nitti
  /-- tyve: Danish 20 -/
  | tyve
  /-- tredive: Danish 30 -/
  | tredive
  /-- fyrre: Danish 40 -/
  | fyrre
  /-- halvtreds: Danish 50, shortened from *halvtredsindstyve*, half-third-times-twenty -/
  | halvtreds
  /-- tres: Danish 60, a score word -/
  | tres
  /-- halvfjerds: Danish 70, a half-score word -/
  | halvfjerds
  /-- firs: Danish 80, a score word -/
  | firs
  /-- halvfems: Danish 90, a half-score word -/
  | halvfems
  deriving DecidableEq, Repr, Fintype

/-- Occurrences of the complete Danish form *halvtredsindstyve* for 50. ((27) discussion,
manuscript p. 10; checked against the page images.) -/
def halvtredsindstyveCount : ℕ := 1180

/-- Occurrences of the mostly monetary Danish form *femti* for 50. ((27) discussion, manuscript
p. 10; checked against the page images.) -/
def danishFemtiCount : ℕ := 988

/-- A row of (19), (20), manuscript p. 8; (22) averages, manuscript p. 9: the total syllables and
the number of words on each scale. -/
structure SyllableCount where
  /-- The total syllables of its number words. -/
  syllables : ℕ
  /-- The number of its number words. -/
  words : ℕ
  deriving DecidableEq, Repr

/-- The cells of (19), (20), manuscript p. 8; (22) averages, manuscript p. 9, by scale; checked
against the page images. -/
def syllableCounts : SyllableScale → SyllableCount
  | .ones => ⟨273, 100⟩
  | .fives => ⟨46, 20⟩
  | .tens => ⟨21, 10⟩
  | .threes => ⟨92, 33⟩
  | .monthsByOne => ⟨44, 24⟩
  | .monthsCoarse => ⟨25, 9⟩

/-- A row of (27), manuscript p. 10: the Google occurrence counts of March 4, 2005 for each word. -/
structure WordCount where
  /-- Its language. -/
  language : Language
  /-- The multiple of ten it names. -/
  number : ℕ
  /-- Its occurrences. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of (27), manuscript p. 10, by word; checked against the page images. -/
def counts : Word → WordCount
  | .tjue => ⟨.norwegian, 20, 61300⟩
  | .tretti => ⟨.norwegian, 30, 43700⟩
  | .foerti => ⟨.norwegian, 40, 39200⟩
  | .femti => ⟨.norwegian, 50, 81200⟩
  | .seksti => ⟨.norwegian, 60, 19400⟩
  | .sytti => ⟨.norwegian, 70, 10200⟩
  | .aatti => ⟨.norwegian, 80, 13100⟩
  | .nitti => ⟨.norwegian, 90, 13500⟩
  | .tyve => ⟨.danish, 20, 121000⟩
  | .tredive => ⟨.danish, 30, 25400⟩
  | .fyrre => ⟨.danish, 40, 26800⟩
  | .halvtreds => ⟨.danish, 50, 15500⟩
  | .tres => ⟨.danish, 60, 36400⟩
  | .halvfjerds => ⟨.danish, 70, 581⟩
  | .firs => ⟨.danish, 80, 3740⟩
  | .halvfems => ⟨.danish, 90, 540⟩

end Krifka2007
