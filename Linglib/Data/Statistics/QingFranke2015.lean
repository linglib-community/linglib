module

public import Linglib.Data.Statistics.Schema

/-!
# QingFranke2015: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/QingFranke2015.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

The forced-choice counts of the one-shot referential game: the word a speaker chose for each target,
and the object a listener chose in the salience condition and on hearing each ambiguous word. A
context has a square and a circle of one colour and a circle of the other; colours and positions
were counterbalanced, and the tables name the objects as in the paper's sample context.

## References

* [qing-franke-2015]
-/

@[expose] public section

namespace QingFranke2015

open Data.Statistics

/-- The three objects of a context, named as in the paper's sample context. -/
inductive Object where
  /-- green square: the object with the unique shape -/
  | greenSquare
  /-- green circle: the object that shares both its features -/
  | greenCircle
  /-- blue circle: the object with the unique colour -/
  | blueCircle
  deriving DecidableEq, Repr, Fintype

/-- The four words a speaker could be offered. -/
inductive Message where
  /-- Green: the shared colour -/
  | green
  /-- Square: the unique shape -/
  | square
  /-- Blue: the unique colour -/
  | blue
  /-- Circle: the shared shape -/
  | circle
  deriving DecidableEq, Repr, Fintype

/-- The three listener conditions. -/
inductive Condition where
  /-- Salience: the utterance is in a language the listener does not understand -/
  | salience
  /-- Green: the listener hears the shared colour -/
  | green
  /-- Circle: the listener hears the shared shape -/
  | circle
  deriving DecidableEq, Repr, Fintype

/-- A row of Table 1: the number of speakers who chose a word for a target, of 144 per target. -/
structure SpeakerChoice where
  /-- The number of speakers who chose the word, with `none` where the word was not offered. -/
  count : Option ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 1, by target and message; from an experiment; checked against the page
images. -/
def speakerChoice : Object → Message → SpeakerChoice
  | .greenSquare, .green => ⟨some 9⟩
  | .greenSquare, .square => ⟨some 135⟩
  | .greenSquare, .blue => ⟨none⟩
  | .greenSquare, .circle => ⟨none⟩
  | .greenCircle, .green => ⟨some 63⟩
  | .greenCircle, .square => ⟨none⟩
  | .greenCircle, .blue => ⟨none⟩
  | .greenCircle, .circle => ⟨some 81⟩
  | .blueCircle, .green => ⟨none⟩
  | .blueCircle, .square => ⟨none⟩
  | .blueCircle, .blue => ⟨some 119⟩
  | .blueCircle, .circle => ⟨some 25⟩

/-- A row of Table 2: the number of listeners who chose an object in a condition, of 240 in the
salience condition and 180 in each of the others. -/
structure ListenerChoice where
  /-- The number of listeners who chose the object. -/
  count : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table 2, by condition and object; from an experiment; checked against the page
images. -/
def listenerChoice : Condition → Object → ListenerChoice
  | .salience, .greenSquare => ⟨71⟩
  | .salience, .greenCircle => ⟨30⟩
  | .salience, .blueCircle => ⟨139⟩
  | .green, .greenSquare => ⟨65⟩
  | .green, .greenCircle => ⟨115⟩
  | .green, .blueCircle => ⟨0⟩
  | .circle, .greenSquare => ⟨1⟩
  | .circle, .greenCircle => ⟨62⟩
  | .circle, .blueCircle => ⟨117⟩

end QingFranke2015
