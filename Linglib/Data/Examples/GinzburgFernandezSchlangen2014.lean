module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `GinzburgFernandezSchlangen2014` — typed example data

Auto-generated from `Linglib/Data/Examples/GinzburgFernandezSchlangen2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GinzburgFernandezSchlangen2014.Examples`.
-/

@[expose] public section

namespace GinzburgFernandezSchlangen2014.Examples

def ex_37d : Datum :=
  { id := "ginzburgfernandezschlangen2014_37d"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(37a), (37d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is Bo here? B: You mean Jo."
    glossedTokens := [("Is", ""), ("Bo", ""), ("here", ""), ("You", ""), ("mean", ""), ("Jo", "")]
    glossedWords := [⟨['I', 's'], [], [⟨['I', 's'], [], none⟩]⟩, ⟨['B', 'o'], [], [⟨['B', 'o'], [], none⟩]⟩, ⟨['h', 'e', 'r', 'e'], [], [⟨['h', 'e', 'r', 'e'], [], none⟩]⟩, ⟨['Y', 'o', 'u'], [], [⟨['Y', 'o', 'u'], [], none⟩]⟩, ⟨['m', 'e', 'a', 'n'], [], [⟨['m', 'e', 'a', 'n'], [], none⟩]⟩, ⟨['J', 'o'], [], [⟨['J', 'o'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "reparandum", some "Bo"⟩, ⟨5, 1, "alteration", some "Jo"⟩]
    paperFeatures := [("direction", "backward looking"), ("turn", "taken")] }

def ex_41 : Datum :=
  { id := "ginzburgfernandezschlangen2014_41"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is Georges here? I meant Jacques."
    glossedTokens := [("Is", ""), ("Georges", ""), ("here", ""), ("I", ""), ("meant", ""), ("Jacques", "")]
    glossedWords := [⟨['I', 's'], [], [⟨['I', 's'], [], none⟩]⟩, ⟨['G', 'e', 'o', 'r', 'g', 'e', 's'], [], [⟨['G', 'e', 'o', 'r', 'g', 'e', 's'], [], none⟩]⟩, ⟨['h', 'e', 'r', 'e'], [], [⟨['h', 'e', 'r', 'e'], [], none⟩]⟩, ⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['m', 'e', 'a', 'n', 't'], [], [⟨['m', 'e', 'a', 'n', 't'], [], none⟩]⟩, ⟨['J', 'a', 'c', 'q', 'u', 'e', 's'], [], [⟨['J', 'a', 'c', 'q', 'u', 'e', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "reparandum", some "Georges"⟩, ⟨5, 1, "alteration", some "Jacques"⟩]
    paperFeatures := [("direction", "backward looking"), ("turn", "kept")] }

def ex_49 : Datum :=
  { id := "ginzburgfernandezschlangen2014_49"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Take that book in I mean from the shelf"
    glossedTokens := [("Take", ""), ("that", ""), ("book", ""), ("in", ""), ("I", ""), ("mean", ""), ("from", ""), ("the", ""), ("shelf", "")]
    glossedWords := [⟨['T', 'a', 'k', 'e'], [], [⟨['T', 'a', 'k', 'e'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩, ⟨['b', 'o', 'o', 'k'], [], [⟨['b', 'o', 'o', 'k'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['m', 'e', 'a', 'n'], [], [⟨['m', 'e', 'a', 'n'], [], none⟩]⟩, ⟨['f', 'r', 'o', 'm'], [], [⟨['f', 'r', 'o', 'm'], [], none⟩]⟩, ⟨['t', 'h', 'e'], [], [⟨['t', 'h', 'e'], [], none⟩]⟩, ⟨['s', 'h', 'e', 'l', 'f'], [], [⟨['s', 'h', 'e', 'l', 'f'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "reparandum", some "in"⟩, ⟨6, 1, "alteration", some "from"⟩]
    paperFeatures := [("direction", "backward looking"), ("turn", "kept")] }

def ex_54 : Datum :=
  { id := "ginzburgfernandezschlangen2014_54"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(54)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Have you seen Mark's erm earphones? Headphones."
    glossedTokens := [("Have", ""), ("you", ""), ("seen", ""), ("Mark's", ""), ("erm", ""), ("earphones", ""), ("Headphones", "")]
    glossedWords := [⟨['H', 'a', 'v', 'e'], [], [⟨['H', 'a', 'v', 'e'], [], none⟩]⟩, ⟨['y', 'o', 'u'], [], [⟨['y', 'o', 'u'], [], none⟩]⟩, ⟨['s', 'e', 'e', 'n'], [], [⟨['s', 'e', 'e', 'n'], [], none⟩]⟩, ⟨['M', 'a', 'r', 'k', '\'', 's'], [], [⟨['M', 'a', 'r', 'k', '\'', 's'], [], none⟩]⟩, ⟨['e', 'r', 'm'], [], [⟨['e', 'r', 'm'], [], none⟩]⟩, ⟨['e', 'a', 'r', 'p', 'h', 'o', 'n', 'e', 's'], [], [⟨['e', 'a', 'r', 'p', 'h', 'o', 'n', 'e', 's'], [], none⟩]⟩, ⟨['H', 'e', 'a', 'd', 'p', 'h', 'o', 'n', 'e', 's'], [], [⟨['H', 'e', 'a', 'd', 'p', 'h', 'o', 'n', 'e', 's'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("I mean headphones", .acceptable)]
    spans := [⟨5, 1, "reparandum", some "earphones"⟩, ⟨6, 1, "alteration", some "headphones"⟩]
    paperFeatures := [("direction", "backward looking"), ("turn", "kept")] }

def iv_swimming : Datum :=
  { id := "ginzburgfernandezschlangen2014_iv_swimming"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "§4 (iv)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was a little bit + swimming"
    glossedTokens := [("I", ""), ("was", ""), ("a", ""), ("little", ""), ("bit", ""), ("+", ""), ("swimming", "")]
    glossedWords := [⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['w', 'a', 's'], [], [⟨['w', 'a', 's'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['l', 'i', 't', 't', 'l', 'e'], [], [⟨['l', 'i', 't', 't', 'l', 'e'], [], none⟩]⟩, ⟨['b', 'i', 't'], [], [⟨['b', 'i', 't'], [], none⟩]⟩, ⟨['+'], [], [⟨['+'], [], none⟩]⟩, ⟨['s', 'w', 'i', 'm', 'm', 'i', 'n', 'g'], [], [⟨['s', 'w', 'i', 'm', 'm', 'i', 'n', 'g'], [], none⟩]⟩]
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := [("I was swimming", .unacceptable)]
    spans := [⟨2, 3, "reparandum", some "a little bit"⟩, ⟨6, 1, "alteration", some "swimming"⟩]
    paperFeatures := [("direction", "backward looking"), ("turn", "kept")] }

def iv_quite_a_bit : Datum :=
  { id := "ginzburgfernandezschlangen2014_iv_quite_a_bit"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "§4 (iv)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was a little bit + actually, quite a bit shocked by that"
    glossedTokens := [("I", ""), ("was", ""), ("a", ""), ("little", ""), ("bit", ""), ("+", ""), ("actually", ""), ("quite", ""), ("a", ""), ("bit", ""), ("shocked", ""), ("by", ""), ("that", "")]
    glossedWords := [⟨['I'], [], [⟨['I'], [], none⟩]⟩, ⟨['w', 'a', 's'], [], [⟨['w', 'a', 's'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['l', 'i', 't', 't', 'l', 'e'], [], [⟨['l', 'i', 't', 't', 'l', 'e'], [], none⟩]⟩, ⟨['b', 'i', 't'], [], [⟨['b', 'i', 't'], [], none⟩]⟩, ⟨['+'], [], [⟨['+'], [], none⟩]⟩, ⟨['a', 'c', 't', 'u', 'a', 'l', 'l', 'y'], [], [⟨['a', 'c', 't', 'u', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['q', 'u', 'i', 't', 'e'], [], [⟨['q', 'u', 'i', 't', 'e'], [], none⟩]⟩, ⟨['a'], [], [⟨['a'], [], none⟩]⟩, ⟨['b', 'i', 't'], [], [⟨['b', 'i', 't'], [], none⟩]⟩, ⟨['s', 'h', 'o', 'c', 'k', 'e', 'd'], [], [⟨['s', 'h', 'o', 'c', 'k', 'e', 'd'], [], none⟩]⟩, ⟨['b', 'y'], [], [⟨['b', 'y'], [], none⟩]⟩, ⟨['t', 'h', 'a', 't'], [], [⟨['t', 'h', 'a', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("I was quite a bit shocked by that", .acceptable)]
    spans := [⟨2, 3, "reparandum", some "a little bit"⟩, ⟨7, 3, "alteration", some "quite a bit"⟩]
    paperFeatures := [("direction", "backward looking"), ("turn", "kept")] }

def ex_67 : Datum :=
  { id := "ginzburgfernandezschlangen2014_67"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Show flights arriving in uh Boston."
    glossedTokens := [("Show", ""), ("flights", ""), ("arriving", ""), ("in", ""), ("uh", ""), ("Boston", "")]
    glossedWords := [⟨['S', 'h', 'o', 'w'], [], [⟨['S', 'h', 'o', 'w'], [], none⟩]⟩, ⟨['f', 'l', 'i', 'g', 'h', 't', 's'], [], [⟨['f', 'l', 'i', 'g', 'h', 't', 's'], [], none⟩]⟩, ⟨['a', 'r', 'r', 'i', 'v', 'i', 'n', 'g'], [], [⟨['a', 'r', 'r', 'i', 'v', 'i', 'n', 'g'], [], none⟩]⟩, ⟨['i', 'n'], [], [⟨['i', 'n'], [], none⟩]⟩, ⟨['u', 'h'], [], [⟨['u', 'h'], [], none⟩]⟩, ⟨['B', 'o', 's', 't', 'o', 'n'], [], [⟨['B', 'o', 's', 't', 'o', 'n'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "reparandum", some "in"⟩, ⟨5, 1, "alteration", some "Boston"⟩]
    paperFeatures := [("direction", "forward looking"), ("turn", "kept")] }

def ex_11a : Datum :=
  { id := "ginzburgfernandezschlangen2014_11a"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(11a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "A: Chilli, has, has, has never really been [pause] er B: A big seller."
    glossedTokens := [("Chilli", ""), ("has", ""), ("has", ""), ("has", ""), ("never", ""), ("really", ""), ("been", ""), ("[pause]", ""), ("er", ""), ("A", ""), ("big", ""), ("seller", "")]
    glossedWords := [⟨['C', 'h', 'i', 'l', 'l', 'i'], [], [⟨['C', 'h', 'i', 'l', 'l', 'i'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['h', 'a', 's'], [], [⟨['h', 'a', 's'], [], none⟩]⟩, ⟨['n', 'e', 'v', 'e', 'r'], [], [⟨['n', 'e', 'v', 'e', 'r'], [], none⟩]⟩, ⟨['r', 'e', 'a', 'l', 'l', 'y'], [], [⟨['r', 'e', 'a', 'l', 'l', 'y'], [], none⟩]⟩, ⟨['b', 'e', 'e', 'n'], [], [⟨['b', 'e', 'e', 'n'], [], none⟩]⟩, ⟨['[', 'p', 'a', 'u', 's', 'e', ']'], [], [⟨['p', 'a', 'u', 's', 'e'], [], none⟩]⟩, ⟨['e', 'r'], [], [⟨['e', 'r'], [], none⟩]⟩, ⟨['A'], [], [⟨['A'], [], none⟩]⟩, ⟨['b', 'i', 'g'], [], [⟨['b', 'i', 'g'], [], none⟩]⟩, ⟨['s', 'e', 'l', 'l', 'e', 'r'], [], [⟨['s', 'e', 'l', 'l', 'e', 'r'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨6, 1, "reparandum", some "been"⟩, ⟨9, 3, "alteration", some "a big seller"⟩]
    paperFeatures := [("direction", "forward looking"), ("turn", "taken")] }

def ex_72a : Datum :=
  { id := "ginzburgfernandezschlangen2014_72a"
    source := ⟨"ginzburg-fernandez-schlangen-2014", "(72a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Carol: Well it's (pause) it's (pause) er (pause) what's his name? Bernard Matthews' turkey roast."
    glossedTokens := [("Well", ""), ("it's", ""), ("(pause)", ""), ("it's", ""), ("(pause)", ""), ("er", ""), ("(pause)", ""), ("what's", ""), ("his", ""), ("name", ""), ("Bernard", ""), ("Matthews'", ""), ("turkey", ""), ("roast", "")]
    glossedWords := [⟨['W', 'e', 'l', 'l'], [], [⟨['W', 'e', 'l', 'l'], [], none⟩]⟩, ⟨['i', 't', '\'', 's'], [], [⟨['i', 't', '\'', 's'], [], none⟩]⟩, ⟨['(', 'p', 'a', 'u', 's', 'e', ')'], [], [⟨['p', 'a', 'u', 's', 'e'], [], none⟩]⟩, ⟨['i', 't', '\'', 's'], [], [⟨['i', 't', '\'', 's'], [], none⟩]⟩, ⟨['(', 'p', 'a', 'u', 's', 'e', ')'], [], [⟨['p', 'a', 'u', 's', 'e'], [], none⟩]⟩, ⟨['e', 'r'], [], [⟨['e', 'r'], [], none⟩]⟩, ⟨['(', 'p', 'a', 'u', 's', 'e', ')'], [], [⟨['p', 'a', 'u', 's', 'e'], [], none⟩]⟩, ⟨['w', 'h', 'a', 't', '\'', 's'], [], [⟨['w', 'h', 'a', 't', '\'', 's'], [], none⟩]⟩, ⟨['h', 'i', 's'], [], [⟨['h', 'i', 's'], [], none⟩]⟩, ⟨['n', 'a', 'm', 'e'], [], [⟨['n', 'a', 'm', 'e'], [], none⟩]⟩, ⟨['B', 'e', 'r', 'n', 'a', 'r', 'd'], [], [⟨['B', 'e', 'r', 'n', 'a', 'r', 'd'], [], none⟩]⟩, ⟨['M', 'a', 't', 't', 'h', 'e', 'w', 's', '\''], [], [⟨['M', 'a', 't', 't', 'h', 'e', 'w', 's', '\''], [], none⟩]⟩, ⟨['t', 'u', 'r', 'k', 'e', 'y'], [], [⟨['t', 'u', 'r', 'k', 'e', 'y'], [], none⟩]⟩, ⟨['r', 'o', 'a', 's', 't'], [], [⟨['r', 'o', 'a', 's', 't'], [], none⟩]⟩]
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "reparandum", some "it's"⟩, ⟨7, 3, "query", none⟩]
    paperFeatures := [("direction", "forward looking"), ("turn", "kept"), ("query", "name")] }

def all : List Datum := [ex_37d, ex_41, ex_49, ex_54, iv_swimming, iv_quite_a_bit, ex_67, ex_11a, ex_72a]

/-- Whether a disfluency looks back to material already uttered or forward to what comes next. -/
inductive Direction where
  /-- backward looking: the alteration replaces material already uttered, the reparandum -/
  | backward
  /-- forward looking: an editing phrase is followed by the continuation of the utterance -/
  | forward
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `direction`. -/
def direction (e : Datum) : Option Direction :=
  e.parse? "direction" [("backward looking", .backward), ("forward looking", .forward)]

/-- Who utters what follows the moment of interruption. -/
inductive Continuer where
  /-- kept: the speaker of the interrupted utterance -/
  | kept
  /-- taken: the addressee -/
  | taken
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `turn`. -/
def continuer (e : Datum) : Option Continuer :=
  e.parse? "turn" [("kept", .kept), ("taken", .taken)]

/-- The kinds of self addressed query the paper finds after a filled pause. -/
inductive Query where
  /-- name: a query for the name of a person or thing, such as what's his name? -/
  | name
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `query`. -/
def query (e : Datum) : Option Query :=
  e.parse? "query" [("name", .name)]

/-- The parts of a disfluency the rows mark. -/
inductive SpanLabel where
  /-- reparandum: the sub-utterance u0 the accommodated question is about: the material replaced, or the word the editing phrase follows -/
  | reparandum
  /-- alteration: what follows the moment of interruption and answers the accommodated question -/
  | alteration
  /-- query: a self addressed query following the moment of interruption -/
  | query
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("reparandum", .reparandum), ("alteration", .alteration), ("query", .query)]

/-- The sub-utterances the spans are forms of. -/
inductive Lexeme where
  /-- Bo: the name Bo -/
  | bo
  /-- Jo: the name Jo -/
  | jo
  /-- Georges: the name Georges -/
  | georges
  /-- Jacques: the name Jacques -/
  | jacques
  /-- Boston: the name Boston -/
  | boston
  /-- in: the preposition in -/
  | inP
  /-- from: the preposition from -/
  | fromP
  /-- earphones: the noun earphones -/
  | earphones
  /-- headphones: the noun headphones -/
  | headphones
  /-- a little bit: the degree phrase a little bit -/
  | aLittleBit
  /-- quite a bit: the degree phrase quite a bit -/
  | quiteABit
  /-- swimming: the verb form swimming -/
  | swimming
  /-- a big seller: the predicative noun phrase a big seller -/
  | aBigSeller
  /-- been: the copula form been -/
  | been
  /-- it's: it's, the pronoun with the copula -/
  | its
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("Bo", .bo), ("Jo", .jo), ("Georges", .georges), ("Jacques", .jacques), ("Boston", .boston), ("in", .inP), ("from", .fromP), ("earphones", .earphones), ("headphones", .headphones), ("a little bit", .aLittleBit), ("quite a bit", .quiteABit), ("swimming", .swimming), ("a big seller", .aBigSeller), ("been", .been), ("it's", .its)])

/-- The examples of the study. -/
inductive Example where
  | ex_37d
  | ex_41
  | ex_49
  | ex_54
  | iv_swimming
  | iv_quite_a_bit
  | ex_67
  | ex_11a
  | ex_72a
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_37d, .ex_41, .ex_49, .ex_54, .iv_swimming, .iv_quite_a_bit, .ex_67, .ex_11a, .ex_72a]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_37d => _root_.GinzburgFernandezSchlangen2014.Examples.ex_37d
  | .ex_41 => _root_.GinzburgFernandezSchlangen2014.Examples.ex_41
  | .ex_49 => _root_.GinzburgFernandezSchlangen2014.Examples.ex_49
  | .ex_54 => _root_.GinzburgFernandezSchlangen2014.Examples.ex_54
  | .iv_swimming => _root_.GinzburgFernandezSchlangen2014.Examples.iv_swimming
  | .iv_quite_a_bit => _root_.GinzburgFernandezSchlangen2014.Examples.iv_quite_a_bit
  | .ex_67 => _root_.GinzburgFernandezSchlangen2014.Examples.ex_67
  | .ex_11a => _root_.GinzburgFernandezSchlangen2014.Examples.ex_11a
  | .ex_72a => _root_.GinzburgFernandezSchlangen2014.Examples.ex_72a

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.GinzburgFernandezSchlangen2014.Examples.all := rfl

/-- The value the example records under `direction`. -/
def Example.direction : Example → Option Direction
  | .ex_37d => some .backward
  | .ex_41 => some .backward
  | .ex_49 => some .backward
  | .ex_54 => some .backward
  | .iv_swimming => some .backward
  | .iv_quite_a_bit => some .backward
  | .ex_67 => some .forward
  | .ex_11a => some .forward
  | .ex_72a => some .forward

theorem Example.direction_datum :
    ∀ x : Example, _root_.GinzburgFernandezSchlangen2014.Examples.direction x.datum = x.direction := by
  decide +kernel

/-- The value the example records under `turn`. -/
def Example.continuer : Example → Option Continuer
  | .ex_37d => some .taken
  | .ex_41 => some .kept
  | .ex_49 => some .kept
  | .ex_54 => some .kept
  | .iv_swimming => some .kept
  | .iv_quite_a_bit => some .kept
  | .ex_67 => some .kept
  | .ex_11a => some .taken
  | .ex_72a => some .kept

theorem Example.continuer_datum :
    ∀ x : Example, _root_.GinzburgFernandezSchlangen2014.Examples.continuer x.datum = x.continuer := by
  decide +kernel

/-- The value the example records under `query`. -/
def Example.query : Example → Option Query
  | .ex_37d => none
  | .ex_41 => none
  | .ex_49 => none
  | .ex_54 => none
  | .iv_swimming => none
  | .iv_quite_a_bit => none
  | .ex_67 => none
  | .ex_11a => none
  | .ex_72a => some .name

theorem Example.query_datum :
    ∀ x : Example, _root_.GinzburgFernandezSchlangen2014.Examples.query x.datum = x.query := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_37d => [(.reparandum, .bo), (.alteration, .jo)]
  | .ex_41 => [(.reparandum, .georges), (.alteration, .jacques)]
  | .ex_49 => [(.reparandum, .inP), (.alteration, .fromP)]
  | .ex_54 => [(.reparandum, .earphones), (.alteration, .headphones)]
  | .iv_swimming => [(.reparandum, .aLittleBit), (.alteration, .swimming)]
  | .iv_quite_a_bit => [(.reparandum, .aLittleBit), (.alteration, .quiteABit)]
  | .ex_67 => [(.reparandum, .inP), (.alteration, .boston)]
  | .ex_11a => [(.reparandum, .been), (.alteration, .aBigSeller)]
  | .ex_72a => [(.reparandum, .its)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.GinzburgFernandezSchlangen2014.Examples.label? · = some l)).filterMap _root_.GinzburgFernandezSchlangen2014.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end GinzburgFernandezSchlangen2014.Examples
