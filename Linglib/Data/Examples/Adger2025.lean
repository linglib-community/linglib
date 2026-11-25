module

public import Linglib.Data.Examples.Schema

/-!
# `Adger2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Adger2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Adger2025.Examples`.
-/

@[expose] public section

namespace Adger2025.Examples

def ch433 : Datum :=
  { id := "adger2025_ch433"
    source := ⟨"adger-2025", "ch. 4 (33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We asked who Anson wrote the book."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "lowering"), ("mover", "who"), ("target", "embedded C")] }

def ch436a : Datum :=
  { id := "adger2025_ch436a"
    source := ⟨"adger-2025", "ch. 4 (36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whose nostril did the doctor look very far into?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "subextraction from PP")] }

def ch436b : Datum :=
  { id := "adger2025_ch436b"
    source := ⟨"adger-2025", "ch. 4 (36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How far did the doctor look into your nostril?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "subextraction from PP")] }

def ch437a : Datum :=
  { id := "adger2025_ch437a"
    source := ⟨"adger-2025", "ch. 4 (37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which cat did you say fell into the pond?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "extraction from clausal complement")] }

def ch437b : Datum :=
  { id := "adger2025_ch437b"
    source := ⟨"adger-2025", "ch. 4 (37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which poem did you say that Anson wrote?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "extraction from clausal complement")] }

def ch443 : Datum :=
  { id := "adger2025_ch443"
    source := ⟨"adger-2025", "ch. 4 (43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Guess) who you said fell?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "successive-cyclic extraction"), ("mover", "who"), ("intermediate", "embedded C[uWh]")] }

def ch448a : Datum :=
  { id := "adger2025_ch448a"
    source := ⟨"adger-2025", "ch. 4 (48a)"⟩
    reportedIn := none
    language := "scot1245"
    primaryText := "Thuirt Daibhidh gum buail Calum an cat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complementizer", "gum")] }

def ch448b : Datum :=
  { id := "adger2025_ch448b"
    source := ⟨"adger-2025", "ch. 4 (48b)"⟩
    reportedIn := none
    language := "scot1245"
    primaryText := "An cat a thuirt Daibhidh a bhuaileas Calum."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("complementizer", "a (relative) at both clauses")] }

def ch448c : Datum :=
  { id := "adger2025_ch448c"
    source := ⟨"adger-2025", "ch. 4 (48c)"⟩
    reportedIn := none
    language := "scot1245"
    primaryText := "An cat a thuirt Daibhidh gum buail Calum."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("complementizer", "gum in the extraction path")] }

def ch454 : Datum :=
  { id := "adger2025_ch454"
    source := ⟨"adger-2025", "ch. 4 (54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who left did you say?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "clausal pied-piping")] }

def ch51b : Datum :=
  { id := "adger2025_ch51b"
    source := ⟨"adger-2025", "ch. 5 (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Guess) what you asked who bought?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("configuration", "wh-island"), ("mover", "what"), ("C 2-part", "who")] }

def ch630 : Datum :=
  { id := "adger2025_ch630"
    source := ⟨"adger-2025", "ch. 6 (30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which display table do booksellers usually recommend a book on?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "locative PP as matching relative")] }

def ch631 : Datum :=
  { id := "adger2025_ch631"
    source := ⟨"adger-2025", "ch. 6 (31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you buy a statue of?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "indefinite"), ("D 2-part", "free")] }

def ch634 : Datum :=
  { id := "adger2025_ch634"
    source := ⟨"adger-2025", "ch. 6 (34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you buy the statue of?"
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "definite"), ("D 2-part", "Det")] }

def ch635a : Datum :=
  { id := "adger2025_ch635a"
    source := ⟨"adger-2025", "ch. 6 (35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you buy that statue of?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "demonstrative"), ("D 2-part", "Dem")] }

def ch635b : Datum :=
  { id := "adger2025_ch635b"
    source := ⟨"adger-2025", "ch. 6 (35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you buy Anson's statue of?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "prenominal possessor"), ("D 2-part", "possessor")] }

def ch635c : Datum :=
  { id := "adger2025_ch635c"
    source := ⟨"adger-2025", "ch. 6 (35c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who did you buy a statue of of Anson's?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "postnominal possessive"), ("D 2-part", "free")] }

def ch636a : Datum :=
  { id := "adger2025_ch636a"
    source := ⟨"adger-2025", "ch. 6 (36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Of whom did you buy a statue?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "indefinite"), ("pied-piping", "of")] }

def ch636b : Datum :=
  { id := "adger2025_ch636b"
    source := ⟨"adger-2025", "ch. 6 (36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Of whom did you buy the statue?"
    glossedTokens := []
    context := ""
    judgment := .questionable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "definite"), ("pied-piping", "of")] }

def ch636c : Datum :=
  { id := "adger2025_ch636c"
    source := ⟨"adger-2025", "ch. 6 (36c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Of whom did you buy that statue?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "demonstrative"), ("pied-piping", "of")] }

def ch636d : Datum :=
  { id := "adger2025_ch636d"
    source := ⟨"adger-2025", "ch. 6 (36d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Of whom did you buy Anson's statue?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "prenominal possessor"), ("pied-piping", "of")] }

def ch640a : Datum :=
  { id := "adger2025_ch640a"
    source := ⟨"adger-2025", "ch. 6 (40a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Worüber hat der Fritz ein Buch gelesen?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "indefinite")] }

def ch640b : Datum :=
  { id := "adger2025_ch640b"
    source := ⟨"adger-2025", "ch. 6 (40b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Worüber hat der Fritz das Buch gelesen?"
    glossedTokens := []
    context := ""
    judgment := .nearlyUngrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "definite")] }

def ch640c : Datum :=
  { id := "adger2025_ch640c"
    source := ⟨"adger-2025", "ch. 6 (40c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Worüber hat die Maria Fritzens Buch gelesen?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "prenominal possessor")] }

def ch641a : Datum :=
  { id := "adger2025_ch641a"
    source := ⟨"adger-2025", "ch. 6 (41a)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Kimea diruz ye she'r az ki xund?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "indefinite"), ("wh", "in situ, matrix scope")] }

def ch641b : Datum :=
  { id := "adger2025_ch641b"
    source := ⟨"adger-2025", "ch. 6 (41b)"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Kimea in she'r az ki ro xund?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "demonstrative"), ("wh", "in situ, matrix scope")] }

def ch642a : Datum :=
  { id := "adger2025_ch642a"
    source := ⟨"adger-2025", "ch. 6 (42a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni faxian-le shei-de diaoxiang?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "indefinite"), ("wh", "in situ, matrix scope")] }

def ch642b : Datum :=
  { id := "adger2025_ch642b"
    source := ⟨"adger-2025", "ch. 6 (42b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni faxian-le na-ge shei-de diaoxiang?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "demonstrative"), ("wh", "in situ, echo question only")] }

def ch643a : Datum :=
  { id := "adger2025_ch643a"
    source := ⟨"adger-2025", "ch. 6 (43a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Shei mai-de shu zui hao?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "indefinite relative"), ("wh", "in situ, matrix scope")] }

def ch643b : Datum :=
  { id := "adger2025_ch643b"
    source := ⟨"adger-2025", "ch. 6 (43b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Shei mai-de nei ben shu zui hao?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "demonstrative relative"), ("wh", "in situ, matrix scope")] }

def ch644a : Datum :=
  { id := "adger2025_ch644a"
    source := ⟨"adger-2025", "ch. 6 (44a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa dare-ga kaita hon-o yonda no."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "indefinite relative"), ("wh", "in situ, matrix scope")] }

def ch644b : Datum :=
  { id := "adger2025_ch644b"
    source := ⟨"adger-2025", "ch. 6 (44b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa dare-ga kaita sono hon-o yonda no."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("nominal", "demonstrative relative"), ("wh", "in situ, matrix scope")] }

def ch759a : Datum :=
  { id := "adger2025_ch759a"
    source := ⟨"adger-2025", "ch. 7 (59a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What were pictures of seen around the globe?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indefinite or weak definite"), ("D 2-part", "free")] }

def ch759b : Datum :=
  { id := "adger2025_ch759b"
    source := ⟨"adger-2025", "ch. 7 (59b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's the kind of policy statement that jokes about are a dime a dozen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indefinite or weak definite"), ("D 2-part", "free")] }

def ch759c : Datum :=
  { id := "adger2025_ch759c"
    source := ⟨"adger-2025", "ch. 7 (59c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are certain topics that jokes about are completely unacceptable."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indefinite or weak definite"), ("D 2-part", "free")] }

def ch759d : Datum :=
  { id := "adger2025_ch759d"
    source := ⟨"adger-2025", "ch. 7 (59d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which car did some pictures of cause a scandal?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indefinite or weak definite"), ("D 2-part", "free")] }

def ch759e : Datum :=
  { id := "adger2025_ch759e"
    source := ⟨"adger-2025", "ch. 7 (59e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did the attempt to find end in failure?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indefinite or weak definite"), ("D 2-part", "free")] }

def ch759f : Datum :=
  { id := "adger2025_ch759f"
    source := ⟨"adger-2025", "ch. 7 (59f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which president would the impeachment of cause more outrage?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indefinite or weak definite"), ("D 2-part", "free")] }

def ch759g : Datum :=
  { id := "adger2025_ch759g"
    source := ⟨"adger-2025", "ch. 7 (59g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have a question that the probability of you knowing the answer to is zero."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indefinite or weak definite"), ("D 2-part", "free")] }

def all : List Datum := [ch433, ch436a, ch436b, ch437a, ch437b, ch443, ch448a, ch448b, ch448c, ch454, ch51b, ch630, ch631, ch634, ch635a, ch635b, ch635c, ch636a, ch636b, ch636c, ch636d, ch640a, ch640b, ch640c, ch641a, ch641b, ch642a, ch642b, ch643a, ch643b, ch644a, ch644b, ch759a, ch759b, ch759c, ch759d, ch759e, ch759f, ch759g]

end Adger2025.Examples
