module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `ParteeBorschev2001` — typed example data

Auto-generated from `Linglib/Data/Examples/ParteeBorschev2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ParteeBorschev2001.Examples`.
-/

@[expose] public section

namespace ParteeBorschev2001.Examples

def ex1c : Datum :=
  { id := "parteeborschev2001_ex1c"
    source := ⟨"partee-1997", "p. 464"⟩
    reportedIn := some ⟨"partee-borschev-2001", "(1c)"⟩
    language := "stan1293"
    primaryText := "That team is John's"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "team"), ("subject", "demonstrative")] }

def ex2c : Datum :=
  { id := "parteeborschev2001_ex2c"
    source := ⟨"partee-1997", "p. 464"⟩
    reportedIn := some ⟨"partee-borschev-2001", "(2c)"⟩
    language := "stan1293"
    primaryText := "That brother is John's"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "brother"), ("subject", "demonstrative")] }

def ex3c : Datum :=
  { id := "parteeborschev2001_ex3c"
    source := ⟨"partee-1997", "p. 464"⟩
    reportedIn := some ⟨"partee-borschev-2001", "(3c)"⟩
    language := "stan1293"
    primaryText := "That favorite movie is John's"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "favorite movie"), ("subject", "demonstrative")] }

def ex17a : Datum :=
  { id := "parteeborschev2001_ex17a"
    source := ⟨"partee-borschev-2001", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That father is John's."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "father"), ("subject", "demonstrative")] }

def ex17b : Datum :=
  { id := "parteeborschev2001_ex17b"
    source := ⟨"partee-borschev-2001", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That favorite movie is John's."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "favorite movie"), ("subject", "demonstrative")] }

def ex17c : Datum :=
  { id := "parteeborschev2001_ex17c"
    source := ⟨"partee-borschev-2001", "(17c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "That teacher is John's."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "teacher"), ("subject", "demonstrative")] }

def ex17d : Datum :=
  { id := "parteeborschev2001_ex17d"
    source := ⟨"partee-borschev-2001", "(17d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "His father is also John's."
    glossedTokens := []
    context := "pointing"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "father"), ("subject", "possessive")] }

def ex17e : Datum :=
  { id := "parteeborschev2001_ex17e"
    source := ⟨"partee-borschev-2001", "(17e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "Dad's favorite movie is also mine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "favorite movie"), ("subject", "possessive")] }

def ex17f : Datum :=
  { id := "parteeborschev2001_ex17f"
    source := ⟨"partee-borschev-2001", "(17f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That father is John's father."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "father"), ("subject", "demonstrative")] }

def ex23a : Datum :=
  { id := "parteeborschev2001_ex23a"
    source := ⟨"partee-borschev-2001", "(23a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Petin stul"
    glossedTokens := [("Petin", "Petja-POSS-M.SG."), ("stul", "chair-M.SG.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "possessive")] }

def ex23b : Datum :=
  { id := "parteeborschev2001_ex23b"
    source := ⟨"partee-borschev-2001", "(23b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Mamin portret"
    glossedTokens := [("Mamin", "Mama-POSS-M.SG."), ("portret", "portrait-M.SG.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "possessive")] }

def ex24a : Datum :=
  { id := "parteeborschev2001_ex24a"
    source := ⟨"partee-borschev-2001", "(24a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "stul Peti"
    glossedTokens := [("stul", "chair-M.SG."), ("Peti", "Petja-GEN.SG.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "genitive")] }

def ex24b : Datum :=
  { id := "parteeborschev2001_ex24b"
    source := ⟨"partee-borschev-2001", "(24b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "portret mamy"
    glossedTokens := [("portret", "portrait-M.SG."), ("mamy", "Mama-GEN.SG.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "genitive")] }

def ex25a : Datum :=
  { id := "parteeborschev2001_ex25a"
    source := ⟨"partee-borschev-2001", "(25a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "ubijca Peti"
    glossedTokens := [("ubijca", "murderer-M.SG."), ("Peti", "Petja-GEN.SG.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("murderer of Petja", .acceptable)]
    paperFeatures := [("construction", "genitive")] }

def ex25b : Datum :=
  { id := "parteeborschev2001_ex25b"
    source := ⟨"partee-borschev-2001", "(25b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Petin ubijca"
    glossedTokens := [("Petin", "Petja-POSS-M.SG."), ("ubijca", "murderer-M.SG.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("murderer of Petja", .unacceptable), ("a murderer Petja has hired", .acceptable)]
    paperFeatures := [("construction", "possessive")] }

def ex26 : Datum :=
  { id := "parteeborschev2001_ex26"
    source := ⟨"partee-borschev-2001", "(26)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Diese Bücher sind alt."
    glossedTokens := [("Diese", "These-N.PL"), ("Bücher", "books-N.PL"), ("sind", "are"), ("alt", "old")]
    context := ""
    judgment := .acceptable
    alternatives := [("Diese Bücher sind alte.", .ungrammatical)]
    readings := []
    paperFeatures := [("agreement", "nonagreeing")] }

def ex27 : Datum :=
  { id := "parteeborschev2001_ex27"
    source := ⟨"partee-borschev-2001", "(27)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Diese Bücher sind meine."
    glossedTokens := [("Diese", "These-N.PL"), ("Bücher", "books"), ("sind", "are"), ("meine", "mine-PL")]
    context := ""
    judgment := .acceptable
    alternatives := [("Diese Bücher sind mein.", .ungrammatical)]
    readings := []
    paperFeatures := [("agreement", "agreeing")] }

def ex28a : Datum :=
  { id := "parteeborschev2001_ex28a"
    source := ⟨"partee-borschev-2001", "(28a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Diese Bücher sind meine."
    glossedTokens := [("Diese", "These-N.PL"), ("Bücher", "books-N.PL"), ("sind", "are"), ("meine", "mine-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("agreement", "agreeing")] }

def ex28b : Datum :=
  { id := "parteeborschev2001_ex28b"
    source := ⟨"partee-borschev-2001", "(28b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Diese Bücher sind mein."
    glossedTokens := [("Diese", "These-N.PL"), ("Bücher", "books-N.PL"), ("sind", "are"), ("mein", "mine")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .unacceptable)]
    paperFeatures := [("agreement", "nonagreeing")] }

def ex29a : Datum :=
  { id := "parteeborschev2001_ex29a"
    source := ⟨"partee-borschev-2001", "(29a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Das Land ist (jetzt) meins."
    glossedTokens := [("Das", "The-N.SG"), ("Land", "land-N.SG"), ("ist", "is"), ("(jetzt)", "(now)"), ("meins", "mine-N.SG")]
    context := "A newly naturalized citizen speaks."
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("agreement", "agreeing")] }

def ex29b : Datum :=
  { id := "parteeborschev2001_ex29b"
    source := ⟨"partee-borschev-2001", "(29b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Das Land ist jetzt mein."
    glossedTokens := [("Das", "The-N.SG"), ("Land", "land-N.SG"), ("ist", "is"), ("jetzt", "now"), ("mein", "mine")]
    context := "A conqueror speaks."
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .unacceptable)]
    paperFeatures := [("agreement", "nonagreeing")] }

def ex30a : Datum :=
  { id := "parteeborschev2001_ex30a"
    source := ⟨"partee-borschev-2001", "(30a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Die Kinder sind meine."
    glossedTokens := [("Die", "The"), ("Kinder", "children"), ("sind", "are"), ("meine", "mine-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("agreement", "agreeing")] }

def ex30b : Datum :=
  { id := "parteeborschev2001_ex30b"
    source := ⟨"partee-borschev-2001", "(30b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1295"
    primaryText := "Die Kinder sind mein."
    glossedTokens := [("Die", "The"), ("Kinder", "children"), ("sind", "are"), ("mein", "mine")]
    context := "A custody fight."
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .unacceptable)]
    paperFeatures := [("agreement", "nonagreeing")] }

def ex32a : Datum :=
  { id := "parteeborschev2001_ex32a"
    source := ⟨"partee-borschev-2001", "(32a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Éta strana byla kogda-to moej"
    glossedTokens := [("Éta", "That-F.NOM.SG"), ("strana", "country-F.NOM.SG"), ("byla", "was-F.SG"), ("kogda-to", "once"), ("moej", "my-F.INSTR.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("case", "instrumental")] }

def ex32b : Datum :=
  { id := "parteeborschev2001_ex32b"
    source := ⟨"partee-borschev-2001", "(32b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Éta strana byla kogda-to moej stranoj"
    glossedTokens := [("Éta", "That-F.NOM.SG"), ("strana", "country-F.NOM.SG"), ("byla", "was-F.SG"), ("kogda-to", "once"), ("moej", "my-F.INSTR.SG"), ("stranoj", "country-F.INSTR.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("case", "instrumental")] }

def ex33a : Datum :=
  { id := "parteeborschev2001_ex33a"
    source := ⟨"partee-borschev-2001", "(33a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Éta strana byla kogda-to moja"
    glossedTokens := [("Éta", "That-F.NOM.SG"), ("strana", "country-F.NOM.SG"), ("byla", "was-F.SG"), ("kogda-to", "once"), ("moja", "my-F.NOM.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .unacceptable)]
    paperFeatures := [("case", "nominative")] }

def ex33b : Datum :=
  { id := "parteeborschev2001_ex33b"
    source := ⟨"partee-borschev-2001", "(33b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Éta strana byla kogda-to moja strana"
    glossedTokens := [("Éta", "That-F.NOM.SG"), ("strana", "country-F.NOM.SG"), ("byla", "was-F.SG"), ("kogda-to", "once"), ("moja", "my-F.NOM.SG"), ("strana", "country-F.NOM.SG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("case", "nominative")] }

def ex34a : Datum :=
  { id := "parteeborschev2001_ex34a"
    source := ⟨"partee-borschev-2001", "(34a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Ten kraj był kiedyś moim."
    glossedTokens := [("Ten", "That-M.NOM.SG"), ("kraj", "country-M.NOM.SG"), ("był", "was-M.SG"), ("kiedyś", "once"), ("moim", "my-M.INSTR.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("case", "instrumental")] }

def ex34b : Datum :=
  { id := "parteeborschev2001_ex34b"
    source := ⟨"partee-borschev-2001", "(34b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Ten kraj był kiedyś moim krajem."
    glossedTokens := [("Ten", "That-M.NOM.SG"), ("kraj", "country-M.NOM.SG"), ("był", "was-M.SG"), ("kiedyś", "once"), ("moim", "my-M.INSTR.SG"), ("krajem", "country-M.INSTR.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("case", "instrumental")] }

def ex35a : Datum :=
  { id := "parteeborschev2001_ex35a"
    source := ⟨"partee-borschev-2001", "(35a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Ten kraj był kiedyś mój."
    glossedTokens := [("Ten", "That-M.NOM.SG"), ("kraj", "country-M.NOM.SG"), ("był", "was-M.SG"), ("kiedyś", "once"), ("mój", "my-M.NOM.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .unacceptable)]
    paperFeatures := [("case", "nominative")] }

def ex35b : Datum :=
  { id := "parteeborschev2001_ex35b"
    source := ⟨"partee-borschev-2001", "(35b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Ten kraj był kiedyś mój kraj."
    glossedTokens := [("Ten", "That-M.NOM.SG"), ("kraj", "country-M.NOM.SG"), ("był", "was-M.SG"), ("kiedyś", "once"), ("mój", "my-M.NOM.SG"), ("kraj", "country-M.SG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("case", "nominative")] }

def ex35c : Datum :=
  { id := "parteeborschev2001_ex35c"
    source := ⟨"partee-borschev-2001", "(35c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Ten kraj to był kiedyś mój kraj."
    glossedTokens := [("Ten", "That-M.NOM.SG"), ("kraj", "country-M.NOM.SG"), ("to", "PRT"), ("był", "was-M.SG"), ("kiedyś", "once"), ("mój", "my-M.NOM.SG"), ("kraj", "country-M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable), ("argument", .acceptable)]
    paperFeatures := [("case", "nominative")] }

def exfn13nom : Datum :=
  { id := "parteeborschev2001_exfn13nom"
    source := ⟨"partee-borschev-2001", "fn. 13"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Ten portret był kiedyś mój."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable)]
    paperFeatures := [("case", "nominative")] }

def exfn13instr : Datum :=
  { id := "parteeborschev2001_exfn13instr"
    source := ⟨"partee-borschev-2001", "fn. 13"⟩
    reportedIn := none
    method := some .elicitation
    language := "poli1260"
    primaryText := "Ten portret był kiedyś moim."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("possession", .unacceptable), ("argument", .acceptable)]
    paperFeatures := [("case", "instrumental")] }

def all : List Datum := [ex1c, ex2c, ex3c, ex17a, ex17b, ex17c, ex17d, ex17e, ex17f, ex23a, ex23b, ex24a, ex24b, ex25a, ex25b, ex26, ex27, ex28a, ex28b, ex29a, ex29b, ex30a, ex30b, ex32a, ex32b, ex33a, ex33b, ex34a, ex34b, ex35a, ex35b, ex35c, exfn13nom, exfn13instr]

/-- The head noun of the subject of a copular clause. -/
inductive Noun where
  /-- team: *team* -/
  | team
  /-- brother: *brother* -/
  | brother
  /-- father: *father* -/
  | father
  /-- favorite movie: *favorite movie* -/
  | favoriteMovie
  /-- teacher: *teacher* -/
  | teacher
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `noun`. -/
def noun (e : Datum) : Option Noun :=
  e.parse? "noun" [("team", .team), ("brother", .brother), ("father", .father),
    ("favorite movie", .favoriteMovie), ("teacher", .teacher)]

/-- The determiner of the subject of a copular clause. -/
inductive Subject where
  /-- demonstrative: *that* -/
  | demonstrative
  /-- possessive: *his*, *Dad's* -/
  | possessive
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `subject`. -/
def subject (e : Datum) : Option Subject :=
  e.parse? "subject" [("demonstrative", .demonstrative), ("possessive", .possessive)]

/-- Whether a German predicate agrees with its subject. -/
inductive Agreement where
  /-- agreeing: agrees, as *meine* -/
  | agreeing
  /-- nonagreeing: does not agree, as *alt* and *mein* -/
  | nonagreeing
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `agreement`. -/
def agreement (e : Datum) : Option Agreement :=
  e.parse? "agreement" [("agreeing", .agreeing), ("nonagreeing", .nonagreeing)]

/-- The case of a Russian or Polish predicate. -/
inductive PredicateCase where
  /-- instrumental: instrumental -/
  | instrumental
  /-- nominative: nominative -/
  | nominative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `case`. -/
def predicateCase (e : Datum) : Option PredicateCase :=
  e.parse? "case" [("instrumental", .instrumental), ("nominative", .nominative)]

end ParteeBorschev2001.Examples
