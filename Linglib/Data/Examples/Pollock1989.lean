module

public import Linglib.Data.Examples.Schema

/-!
# `Pollock1989` — typed example data

Auto-generated from `Linglib/Data/Examples/Pollock1989.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pollock1989.Examples`.
-/

@[expose] public section

namespace Pollock1989.Examples

def ex2a : Datum :=
  { id := "pollock1989_ex2a"
    source := ⟨"pollock-1989", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John likes not Mary."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex2b : Datum :=
  { id := "pollock1989_ex2b"
    source := ⟨"pollock-1989", "(2b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jean (n')aime pas Marie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex3a : Datum :=
  { id := "pollock1989_ex3a"
    source := ⟨"pollock-1989", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Likes he Mary?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "inversion"), ("verbPrecedes", "true")] }

def ex3b : Datum :=
  { id := "pollock1989_ex3b"
    source := ⟨"pollock-1989", "(3b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Aime-t-il Marie?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "inversion"), ("verbPrecedes", "true")] }

def ex4a : Datum :=
  { id := "pollock1989_ex4a"
    source := ⟨"pollock-1989", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John kisses often Mary."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def ex4b : Datum :=
  { id := "pollock1989_ex4b"
    source := ⟨"pollock-1989", "(4b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jean embrasse souvent Marie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def ex4c : Datum :=
  { id := "pollock1989_ex4c"
    source := ⟨"pollock-1989", "(4c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John often kisses Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "false")] }

def ex4d : Datum :=
  { id := "pollock1989_ex4d"
    source := ⟨"pollock-1989", "(4d)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jean souvent embrasse Marie."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "false")] }

def ex5a : Datum :=
  { id := "pollock1989_ex5a"
    source := ⟨"pollock-1989", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My friends love all Mary."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "floatingQ"), ("verbPrecedes", "true")] }

def ex5b : Datum :=
  { id := "pollock1989_ex5b"
    source := ⟨"pollock-1989", "(5b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mes amis aiment tous Marie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "floatingQ"), ("verbPrecedes", "true")] }

def ex5c : Datum :=
  { id := "pollock1989_ex5c"
    source := ⟨"pollock-1989", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My friends all love Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "floatingQ"), ("verbPrecedes", "false")] }

def ex5d : Datum :=
  { id := "pollock1989_ex5d"
    source := ⟨"pollock-1989", "(5d)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mes amis tous aiment Marie."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "lexical"), ("diagnostic", "floatingQ"), ("verbPrecedes", "false")] }

def ex7a : Datum :=
  { id := "pollock1989_ex7a"
    source := ⟨"pollock-1989", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex7b : Datum :=
  { id := "pollock1989_ex7b"
    source := ⟨"pollock-1989", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John does not be happy."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "false")] }

def ex11a_neg : Datum :=
  { id := "pollock1989_ex11a_neg"
    source := ⟨"pollock-1989", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He hasn't understood."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex11a_inv : Datum :=
  { id := "pollock1989_ex11a_inv"
    source := ⟨"pollock-1989", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has he understood?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "inversion"), ("verbPrecedes", "true")] }

def ex11b_neg : Datum :=
  { id := "pollock1989_ex11b_neg"
    source := ⟨"pollock-1989", "(11b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il (n')a pas compris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex11b_inv : Datum :=
  { id := "pollock1989_ex11b_inv"
    source := ⟨"pollock-1989", "(11b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "A-t-il compris?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "inversion"), ("verbPrecedes", "true")] }

def ex11c_adv : Datum :=
  { id := "pollock1989_ex11c_adv"
    source := ⟨"pollock-1989", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is seldom satisfied."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def ex11c_fq : Datum :=
  { id := "pollock1989_ex11c_fq"
    source := ⟨"pollock-1989", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They are all satisfied."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "floatingQ"), ("verbPrecedes", "true")] }

def ex11d_adv : Datum :=
  { id := "pollock1989_ex11d_adv"
    source := ⟨"pollock-1989", "(11d)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il est rarement satisfait."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def ex11d_fq : Datum :=
  { id := "pollock1989_ex11d_fq"
    source := ⟨"pollock-1989", "(11d)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ils sont tous satisfaits."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "floatingQ"), ("verbPrecedes", "true")] }

def ex12a : Datum :=
  { id := "pollock1989_ex12a"
    source := ⟨"pollock-1989", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't have sung."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "yes"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "false")] }

def ex15a : Datum :=
  { id := "pollock1989_ex15a"
    source := ⟨"pollock-1989", "(15a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ne pas être heureux est une condition pour écrire des romans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "false")] }

def ex15b : Datum :=
  { id := "pollock1989_ex15b"
    source := ⟨"pollock-1989", "(15b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "N'être pas heureux est une condition pour écrire des romans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex16a : Datum :=
  { id := "pollock1989_ex16a"
    source := ⟨"pollock-1989", "(16a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ne pas sembler heureux est une condition pour écrire des romans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "negation"), ("verbPrecedes", "false")] }

def ex16b : Datum :=
  { id := "pollock1989_ex16b"
    source := ⟨"pollock-1989", "(16b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ne sembler pas heureux est une condition pour écrire des romans."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex21a : Datum :=
  { id := "pollock1989_ex21a"
    source := ⟨"pollock-1989", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not to be happy is a prerequisite for writing novels."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "false")] }

def ex21b : Datum :=
  { id := "pollock1989_ex21b"
    source := ⟨"pollock-1989", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To be not happy is a prerequisite for writing novels."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "auxiliary"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex22a : Datum :=
  { id := "pollock1989_ex22a"
    source := ⟨"pollock-1989", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not to seem happy is a prerequisite for writing novels."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "negation"), ("verbPrecedes", "false")] }

def ex22b : Datum :=
  { id := "pollock1989_ex22b"
    source := ⟨"pollock-1989", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To seem not happy is a prerequisite for writing novels."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex24b : Datum :=
  { id := "pollock1989_ex24b"
    source := ⟨"pollock-1989", "(24b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Souvent paraître triste pendant son voyage de noce, c'est rare."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "false")] }

def ex27b : Datum :=
  { id := "pollock1989_ex27b"
    source := ⟨"pollock-1989", "(27b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Paraître souvent triste pendant son voyage de noce, c'est rare."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def ex28a : Datum :=
  { id := "pollock1989_ex28a"
    source := ⟨"pollock-1989", "(28a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "On imagine mal les députés démissionner tous en même temps."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "floatingQ"), ("verbPrecedes", "true")] }

def ex29c : Datum :=
  { id := "pollock1989_ex29c"
    source := ⟨"pollock-1989", "(29c)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Ne paraître pas triste pendant son voyage de noce, c'est normal."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "negation"), ("verbPrecedes", "true")] }

def ex37b : Datum :=
  { id := "pollock1989_ex37b"
    source := ⟨"pollock-1989", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To often look sad during one's honeymoon is rare."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "false")] }

def ex38b : Datum :=
  { id := "pollock1989_ex38b"
    source := ⟨"pollock-1989", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To look often sad during one's honeymoon is rare."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def ex39a : Datum :=
  { id := "pollock1989_ex39a"
    source := ⟨"pollock-1989", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe John to often be sarcastic."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "auxiliary"), ("diagnostic", "adverb"), ("verbPrecedes", "false")] }

def ex39c : Datum :=
  { id := "pollock1989_ex39c"
    source := ⟨"pollock-1989", "(39c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe John to be often sarcastic."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "auxiliary"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def ex39d : Datum :=
  { id := "pollock1989_ex39d"
    source := ⟨"pollock-1989", "(39d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I believe John to sound often sarcastic."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("finite", "no"), ("verb", "lexical"), ("diagnostic", "adverb"), ("verbPrecedes", "true")] }

def all : List Datum := [ex2a, ex2b, ex3a, ex3b, ex4a, ex4b, ex4c, ex4d, ex5a, ex5b, ex5c, ex5d, ex7a, ex7b, ex11a_neg, ex11a_inv, ex11b_neg, ex11b_inv, ex11c_adv, ex11c_fq, ex11d_adv, ex11d_fq, ex12a, ex15a, ex15b, ex16a, ex16b, ex21a, ex21b, ex22a, ex22b, ex24b, ex27b, ex28a, ex29c, ex37b, ex38b, ex39a, ex39c, ex39d]

end Pollock1989.Examples
