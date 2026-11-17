module

public import Linglib.Data.Examples.Schema

/-!
# `BarLev2021` — typed example data

Auto-generated from `Linglib/Data/Examples/BarLev2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarLev2021.Examples`.
-/

@[expose] public section

namespace BarLev2021.Examples

def ex_1a : Datum :=
  { id := "barlev2021_1a"
    source := ⟨"bar-lev-2021", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids laughed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("all the kids laughed", .acceptable), ("some of the kids laughed", .unacceptable)]
    paperFeatures := [("polarity", "positive")] }

def ex_1b : Datum :=
  { id := "barlev2021_1b"
    source := ⟨"bar-lev-2021", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids didn't laugh."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not all the kids laughed", .unacceptable), ("none of the kids laughed", .acceptable)]
    paperFeatures := [("polarity", "negative")] }

def ex_2 : Datum :=
  { id := "barlev2021_2"
    source := ⟨"bar-lev-2021", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy found his presents."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("no boy found all of his presents", .unacceptable), ("no boy found any of his presents", .acceptable)]
    paperFeatures := [("polarity", "negative"), ("scope", "definite plural bound below negation")] }

def ex_3b : Datum :=
  { id := "barlev2021_3b"
    source := ⟨"bar-lev-2021", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids laughed."
    glossedTokens := []
    context := "There was a clown at my kid's birthday party. Someone asks me if they gave a funny performance."
    judgment := .acceptable
    contrasts := []
    readings := [("true if most of the kids laughed", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("reading", "non-maximal")] }

def ex_4b : Datum :=
  { id := "barlev2021_4b"
    source := ⟨"bar-lev-2021", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids laughed."
    glossedTokens := []
    context := "Someone asks me who among the five adults and the ten kids at the birthday party laughed."
    judgment := .acceptable
    contrasts := []
    readings := [("true if most of the kids laughed", .unacceptable)]
    paperFeatures := [("polarity", "positive"), ("reading", "maximal")] }

def ex_9b : Datum :=
  { id := "barlev2021_9b"
    source := ⟨"bar-lev-2021", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids didn't laugh."
    glossedTokens := []
    context := "There was a clown at my kid's birthday party. Someone asks me if they gave a funny performance."
    judgment := .acceptable
    contrasts := []
    readings := [("true if most of the kids didn't laugh", .questionable)]
    paperFeatures := [("polarity", "negative")] }

def ex_10a : Datum :=
  { id := "barlev2021_10a"
    source := ⟨"bar-lev-2021", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the kids took their vitamins."
    glossedTokens := []
    context := "The kids are required to take at least 2 of the 4 vitamins I gave each of them."
    judgment := .acceptable
    contrasts := []
    readings := [("every kid took at least 2 vitamins", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("scope", "definite plural bound")] }

def ex_10b : Datum :=
  { id := "barlev2021_10b"
    source := ⟨"bar-lev-2021", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the kids took their vitamins."
    glossedTokens := []
    context := "The kids are required to take at least 2 of the 4 vitamins I gave each of them."
    judgment := .acceptable
    contrasts := []
    readings := [("no kid took any vitamin", .acceptable), ("no kid took at least 2 vitamins", .questionable)]
    paperFeatures := [("polarity", "negative"), ("scope", "definite plural bound")] }

def ex_11a : Datum :=
  { id := "barlev2021_11a"
    source := ⟨"bar-lev-2021", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All of the kids came with their parents to the meeting."
    glossedTokens := []
    context := "Context B: the kids were told to come with at least one parent to the meeting."
    judgment := .acceptable
    contrasts := []
    readings := [("every kid came with at least one parent", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("scope", "definite plural bound")] }

def ex_11b : Datum :=
  { id := "barlev2021_11b"
    source := ⟨"bar-lev-2021", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the kids came with their parents to the meeting."
    glossedTokens := []
    context := "Context B: the kids were told to come with at least one parent to the meeting."
    judgment := .acceptable
    contrasts := []
    readings := [("no kid came with any parent", .acceptable)]
    paperFeatures := [("polarity", "negative"), ("scope", "definite plural bound")] }

def ex_14a : Datum :=
  { id := "barlev2021_14a"
    source := ⟨"bar-lev-2021", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In every performance by this clown the kids who sit on the first 3 rows laugh. (Well, of course, not all of those kids do.)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("scope", "definite plural bound")] }

def ex_14b : Datum :=
  { id := "barlev2021_14b"
    source := ⟨"bar-lev-2021", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In no performance by this clown the kids who sit on the first 3 rows laugh. (# Well, of course, some of those kids do.)"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("scope", "definite plural bound")] }

def ex_17 : Datum :=
  { id := "barlev2021_17"
    source := ⟨"bar-lev-2021", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is allowed to read \"War and Peace\" or \"Anna Karenina\"."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("allowed to read W&P and allowed to read AK", .acceptable), ("allowed to read W&P or allowed to read AK", .unacceptable)]
    paperFeatures := [("phenomenon", "free choice")] }

def ex_18 : Datum :=
  { id := "barlev2021_18"
    source := ⟨"bar-lev-2021", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is not allowed to read \"War and Peace\" or \"Anna Karenina\"."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("not both allowed", .unacceptable), ("allowed to read neither", .acceptable)]
    paperFeatures := [("phenomenon", "free choice"), ("polarity", "negative")] }

def ex_21 : Datum :=
  { id := "barlev2021_21"
    source := ⟨"bar-lev-2021", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly one student read the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("one student read all of the books and no more than one read any", .acceptable)]
    paperFeatures := [("environment", "non-monotonic")] }

def ex_23 : Datum :=
  { id := "barlev2021_23"
    source := ⟨"bar-lev-2021", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary read the books, but John didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary read all and John read none", .acceptable)]
    paperFeatures := [("environment", "ellipsis")] }

def ex_41a : Datum :=
  { id := "barlev2021_41a"
    source := ⟨"bar-lev-2021", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kelly or Jane laughed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Kelly or Jane laughed but not both", .acceptable)]
    paperFeatures := [("alternatives", "with conjunction")] }

def ex_41b : Datum :=
  { id := "barlev2021_41b"
    source := ⟨"bar-lev-2021", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids laughed."
    glossedTokens := []
    context := "The kids are Kelly and Jane."
    judgment := .acceptable
    contrasts := []
    readings := [("Kelly and Jane laughed", .acceptable)]
    paperFeatures := [("alternatives", "subdomain only")] }

def ex_71b : Datum :=
  { id := "barlev2021_71b"
    source := ⟨"bar-lev-2021", "(71b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "None of the guests ate their poisoned peas."
    glossedTokens := []
    context := "Each of the guests in the party was served a plate containing 10 poisoned peas. Eating 3 of those peas is entirely harmless, but eating 4 or more leads to certain death."
    judgment := .acceptable
    contrasts := []
    readings := [("no guest ate more than 3 poisoned peas", .acceptable)]
    paperFeatures := [("polarity", "negative"), ("scope", "definite plural bound")] }

def ex_72b : Datum :=
  { id := "barlev2021_72b"
    source := ⟨"bar-lev-2021", "(72b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No contestant ate their pies."
    glossedTokens := []
    context := "Each contestant in a pie eating contest is provided with 25 pies. In order to move on to the next round a contestant must eat at least 20 pies (they get more points for eating more)."
    judgment := .acceptable
    contrasts := []
    readings := [("no contestant ate at least 20 pies", .acceptable)]
    paperFeatures := [("polarity", "negative"), ("scope", "definite plural bound")] }

def ex_73 : Datum :=
  { id := "barlev2021_73"
    source := ⟨"bar-lev-2021", "(73)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary read the books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if Mary read all of the books", .acceptable), ("false if Mary read none", .acceptable), ("neither true nor false if some but not all", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("gappiness", "yes")] }

def ex_74a : Datum :=
  { id := "barlev2021_74a"
    source := ⟨"bar-lev-2021", "(74a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary read the 4 books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary read all of the 4 books", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("gappiness", "no"), ("non_maximality", "no")] }

def ex_74b : Datum :=
  { id := "barlev2021_74b"
    source := ⟨"bar-lev-2021", "(74b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't read the 4 books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mary didn't read any of the 4 books", .acceptable)]
    paperFeatures := [("polarity", "negative"), ("gappiness", "no")] }

def ex_76 : Datum :=
  { id := "barlev2021_76"
    source := ⟨"bar-lev-2021", "(76)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary read the 4 books."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if Mary read all of the 4 books", .acceptable), ("false otherwise", .acceptable)]
    paperFeatures := [("gappiness", "no")] }

def ex_77 : Datum :=
  { id := "barlev2021_77"
    source := ⟨"bar-lev-2021", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue read \"Anna Karenina\" and \"War and Peace\"."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if both", .acceptable), ("false otherwise", .acceptable)]
    paperFeatures := [("gappiness", "no")] }

def ex_80 : Datum :=
  { id := "barlev2021_80"
    source := ⟨"bar-lev-2021", "(80)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary read the books."
    glossedTokens := []
    context := "If Mary reads any five of the ten books she is guaranteed to pass the test; if she reads less than five she is guaranteed to fail."
    judgment := .acceptable
    contrasts := []
    readings := [("true if Mary read at least five of the ten books", .acceptable), ("false otherwise", .acceptable)]
    paperFeatures := [("gappiness", "no"), ("reading", "at least five")] }

def ex_81 : Datum :=
  { id := "barlev2021_81"
    source := ⟨"bar-lev-2021", "(81)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary read the books."
    glossedTokens := []
    context := "To pass the test, Mary has to read all of the ten books on the reading list; if she reads less than ten she is guaranteed to fail."
    judgment := .acceptable
    contrasts := []
    readings := [("true if Mary read all of the ten books", .acceptable), ("false otherwise", .acceptable)]
    paperFeatures := [("gappiness", "no"), ("reading", "maximal")] }

def ex_82a : Datum :=
  { id := "barlev2021_82a"
    source := ⟨"bar-lev-2021", "(82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The squares are red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("neither true nor false if some but not all of the squares are red", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("gappiness", "yes")] }

def ex_82b : Datum :=
  { id := "barlev2021_82b"
    source := ⟨"bar-lev-2021", "(82b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The squares aren't red."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("neither true nor false if some but not all of the squares are red", .questionable)]
    paperFeatures := [("polarity", "negative"), ("gappiness", "reduced")] }

def ex_84a : Datum :=
  { id := "barlev2021_84a"
    source := ⟨"bar-lev-2021", "(84a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John read the books, I don't know which."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "cancellation")] }

def ex_84b : Datum :=
  { id := "barlev2021_84b"
    source := ⟨"bar-lev-2021", "(84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are allowed to eat ice cream or cake, I don't know which."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "cancellation")] }

def ex_85a : Datum :=
  { id := "barlev2021_85a"
    source := ⟨"bar-lev-2021", "(85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids laughed. In fact, Kelly and Bill did but Jane didn't."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "cancellation")] }

def ex_85b : Datum :=
  { id := "barlev2021_85b"
    source := ⟨"bar-lev-2021", "(85b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You are allowed to have ice cream or cake. In fact, you are allowed to have ice cream but not cake."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("phenomenon", "cancellation")] }

def ex_88a : Datum :=
  { id := "barlev2021_88a"
    source := ⟨"bar-lev-2021", "(88a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids lifted the piano."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if half of the kids lifted it together and no one else did", .unacceptable)]
    paperFeatures := [("predicate", "non-distributive")] }

def ex_88b : Datum :=
  { id := "barlev2021_88b"
    source := ⟨"bar-lev-2021", "(88b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The kids didn't lift the piano."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("true if half of the kids lifted it together and no one else did", .unacceptable)]
    paperFeatures := [("predicate", "non-distributive"), ("polarity", "negative")] }

def ex_94a : Datum :=
  { id := "barlev2021_94a"
    source := ⟨"bar-lev-2021", "(94a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girls danced with the boys."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("every girl danced with some boy and every boy with some girl", .acceptable)]
    paperFeatures := [("predicate", "two-place")] }

def ex_94b : Datum :=
  { id := "barlev2021_94b"
    source := ⟨"bar-lev-2021", "(94b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girls didn't dance with the boys."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("no girl danced with any boy", .acceptable)]
    paperFeatures := [("predicate", "two-place"), ("polarity", "negative")] }

def all : List Datum := [ex_1a, ex_1b, ex_2, ex_3b, ex_4b, ex_9b, ex_10a, ex_10b, ex_11a, ex_11b, ex_14a, ex_14b, ex_17, ex_18, ex_21, ex_23, ex_41a, ex_41b, ex_71b, ex_72b, ex_73, ex_74a, ex_74b, ex_76, ex_77, ex_80, ex_81, ex_82a, ex_82b, ex_84a, ex_84b, ex_85a, ex_85b, ex_88a, ex_88b, ex_94a, ex_94b]

end BarLev2021.Examples
