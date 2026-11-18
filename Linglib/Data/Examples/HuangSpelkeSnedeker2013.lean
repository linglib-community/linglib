module

public import Linglib.Data.Examples.Schema

/-!
# `HuangSpelkeSnedeker2013` — typed example data

Auto-generated from `Linglib/Data/Examples/HuangSpelkeSnedeker2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HuangSpelkeSnedeker2013.Examples`.
-/

@[expose] public section

namespace HuangSpelkeSnedeker2013.Examples

def huang2013_ex1 : Datum :=
  { id := "huang2013_ex1"
    source := ⟨"huang-spelke-snedeker-2013", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A bicycle has two wheels, while a tricycle has three."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("term", "two"), ("reading", "exact")] }

def huang2013_ex2 : Datum :=
  { id := "huang2013_ex2"
    source := ⟨"huang-spelke-snedeker-2013", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bonnie: I need to borrow two chairs. Do you know where I could get them? David: Sure, I've got two chairs in my office."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("term", "two"), ("reading", "lower-bounded")] }

def huang2013_ex3 : Datum :=
  { id := "huang2013_ex3"
    source := ⟨"huang-spelke-snedeker-2013", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Henry: I ate some of the ice cream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1"), ("term", "some"), ("reading", "some but not all"), ("implicature", "calculated")] }

def huang2013_ex4 : Datum :=
  { id := "huang2013_ex4"
    source := ⟨"huang-spelke-snedeker-2013", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Eva: Did anyone try the lutefisk? Karl: Yeah, Leif ate some of it. In fact, he ate all of it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1"), ("term", "some"), ("reading", "lower-bounded"), ("implicature", "cancelled")] }

def huang2013_ex5 : Datum :=
  { id := "huang2013_ex5"
    source := ⟨"huang-spelke-snedeker-2013", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Henry: I ate all of the ice cream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.1"), ("term", "all"), ("role", "stronger alternative to (3)")] }

def huang2013_ex6 : Datum :=
  { id := "huang2013_ex6"
    source := ⟨"huang-spelke-snedeker-2013", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who ate some of their berries felt fine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2"), ("term", "some"), ("environment", "restrictor of a universal"), ("reading", "lower-bounded")] }

def huang2013_ex7 : Datum :=
  { id := "huang2013_ex7"
    source := ⟨"huang-spelke-snedeker-2013", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who ate two of their berries felt fine."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2"), ("term", "two"), ("environment", "restrictor of a universal"), ("reading", "exact")] }

def huang2013_ex8 : Datum :=
  { id := "huang2013_ex8"
    source := ⟨"huang-spelke-snedeker-2013", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody came to Allison's party."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1.2"), ("term", "everybody"), ("phenomenon", "implicit domain restriction")] }

def huang2013_exp1_some : Datum :=
  { id := "huang2013_exp1_some"
    source := ⟨"huang-spelke-snedeker-2013", "Exp. 1, scalar condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give me the box where Cookie Monster has some of the cookies."
    glossedTokens := []
    context := "Two open boxes showing Cookie Monster's and Big Bird's shares of a set of cookies, and a covered box."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1.2"), ("term", "some"), ("task", "covered box"), ("trials", "some(NONE,SOME), some(SOME,ALL), some(NONE,ALL)")] }

def huang2013_exp1_two : Datum :=
  { id := "huang2013_exp1_two"
    source := ⟨"huang-spelke-snedeker-2013", "Exp. 1, number condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give me the box with two fish."
    glossedTokens := []
    context := "Two open boxes containing sets of fish, and a covered box."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1.2"), ("term", "two"), ("task", "covered box"), ("trials", "two(1,2), two(2,3V5), two(1,3V5)")] }

def huang2013_exp2_giveN_some : Datum :=
  { id := "huang2013_exp2_giveN_some"
    source := ⟨"huang-spelke-snedeker-2013", "Exp. 2, pretest"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put some of the fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1.2"), ("term", "some"), ("task", "Give-N")] }

def huang2013_exp2_giveN_all : Datum :=
  { id := "huang2013_exp2_giveN_all"
    source := ⟨"huang-spelke-snedeker-2013", "Exp. 2, pretest"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Put all of the fish."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1.2"), ("term", "all"), ("task", "Give-N")] }

def huang2013_exp3_all : Datum :=
  { id := "huang2013_exp3_all"
    source := ⟨"huang-spelke-snedeker-2013", "Exp. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give me the box where Cookie Monster has all of the cookies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.1.2"), ("term", "all"), ("task", "covered box"), ("trials", "all(NONE,ALL), all(SOME,ALL), all(SOME,NONE)")] }

def huang2013_exp4_two : Datum :=
  { id := "huang2013_exp4_two"
    source := ⟨"huang-spelke-snedeker-2013", "Exp. 4, two(1,3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Give me the box where Cookie Monster has two of the cookies."
    glossedTokens := []
    context := "Cookie Monster has 1 of 4 cookies in one open box and 3 of 4 in the other; the third box is covered."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1.2"), ("term", "two"), ("task", "covered box"), ("trials", "two(1,3)")] }

def huang2013_s62_some : Datum :=
  { id := "huang2013_s62_some"
    source := ⟨"huang-spelke-snedeker-2013", "§6.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Point to the girl that has some of the socks."
    glossedTokens := []
    context := "A girl with 2 of 4 socks and a girl with 3 of 3 soccer balls."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2"), ("term", "some"), ("task", "visual world"), ("ambiguity", "some of the soc-")] }

def huang2013_s62_three : Datum :=
  { id := "huang2013_s62_three"
    source := ⟨"huang-spelke-snedeker-2013", "§6.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Point to the girl that has three of the socks."
    glossedTokens := []
    context := "A girl with 3 socks and a girl with 2 soccer balls."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2"), ("term", "three"), ("task", "visual world"), ("role", "lower-bound control")] }

def huang2013_s62_two : Datum :=
  { id := "huang2013_s62_two"
    source := ⟨"huang-spelke-snedeker-2013", "§6.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Point to the girl that has two of the socks."
    glossedTokens := []
    context := "A girl with 2 socks and a girl with 3 soccer balls."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2"), ("term", "two"), ("task", "visual world"), ("role", "upper-bound probe")] }

def all : List Datum := [huang2013_ex1, huang2013_ex2, huang2013_ex3, huang2013_ex4, huang2013_ex5, huang2013_ex6, huang2013_ex7, huang2013_ex8, huang2013_exp1_some, huang2013_exp1_two, huang2013_exp2_giveN_some, huang2013_exp2_giveN_all, huang2013_exp3_all, huang2013_exp4_two, huang2013_s62_some, huang2013_s62_three, huang2013_s62_two]

end HuangSpelkeSnedeker2013.Examples
