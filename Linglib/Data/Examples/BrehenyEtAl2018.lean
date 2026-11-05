module

public import Linglib.Data.Examples.Schema

/-!
# `BrehenyEtAl2018` — typed example data

Auto-generated from `Linglib/Data/Examples/BrehenyEtAl2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BrehenyEtAl2018.Examples`.
-/

@[expose] public section

namespace BrehenyEtAl2018.Examples

def ex_1 : Datum :=
  { id := "brehenyetal2018_1"
    source := ⟨"breheny-et-al-2018", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did some of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John didn't do all of the homework", .acceptable), ("inference: John did all of the homework", .unacceptable)]
    paperFeatures := [("case", "direct"), ("prejacent", "some"), ("alternative", "all"), ("symmetric alternative", "some but not all")] }

def ex_11 : Datum :=
  { id := "brehenyetal2018_11"
    source := ⟨"breheny-et-al-2018", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He smoked pot."
    glossedTokens := []
    context := "Mary got drunk. What did John do?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John didn't get drunk", .acceptable)]
    paperFeatures := [("case", "particularised"), ("prejacent", "smoked pot"), ("alternative", "got drunk")] }

def ex_12 : Datum :=
  { id := "brehenyetal2018_12"
    source := ⟨"breheny-et-al-2018", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't do all of the homework."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John did some of the homework", .acceptable)]
    paperFeatures := [("case", "indirect"), ("prejacent", "not all"), ("alternative", "not any"), ("symmetric alternative", "some")] }

def ex_17 : Datum :=
  { id := "brehenyetal2018_17"
    source := ⟨"breheny-et-al-2018", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John (my favourite student) didn't do all of the homework."
    glossedTokens := []
    context := "What happened at school today?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John did some of the homework", .acceptable)]
    paperFeatures := [("case", "indirect"), ("prejacent", "not all"), ("focus", "broad")] }

def ex_18 : Datum :=
  { id := "brehenyetal2018_18"
    source := ⟨"trinh-haida-2015", "(5)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(18)"⟩
    language := "stan1293"
    primaryText := "John went for a run."
    glossedTokens := []
    context := "Bill went for a run and didn't smoke. What did John do?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John smoked", .acceptable)]
    paperFeatures := [("case", "particularised"), ("prejacent", "run"), ("alternative", "run and not smoke"), ("symmetric alternative", "run and smoke")] }

def ex_28 : Datum :=
  { id := "brehenyetal2018_28"
    source := ⟨"breheny-et-al-2018", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went for a run."
    glossedTokens := []
    context := "Bill went for a run. He didn't smoke. What did John do?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John smoked", .acceptable)]
    paperFeatures := [("case", "particularised"), ("prejacent", "run"), ("alternative", "not smoke"), ("symmetric alternative", "smoke")] }

def ex_32 : Datum :=
  { id := "brehenyetal2018_32"
    source := ⟨"breheny-et-al-2018", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that the glass is full."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not empty", .acceptable), ("inference: the glass is empty", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not full"), ("alternative", "not empty"), ("symmetric alternative", "empty")] }

def ex_33 : Datum :=
  { id := "brehenyetal2018_33"
    source := ⟨"breheny-et-al-2018", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that the glass is empty."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not full", .acceptable), ("inference: the glass is full", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not empty"), ("alternative", "not full"), ("symmetric alternative", "full")] }

def ex_34 : Datum :=
  { id := "brehenyetal2018_34"
    source := ⟨"breheny-et-al-2018", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that a tie is required."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: a tie is allowed", .acceptable), ("inference: a tie is mandatory", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not required"), ("alternative", "not allowed")] }

def ex_35 : Datum :=
  { id := "brehenyetal2018_35"
    source := ⟨"breheny-et-al-2018", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that Mary's promotion is certain."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: Mary's promotion is possible", .acceptable), ("inference: Mary's promotion is impossible", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not certain"), ("alternative", "not possible")] }

def ex_38a : Datum :=
  { id := "brehenyetal2018_38a"
    source := ⟨"breheny-et-al-2018", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This neighbourhood is not safe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: this neighbourhood is not dangerous", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not safe"), ("scale", "upper closed")] }

def ex_38b : Datum :=
  { id := "brehenyetal2018_38b"
    source := ⟨"breheny-et-al-2018", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John is not small", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not tall"), ("scale", "open")] }

def ex_38c : Datum :=
  { id := "brehenyetal2018_38c"
    source := ⟨"breheny-et-al-2018", "(38c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The glass is not transparent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not opaque", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not transparent"), ("scale", "closed")] }

def ex_41 : Datum :=
  { id := "brehenyetal2018_41"
    source := ⟨"breheny-et-al-2018", "(41)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa ki-te yoi."
    glossedTokens := [("John-wa", "John-TOP"), ("ki-te", "come-GERUND"), ("yoi", "good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John is not required to come", .acceptable)]
    paperFeatures := [("case", "too few lexical alternatives"), ("prejacent", "allowed"), ("alternative", "required")] }

def ex_42a : Datum :=
  { id := "brehenyetal2018_42a"
    source := ⟨"breheny-et-al-2018", "(42a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa ko-naku-te-wa nar-anai."
    glossedTokens := [("John-wa", "John-TOP"), ("ko-naku-te-wa", "come-NEG-GERUND-TOP"), ("nar-anai", "become-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := [("John-wa ko-naku-te-wa ike-nai.", .acceptable)]
    readings := []
    paperFeatures := [("case", "too few lexical alternatives"), ("prejacent", "required")] }

def ex_42b : Datum :=
  { id := "brehenyetal2018_42b"
    source := ⟨"breheny-et-al-2018", "(42b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa kuru hitsuyoo-ga aru."
    glossedTokens := [("John-wa", "John-TOP"), ("kuru", "come"), ("hitsuyoo-ga", "necessity-NOM"), ("aru", "exist")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("case", "too few lexical alternatives"), ("prejacent", "required")] }

def ex_44 : Datum :=
  { id := "brehenyetal2018_44"
    source := ⟨"swanson-2010", "(3)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(44)"⟩
    language := "stan1293"
    primaryText := "Going to confession is permitted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: going to confession is optional", .acceptable), ("inference: going to confession is required", .unacceptable)]
    paperFeatures := [("case", "too many lexical alternatives"), ("prejacent", "permitted"), ("alternative", "required"), ("symmetric alternative", "optional")] }

def ex_45 : Datum :=
  { id := "brehenyetal2018_45"
    source := ⟨"swanson-2010", "(2)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(45)"⟩
    language := "stan1293"
    primaryText := "The heater sometimes squeaks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the heater intermittently squeaks", .acceptable), ("inference: the heater constantly squeaks", .unacceptable)]
    paperFeatures := [("case", "too many lexical alternatives"), ("prejacent", "sometimes"), ("alternative", "constantly"), ("symmetric alternative", "intermittently")] }

def ex_46 : Datum :=
  { id := "brehenyetal2018_46"
    source := ⟨"breheny-et-al-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw some of the students."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John didn't see all of the students", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "some"), ("alternative", "all"), ("symmetric alternative", "just some")] }

def ex_48 : Datum :=
  { id := "brehenyetal2018_48"
    source := ⟨"breheny-et-al-2018", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't see all of the students."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John saw some of the students", .acceptable), ("inference, when many is relevant: John saw many of the students", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "not all"), ("alternative", "none"), ("symmetric alternative", "some")] }

def ex_50 : Datum :=
  { id := "brehenyetal2018_50"
    source := ⟨"breheny-et-al-2018", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The glass is not full."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not empty", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "not full"), ("alternative", "not empty"), ("symmetric alternative", "empty")] }

def ex_55 : Datum :=
  { id := "brehenyetal2018_55"
    source := ⟨"trinh-haida-2015", "(5)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(55)"⟩
    language := "stan1293"
    primaryText := "John ran."
    glossedTokens := []
    context := "Bill ran and didn't smoke."
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John smoked", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "run"), ("alternative", "run and not smoke"), ("symmetric alternative", "run and smoke")] }

def ex_57 : Datum :=
  { id := "brehenyetal2018_57"
    source := ⟨"breheny-et-al-2018", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The heater often squeaks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("case", "rsa"), ("prejacent", "often"), ("alternative", "always"), ("symmetric alternative", "intermittently")] }

def all : List Datum := [ex_1, ex_11, ex_12, ex_17, ex_18, ex_28, ex_32, ex_33, ex_34, ex_35, ex_38a, ex_38b, ex_38c, ex_41, ex_42a, ex_42b, ex_44, ex_45, ex_46, ex_48, ex_50, ex_55, ex_57]

end BrehenyEtAl2018.Examples
