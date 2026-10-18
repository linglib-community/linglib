module

public import Linglib.Data.Examples.Schema

/-!
# `Arnold2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Arnold2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Arnold2026.Examples`.
-/

@[expose] public section

namespace Arnold2026.Examples

def homework : Datum :=
  { id := "arnold2026_homework"
    source := ⟨"arnold-2026", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every student does their homework"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "quantified"), ("representation", "underspecified")] }

def lovato : Datum :=
  { id := "arnold2026_lovato"
    source := ⟨"arnold-2026", "§1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'I've had the revelation that I identify as non-binary,' they said"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "personal"), ("pronouns", "they/them")] }

def bed : Datum :=
  { id := "arnold2026_bed"
    source := ⟨"arnold-2026", "§2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone should make their bed"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "quantified"), ("representation", "underspecified")] }

def teacher : Datum :=
  { id := "arnold2026_teacher"
    source := ⟨"arnold-2026", "§2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A teacher should know their students"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "indefinite"), ("referentGender", "unknown"), ("representation", "underspecified")] }

def clerk : Datum :=
  { id := "arnold2026_clerk"
    source := ⟨"arnold-2026", "§2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The clerk had their back to me"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "definite"), ("referentGender", "unknown"), ("representation", "underspecified")] }

def neighbor : Datum :=
  { id := "arnold2026_neighbor"
    source := ⟨"arnold-2026", "§2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My neighbor said they would stop by"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "definite"), ("referentGender", "known"), ("representation", "underspecified")] }

def shakespeare : Datum :=
  { id := "arnold2026_shakespeare"
    source := ⟨"arnold-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There's not a man I meet but doth salute me as if I were their well-acquainted friend"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "quantified"), ("referentGender", "known"), ("representation", "underspecified")] }

def landlord : Datum :=
  { id := "arnold2026_landlord"
    source := ⟨"arnold-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a single mother and their three children"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "indefinite"), ("referentGender", "known"), ("representation", "underspecified")] }

def son : Datum :=
  { id := "arnold2026_son"
    source := ⟨"arnold-2026", "Table 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Me: My son will swing by to pick up my order. Store clerk: just have them call us when they are here so we can bring it out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "definite"), ("referentGender", "known"), ("representation", "underspecified")] }

def alex : Datum :=
  { id := "arnold2026_alex"
    source := ⟨"arnold-2026", "§4.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex made breakfast with Will. They broke some plates."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Alex broke some plates", .acceptable), ("Alex and Will broke some plates", .acceptable)]
    paperFeatures := [("kind", "personal"), ("pronouns", "they/them"), ("ambiguity", "singular or plural")] }

def dillon : Datum :=
  { id := "arnold2026_dillon"
    source := ⟨"arnold-2026", "§6.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Asia Kate Dillon (born November 15, 1984) is an American actor. They are known for their roles as…"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "personal"), ("pronouns", "they/them"), ("representation", "elaborated")] }

def mother : Datum :=
  { id := "arnold2026_mother"
    source := ⟨"arnold-2026", "§6.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "my mother … they"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "underspecified"), ("antecedent", "definite"), ("referentGender", "known"), ("representation", "elaborated"), ("counterexample", "true")] }

def butler : Datum :=
  { id := "arnold2026_butler"
    source := ⟨"arnold-2026", "fn. 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "… Butler, who uses they/them pronouns, repeatedly affirms that…"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "personal"), ("pronouns", "they/them"), ("pronounsIntroduced", "true")] }

def all : List Datum := [homework, lovato, bed, teacher, clerk, neighbor, shakespeare, landlord, son, alex, dillon, mother, butler]

end Arnold2026.Examples
