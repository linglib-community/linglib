module

public import Linglib.Data.Examples.Schema

/-!
# `BhattPancheva2004` — typed example data

Auto-generated from `Linglib/Data/Examples/BhattPancheva2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BhattPancheva2004.Examples`.
-/

@[expose] public section

namespace BhattPancheva2004.Examples

def bp2004_22 : Datum :=
  { id := "bp2004_22"
    source := ⟨"bhatt-pancheva-2004", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl is exactly 1 inch taller than that."
    glossedTokens := []
    context := "John is 4 feet tall."
    judgment := .acceptable
    alternatives := []
    readings := [("every > -er", .acceptable), ("-er > every", .unacceptable)]
    paperFeatures := [("section", "4.1"), ("claim", "the reading (22b), -er over every, is unavailable")] }

def bp2004_23a : Datum :=
  { id := "bp2004_23a"
    source := ⟨"bhatt-pancheva-2004", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary set every post exactly 2 feet deeper than that."
    glossedTokens := []
    context := "The frostline is 3½ feet deep."
    judgment := .acceptable
    alternatives := []
    readings := [("every > -er", .acceptable), ("-er > every", .unacceptable)]
    paperFeatures := [("section", "4.1")] }

def bp2004_23b : Datum :=
  { id := "bp2004_23b"
    source := ⟨"bhatt-pancheva-2004", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was less impressed with every candidate than that."
    glossedTokens := []
    context := "John gave every candidate an A."
    judgment := .marginal
    alternatives := []
    readings := [("every > -er", .acceptable), ("-er > every", .unacceptable)]
    paperFeatures := [("section", "4.1")] }

def bp2004_27a : Datum :=
  { id := "bp2004_27a"
    source := ⟨"bhatt-pancheva-2004", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is required to be exactly 5 pages longer than that."
    glossedTokens := []
    context := "This draft is 10 pages long."
    judgment := .acceptable
    alternatives := []
    readings := [("-er > require", .acceptable), ("require > -er", .acceptable)]
    paperFeatures := [("section", "4.2"), ("verb", "require")] }

def bp2004_27b : Datum :=
  { id := "bp2004_27b"
    source := ⟨"bhatt-pancheva-2004", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is allowed to be exactly 5 pages longer than that."
    glossedTokens := []
    context := "This draft is 10 pages long."
    judgment := .acceptable
    alternatives := []
    readings := [("-er > allow", .acceptable), ("allow > -er", .acceptable)]
    paperFeatures := [("section", "4.2"), ("verb", "allow")] }

def bp2004_27c : Datum :=
  { id := "bp2004_27c"
    source := ⟨"bhatt-pancheva-2004", "(27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is required to be less long than that."
    glossedTokens := []
    context := "This draft is 10 pages long."
    judgment := .acceptable
    alternatives := []
    readings := [("-er > require", .acceptable), ("require > -er", .acceptable)]
    paperFeatures := [("section", "4.2"), ("verb", "require")] }

def bp2004_27d : Datum :=
  { id := "bp2004_27d"
    source := ⟨"bhatt-pancheva-2004", "(27d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is allowed to be less long than that."
    glossedTokens := []
    context := "This draft is 10 pages long."
    judgment := .acceptable
    alternatives := []
    readings := [("-er > allow", .acceptable), ("allow > -er", .acceptable)]
    paperFeatures := [("section", "4.2"), ("verb", "allow")] }

def bp2004_30a : Datum :=
  { id := "bp2004_30a"
    source := ⟨"bhatt-pancheva-2004", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is required to be longer than that."
    glossedTokens := []
    context := "The draft is 10 pages long."
    judgment := .acceptable
    alternatives := []
    readings := [("-er > require", .acceptable), ("require > -er", .acceptable)]
    paperFeatures := [("section", "4.2"), ("verb", "require"), ("claim", "the two scopes are truth-conditionally equivalent")] }

def bp2004_30b : Datum :=
  { id := "bp2004_30b"
    source := ⟨"bhatt-pancheva-2004", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The paper is allowed to be longer than that."
    glossedTokens := []
    context := "The draft is 10 pages long."
    judgment := .acceptable
    alternatives := []
    readings := [("-er > allow", .acceptable), ("allow > -er", .acceptable)]
    paperFeatures := [("section", "4.2"), ("verb", "allow"), ("claim", "the two scopes are truth-conditionally equivalent")] }

def bp2004_34a : Datum :=
  { id := "bp2004_34a"
    source := ⟨"bhatt-pancheva-2004", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will tell him a sillier rumor (about Ann) than Mary told John."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("coreference", "him = John"), ("claim", "string-vacuous high attachment is blocked by minimal attachment")] }

def bp2004_34b : Datum :=
  { id := "bp2004_34b"
    source := ⟨"bhatt-pancheva-2004", "(34b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will tell him a sillier rumor (about Ann) tomorrow than Mary told John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("coreference", "him = John"), ("claim", "the degree clause is merged late outside the pronoun's c-command domain")] }

def bp2004_35 : Datum :=
  { id := "bp2004_35"
    source := ⟨"bhatt-pancheva-2004", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will tell him a silly rumor tomorrow that Mary likes John."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("coreference", "him = John"), ("claim", "the complement of a nominal cannot be merged late")] }

def bp2004_40 : Datum :=
  { id := "bp2004_40"
    source := ⟨"bhatt-pancheva-2004", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I read every book before you did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before > every", .acceptable), ("every > before", .acceptable)]
    paperFeatures := [("section", "5.2")] }

def bp2004_41 : Datum :=
  { id := "bp2004_41"
    source := ⟨"bhatt-pancheva-2004", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I read every book that John had recommended before you did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before > every", .acceptable), ("every > before", .acceptable)]
    paperFeatures := [("section", "5.2"), ("site", "low"), ("mover", "DP")] }

def bp2004_42 : Datum :=
  { id := "bp2004_42"
    source := ⟨"bhatt-pancheva-2004", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I read every book before you did that John had recommended."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before > every", .unacceptable), ("every > before", .acceptable)]
    paperFeatures := [("section", "5.2"), ("site", "high"), ("mover", "DP")] }

def bp2004_43 : Datum :=
  { id := "bp2004_43"
    source := ⟨"bhatt-pancheva-2004", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary climbed higher than 1,000 feet before you did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before > -er", .acceptable), ("-er > before", .unacceptable)]
    paperFeatures := [("section", "5.2"), ("site", "low"), ("mover", "DegP")] }

def bp2004_44 : Datum :=
  { id := "bp2004_44"
    source := ⟨"bhatt-pancheva-2004", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary climbed higher before you did than 1,000 feet."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("site", "high"), ("mover", "DegP"), ("claim", "the position of the degree clause presupposes high scope for -er, which the Heim-Kennedy Constraint excludes")] }

def bp2004_45 : Datum :=
  { id := "bp2004_45"
    source := ⟨"bhatt-pancheva-2004", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John read more books than Mary published in her life before you did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before > -er d-many books", .acceptable), ("-er d-many books > before", .acceptable), ("-er > before > d-many books", .unacceptable)]
    paperFeatures := [("section", "5.2"), ("site", "low"), ("mover", "DP")] }

def bp2004_46 : Datum :=
  { id := "bp2004_46"
    source := ⟨"bhatt-pancheva-2004", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John read more books before you did than Mary published in her life."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("before > -er d-many books", .unacceptable), ("-er d-many books > before", .acceptable), ("-er > before > d-many books", .unacceptable)]
    paperFeatures := [("section", "5.2"), ("site", "high"), ("mover", "DP")] }

def bp2004_48a : Datum :=
  { id := "bp2004_48a"
    source := ⟨"bhatt-pancheva-2004", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "So many people ate faster yesterday [than we had expected] [that we were all done by 9 p.m.]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("claim", "the two degree abstractions need not cross")] }

def bp2004_48b : Datum :=
  { id := "bp2004_48b"
    source := ⟨"bhatt-pancheva-2004", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "So many people ate faster yesterday [that we were all done by 9 p.m.] [than we had expected]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("claim", "result clauses follow comparative clauses")] }

def bp2004_50a : Datum :=
  { id := "bp2004_50a"
    source := ⟨"bhatt-pancheva-2004", "(50a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people ate so fast yesterday [than we had expected] [that we were all done by 9 p.m.]."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("claim", "crossing degree abstractions, excluded by the Heim-Kennedy Constraint"), ("alsoJudged", "ungrammatical")] }

def bp2004_50b : Datum :=
  { id := "bp2004_50b"
    source := ⟨"bhatt-pancheva-2004", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people ate so fast yesterday [that we were all done by 9 p.m.] [than we had expected]."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("claim", "result clauses follow comparative clauses")] }

def bp2004_53a : Datum :=
  { id := "bp2004_53a"
    source := ⟨"bhatt-pancheva-2004", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is required [to publish fewer papers this year [than that number] in a major journal] [to get tenure]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > fewer", .acceptable), ("fewer > required", .unacceptable)]
    paperFeatures := [("section", "5.2"), ("site", "low"), ("mover", "DegP")] }

def bp2004_53b : Datum :=
  { id := "bp2004_53b"
    source := ⟨"bhatt-pancheva-2004", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is required [to publish fewer papers this year in a major journal] [to get tenure] [than that number]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > fewer", .unacceptable), ("fewer > required", .acceptable)]
    paperFeatures := [("section", "5.2"), ("site", "high"), ("mover", "DegP")] }

def bp2004_54a : Datum :=
  { id := "bp2004_54a"
    source := ⟨"bhatt-pancheva-2004", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is required [to publish exactly 5 more papers this year [than that number] in a major journal] [to get tenure]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > exactly 5 more", .acceptable), ("exactly 5 more > required", .unacceptable)]
    paperFeatures := [("section", "5.2"), ("site", "low"), ("mover", "DegP")] }

def bp2004_54b : Datum :=
  { id := "bp2004_54b"
    source := ⟨"bhatt-pancheva-2004", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is required [to publish exactly 5 more papers this year in a major journal] [to get tenure] [than that number]."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("required > exactly 5 more", .unacceptable), ("exactly 5 more > required", .acceptable)]
    paperFeatures := [("section", "5.2"), ("site", "high"), ("mover", "DegP")] }

def bp2004_60 : Datum :=
  { id := "bp2004_60"
    source := ⟨"bhatt-pancheva-2004", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's father tells her to work harder than her boss does."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("tell > -er, elided VP: work d-hard", .acceptable), ("tell > -er, elided VP: tell her to work d-hard", .unacceptable), ("-er > tell, elided VP: work d-hard", .acceptable), ("-er > tell, elided VP: tell her to work d-hard", .acceptable)]
    paperFeatures := [("section", "6.1")] }

def bp2004_61 : Datum :=
  { id := "bp2004_61"
    source := ⟨"bhatt-pancheva-2004", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's father tells her to work harder than her boss tells her to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("tell > -er, elided VP: work d-hard", .acceptable), ("-er > tell, elided VP: work d-hard", .acceptable)]
    paperFeatures := [("section", "6.1")] }

def bp2004_63 : Datum :=
  { id := "bp2004_63"
    source := ⟨"bhatt-pancheva-2004", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her father tells her_i to work harder than Mary_i's boss does."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("tell > -er, elided VP: work d-hard", .unacceptable), ("tell > -er, elided VP: tell her to work d-hard", .unacceptable), ("-er > tell, elided VP: work d-hard", .acceptable), ("-er > tell, elided VP: tell her to work d-hard", .acceptable)]
    paperFeatures := [("section", "6.2"), ("coreference", "her = Mary")] }

def bp2004_64a : Datum :=
  { id := "bp2004_64a"
    source := ⟨"bhatt-pancheva-2004", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her father tells her_i to work harder than Mary's_i boss tells her to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("tell > -er", .unacceptable), ("-er > tell", .acceptable)]
    paperFeatures := [("section", "6.2"), ("coreference", "her = Mary")] }

def bp2004_64b : Datum :=
  { id := "bp2004_64b"
    source := ⟨"bhatt-pancheva-2004", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her father tells Mary_i to work harder than her_i boss tells her to."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("tell > -er", .acceptable), ("-er > tell", .acceptable)]
    paperFeatures := [("section", "6.2"), ("coreference", "her = Mary")] }

def bp2004_85 : Datum :=
  { id := "bp2004_85"
    source := ⟨"bhatt-pancheva-2004", "(85)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is taller than Bill is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("claim", "the set of degrees to which Bill is tall is a proper subset of the set to which John is tall")] }

def bp2004_91a : Datum :=
  { id := "bp2004_91a"
    source := ⟨"bhatt-pancheva-2004", "(91a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which rumor that John_i liked Mary did he_i later deny?"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.4"), ("coreference", "he = John"), ("claim", "the complement of rumor cannot be merged late")] }

def bp2004_91b : Datum :=
  { id := "bp2004_91b"
    source := ⟨"bhatt-pancheva-2004", "(91b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will tell him_i a sillier rumor (about Ann) tomorrow than Mary told John_i."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.4"), ("coreference", "him = John"), ("claim", "the complement of -er can be merged late")] }

def bp2004_93a : Datum :=
  { id := "bp2004_93a"
    source := ⟨"bhatt-pancheva-2004", "(93a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John desires that more people than I do take syntax."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "8")] }

def bp2004_93b : Datum :=
  { id := "bp2004_93b"
    source := ⟨"bhatt-pancheva-2004", "(93b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John desires that more people take syntax than I do."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "8")] }

def all : List Datum := [bp2004_22, bp2004_23a, bp2004_23b, bp2004_27a, bp2004_27b, bp2004_27c, bp2004_27d, bp2004_30a, bp2004_30b, bp2004_34a, bp2004_34b, bp2004_35, bp2004_40, bp2004_41, bp2004_42, bp2004_43, bp2004_44, bp2004_45, bp2004_46, bp2004_48a, bp2004_48b, bp2004_50a, bp2004_50b, bp2004_53a, bp2004_53b, bp2004_54a, bp2004_54b, bp2004_60, bp2004_61, bp2004_63, bp2004_64a, bp2004_64b, bp2004_85, bp2004_91a, bp2004_91b, bp2004_93a, bp2004_93b]

end BhattPancheva2004.Examples
