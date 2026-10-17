module

public import Linglib.Data.Examples.Schema

/-!
# `Aikhenvald2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Aikhenvald2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aikhenvald2004.Examples`.
-/

@[expose] public section

namespace Aikhenvald2004.Examples

def ex1_1 : Datum :=
  { id := "aikhenvald2004_ex1_1"
    source := ⟨"aikhenvald-2004", "(1.1)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-ka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-ka", "3sgnf-play-REC.P.VIS")]
    context := "The speaker saw José play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "visual"), ("source", "visual")] }

def ex1_2 : Datum :=
  { id := "aikhenvald2004_ex1_2"
    source := ⟨"aikhenvald-2004", "(1.2)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-mahka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-mahka", "3sgnf-play-REC.P.NONVIS")]
    context := "The speaker heard the noise of a game but could not see it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "nonvisual"), ("source", "nonvisual")] }

def ex1_3 : Datum :=
  { id := "aikhenvald2004_ex1_3"
    source := ⟨"aikhenvald-2004", "(1.3)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-nihka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-nihka", "3sgnf-play-REC.P.INFR")]
    context := "The football and José's boots are gone and crowds return from the ground."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "inferred"), ("source", "inference")] }

def ex1_4 : Datum :=
  { id := "aikhenvald2004_ex1_4"
    source := ⟨"aikhenvald-2004", "(1.4)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-sika"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-sika", "3sgnf-play-REC.P.ASSUM")]
    context := "José is out on a Sunday afternoon, when he usually plays."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "assumed"), ("source", "assumption")] }

def ex1_5 : Datum :=
  { id := "aikhenvald2004_ex1_5"
    source := ⟨"aikhenvald-2004", "(1.5)"⟩
    reportedIn := none
    language := "tari1256"
    primaryText := "Juse iɾida di-manika-pidaka"
    glossedTokens := [("Juse", "José"), ("iɾida", "football"), ("di-manika-pidaka", "3sgnf-play-REC.P.REP")]
    context := "Someone told the speaker."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "D1"), ("term", "reported"), ("source", "report")] }

def ex2_16 : Datum :=
  { id := "aikhenvald2004_ex2_16"
    source := ⟨"aikhenvald-2004", "(2.16)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "bakan hasta-ymış"
    glossedTokens := [("bakan", "minister"), ("hasta-ymış", "sick-NONFIRSTH.COP")]
    context := "Said by somebody told about the sickness."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "report")] }

def ex2_17 : Datum :=
  { id := "aikhenvald2004_ex2_17"
    source := ⟨"aikhenvald-2004", "(2.17)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "uyu-muş-um"
    glossedTokens := [("uyu-muş-um", "sleep-NONFIRSTH.PAST-1sg")]
    context := "Said by somebody who has just woken up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "inference")] }

def ex2_18 : Datum :=
  { id := "aikhenvald2004_ex2_18"
    source := ⟨"aikhenvald-2004", "(2.18)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "iyi çal-Iyor-muş"
    glossedTokens := [("iyi", "good"), ("çal-Iyor-muş", "play-INTRATERM.ASP-NONFIRSTH.COP")]
    context := "Said by somebody listening to her play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "nonvisual")] }

def ex2_40 : Datum :=
  { id := "aikhenvald2004_ex2_40"
    source := ⟨"aikhenvald-2004", "(2.40)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Chay-chruu-mi achka wamla-pis walashr-pis alma-ku-lkaa-ña"
    glossedTokens := [("Chay-chruu-mi", "this-LOC-DIR.EV"), ("achka", "many"), ("wamla-pis", "girl-TOO"), ("walashr-pis", "boy-TOO"), ("alma-ku-lkaa-ña", "bathe-REFL-IMPF.PL-NARR.PAST")]
    context := "The speaker saw them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "direct"), ("source", "visual")] }

def ex2_41 : Datum :=
  { id := "aikhenvald2004_ex2_41"
    source := ⟨"aikhenvald-2004", "(2.41)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Daañu pawa-shra-si ka-ya-n-chr-ari"
    glossedTokens := [("Daañu", "field"), ("pawa-shra-si", "finish-PART-EVEN"), ("ka-ya-n-chr-ari", "be-IMPF-3-INFR-EMPH")]
    context := "The speaker infers it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "inferred"), ("source", "inference")] }

def ex2_42 : Datum :=
  { id := "aikhenvald2004_ex2_42"
    source := ⟨"aikhenvald-2004", "(2.42)"⟩
    reportedIn := none
    language := "jauj1238"
    primaryText := "Ancha-p-shi wa'a-chi-nki wamla-a-ta"
    glossedTokens := [("Ancha-p-shi", "too.much-GEN-REP"), ("wa'a-chi-nki", "cry-CAUS-2"), ("wamla-a-ta", "girl-1p-ACC")]
    context := "The speaker was told."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "B1"), ("term", "reported"), ("source", "report")] }

def ex4_7 : Datum :=
  { id := "aikhenvald2004_ex4_7"
    source := ⟨"aikhenvald-2004", "(4.7)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "varsken-s ianvr-is rva-s p'irvel-ad (ø-)u-c'am-eb-i-a šušanik'-i"
    glossedTokens := [("varsken-s", "Varsken-DAT"), ("ianvr-is", "January-GEN"), ("rva-s", "8-DAT"), ("p'irvel-ad", "first-ADV"), ("(ø-)u-c'am-eb-i-a", "(he-)OV-torture-TS-PERF-her"), ("šušanik'-i", "Shushanik'-NOM")]
    context := "A past action the speaker did not witness but assumes from a present result or a report."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "perfect"), ("source", "nonfirsthand")] }

def ex4_55 : Datum :=
  { id := "aikhenvald2004_ex4_55"
    source := ⟨"aikhenvald-2004", "(4.55)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Dumat, zmejat sljazăl v našata niva"
    glossedTokens := [("Dumat", "think.PRES.3PL"), ("zmejat", "dragon"), ("sljazăl", "come.down.REPORTIVE.SG"), ("v", "into"), ("našata", "our"), ("niva", "field")]
    context := "Reported information the speaker distances themself from."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("system", "A2"), ("term", "nonfirsthand"), ("source", "report"), ("extension", "epistemic")] }

def all : List Datum := [ex1_1, ex1_2, ex1_3, ex1_4, ex1_5, ex2_16, ex2_17, ex2_18, ex2_40, ex2_41, ex2_42, ex4_7, ex4_55]

end Aikhenvald2004.Examples
