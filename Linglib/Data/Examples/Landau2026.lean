module

public import Linglib.Data.Examples.Schema

/-!
# `Landau2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Landau2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Landau2026.Examples`.
-/

@[expose] public section

namespace Landau2026.Examples

def hebrewEN : Datum :=
  { id := "landau2026_hebrewEN"
    source := ⟨"landau-2026", "(18a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš la'hakot še-ahavti et ha-šeni."
    glossedTokens := []
    context := "Empty noun (EN), deep anaphor: a bare n head with no internal structure to host the resumptive pronoun bound by the Ā-operator."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("domain", "nP"), ("depth", "deep"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")] }

def hebrewENP : Datum :=
  { id := "landau2026_hebrewENP"
    source := ⟨"landau-2026", "(19a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš la'hakot še-ahavti et ha-albom ha-rišon šela'hen, ve-yeš la'hakot še-ahavti et ha-šeni."
    glossedTokens := []
    context := "Elided noun phrase (ENP), surface anaphor: full nP structure deleted under identity, licensed by [E] on Num."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("domain", "nP"), ("depth", "surface"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, maximizing relative")] }

def hebrewNCA_DP : Datum :=
  { id := "landau2026_hebrewNCA_DP"
    source := ⟨"landau-2026", "(31a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš li xaver exad še-maxarti."
    glossedTokens := []
    context := "Null complement anaphora (NCA) / pro, deep anaphor in the DP domain."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("domain", "DP"), ("depth", "deep"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")] }

def hebrewAE : Datum :=
  { id := "landau2026_hebrewAE"
    source := ⟨"landau-2026", "(32a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš li xaver exad še-kaniti et ha-oto šelo, ve-yeš li xaver axer še-maxarti."
    glossedTokens := []
    context := "Argument ellipsis (AE) / DP-ellipsis, surface anaphor: full DP structure deleted under identity."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("domain", "DP"), ("depth", "surface"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")] }

def hebrewNCA_PP : Datum :=
  { id := "landau2026_hebrewNCA_PP"
    source := ⟨"landau-2026", "(37a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš irgunim še-ani lo xotemet."
    glossedTokens := []
    context := "Null PP via NCA, deep anaphor: PP argument omitted, content recovered pragmatically."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("domain", "PP"), ("depth", "deep"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")] }

def hebrewPPE : Datum :=
  { id := "landau2026_hebrewPPE"
    source := ⟨"landau-2026", "(38a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yeš irgunim še-ani xotemet al ha-acumot šelahem, ve-yeš irgunim še-ani lo xotemet."
    glossedTokens := []
    context := "PP-ellipsis (PPE), surface anaphor: full PP structure deleted under identity. Data are Landau's own (first documented in Vardi 2022)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("domain", "PP"), ("depth", "surface"), ("extractionAvailable", "false"), ("abarContext", "restrictive relative, interrogative, free relative")] }

def englishVPE : Datum :=
  { id := "landau2026_englishVPE"
    source := ⟨"landau-2026", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Deep Purple, I never bought their records. Led Zeppelin, I did."
    glossedTokens := []
    context := "VP-ellipsis, surface anaphor: left-dislocated constituent binds a resumptive possessive inside the elided VP. Contrastive baseline for do so."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "surface"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")] }

def englishDoSo : Datum :=
  { id := "landau2026_englishDoSo"
    source := ⟨"landau-2026", "(44c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Deep Purple, I never bought their records. Led Zeppelin, I did so."
    glossedTokens := []
    context := "do so, deep VP anaphor: left-dislocation with resumptive binding into do so is ungrammatical."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")] }

def dutchDatDoen : Datum :=
  { id := "landau2026_dutchDatDoen"
    source := ⟨"landau-2026", "(45a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan, ik heb zijn muffins al eens geproefd; maar Wim, ik heb dat nog niet gedaan."
    glossedTokens := []
    context := "dat doen 'do that', deep VP anaphor: blocks most Ā-extractions and fails EIR."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")] }

def danishDet : Datum :=
  { id := "landau2026_danishDet"
    source := ⟨"landau-2026", "(46b)"⟩
    reportedIn := none
    language := "dani1285"
    primaryText := "Den gamle bager, jeg har smagt hans rugbrød, men den nye bager, jeg har det ikke."
    glossedTokens := []
    context := "det 'it', deep VP anaphor: allows A-dependencies but not Ā-dependencies, so it fails EIR."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("domain", "VP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")] }

def koreanNullObj : Datum :=
  { id := "landau2026_koreanNullObj"
    source := ⟨"landau-2026", "(47b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Na-uy i chinkwu, nay-ka ku-uy cha-lul sasse. Nay-uy ce chinkwu, nay-ka phalasse."
    glossedTokens := []
    context := "Korean null object, deep anaphor (pro): left-dislocation mandates a resumptive, but the null object fails to host one."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("domain", "DP"), ("depth", "deep"), ("extractionAvailable", "true"), ("abarContext", "left-dislocation")] }

def all : List Datum := [hebrewEN, hebrewENP, hebrewNCA_DP, hebrewAE, hebrewNCA_PP, hebrewPPE, englishVPE, englishDoSo, dutchDatDoen, danishDet, koreanNullObj]

end Landau2026.Examples
