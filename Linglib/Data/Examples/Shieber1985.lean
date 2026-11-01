module

public import Linglib.Data.Examples.Schema

/-!
# `Shieber1985` — typed example data

Auto-generated from `Linglib/Data/Examples/Shieber1985.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Shieber1985.Examples`.
-/

@[expose] public section

namespace Shieber1985.Examples

def ex1 : Datum :=
  { id := "shieber1985_ex1"
    source := ⟨"shieber-1985", "(1)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans es huus hälfed aastriiche"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("es huus", "the house-ACC"), ("hälfed", "helped"), ("aastriiche", "paint")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex2 : Datum :=
  { id := "shieber1985_ex2"
    source := ⟨"shieber-1985", "(2)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer de Hans es huus lönd aastriiche"
    glossedTokens := [("mer", "we"), ("de Hans", "Hans-ACC"), ("es huus", "the house-ACC"), ("lönd", "let"), ("aastriiche", "paint")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex3 : Datum :=
  { id := "shieber1985_ex3"
    source := ⟨"shieber-1985", "(3)"⟩
    reportedIn := none
    method := some .elicitation
    language := "zuri1239"
    primaryText := "mer em Hans es huus lönd aastriiche"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("es huus", "the house-ACC"), ("lönd", "let"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex4 : Datum :=
  { id := "shieber1985_ex4"
    source := ⟨"shieber-1985", "(4)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer de Hans em huus lönd aastriiche"
    glossedTokens := [("mer", "we"), ("de Hans", "Hans-ACC"), ("em huus", "the house-DAT"), ("lönd", "let"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex5 : Datum :=
  { id := "shieber1985_ex5"
    source := ⟨"shieber-1985", "(5)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer d'chind em Hans es huus lönd hälfe aastriiche"
    glossedTokens := [("mer", "we"), ("d'chind", "the children-ACC"), ("em Hans", "Hans-DAT"), ("es huus", "the house-ACC"), ("lönd", "let"), ("hälfe", "help"), ("aastriiche", "paint")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex6 : Datum :=
  { id := "shieber1985_ex6"
    source := ⟨"shieber-1985", "(6)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer d'chind de Hans es huus lönd hälfe aastriiche"
    glossedTokens := [("mer", "we"), ("d'chind", "the children-ACC"), ("de Hans", "Hans-ACC"), ("es huus", "the house-ACC"), ("lönd", "let"), ("hälfe", "help"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex7 : Datum :=
  { id := "shieber1985_ex7"
    source := ⟨"shieber-1985", "(7)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans es huus haend wele hälfe aastriiche"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("es huus", "the house-ACC"), ("haend", "have"), ("wele", "wanted"), ("hälfe", "help"), ("aastriiche", "paint")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex8 : Datum :=
  { id := "shieber1985_ex8"
    source := ⟨"shieber-1985", "(8)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer d'chind em Hans es huus haend wele laa hälfe aastriiche"
    glossedTokens := [("mer", "we"), ("d'chind", "the children-ACC"), ("em Hans", "Hans-DAT"), ("es huus", "the house-ACC"), ("haend", "have"), ("wele", "wanted"), ("laa", "let"), ("hälfe", "help"), ("aastriiche", "paint")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def ex9 : Datum :=
  { id := "shieber1985_ex9"
    source := ⟨"shieber-1985", "(9)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans hälfed es huus aastriiche"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("hälfed", "helped"), ("es huus", "the house-ACC"), ("aastriiche", "paint")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex10 : Datum :=
  { id := "shieber1985_ex10"
    source := ⟨"shieber-1985", "(10)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans es huus aastriiche hälfed"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("es huus", "the house-ACC"), ("aastriiche", "paint"), ("hälfed", "helped")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex11 : Datum :=
  { id := "shieber1985_ex11"
    source := ⟨"shieber-1985", "(11)"⟩
    reportedIn := none
    method := some .elicitation
    language := "zuri1239"
    primaryText := "em Hans mer es huus hälfed aastriiche"
    glossedTokens := [("em Hans", "Hans"), ("mer", "we"), ("es huus", "the house"), ("hälfed", "helped"), ("aastriiche", "paint")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex12 : Datum :=
  { id := "shieber1985_ex12"
    source := ⟨"shieber-1985", "(12)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer de Hans hälfed es huus aastriiche"
    glossedTokens := [("mer", "we"), ("de Hans", "Hans-ACC"), ("hälfed", "helped"), ("es huus", "the house-ACC"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex13 : Datum :=
  { id := "shieber1985_ex13"
    source := ⟨"shieber-1985", "(13)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans hälfed em huus aastriiche"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("hälfed", "helped"), ("em huus", "the house-DAT"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex14 : Datum :=
  { id := "shieber1985_ex14"
    source := ⟨"shieber-1985", "(14)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans lönd es huus aastriiche"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("lönd", "let"), ("es huus", "the house-ACC"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex15 : Datum :=
  { id := "shieber1985_ex15"
    source := ⟨"shieber-1985", "(15)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer de Hans lönd em huus aastriiche"
    glossedTokens := [("mer", "we"), ("de Hans", "Hans-ACC"), ("lönd", "let"), ("em huus", "the house-DAT"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex16 : Datum :=
  { id := "shieber1985_ex16"
    source := ⟨"shieber-1985", "(16)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer de Hans es huus aastriiche hälfed"
    glossedTokens := [("mer", "we"), ("de Hans", "Hans-ACC"), ("es huus", "the house-ACC"), ("aastriiche", "paint"), ("hälfed", "helped")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex17 : Datum :=
  { id := "shieber1985_ex17"
    source := ⟨"shieber-1985", "(17)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans em huus aastriiche hälfed"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("em huus", "the house-DAT"), ("aastriiche", "paint"), ("hälfed", "helped")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex18 : Datum :=
  { id := "shieber1985_ex18"
    source := ⟨"shieber-1985", "(18)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer em Hans es huus aastriiche lönd"
    glossedTokens := [("mer", "we"), ("em Hans", "Hans-DAT"), ("es huus", "the house-ACC"), ("aastriiche", "paint"), ("lönd", "let")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex19 : Datum :=
  { id := "shieber1985_ex19"
    source := ⟨"shieber-1985", "(19)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer de Hans em huus aastriiche lönd"
    glossedTokens := [("mer", "we"), ("de Hans", "Hans-ACC"), ("em huus", "the house-DAT"), ("aastriiche", "paint"), ("lönd", "let")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex20 : Datum :=
  { id := "shieber1985_ex20"
    source := ⟨"shieber-1985", "(20)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer de Hans haend wele hälfe es huus aastriiche"
    glossedTokens := [("mer", "we"), ("de Hans", "Hans-ACC"), ("haend", "have"), ("wele", "wanted"), ("hälfe", "help"), ("es huus", "the house-ACC"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex21 : Datum :=
  { id := "shieber1985_ex21"
    source := ⟨"shieber-1985", "(21)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer d'chind lönd de Hans hälfe es huus aastriiche"
    glossedTokens := [("mer", "we"), ("d'chind", "the children-ACC"), ("lönd", "let"), ("de Hans", "Hans-ACC"), ("hälfe", "help"), ("es huus", "the house-ACC"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "other")] }

def ex22 : Datum :=
  { id := "shieber1985_ex22"
    source := ⟨"shieber-1985", "(22)"⟩
    reportedIn := none
    language := "zuri1239"
    primaryText := "mer d'chind de Hans es huus lönd hälfe aastriiche"
    glossedTokens := [("mer", "we"), ("d'chind", "the children-ACC"), ("de Hans", "Hans-ACC"), ("es huus", "the house-ACC"), ("lönd", "let"), ("hälfe", "help"), ("aastriiche", "paint")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("order", "crossSerial")] }

def all : List Datum := [ex1, ex2, ex3, ex4, ex5, ex6, ex7, ex8, ex9, ex10, ex11, ex12, ex13, ex14, ex15, ex16, ex17, ex18, ex19, ex20, ex21, ex22]

end Shieber1985.Examples
