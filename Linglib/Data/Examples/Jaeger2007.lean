module

public import Linglib.Data.Examples.Schema

/-!
# `Jaeger2007` — typed example data

Auto-generated from `Linglib/Data/Examples/Jaeger2007.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jaeger2007.Examples`.
-/

@[expose] public section

namespace Jaeger2007.Examples

def t1_cv : Datum :=
  { id := "jaeger2007_t1_cv"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "CV"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "1"), ("coda", "0"), ("frequency", "44.81"), ("permyriad", "4481")] }

def t1_cvc : Datum :=
  { id := "jaeger2007_t1_cvc"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "CVC"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "1"), ("coda", "1"), ("frequency", "32.05"), ("permyriad", "3205")] }

def t1_vc : Datum :=
  { id := "jaeger2007_t1_vc"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "VC"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "0"), ("coda", "1"), ("frequency", "11.99"), ("permyriad", "1199")] }

def t1_v : Datum :=
  { id := "jaeger2007_t1_v"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "V"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "0"), ("coda", "0"), ("frequency", "3.85"), ("permyriad", "385")] }

def t1_cvcc : Datum :=
  { id := "jaeger2007_t1_cvcc"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "CVCC"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "1"), ("coda", "2"), ("frequency", "3.25"), ("permyriad", "325")] }

def t1_ccvc : Datum :=
  { id := "jaeger2007_t1_ccvc"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "CCVC"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "2"), ("coda", "1"), ("frequency", "1.98"), ("permyriad", "198")] }

def t1_ccv : Datum :=
  { id := "jaeger2007_t1_ccv"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "CCV"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "2"), ("coda", "0"), ("frequency", "1.38"), ("permyriad", "138")] }

def t1_vcc : Datum :=
  { id := "jaeger2007_t1_vcc"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "VCC"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "0"), ("coda", "2"), ("frequency", "0.42"), ("permyriad", "42")] }

def t1_ccvcc : Datum :=
  { id := "jaeger2007_t1_ccvcc"
    source := ⟨"jaeger-2007", "Table 1"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "CCVCC"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("onset", "2"), ("coda", "2"), ("frequency", "0.26"), ("permyriad", "26")] }

def all : List Datum := [t1_cv, t1_cvc, t1_vc, t1_v, t1_cvcc, t1_ccvc, t1_ccv, t1_vcc, t1_ccvcc]

end Jaeger2007.Examples
