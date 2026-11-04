module

public import Linglib.Data.Examples.Schema

/-!
# `MacCartneyManning2009` — typed example data

Auto-generated from `Linglib/Data/Examples/MacCartneyManning2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MacCartneyManning2009.Examples`.
-/

@[expose] public section

namespace MacCartneyManning2009.Examples

def manage : Datum :=
  { id := "maccartneymanning2009_manage"
    source := ⟨"maccartney-manning-2009", "Section 6 table, +/−"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he managed to escape"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "+/−"), ("deletion", "≡"), ("insertion", "≡"), ("hypothesis", "he escaped"), ("monotonicity", "up")] }

def force : Datum :=
  { id := "maccartneymanning2009_force"
    source := ⟨"maccartney-manning-2009", "Section 6 table, +/◦"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he was forced to sell"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "+/◦"), ("deletion", "⊏"), ("insertion", "⊐"), ("hypothesis", "he sold"), ("monotonicity", "up")] }

def permit : Datum :=
  { id := "maccartneymanning2009_permit"
    source := ⟨"maccartney-manning-2009", "Section 6 table, ◦/−"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he was permitted to live"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "◦/−"), ("deletion", "⊐"), ("insertion", "⊏"), ("hypothesis", "he lived"), ("monotonicity", "up")] }

def forget : Datum :=
  { id := "maccartneymanning2009_forget"
    source := ⟨"maccartney-manning-2009", "Section 6 table, −/+"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he forgot to pay"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "−/+"), ("deletion", "^"), ("insertion", "^"), ("hypothesis", "he paid"), ("monotonicity", "down")] }

def refuse : Datum :=
  { id := "maccartneymanning2009_refuse"
    source := ⟨"maccartney-manning-2009", "Section 6 table, −/◦"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he refused to fight"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "−/◦"), ("deletion", "|"), ("insertion", "|"), ("hypothesis", "he fought"), ("monotonicity", "down")] }

def hesitate : Datum :=
  { id := "maccartneymanning2009_hesitate"
    source := ⟨"maccartney-manning-2009", "Section 6 table, ◦/+"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he hesitated to ask"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "◦/+"), ("deletion", "⌣"), ("insertion", "⌣"), ("hypothesis", "he asked"), ("monotonicity", "down")] }

def admit : Datum :=
  { id := "maccartneymanning2009_admit"
    source := ⟨"maccartney-manning-2009", "Section 6 table, +/+"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he admitted that he knew"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "+/+"), ("deletion", "⊏"), ("insertion", "⊐"), ("hypothesis", "he knew"), ("monotonicity", "non")] }

def pretend : Datum :=
  { id := "maccartneymanning2009_pretend"
    source := ⟨"maccartney-manning-2009", "Section 6 table, −/−"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he pretended he was sick"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "−/−"), ("deletion", "|"), ("insertion", "|"), ("hypothesis", "he was sick"), ("monotonicity", "non")] }

def want : Datum :=
  { id := "maccartneymanning2009_want"
    source := ⟨"maccartney-manning-2009", "Section 6 table, ◦/◦"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he wanted to fly"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "◦/◦"), ("deletion", "#"), ("insertion", "#"), ("hypothesis", "he flew"), ("monotonicity", "non")] }

def permit_neg : Datum :=
  { id := "maccartneymanning2009_permit_neg"
    source := ⟨"maccartney-manning-2009", "Section 6, second observation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he wasn't permitted to live"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "◦/−"), ("relation", "⊏"), ("hypothesis", "he didn't live")] }

def hesitate_neg : Datum :=
  { id := "maccartneymanning2009_hesitate_neg"
    source := ⟨"maccartney-manning-2009", "Section 6, second observation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he didn't hesitate to ask"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "◦/+"), ("relation", "|"), ("hypothesis", "he didn't ask")] }

def admit_neg : Datum :=
  { id := "maccartneymanning2009_admit_neg"
    source := ⟨"maccartney-manning-2009", "Section 6, third observation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "he didn't admit that he knew"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("signature", "+/+"), ("relation", "|"), ("hypothesis", "he didn't know")] }

def all : List Datum := [manage, force, permit, forget, refuse, hesitate, admit, pretend, want, permit_neg, hesitate_neg, admit_neg]

end MacCartneyManning2009.Examples
