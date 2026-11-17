module

public import Linglib.Data.Examples.Schema

/-!
# `RotterLiu2025` — typed example data

Auto-generated from `Linglib/Data/Examples/RotterLiu2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RotterLiu2025.Examples`.
-/

@[expose] public section

namespace RotterLiu2025.Examples

def close_nece_sm : Datum :=
  { id := "rotterliu2025_close_nece_sm"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) close necessity SM"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must have lost my keys."
    glossedTokens := []
    context := "A woman says to the boyfriend (close interlocutor): S2. Participant rates speaker commitment (Q1), appropriateness (Q2), grammaticality (Q3), and the speaker's social background + persona. Necessity single-modal (SM), close context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "close"), ("force", "necessity"), ("number", "SM"), ("commitment", "603"), ("grammaticality", "625"), ("appropriateness", "603"), ("ses", "452"), ("education", "465"), ("formality", "406"), ("politeness", "527"), ("confidence", "506"), ("friendliness", "514"), ("warmth", "491"), ("coolness", "455"), ("rebelliousness", "355")] }

def close_nece_mc : Datum :=
  { id := "rotterliu2025_close_nece_mc"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) close necessity MC"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must certainly have lost my keys."
    glossedTokens := []
    context := "A woman says to the boyfriend (close interlocutor): S2. Necessity modal-concord (MC), close context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "close"), ("force", "necessity"), ("number", "MC"), ("commitment", "628"), ("grammaticality", "489"), ("appropriateness", "530"), ("ses", "452"), ("education", "463"), ("formality", "447"), ("politeness", "531"), ("confidence", "528"), ("friendliness", "498"), ("warmth", "474"), ("coolness", "430"), ("rebelliousness", "350")] }

def close_poss_sm : Datum :=
  { id := "rotterliu2025_close_poss_sm"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) close possibility SM"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I may have lost my keys."
    glossedTokens := []
    context := "A woman says to the boyfriend (close interlocutor): S2. Possibility single-modal (SM), close context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "close"), ("force", "possibility"), ("number", "SM"), ("commitment", "538"), ("grammaticality", "629"), ("appropriateness", "599"), ("ses", "456"), ("education", "470"), ("formality", "417"), ("politeness", "533"), ("confidence", "450"), ("friendliness", "519"), ("warmth", "494"), ("coolness", "450"), ("rebelliousness", "347")] }

def close_poss_mc : Datum :=
  { id := "rotterliu2025_close_poss_mc"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) close possibility MC"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I may possibly have lost my keys."
    glossedTokens := []
    context := "A woman says to the boyfriend (close interlocutor): S2. Possibility modal-concord (MC), close context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "close"), ("force", "possibility"), ("number", "MC"), ("commitment", "520"), ("grammaticality", "510"), ("appropriateness", "542"), ("ses", "449"), ("education", "454"), ("formality", "420"), ("politeness", "530"), ("confidence", "421"), ("friendliness", "505"), ("warmth", "485"), ("coolness", "443"), ("rebelliousness", "351")] }

def distant_nece_sm : Datum :=
  { id := "rotterliu2025_distant_nece_sm"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) distant necessity SM"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must have lost my keys."
    glossedTokens := []
    context := "A woman says to the landlord (distant interlocutor): S2. Necessity single-modal (SM), distant context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "distant"), ("force", "necessity"), ("number", "SM"), ("commitment", "598"), ("grammaticality", "625"), ("appropriateness", "594"), ("ses", "451"), ("education", "466"), ("formality", "454"), ("politeness", "524"), ("confidence", "498"), ("friendliness", "498"), ("warmth", "481"), ("coolness", "449"), ("rebelliousness", "346")] }

def distant_nece_mc : Datum :=
  { id := "rotterliu2025_distant_nece_mc"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) distant necessity MC"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must certainly have lost my keys."
    glossedTokens := []
    context := "A woman says to the landlord (distant interlocutor): S2. Necessity modal-concord (MC), distant context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "distant"), ("force", "necessity"), ("number", "MC"), ("commitment", "626"), ("grammaticality", "483"), ("appropriateness", "526"), ("ses", "442"), ("education", "452"), ("formality", "485"), ("politeness", "527"), ("confidence", "524"), ("friendliness", "485"), ("warmth", "465"), ("coolness", "428"), ("rebelliousness", "347")] }

def distant_poss_sm : Datum :=
  { id := "rotterliu2025_distant_poss_sm"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) distant possibility SM"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I may have lost my keys."
    glossedTokens := []
    context := "A woman says to the landlord (distant interlocutor): S2. Possibility single-modal (SM), distant context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "distant"), ("force", "possibility"), ("number", "SM"), ("commitment", "534"), ("grammaticality", "624"), ("appropriateness", "589"), ("ses", "458"), ("education", "466"), ("formality", "469"), ("politeness", "538"), ("confidence", "440"), ("friendliness", "506"), ("warmth", "485"), ("coolness", "451"), ("rebelliousness", "341")] }

def distant_poss_mc : Datum :=
  { id := "rotterliu2025_distant_poss_mc"
    source := ⟨"rotter-liu-2025", "Exp 2 (6) distant possibility MC"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I may possibly have lost my keys."
    glossedTokens := []
    context := "A woman says to the landlord (distant interlocutor): S2. Possibility modal-concord (MC), distant context."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("context", "distant"), ("force", "possibility"), ("number", "MC"), ("commitment", "517"), ("grammaticality", "498"), ("appropriateness", "530"), ("ses", "445"), ("education", "448"), ("formality", "464"), ("politeness", "530"), ("confidence", "408"), ("friendliness", "499"), ("warmth", "479"), ("coolness", "433"), ("rebelliousness", "344")] }

def all : List Datum := [close_nece_sm, close_nece_mc, close_poss_sm, close_poss_mc, distant_nece_sm, distant_nece_mc, distant_poss_sm, distant_poss_mc]

end RotterLiu2025.Examples
