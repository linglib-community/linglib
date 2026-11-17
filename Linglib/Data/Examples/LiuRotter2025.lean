module

public import Linglib.Data.Examples.Schema

/-!
# `LiuRotter2025` — typed example data

Auto-generated from `Linglib/Data/Examples/LiuRotter2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LiuRotter2025.Examples`.
-/

@[expose] public section

namespace LiuRotter2025.Examples

def poss_sm : Datum :=
  { id := "liurotter2025_poss_sm"
    source := ⟨"liu-rotter-2025", "(3) possibility SM"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I may have gotten the wrong address."
    glossedTokens := []
    context := "Somebody says S; participant rates speaker commitment (Q1) and grammaticality (Q2), then rates the speaker on social-background and persona dimensions. Possibility single-modal (SM) cell of the 2x2 FORCE x NUMBER design."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force", "possibility"), ("number", "SM"), ("commitment", "522"), ("grammaticality", "645"), ("ses", "487"), ("education", "494"), ("formality", "484"), ("politeness", "545"), ("confidence", "436"), ("friendliness", "503"), ("warmth", "494"), ("coolness", "456"), ("rebelliousness", "309")] }

def poss_mc : Datum :=
  { id := "liurotter2025_poss_mc"
    source := ⟨"liu-rotter-2025", "(3) possibility MC"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I may possibly have gotten the wrong address."
    glossedTokens := []
    context := "Somebody says S; participant rates speaker commitment (Q1) and grammaticality (Q2), then rates the speaker on social-background and persona dimensions. Possibility modal-concord (MC) cell of the 2x2 FORCE x NUMBER design."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force", "possibility"), ("number", "MC"), ("commitment", "511"), ("grammaticality", "506"), ("ses", "473"), ("education", "469"), ("formality", "473"), ("politeness", "536"), ("confidence", "403"), ("friendliness", "492"), ("warmth", "482"), ("coolness", "429"), ("rebelliousness", "311")] }

def nece_sm : Datum :=
  { id := "liurotter2025_nece_sm"
    source := ⟨"liu-rotter-2025", "(3) necessity SM"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must have gotten the wrong address."
    glossedTokens := []
    context := "Somebody says S; participant rates speaker commitment (Q1) and grammaticality (Q2), then rates the speaker on social-background and persona dimensions. Necessity single-modal (SM) cell of the 2x2 FORCE x NUMBER design."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force", "necessity"), ("number", "SM"), ("commitment", "612"), ("grammaticality", "641"), ("ses", "487"), ("education", "489"), ("formality", "476"), ("politeness", "528"), ("confidence", "519"), ("friendliness", "497"), ("warmth", "486"), ("coolness", "453"), ("rebelliousness", "312")] }

def nece_mc : Datum :=
  { id := "liurotter2025_nece_mc"
    source := ⟨"liu-rotter-2025", "(3) necessity MC"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I must certainly have gotten the wrong address."
    glossedTokens := []
    context := "Somebody says S; participant rates speaker commitment (Q1) and grammaticality (Q2), then rates the speaker on social-background and persona dimensions. Necessity modal-concord (MC) cell of the 2x2 FORCE x NUMBER design."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("force", "necessity"), ("number", "MC"), ("commitment", "640"), ("grammaticality", "490"), ("ses", "485"), ("education", "480"), ("formality", "499"), ("politeness", "539"), ("confidence", "548"), ("friendliness", "476"), ("warmth", "462"), ("coolness", "420"), ("rebelliousness", "304")] }

def all : List Datum := [poss_sm, poss_mc, nece_sm, nece_mc]

end LiuRotter2025.Examples
