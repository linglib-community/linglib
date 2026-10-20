module

public import Linglib.Data.Examples.Schema

/-!
# `Landau2024a` — typed example data

Auto-generated from `Linglib/Data/Examples/Landau2024a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Landau2024a.Examples`.
-/

@[expose] public section

namespace Landau2024a.Examples

def ex_20a : Datum :=
  { id := "landau2024a_20a"
    source := ⟨"landau-2024a", "(20a)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Jeg ble lovet å gi meg gaver."
    glossedTokens := [("Jeg", "I"), ("ble", "was"), ("lovet", "promised"), ("å", "COMP"), ("gi", "give.INF"), ("meg", "me.ACC"), ("gaver", "gifts")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("controller", "implicit"), ("tAgrees", "referential")] }

def ex_20b : Datum :=
  { id := "landau2024a_20b"
    source := ⟨"landau-2024a", "(20b)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Det ble lovet å gi meg gaver."
    glossedTokens := [("Det", "there"), ("ble", "was"), ("lovet", "promised"), ("å", "COMP"), ("gi", "give.INF"), ("meg", "me.ACC"), ("gaver", "gifts")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("controller", "implicit"), ("tAgrees", "expletive")] }

def ex_22a : Datum :=
  { id := "landau2024a_22a"
    source := ⟨"landau-2024a", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary was asked where to throw the trash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("controller", "implicit"), ("tAgrees", "referential")] }

def ex_35a : Datum :=
  { id := "landau2024a_35a"
    source := ⟨"landau-2024a", "(35a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Inho-ka Hwun-eykey swuyeng-ha-n-ta-ko mal-ha-yess-ta."
    glossedTokens := [("Inho-ka", "Inho-NOM"), ("Hwun-eykey", "Hwun-DAT"), ("swuyeng-ha-n-ta-ko", "swim-do-IND-DC-C"), ("mal-ha-yess-ta", "tell-do-PST-DC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("subject", .acceptable), ("object", .acceptable), ("free", .acceptable)]
    paperFeatures := [("verb", "mal"), ("mood", "indicative")] }

def ex_35b : Datum :=
  { id := "landau2024a_35b"
    source := ⟨"landau-2024a", "(35b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Inho-ka Hwun-eykey swuyeng-ha-keyss-ta-ko mal-ha-yess-ta."
    glossedTokens := [("Inho-ka", "Inho-NOM"), ("Hwun-eykey", "Hwun-DAT"), ("swuyeng-ha-keyss-ta-ko", "swim-VOL-DC-C"), ("mal-ha-yess-ta", "tell-do-PST-DC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("subject", .acceptable), ("object", .ungrammatical), ("free", .ungrammatical)]
    paperFeatures := [("verb", "mal"), ("mood", "volitional")] }

def ex_35c : Datum :=
  { id := "landau2024a_35c"
    source := ⟨"landau-2024a", "(35c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Inho-ka Hwun-eykey swuyeng-ha-la-ko mal-ha-yess-ta."
    glossedTokens := [("Inho-ka", "Inho-NOM"), ("Hwun-eykey", "Hwun-DAT"), ("swuyeng-ha-la-ko", "swim-do-IMP-C"), ("mal-ha-yess-ta", "tell-do-PST-DC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("subject", .ungrammatical), ("object", .acceptable), ("free", .ungrammatical)]
    paperFeatures := [("verb", "mal"), ("mood", "imperative")] }

def ex_35d : Datum :=
  { id := "landau2024a_35d"
    source := ⟨"landau-2024a", "(35d)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Inho-ka Hwun-eykey swuyeng-ha-ca-ko mal-ha-yess-ta."
    glossedTokens := [("Inho-ka", "Inho-NOM"), ("Hwun-eykey", "Hwun-DAT"), ("swuyeng-ha-ca-ko", "swim-do-EXH-C"), ("mal-ha-yess-ta", "tell-do-PST-DC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("split", .acceptable), ("subject", .ungrammatical), ("object", .ungrammatical), ("free", .ungrammatical)]
    paperFeatures := [("verb", "mal"), ("mood", "exhortative")] }

def ex_36b : Datum :=
  { id := "landau2024a_36b"
    source := ⟨"landau-2024a", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We thought that Bill regretted meeting without a concrete agenda."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "regret"), ("reading", "partial")] }

def ex_36c : Datum :=
  { id := "landau2024a_36c"
    source := ⟨"landau-2024a", "(36c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We thought that Mary wondered whether to apply together for the grant."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wonder"), ("reading", "partial")] }

def ex_37a : Datum :=
  { id := "landau2024a_37a"
    source := ⟨"landau-2024a", "(37a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We thought that John managed to gather at 6."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "manage"), ("reading", "partial")] }

def ex_41a : Datum :=
  { id := "landau2024a_41a"
    source := ⟨"landau-2024a", "(41a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan quería comprar un caballo."
    glossedTokens := [("Juan", "Juan"), ("quería", "wanted"), ("comprar", "to.buy"), ("un", "a"), ("caballo", "horse")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free", .ungrammatical)]
    paperFeatures := [("clause", "infinitive"), ("position", "complement")] }

def ex_41b : Datum :=
  { id := "landau2024a_41b"
    source := ⟨"landau-2024a", "(41b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Comprar un caballo sería un error."
    glossedTokens := [("comprar", "to.buy"), ("un", "a"), ("caballo", "horse"), ("sería", "would.be"), ("un", "an"), ("error", "error")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free", .acceptable)]
    paperFeatures := [("clause", "infinitive"), ("position", "subject")] }

def ex_41c : Datum :=
  { id := "landau2024a_41c"
    source := ⟨"landau-2024a", "(41c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan recordó que había comprado un caballo."
    glossedTokens := [("Juan", "Juan"), ("recordó", "remembered"), ("que", "that"), ("había", "had"), ("comprado", "bought"), ("un", "a"), ("caballo", "horse")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free", .acceptable)]
    paperFeatures := [("clause", "finite"), ("position", "complement")] }

def ex_41d : Datum :=
  { id := "landau2024a_41d"
    source := ⟨"landau-2024a", "(41d)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Que compro un caballo fue un error."
    glossedTokens := [("Que", "that"), ("compro", "bought"), ("un", "a"), ("caballo", "horse"), ("fue", "was"), ("un", "an"), ("error", "error")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free", .acceptable)]
    paperFeatures := [("clause", "finite"), ("position", "subject")] }

def ex_52a : Datum :=
  { id := "landau2024a_52a"
    source := ⟨"landau-2024a", "(52a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What about the certificates of appreciation? What happened to them? They were handed out before announcing the winners."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("control", "NOC"), ("controller", "implicit agent"), ("topic", "-"), ("logophoric", "+")] }

def ex_52b : Datum :=
  { id := "landau2024a_52b"
    source := ⟨"landau-2024a", "(52b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What about Mary? Is she available? Well, after sneaking outside last night, her father grounded her for a week."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("control", "NOC"), ("controller", "Mary"), ("topic", "+"), ("logophoric", "-")] }

def ex_87a : Datum :=
  { id := "landau2024a_87a"
    source := ⟨"landau-2024a", "(87a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wept for his wife to hear the tragic story."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjunct", "stimulus"), ("subject", "lexical")] }

def ex_87b : Datum :=
  { id := "landau2024a_87b"
    source := ⟨"landau-2024a", "(87b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her kids wept to hear the tragic story."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("adjunct", "stimulus"), ("antecedent", "nonCCommanding")] }

def ex_88a : Datum :=
  { id := "landau2024a_88a"
    source := ⟨"landau-2024a", "(88a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Our life was blessed for her being so much a part of it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjunct", "justification"), ("subject", "lexical")] }

def ex_88b : Datum :=
  { id := "landau2024a_88b"
    source := ⟨"landau-2024a", "(88b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her kids were punished for letting them ruin the place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjunct", "justification"), ("antecedent", "nonCCommanding")] }

def all : List Datum := [ex_20a, ex_20b, ex_22a, ex_35a, ex_35b, ex_35c, ex_35d, ex_36b, ex_36c, ex_37a, ex_41a, ex_41b, ex_41c, ex_41d, ex_52a, ex_52b, ex_87a, ex_87b, ex_88a, ex_88b]

end Landau2024a.Examples
