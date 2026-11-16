module

public import Linglib.Data.Examples.Schema

/-!
# `TurkHirsch2026` — typed example data

Auto-generated from `Linglib/Data/Examples/TurkHirsch2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TurkHirsch2026.Examples`.
-/

@[expose] public section

namespace TurkHirsch2026.Examples

def ex_4 : Datum :=
  { id := "turkhirsch2026_4"
    source := ⟨"turk-hirsch-2026", "(4)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali uyudu=mu?"
    glossedTokens := [("Ali", "Ali[NOM]"), ("uyu-du=mu", "sleep-PST.3SG=FM")]
    glossedWords := [⟨[['A', 'l', 'i']], [['A', 'l', 'i', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['u', 'y', 'u'], ['d', 'u'], ['m', 'u']], [['s', 'l', 'e', 'e', 'p'], ['P', 'S', 'T', '.', '3', 'S', 'G'], ['F', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "default"), ("focus", "sigma")] }

def ex_5 : Datum :=
  { id := "turkhirsch2026_5"
    source := ⟨"turk-hirsch-2026", "(5)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "ALI=mi uyudu?"
    glossedTokens := [("ALI=mi", "Ali[NOM]=FM"), ("uyu-du", "sleep-PST.3SG")]
    glossedWords := [⟨[['A', 'L', 'I'], ['m', 'i']], [['A', 'l', 'i', '[', 'N', 'O', 'M', ']'], ['F', 'M']]⟩, ⟨[['u', 'y', 'u'], ['d', 'u']], [['s', 'l', 'e', 'e', 'p'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "subject"), ("focus", "subject")] }

def ex_6a : Datum :=
  { id := "turkhirsch2026_6a"
    source := ⟨"turk-hirsch-2026", "(6a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Hayır."
    glossedTokens := [("Hayır", "no")]
    glossedWords := [⟨[['H', 'a', 'y', 'ı', 'r']], [['n', 'o']]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to (5)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "negative particle"), ("complete", "no")] }

def ex_6b : Datum :=
  { id := "turkhirsch2026_6b"
    source := ⟨"turk-hirsch-2026", "(6b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Hayır, Veli uyudu."
    glossedTokens := [("Hayır", "no"), ("Veli", "Veli[NOM]"), ("uyu-du", "sleep-PST.3SG")]
    glossedWords := [⟨[['H', 'a', 'y', 'ı', 'r']], [['n', 'o']]⟩, ⟨[['V', 'e', 'l', 'i']], [['V', 'e', 'l', 'i', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['u', 'y', 'u'], ['d', 'u']], [['s', 'l', 'e', 'e', 'p'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to (5)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "negative particle with continuation"), ("complete", "yes")] }

def ex_14 : Datum :=
  { id := "turkhirsch2026_14"
    source := ⟨"turk-hirsch-2026", "(14)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Yannis Ali uyudu=mu diye meraketti."
    glossedTokens := [("Yannis", "Yannis[NOM]"), ("Ali", "Ali[NOM]"), ("uyu-du=mu", "sleep-PST=FM"), ("diye", "that"), ("meraket-ti", "wonder-PST")]
    glossedWords := [⟨[['Y', 'a', 'n', 'n', 'i', 's']], [['Y', 'a', 'n', 'n', 'i', 's', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['A', 'l', 'i']], [['A', 'l', 'i', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['u', 'y', 'u'], ['d', 'u'], ['m', 'u']], [['s', 'l', 'e', 'e', 'p'], ['P', 'S', 'T'], ['F', 'M']]⟩, ⟨[['d', 'i', 'y', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['m', 'e', 'r', 'a', 'k', 'e', 't'], ['t', 'i']], [['w', 'o', 'n', 'd', 'e', 'r'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "below diye"), ("matrix", "declarative")] }

def ex_18 : Datum :=
  { id := "turkhirsch2026_18"
    source := ⟨"turk-hirsch-2026", "(18)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Yannis Ali uyudu diye=mi meraketti?"
    glossedTokens := [("Yannis", "Yannis[NOM]"), ("Ali", "Ali[NOM]"), ("uyu-du", "sleep-PST"), ("diye=mi", "that=FM"), ("meraket-ti", "wonder-PST")]
    glossedWords := [⟨[['Y', 'a', 'n', 'n', 'i', 's']], [['Y', 'a', 'n', 'n', 'i', 's', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['A', 'l', 'i']], [['A', 'l', 'i', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['u', 'y', 'u'], ['d', 'u']], [['s', 'l', 'e', 'e', 'p'], ['P', 'S', 'T']]⟩, ⟨[['d', 'i', 'y', 'e'], ['m', 'i']], [['t', 'h', 'a', 't'], ['F', 'M']]⟩, ⟨[['m', 'e', 'r', 'a', 'k', 'e', 't'], ['t', 'i']], [['w', 'o', 'n', 'd', 'e', 'r'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "above diye"), ("matrix", "question")] }

def ex_35a : Datum :=
  { id := "turkhirsch2026_35a"
    source := ⟨"turk-hirsch-2026", "(35a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Evet, Ali uyudu."
    glossedTokens := [("Evet", "yes"), ("Ali", "Ali[NOM]"), ("uyu-du", "sleep-PST.3SG")]
    glossedWords := [⟨[['E', 'v', 'e', 't']], [['y', 'e', 's']]⟩, ⟨[['A', 'l', 'i']], [['A', 'l', 'i', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['u', 'y', 'u'], ['d', 'u']], [['s', 'l', 'e', 'e', 'p'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to (22) at a world where Ali had to sleep and did sleep."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "positive"), ("complete", "yes")] }

def ex_35b : Datum :=
  { id := "turkhirsch2026_35b"
    source := ⟨"turk-hirsch-2026", "(35b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Evet, Ali uyumak zorundaydı ve uyudu."
    glossedTokens := [("Evet", "yes"), ("Ali", "Ali[NOM]"), ("uyu-mak", "sleep-INF"), ("zorunda-ydı", "obligation-PST.3SG"), ("ve", "and"), ("uyu-du", "sleep-PST.3SG")]
    glossedWords := [⟨[['E', 'v', 'e', 't']], [['y', 'e', 's']]⟩, ⟨[['A', 'l', 'i']], [['A', 'l', 'i', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['u', 'y', 'u'], ['m', 'a', 'k']], [['s', 'l', 'e', 'e', 'p'], ['I', 'N', 'F']]⟩, ⟨[['z', 'o', 'r', 'u', 'n', 'd', 'a'], ['y', 'd', 'ı']], [['o', 'b', 'l', 'i', 'g', 'a', 't', 'i', 'o', 'n'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['v', 'e']], [['a', 'n', 'd']]⟩, ⟨[['u', 'y', 'u'], ['d', 'u']], [['s', 'l', 'e', 'e', 'p'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to (22) at a world where Ali had to sleep and did sleep."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "modal conjunction"), ("complete", "over-informative")] }

def ex_41 : Datum :=
  { id := "turkhirsch2026_41"
    source := ⟨"turk-hirsch-2026", "(41)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali uyumak zorundaydı."
    glossedTokens := [("Ali", "Ali[NOM]"), ("uyu-mak", "sleep-INF"), ("zorunda-y-dı", "obliged-COP-PST.3SG")]
    glossedWords := [⟨[['A', 'l', 'i']], [['A', 'l', 'i', '[', 'N', 'O', 'M', ']']]⟩, ⟨[['u', 'y', 'u'], ['m', 'a', 'k']], [['s', 'l', 'e', 'e', 'p'], ['I', 'N', 'F']]⟩, ⟨[['z', 'o', 'r', 'u', 'n', 'd', 'a'], ['y'], ['d', 'ı']], [['o', 'b', 'l', 'i', 'g', 'e', 'd'], ['C', 'O', 'P'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "(39): Ali injured himself and went to the doctor for instructions; his partner tells us he slept for several hours after the appointment; we ask (22)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "modal"), ("complete", "no")] }

def all : List Datum := [ex_4, ex_5, ex_6a, ex_6b, ex_14, ex_18, ex_35a, ex_35b, ex_41]

end TurkHirsch2026.Examples
