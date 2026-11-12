module

public import Linglib.Data.Examples.Schema

/-!
# `AlonsoOvalleMoghiseh2025b` — typed example data

Auto-generated from `Linglib/Data/Examples/AlonsoOvalleMoghiseh2025b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlonsoOvalleMoghiseh2025b.Examples`.
-/

@[expose] public section

namespace AlonsoOvalleMoghiseh2025b.Examples

def ex_1 : Datum :=
  { id := "alonsoovallemoghiseh2025b_1"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What book did you buy?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_2 : Datum :=
  { id := "alonsoovallemoghiseh2025b_2"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you buy?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "BI")] }

def ex_7 : Datum :=
  { id := "alonsoovallemoghiseh2025b_7"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What books did you buy?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_20 : Datum :=
  { id := "alonsoovallemoghiseh2025b_20"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz chi xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("chi", "what.SG"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_21 : Datum :=
  { id := "alonsoovallemoghiseh2025b_21"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(21)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz chi-a xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("chi-a", "what.PL"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_16 : Datum :=
  { id := "alonsoovallemoghiseh2025b_16"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(16)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿A quién viste?"
    glossedTokens := [("A", "OBJ"), ("quién", "who.SG"), ("viste", "saw")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_17 : Datum :=
  { id := "alonsoovallemoghiseh2025b_17"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(17)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿A quiénes viste?"
    glossedTokens := [("A", "OBJ"), ("quiénes", "who.PL"), ("viste", "saw")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PBI")] }

def ex_22 : Datum :=
  { id := "alonsoovallemoghiseh2025b_22"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(22)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿A qué estudiante viste?"
    glossedTokens := [("A", "OBJ"), ("qué", "what"), ("estudiante", "student"), ("viste", "saw.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_23 : Datum :=
  { id := "alonsoovallemoghiseh2025b_23"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(23)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz che ketab-i xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("che", "what"), ("ketab-i", "book.SG.INDEF"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_24 : Datum :=
  { id := "alonsoovallemoghiseh2025b_24"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(24)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "¿A qué estudiantes viste?"
    glossedTokens := [("A", "OBJ"), ("qué", "what"), ("estudiantes", "student.PL"), ("viste", "saw.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_25 : Datum :=
  { id := "alonsoovallemoghiseh2025b_25"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(25)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz che ketab-a-i xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("che", "what"), ("ketab-a-i", "book.PL.INDEF"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_26 : Datum :=
  { id := "alonsoovallemoghiseh2025b_26"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(26)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz chi ro xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("chi", "what.SG"), ("ro", "ACC"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_27 : Datum :=
  { id := "alonsoovallemoghiseh2025b_27"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(27)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz che ketab-i ro xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("che", "what"), ("ketab-i", "book.SG.INDEF"), ("ro", "ACC"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_28 : Datum :=
  { id := "alonsoovallemoghiseh2025b_28"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(28)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz che ketab-a-i ro xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("che", "what"), ("ketab-a-i", "book.PL.INDEF"), ("ro", "ACC"), ("xarid", "bought")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .unacceptable), ("plural answer", .acceptable)]
    paperFeatures := [("type", "PCI")] }

def ex_30 : Datum :=
  { id := "alonsoovallemoghiseh2025b_30"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(30)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya bayad chi bexar-e?"
    glossedTokens := [("Roya", "Roya"), ("bayad", "must"), ("chi", "what.SG"), ("bexar-e", "buy.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_31 : Datum :=
  { id := "alonsoovallemoghiseh2025b_31"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(31)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya bayad che ketab-i bexar-e?"
    glossedTokens := [("Roya", "Roya"), ("bayad", "must"), ("che", "what"), ("ketab-i", "book.SG.INDEF"), ("bexar-e", "buy.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice answer", .acceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_47 : Datum :=
  { id := "alonsoovallemoghiseh2025b_47"
    source := ⟨"karimi-2003", "p. 92"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025b", "(47)"⟩
    method := some .description
    language := "west2369"
    primaryText := "Kimea aghlab ye sher az Hafez ro bara ma mixun-e."
    glossedTokens := [("Kimea", "Kimea"), ("aghlab", "often"), ("ye", "a"), ("sher", "poem"), ("az", "by"), ("Hafez", "Hafez"), ("ro", "ACC"), ("bara", "for"), ("ma", "us"), ("mixun-e", "read.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "specificity")] }

def ex_56 : Datum :=
  { id := "alonsoovallemoghiseh2025b_56"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(56)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya chi (ro) baham ghati kard?"
    glossedTokens := [("Roya", "Roya"), ("chi", "what.SG"), ("(ro)", "(ACC)"), ("baham", "together"), ("ghati", "mix"), ("kard", "did")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("collective answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_57 : Datum :=
  { id := "alonsoovallemoghiseh2025b_57"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(57)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya che rang-i (ro) baham ghati kard?"
    glossedTokens := [("Roya", "Roya"), ("che", "what"), ("rang-i", "color-IND"), ("(ro)", "(ACC)"), ("baham", "together"), ("ghati", "mix"), ("kard", "did")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "SCI")] }

def ex_60 : Datum :=
  { id := "alonsoovallemoghiseh2025b_60"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(60)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya fahmid Forood bayad chi bexar-e."
    glossedTokens := [("Roya", "Roya"), ("fahmid", "found.out"), ("Forood", "Forood"), ("bayad", "must"), ("chi", "what.SG"), ("bexar-e", "buy.3SG")]
    context := "Forood must buy one of two things / books. He is not required to buy either but permitted to do so. Roya found out that this is the case."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("type", "SBI")] }

def ex_61 : Datum :=
  { id := "alonsoovallemoghiseh2025b_61"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(61)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya fahmid Forood bayad che ketab-i bexar-e."
    glossedTokens := [("Roya", "Roya"), ("fahmid", "found.out"), ("Forood", "Forood"), ("bayad", "must"), ("che", "what"), ("ketab-i", "book.SG.INDEF"), ("bexar-e", "buy.3SG")]
    context := "Forood must buy one of two things / books. He is not required to buy either but permitted to do so. Roya found out that this is the case."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("type", "SCI")] }

def ex_62 : Datum :=
  { id := "alonsoovallemoghiseh2025b_62"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(62)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya fahmid Forood bayad chi ro bexar-e."
    glossedTokens := [("Roya", "Roya"), ("fahmid", "found.out"), ("Forood", "Forood"), ("bayad", "must"), ("chi", "what.SG"), ("ro", "ACC"), ("bexar-e", "buy.3SG")]
    context := "Forood must buy one of two things / books. He is not required to buy either but permitted to do so. Roya found out that this is the case."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "SBI")] }

def ex_63 : Datum :=
  { id := "alonsoovallemoghiseh2025b_63"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(63)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya fahmid Forood bayad che ketab-i ro bexar-e."
    glossedTokens := [("Roya", "Roya"), ("fahmid", "found.out"), ("Forood", "Forood"), ("bayad", "must"), ("che", "what"), ("ketab-i", "book.SG.INDEF"), ("ro", "ACC"), ("bexar-e", "buy.3SG")]
    context := "Forood must buy one of two things / books. He is not required to buy either but permitted to do so. Roya found out that this is the case."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "SCI")] }

def ex_64 : Datum :=
  { id := "alonsoovallemoghiseh2025b_64"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(64)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Forood bayad chi ro bexar-e?"
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("chi", "what.SG"), ("ro", "ACC"), ("bexar-e", "buy.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice answer", .acceptable)]
    paperFeatures := [("type", "SBI")] }

def ex_65 : Datum :=
  { id := "alonsoovallemoghiseh2025b_65"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(65)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Forood bayad che ketab-i ro bexar-e?"
    glossedTokens := [("Forood", "Forood"), ("bayad", "must"), ("che", "what"), ("ketab-i", "book.SG.INDEF"), ("ro", "ACC"), ("bexar-e", "buy.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free choice answer", .acceptable)]
    paperFeatures := [("type", "SCI")] }

def ex_66 : Datum :=
  { id := "alonsoovallemoghiseh2025b_66"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(66)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz chi (ro) xarid."
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("chi", "what.SG"), ("(ro)", "(ACC)"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Maybe this thing", .acceptable), ("Maybe this thing and that thing", .acceptable)]
    paperFeatures := [("type", "SBI"), ("use", "epistemic indefinite")] }

def ex_67 : Datum :=
  { id := "alonsoovallemoghiseh2025b_67"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(67)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz che ketab-i (ro) xarid."
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("che", "what"), ("ketab-i", "book.SG.INDEF"), ("(ro)", "(ACC)"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Maybe this book", .acceptable), ("Maybe this book and that book", .unacceptable)]
    paperFeatures := [("type", "SCI"), ("use", "epistemic indefinite")] }

def ex_69 : Datum :=
  { id := "alonsoovallemoghiseh2025b_69"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(69)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Forood faramoosh kard-e kodoom ketab ro xarid-e."
    glossedTokens := [("Forood", "Forood"), ("faramoosh", "forget"), ("kard-e", "did.3SG"), ("kodoom", "which"), ("ketab", "book.SG"), ("ro", "ACC"), ("xarid-e", "bought.3SG")]
    context := "Forood looks confused. Ava sees him and asks Roya what is going on. Roya replies:"
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "which CI"), ("property", "D-linked")] }

def ex_70a : Datum :=
  { id := "alonsoovallemoghiseh2025b_70a"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(70a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz kodoom ketab xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("kodoom", "which"), ("ketab", "book.SG"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("type", "which CI")] }

def ex_70b : Datum :=
  { id := "alonsoovallemoghiseh2025b_70b"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(70b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya diruz kodoom ketab ro xarid?"
    glossedTokens := [("Roya", "Roya"), ("diruz", "yesterday"), ("kodoom", "which"), ("ketab", "book.SG"), ("ro", "ACC"), ("xarid", "bought.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("singular answer", .acceptable), ("plural answer", .unacceptable)]
    paperFeatures := [("type", "which CI")] }

def ex_73 : Datum :=
  { id := "alonsoovallemoghiseh2025b_73"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(73)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya fahmid Forood bayad kodoom ketab ro bexar-e."
    glossedTokens := [("Roya", "Roya"), ("fahmid", "found.out"), ("Forood", "Forood"), ("bayad", "must"), ("kodoom", "which"), ("ketab", "book.SG"), ("ro", "ACC"), ("bexar-e", "buy.3SG")]
    context := "Forood must buy one of two books. He is not required to buy either but permitted to do so. Roya found out that this is the case."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("type", "which CI"), ("inference", "free choice")] }

def ex_74 : Datum :=
  { id := "alonsoovallemoghiseh2025b_74"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(74)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Roya found out which book Forood must buy."
    glossedTokens := []
    context := "Forood must buy one of two books. He is not required to buy either but permitted to do so. Roya found out that this is the case."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "which CI")] }

def ex_75 : Datum :=
  { id := "alonsoovallemoghiseh2025b_75"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "(75)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Roya fahmid Forood bayad kodoom ketab-æ ro bexar-e."
    glossedTokens := [("Roya", "Roya"), ("fahmid", "found.out"), ("Forood", "Forood"), ("bayad", "must"), ("kodoom", "which"), ("ketab-æ", "book.SG-æ"), ("ro", "ACC"), ("bexar-e", "buy.3SG")]
    context := "Forood must buy one of two books. He is not required to buy either but permitted to do so. Roya found out that this is the case."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("type", "which CI")] }

def fn2 : Datum :=
  { id := "alonsoovallemoghiseh2025b_fn2"
    source := ⟨"alonso-ovalle-moghiseh-2025b", "fn. 2 (i)"⟩
    reportedIn := none
    method := some .elicitation
    language := "west2369"
    primaryText := "Chi az roo miz oftad?"
    glossedTokens := [("Chi", "what.SG"), ("az", "from"), ("roo", "top"), ("miz", "table"), ("oftad", "fell.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("type", "SBI"), ("agreement", "singular")] }

def all : List Datum := [ex_1, ex_2, ex_7, ex_20, ex_21, ex_16, ex_17, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27, ex_28, ex_30, ex_31, ex_47, ex_56, ex_57, ex_60, ex_61, ex_62, ex_63, ex_64, ex_65, ex_66, ex_67, ex_69, ex_70a, ex_70b, ex_73, ex_74, ex_75, fn2]

end AlonsoOvalleMoghiseh2025b.Examples
