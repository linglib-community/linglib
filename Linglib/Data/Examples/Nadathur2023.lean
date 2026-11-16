module

public import Linglib.Data.Examples.Schema

/-!
# `Nadathur2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Nadathur2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Nadathur2023.Examples`.
-/

@[expose] public section

namespace Nadathur2023.Examples

def ex_2a : Datum :=
  { id := "nadathur2023_2a"
    source := ⟨"nadathur-2023-implicatives", "(2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman onnistu-i kuitenkin pakenema-an."
    glossedTokens := [("Eman", "Eman"), ("onnistu-i", "succeed-PST.3SG"), ("kuitenkin", "however"), ("pakenema-an", "flee-INF.ILL")]
    glossedWords := [⟨[['E', 'm', 'a', 'n']], [['E', 'm', 'a', 'n']]⟩, ⟨[['o', 'n', 'n', 'i', 's', 't', 'u'], ['i']], [['s', 'u', 'c', 'c', 'e', 'e', 'd'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['k', 'u', 'i', 't', 'e', 'n', 'k', 'i', 'n']], [['h', 'o', 'w', 'e', 'v', 'e', 'r']]⟩, ⟨[['p', 'a', 'k', 'e', 'n', 'e', 'm', 'a'], ['a', 'n']], [['f', 'l', 'e', 'e'], ['I', 'N', 'F', '.', 'I', 'L', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "positive"), ("entails", "complement")] }

def ex_2b : Datum :=
  { id := "nadathur2023_2b"
    source := ⟨"nadathur-2023-implicatives", "(2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman e-i onnistu-nut kuitenkaan pakenema-an."
    glossedTokens := [("Eman", "Eman"), ("e-i", "NEG-3SG"), ("onnistu-nut", "succeed-SG.PP"), ("kuitenkaan", "however"), ("pakenema-an", "flee-INF.ILL")]
    glossedWords := [⟨[['E', 'm', 'a', 'n']], [['E', 'm', 'a', 'n']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['o', 'n', 'n', 'i', 's', 't', 'u'], ['n', 'u', 't']], [['s', 'u', 'c', 'c', 'e', 'e', 'd'], ['S', 'G', '.', 'P', 'P']]⟩, ⟨[['k', 'u', 'i', 't', 'e', 'n', 'k', 'a', 'a', 'n']], [['h', 'o', 'w', 'e', 'v', 'e', 'r']]⟩, ⟨[['p', 'a', 'k', 'e', 'n', 'e', 'm', 'a'], ['a', 'n']], [['f', 'l', 'e', 'e'], ['I', 'N', 'F', '.', 'I', 'L', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "negated"), ("entails", "negation")] }

def ex_4a : Datum :=
  { id := "nadathur2023_4a"
    source := ⟨"nadathur-2023-implicatives", "(4a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno uskals-i avat-a ove-n."
    glossedTokens := [("Juno", "Juno"), ("uskals-i", "dare-PST.3SG"), ("avat-a", "open-INF"), ("ove-n", "door-GEN/ACC")]
    glossedWords := [⟨[['J', 'u', 'n', 'o']], [['J', 'u', 'n', 'o']]⟩, ⟨[['u', 's', 'k', 'a', 'l', 's'], ['i']], [['d', 'a', 'r', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['a', 'v', 'a', 't'], ['a']], [['o', 'p', 'e', 'n'], ['I', 'N', 'F']]⟩, ⟨[['o', 'v', 'e'], ['n']], [['d', 'o', 'o', 'r'], ['G', 'E', 'N', '/', 'A', 'C', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_4b : Datum :=
  { id := "nadathur2023_4b"
    source := ⟨"nadathur-2023-implicatives", "(4b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i uskalta-nut avat-a ove-a."
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("uskalta-nut", "dare-SG.PP"), ("avat-a", "open-INF"), ("ove-a", "door-PART")]
    glossedWords := [⟨[['J', 'u', 'n', 'o']], [['J', 'u', 'n', 'o']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['u', 's', 'k', 'a', 'l', 't', 'a'], ['n', 'u', 't']], [['d', 'a', 'r', 'e'], ['S', 'G', '.', 'P', 'P']]⟩, ⟨[['a', 'v', 'a', 't'], ['a']], [['o', 'p', 'e', 'n'], ['I', 'N', 'F']]⟩, ⟨[['o', 'v', 'e'], ['a']], [['d', 'o', 'o', 'r'], ['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_5a : Datum :=
  { id := "nadathur2023_5a"
    source := ⟨"nadathur-2023-implicatives", "(5a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo jakso-i noust-a."
    glossedTokens := [("Sampo", "Sampo"), ("jakso-i", "have.strength-PST.3SG"), ("noust-a", "rise-INF")]
    glossedWords := [⟨[['S', 'a', 'm', 'p', 'o']], [['S', 'a', 'm', 'p', 'o']]⟩, ⟨[['j', 'a', 'k', 's', 'o'], ['i']], [['h', 'a', 'v', 'e', '.', 's', 't', 'r', 'e', 'n', 'g', 't', 'h'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['n', 'o', 'u', 's', 't'], ['a']], [['r', 'i', 's', 'e'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_5b : Datum :=
  { id := "nadathur2023_5b"
    source := ⟨"nadathur-2023-implicatives", "(5b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo e-i jaksa-nut noust-a."
    glossedTokens := [("Sampo", "Sampo"), ("e-i", "NEG-3SG"), ("jaksa-nut", "have.strength-PP.SG"), ("noust-a", "rise-INF")]
    glossedWords := [⟨[['S', 'a', 'm', 'p', 'o']], [['S', 'a', 'm', 'p', 'o']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['j', 'a', 'k', 's', 'a'], ['n', 'u', 't']], [['h', 'a', 'v', 'e', '.', 's', 't', 'r', 'e', 'n', 'g', 't', 'h'], ['P', 'P', '.', 'S', 'G']]⟩, ⟨[['n', 'o', 'u', 's', 't'], ['a']], [['r', 'i', 's', 'e'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_10a : Datum :=
  { id := "nadathur2023_10a"
    source := ⟨"nadathur-2023-implicatives", "(10a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän viits-i vastat-a."
    glossedTokens := [("Hän", "he.NOM"), ("viits-i", "bother-PST.3SG"), ("vastat-a", "answer-INF")]
    glossedWords := [⟨[['H', 'ä', 'n']], [['h', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['v', 'i', 'i', 't', 's'], ['i']], [['b', 'o', 't', 'h', 'e', 'r'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['v', 'a', 's', 't', 'a', 't'], ['a']], [['a', 'n', 's', 'w', 'e', 'r'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "positive"), ("entails", "complement")] }

def ex_10b : Datum :=
  { id := "nadathur2023_10b"
    source := ⟨"nadathur-2023-implicatives", "(10b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i viitsi-nyt vastat-a."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("viitsi-nyt", "bother-PP.SG"), ("vastat-a", "answer-INF")]
    glossedWords := [⟨[['H', 'ä', 'n']], [['h', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['v', 'i', 'i', 't', 's', 'i'], ['n', 'y', 't']], [['b', 'o', 't', 'h', 'e', 'r'], ['P', 'P', '.', 'S', 'G']]⟩, ⟨[['v', 'a', 's', 't', 'a', 't'], ['a']], [['a', 'n', 's', 'w', 'e', 'r'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "negated"), ("entails", "negation")] }

def ex_11a : Datum :=
  { id := "nadathur2023_11a"
    source := ⟨"nadathur-2023-implicatives", "(11a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja maltto-i odotta-a."
    glossedTokens := [("Marja", "Marja"), ("maltto-i", "have.patience-PST.3SG"), ("odotta-a", "wait-INF")]
    glossedWords := [⟨[['M', 'a', 'r', 'j', 'a']], [['M', 'a', 'r', 'j', 'a']]⟩, ⟨[['m', 'a', 'l', 't', 't', 'o'], ['i']], [['h', 'a', 'v', 'e', '.', 'p', 'a', 't', 'i', 'e', 'n', 'c', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['o', 'd', 'o', 't', 't', 'a'], ['a']], [['w', 'a', 'i', 't'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_11b : Datum :=
  { id := "nadathur2023_11b"
    source := ⟨"nadathur-2023-implicatives", "(11b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja e-i maltta-nut odotta-a."
    glossedTokens := [("Marja", "Marja"), ("e-i", "NEG-3SG"), ("maltta-nut", "have.patience-SG.PP"), ("odotta-a", "wait-INF")]
    glossedWords := [⟨[['M', 'a', 'r', 'j', 'a']], [['M', 'a', 'r', 'j', 'a']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['m', 'a', 'l', 't', 't', 'a'], ['n', 'u', 't']], [['h', 'a', 'v', 'e', '.', 'p', 'a', 't', 'i', 'e', 'n', 'c', 'e'], ['S', 'G', '.', 'P', 'P']]⟩, ⟨[['o', 'd', 'o', 't', 't', 'a'], ['a']], [['w', 'a', 'i', 't'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_27a : Datum :=
  { id := "nadathur2023_27a"
    source := ⟨"nadathur-2023-implicatives", "(27a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän henno-i tappa-a kissa-n."
    glossedTokens := [("Hän", "he.NOM"), ("henno-i", "have.heart-PST.3SG"), ("tappa-a", "kill-INF"), ("kissa-n", "cat-GEN/ACC")]
    glossedWords := [⟨[['H', 'ä', 'n']], [['h', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'e', 'n', 'n', 'o'], ['i']], [['h', 'a', 'v', 'e', '.', 'h', 'e', 'a', 'r', 't'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['t', 'a', 'p', 'p', 'a'], ['a']], [['k', 'i', 'l', 'l'], ['I', 'N', 'F']]⟩, ⟨[['k', 'i', 's', 's', 'a'], ['n']], [['c', 'a', 't'], ['G', 'E', 'N', '/', 'A', 'C', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_27b : Datum :=
  { id := "nadathur2023_27b"
    source := ⟨"nadathur-2023-implicatives", "(27b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i henno-nut tappa-a kissa-a."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("henno-nut", "have.heart-SG.PP"), ("tappa-a", "kill-INF"), ("kissa-a", "cat-PART")]
    glossedWords := [⟨[['H', 'ä', 'n']], [['h', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['h', 'e', 'n', 'n', 'o'], ['n', 'u', 't']], [['h', 'a', 'v', 'e', '.', 'h', 'e', 'a', 'r', 't'], ['S', 'G', '.', 'P', 'P']]⟩, ⟨[['t', 'a', 'p', 'p', 'a'], ['a']], [['k', 'i', 'l', 'l'], ['I', 'N', 'F']]⟩, ⟨[['k', 'i', 's', 's', 'a'], ['a']], [['c', 'a', 't'], ['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_29a : Datum :=
  { id := "nadathur2023_29a"
    source := ⟨"nadathur-2023-implicatives", "(29a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit pysty-i tappelema-an."
    glossedTokens := [("Maarit", "Maarit"), ("pysty-i", "able-PST.3SG"), ("tappelema-an", "fight-INF")]
    glossedWords := [⟨[['M', 'a', 'a', 'r', 'i', 't']], [['M', 'a', 'a', 'r', 'i', 't']]⟩, ⟨[['p', 'y', 's', 't', 'y'], ['i']], [['a', 'b', 'l', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['t', 'a', 'p', 'p', 'e', 'l', 'e', 'm', 'a'], ['a', 'n']], [['f', 'i', 'g', 'h', 't'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_29b : Datum :=
  { id := "nadathur2023_29b"
    source := ⟨"nadathur-2023-implicatives", "(29b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit e-i pysty-nyt tappelema-an."
    glossedTokens := [("Maarit", "Maarit"), ("e-i", "NEG-3SG"), ("pysty-nyt", "able-SG.PP"), ("tappelema-an", "fight-INF")]
    glossedWords := [⟨[['M', 'a', 'a', 'r', 'i', 't']], [['M', 'a', 'a', 'r', 'i', 't']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['p', 'y', 's', 't', 'y'], ['n', 'y', 't']], [['a', 'b', 'l', 'e'], ['S', 'G', '.', 'P', 'P']]⟩, ⟨[['t', 'a', 'p', 'p', 'e', 'l', 'e', 'm', 'a'], ['a', 'n']], [['f', 'i', 'g', 'h', 't'], ['I', 'N', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "negated"), ("entails", "negation")] }

def ex_30a : Datum :=
  { id := "nadathur2023_30a"
    source := ⟨"nadathur-2023-implicatives", "(30a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija mahtu-i kulke-ma-an ove-sta."
    glossedTokens := [("Freija", "Freija"), ("mahtu-i", "fit-PST.3SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    glossedWords := [⟨[['F', 'r', 'e', 'i', 'j', 'a']], [['F', 'r', 'e', 'i', 'j', 'a']]⟩, ⟨[['m', 'a', 'h', 't', 'u'], ['i']], [['f', 'i', 't'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['k', 'u', 'l', 'k', 'e'], ['m', 'a'], ['a', 'n']], [['g', 'o'], ['I', 'N', 'F'], ['I', 'L', 'L']]⟩, ⟨[['o', 'v', 'e'], ['s', 't', 'a']], [['d', 'o', 'o', 'r'], ['E', 'L', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_30b : Datum :=
  { id := "nadathur2023_30b"
    source := ⟨"nadathur-2023-implicatives", "(30b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija e-i mahtu-nut kulke-ma-an ove-sta."
    glossedTokens := [("Freija", "Freija"), ("e-i", "NEG-3SG"), ("mahtu-nut", "fit-PP.SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    glossedWords := [⟨[['F', 'r', 'e', 'i', 'j', 'a']], [['F', 'r', 'e', 'i', 'j', 'a']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['m', 'a', 'h', 't', 'u'], ['n', 'u', 't']], [['f', 'i', 't'], ['P', 'P', '.', 'S', 'G']]⟩, ⟨[['k', 'u', 'l', 'k', 'e'], ['m', 'a'], ['a', 'n']], [['g', 'o'], ['I', 'N', 'F'], ['I', 'L', 'L']]⟩, ⟨[['o', 'v', 'e'], ['s', 't', 'a']], [['d', 'o', 'o', 'r'], ['E', 'L', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "negated"), ("entails", "negation")] }

def ex_44a : Datum :=
  { id := "nadathur2023_44a"
    source := ⟨"nadathur-2023-implicatives", "(44a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän laiminlö-i korjat-a virhee-n."
    glossedTokens := [("Hän", "he.NOM"), ("laiminlö-i", "neglect-PST.3SG"), ("korjat-a", "repair-INF"), ("virhee-n", "error-GEN/ACC")]
    glossedWords := [⟨[['H', 'ä', 'n']], [['h', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['l', 'a', 'i', 'm', 'i', 'n', 'l', 'ö'], ['i']], [['n', 'e', 'g', 'l', 'e', 'c', 't'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['k', 'o', 'r', 'j', 'a', 't'], ['a']], [['r', 'e', 'p', 'a', 'i', 'r'], ['I', 'N', 'F']]⟩, ⟨[['v', 'i', 'r', 'h', 'e', 'e'], ['n']], [['e', 'r', 'r', 'o', 'r'], ['G', 'E', 'N', '/', 'A', 'C', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "positive"), ("entails", "negation")] }

def ex_44b : Datum :=
  { id := "nadathur2023_44b"
    source := ⟨"nadathur-2023-implicatives", "(44b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i laiminlyö-nyt korjat-a virhe-ttä."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("laiminlyö-nyt", "neglect-PP.SG"), ("korjat-a", "repair-INF"), ("virhe-ttä", "error-PART")]
    glossedWords := [⟨[['H', 'ä', 'n']], [['h', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['l', 'a', 'i', 'm', 'i', 'n', 'l', 'y', 'ö'], ['n', 'y', 't']], [['n', 'e', 'g', 'l', 'e', 'c', 't'], ['P', 'P', '.', 'S', 'G']]⟩, ⟨[['k', 'o', 'r', 'j', 'a', 't'], ['a']], [['r', 'e', 'p', 'a', 'i', 'r'], ['I', 'N', 'F']]⟩, ⟨[['v', 'i', 'r', 'h', 'e'], ['t', 't', 'ä']], [['e', 'r', 'r', 'o', 'r'], ['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "negated"), ("entails", "complement")] }

def ex_46a : Datum :=
  { id := "nadathur2023_46a"
    source := ⟨"nadathur-2023-implicatives", "(46a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno epärö-i otta-a osa-a kilpailu-un."
    glossedTokens := [("Juno", "Juno"), ("epärö-i", "hesitate-PST.3SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    glossedWords := [⟨[['J', 'u', 'n', 'o']], [['J', 'u', 'n', 'o']]⟩, ⟨[['e', 'p', 'ä', 'r', 'ö'], ['i']], [['h', 'e', 's', 'i', 't', 'a', 't', 'e'], ['P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['o', 't', 't', 'a'], ['a']], [['t', 'a', 'k', 'e'], ['I', 'N', 'F']]⟩, ⟨[['o', 's', 'a'], ['a']], [['p', 'a', 'r', 't'], ['P', 'A', 'R', 'T']]⟩, ⟨[['k', 'i', 'l', 'p', 'a', 'i', 'l', 'u'], ['u', 'n']], [['r', 'a', 'c', 'e'], ['I', 'L', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_46b : Datum :=
  { id := "nadathur2023_46b"
    source := ⟨"nadathur-2023-implicatives", "(46b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i epäröi-nyt otta-a osa-a kilpailu-un."
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("epäröi-nyt", "hesitate-PP.SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    glossedWords := [⟨[['J', 'u', 'n', 'o']], [['J', 'u', 'n', 'o']]⟩, ⟨[['e'], ['i']], [['N', 'E', 'G'], ['3', 'S', 'G']]⟩, ⟨[['e', 'p', 'ä', 'r', 'ö', 'i'], ['n', 'y', 't']], [['h', 'e', 's', 'i', 't', 'a', 't', 'e'], ['P', 'P', '.', 'S', 'G']]⟩, ⟨[['o', 't', 't', 'a'], ['a']], [['t', 'a', 'k', 'e'], ['I', 'N', 'F']]⟩, ⟨[['o', 's', 'a'], ['a']], [['p', 'a', 'r', 't'], ['P', 'A', 'R', 'T']]⟩, ⟨[['k', 'i', 'l', 'p', 'a', 'i', 'l', 'u'], ['u', 'n']], [['r', 'a', 'c', 'e'], ['I', 'L', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "negated"), ("entails", "complement")] }

def all : List Datum := [ex_2a, ex_2b, ex_4a, ex_4b, ex_5a, ex_5b, ex_10a, ex_10b, ex_11a, ex_11b, ex_27a, ex_27b, ex_29a, ex_29b, ex_30a, ex_30b, ex_44a, ex_44b, ex_46a, ex_46b]

end Nadathur2023.Examples
