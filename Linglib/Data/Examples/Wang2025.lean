module

public import Linglib.Data.Examples.Schema

/-!
# `Wang2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Wang2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wang2025.Examples`.
-/

@[expose] public section

namespace Wang2025.Examples

def ex_3_4 : Datum :=
  { id := "wang2025_3_4"
    source := ⟨"wang-2025", "Ch. 3 (4)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan ye zai jichang chi le wanfan."
    glossedTokens := [("Zhangsan", "Zhangsan"), ("ye", "also"), ("zai", "at"), ("jichang", "airport"), ("chi", "eat"), ("le", "LE"), ("wanfan", "dinner")]
    glossedWords := [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['y', 'e'], ['a', 'l', 's', 'o'], [⟨['y', 'e'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['z', 'a', 'i'], ['a', 't'], [⟨['z', 'a', 'i'], ['a', 't'], none⟩]⟩, ⟨['j', 'i', 'c', 'h', 'a', 'n', 'g'], ['a', 'i', 'r', 'p', 'o', 'r', 't'], [⟨['j', 'i', 'c', 'h', 'a', 'n', 'g'], ['a', 'i', 'r', 'p', 'o', 'r', 't'], none⟩]⟩, ⟨['c', 'h', 'i'], ['e', 'a', 't'], [⟨['c', 'h', 'i'], ['e', 'a', 't'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['w', 'a', 'n', 'f', 'a', 'n'], ['d', 'i', 'n', 'n', 'e', 'r'], [⟨['w', 'a', 'n', 'f', 'a', 'n'], ['d', 'i', 'n', 'n', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ye"), ("focus", "Zhangsan")] }

def ex_3_39 : Datum :=
  { id := "wang2025_3_39"
    source := ⟨"wang-2025", "Ch. 3 (39)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan mei lai. Lisi fan'er lai le."
    glossedTokens := [("Zhangsan", "Zhangsan"), ("mei", "not"), ("lai", "come"), ("Lisi", "Lisi"), ("fan'er", "instead"), ("lai", "come"), ("le", "LE")]
    glossedWords := [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['m', 'e', 'i'], ['n', 'o', 't'], [⟨['m', 'e', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], [⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], [⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], none⟩]⟩, ⟨['f', 'a', 'n', '\'', 'e', 'r'], ['i', 'n', 's', 't', 'e', 'a', 'd'], [⟨['f', 'a', 'n', '\'', 'e', 'r'], ['i', 'n', 's', 't', 'e', 'a', 'd'], none⟩]⟩, ⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], [⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "fan'er"), ("focus", "Lisi")] }

def ex_3_40 : Datum :=
  { id := "wang2025_3_40"
    source := ⟨"wang-2025", "Ch. 3 (40)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Lisi mei qu gongyuan. Ta fan'er qu le xuexiao."
    glossedTokens := [("Lisi", "Lisi"), ("mei", "not"), ("qu", "go"), ("gongyuan", "park"), ("Ta", "he"), ("fan'er", "instead"), ("qu", "go"), ("le", "LE"), ("xuexiao", "school")]
    glossedWords := [⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], [⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], none⟩]⟩, ⟨['m', 'e', 'i'], ['n', 'o', 't'], [⟨['m', 'e', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['q', 'u'], ['g', 'o'], [⟨['q', 'u'], ['g', 'o'], none⟩]⟩, ⟨['g', 'o', 'n', 'g', 'y', 'u', 'a', 'n'], ['p', 'a', 'r', 'k'], [⟨['g', 'o', 'n', 'g', 'y', 'u', 'a', 'n'], ['p', 'a', 'r', 'k'], none⟩]⟩, ⟨['T', 'a'], ['h', 'e'], [⟨['T', 'a'], ['h', 'e'], none⟩]⟩, ⟨['f', 'a', 'n', '\'', 'e', 'r'], ['i', 'n', 's', 't', 'e', 'a', 'd'], [⟨['f', 'a', 'n', '\'', 'e', 'r'], ['i', 'n', 's', 't', 'e', 'a', 'd'], none⟩]⟩, ⟨['q', 'u'], ['g', 'o'], [⟨['q', 'u'], ['g', 'o'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['x', 'u', 'e', 'x', 'i', 'a', 'o'], ['s', 'c', 'h', 'o', 'o', 'l'], [⟨['x', 'u', 'e', 'x', 'i', 'a', 'o'], ['s', 'c', 'h', 'o', 'o', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "fan'er"), ("focus", "xuexiao")] }

def ex_4_35a : Datum :=
  { id := "wang2025_4_35a"
    source := ⟨"wang-2025", "Ch. 4 (35a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Yaome Zhangsan chi le binggan, yaome ta chi le dangao."
    glossedTokens := [("Yaome", "or"), ("Zhangsan", "Zhangsan"), ("chi", "eat"), ("le", "LE"), ("binggan", "cookie"), ("yaome", "or"), ("ta", "he"), ("chi", "eat"), ("le", "LE"), ("dangao", "cake")]
    glossedWords := [⟨['Y', 'a', 'o', 'm', 'e'], ['o', 'r'], [⟨['Y', 'a', 'o', 'm', 'e'], ['o', 'r'], none⟩]⟩, ⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['c', 'h', 'i'], ['e', 'a', 't'], [⟨['c', 'h', 'i'], ['e', 'a', 't'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['b', 'i', 'n', 'g', 'g', 'a', 'n'], ['c', 'o', 'o', 'k', 'i', 'e'], [⟨['b', 'i', 'n', 'g', 'g', 'a', 'n'], ['c', 'o', 'o', 'k', 'i', 'e'], none⟩]⟩, ⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], [⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['c', 'h', 'i'], ['e', 'a', 't'], [⟨['c', 'h', 'i'], ['e', 'a', 't'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['d', 'a', 'n', 'g', 'a', 'o'], ['c', 'a', 'k', 'e'], [⟨['d', 'a', 'n', 'g', 'a', 'o'], ['c', 'a', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "yaome-yaome")] }

def ex_4_35b : Datum :=
  { id := "wang2025_4_35b"
    source := ⟨"wang-2025", "Ch. 4 (35b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni yaome keyi chi binggan, yaome keyi chi dangao."
    glossedTokens := [("Ni", "you"), ("yaome", "or"), ("keyi", "can"), ("chi", "eat"), ("binggan", "cookie"), ("yaome", "or"), ("keyi", "can"), ("chi", "eat"), ("dangao", "cake")]
    glossedWords := [⟨['N', 'i'], ['y', 'o', 'u'], [⟨['N', 'i'], ['y', 'o', 'u'], none⟩]⟩, ⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], [⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], none⟩]⟩, ⟨['k', 'e', 'y', 'i'], ['c', 'a', 'n'], [⟨['k', 'e', 'y', 'i'], ['c', 'a', 'n'], none⟩]⟩, ⟨['c', 'h', 'i'], ['e', 'a', 't'], [⟨['c', 'h', 'i'], ['e', 'a', 't'], none⟩]⟩, ⟨['b', 'i', 'n', 'g', 'g', 'a', 'n'], ['c', 'o', 'o', 'k', 'i', 'e'], [⟨['b', 'i', 'n', 'g', 'g', 'a', 'n'], ['c', 'o', 'o', 'k', 'i', 'e'], none⟩]⟩, ⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], [⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], none⟩]⟩, ⟨['k', 'e', 'y', 'i'], ['c', 'a', 'n'], [⟨['k', 'e', 'y', 'i'], ['c', 'a', 'n'], none⟩]⟩, ⟨['c', 'h', 'i'], ['e', 'a', 't'], [⟨['c', 'h', 'i'], ['e', 'a', 't'], none⟩]⟩, ⟨['d', 'a', 'n', 'g', 'a', 'o'], ['c', 'a', 'k', 'e'], [⟨['d', 'a', 'n', 'g', 'a', 'o'], ['c', 'a', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "yaome-yaome"), ("modal", "above disjunction")] }

def ex_4_35c : Datum :=
  { id := "wang2025_4_35c"
    source := ⟨"wang-2025", "Ch. 4 (35c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni keyi yaome chi binggan, yaome chi dangao."
    glossedTokens := [("Ni", "you"), ("keyi", "can"), ("yaome", "or"), ("chi", "eat"), ("binggan", "cookie"), ("yaome", "or"), ("chi", "eat"), ("dangao", "cake")]
    glossedWords := [⟨['N', 'i'], ['y', 'o', 'u'], [⟨['N', 'i'], ['y', 'o', 'u'], none⟩]⟩, ⟨['k', 'e', 'y', 'i'], ['c', 'a', 'n'], [⟨['k', 'e', 'y', 'i'], ['c', 'a', 'n'], none⟩]⟩, ⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], [⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], none⟩]⟩, ⟨['c', 'h', 'i'], ['e', 'a', 't'], [⟨['c', 'h', 'i'], ['e', 'a', 't'], none⟩]⟩, ⟨['b', 'i', 'n', 'g', 'g', 'a', 'n'], ['c', 'o', 'o', 'k', 'i', 'e'], [⟨['b', 'i', 'n', 'g', 'g', 'a', 'n'], ['c', 'o', 'o', 'k', 'i', 'e'], none⟩]⟩, ⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], [⟨['y', 'a', 'o', 'm', 'e'], ['o', 'r'], none⟩]⟩, ⟨['c', 'h', 'i'], ['e', 'a', 't'], [⟨['c', 'h', 'i'], ['e', 'a', 't'], none⟩]⟩, ⟨['d', 'a', 'n', 'g', 'a', 'o'], ['c', 'a', 'k', 'e'], [⟨['d', 'a', 'n', 'g', 'a', 'o'], ['c', 'a', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "yaome-yaome"), ("modal", "below disjunction")] }

def ex_4_36 : Datum :=
  { id := "wang2025_4_36"
    source := ⟨"wang-2025", "Ch. 4 (36)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan yexu qu le. Lisi qu le."
    glossedTokens := [("Zhangsan", "Zhangsan"), ("yexu", "maybe"), ("qu", "go"), ("le", "LE"), ("Lisi", "Lisi"), ("qu", "go"), ("le", "LE")]
    glossedWords := [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['y', 'e', 'x', 'u'], ['m', 'a', 'y', 'b', 'e'], [⟨['y', 'e', 'x', 'u'], ['m', 'a', 'y', 'b', 'e'], none⟩]⟩, ⟨['q', 'u'], ['g', 'o'], [⟨['q', 'u'], ['g', 'o'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], [⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], none⟩]⟩, ⟨['q', 'u'], ['g', 'o'], [⟨['q', 'u'], ['g', 'o'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A: Who went skiing? Did Zhangsan go?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "positive evidence"), ("trigger", "ye omitted")] }

def ex_4_42 : Datum :=
  { id := "wang2025_4_42"
    source := ⟨"wang-2025", "Ch. 4 (42)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan yexu qu le. Lisi qu le."
    glossedTokens := [("Zhangsan", "Zhangsan"), ("yexu", "possibly"), ("qu", "go"), ("le", "LE"), ("Lisi", "Lisi"), ("qu", "go"), ("le", "LE")]
    glossedWords := [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['y', 'e', 'x', 'u'], ['p', 'o', 's', 's', 'i', 'b', 'l', 'y'], [⟨['y', 'e', 'x', 'u'], ['p', 'o', 's', 's', 'i', 'b', 'l', 'y'], none⟩]⟩, ⟨['q', 'u'], ['g', 'o'], [⟨['q', 'u'], ['g', 'o'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], [⟨['L', 'i', 's', 'i'], ['L', 'i', 's', 'i'], none⟩]⟩, ⟨['q', 'u'], ['g', 'o'], [⟨['q', 'u'], ['g', 'o'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A: Who went skiing? Did Zhangsan go?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "positive evidence"), ("focus", "yexu")] }

def ex_4_45 : Datum :=
  { id := "wang2025_4_45"
    source := ⟨"wang-2025", "Ch. 4 (45)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan yexu yiqian zong chuchai. Xianzai ta buzai jingchang chuchai le."
    glossedTokens := [("Zhangsan", "Zhangsan"), ("yexu", "possibly"), ("yiqian", "past"), ("zong", "frequently"), ("chuchai", "on.business.trip"), ("Xianzai", "now"), ("ta", "he"), ("buzai", "not.anymore"), ("jingchang", "often"), ("chuchai", "on.business.trip"), ("le", "LE")]
    glossedWords := [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['y', 'e', 'x', 'u'], ['p', 'o', 's', 's', 'i', 'b', 'l', 'y'], [⟨['y', 'e', 'x', 'u'], ['p', 'o', 's', 's', 'i', 'b', 'l', 'y'], none⟩]⟩, ⟨['y', 'i', 'q', 'i', 'a', 'n'], ['p', 'a', 's', 't'], [⟨['y', 'i', 'q', 'i', 'a', 'n'], ['p', 'a', 's', 't'], none⟩]⟩, ⟨['z', 'o', 'n', 'g'], ['f', 'r', 'e', 'q', 'u', 'e', 'n', 't', 'l', 'y'], [⟨['z', 'o', 'n', 'g'], ['f', 'r', 'e', 'q', 'u', 'e', 'n', 't', 'l', 'y'], none⟩]⟩, ⟨['c', 'h', 'u', 'c', 'h', 'a', 'i'], ['o', 'n', '.', 'b', 'u', 's', 'i', 'n', 'e', 's', 's', '.', 't', 'r', 'i', 'p'], [⟨['c', 'h', 'u', 'c', 'h', 'a', 'i'], ['o', 'n', '.', 'b', 'u', 's', 'i', 'n', 'e', 's', 's', '.', 't', 'r', 'i', 'p'], none⟩]⟩, ⟨['X', 'i', 'a', 'n', 'z', 'a', 'i'], ['n', 'o', 'w'], [⟨['X', 'i', 'a', 'n', 'z', 'a', 'i'], ['n', 'o', 'w'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['b', 'u', 'z', 'a', 'i'], ['n', 'o', 't', '.', 'a', 'n', 'y', 'm', 'o', 'r', 'e'], [⟨['b', 'u', 'z', 'a', 'i'], ['n', 'o', 't', '.', 'a', 'n', 'y', 'm', 'o', 'r', 'e'], none⟩]⟩, ⟨['j', 'i', 'n', 'g', 'c', 'h', 'a', 'n', 'g'], ['o', 'f', 't', 'e', 'n'], [⟨['j', 'i', 'n', 'g', 'c', 'h', 'a', 'n', 'g'], ['o', 'f', 't', 'e', 'n'], none⟩]⟩, ⟨['c', 'h', 'u', 'c', 'h', 'a', 'i'], ['o', 'n', '.', 'b', 'u', 's', 'i', 'n', 'e', 's', 's', '.', 't', 'r', 'i', 'p'], [⟨['c', 'h', 'u', 'c', 'h', 'a', 'i'], ['o', 'n', '.', 'b', 'u', 's', 'i', 'n', 'e', 's', 's', '.', 't', 'r', 'i', 'p'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A: Did Zhangsan often go on business trips?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "buzai"), ("context", "positive evidence"), ("contrast", "polarity and time")] }

def all : List Datum := [ex_3_4, ex_3_39, ex_3_40, ex_4_35a, ex_4_35b, ex_4_35c, ex_4_36, ex_4_42, ex_4_45]

end Wang2025.Examples
