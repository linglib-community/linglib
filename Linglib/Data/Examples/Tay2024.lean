module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Tay2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Tay2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Tay2024.Examples`.
-/

@[expose] public section

namespace Tay2024.Examples

def ex_41 : Datum :=
  { id := "tay2024_41"
    source := ⟨"tay-2024", "(41), (43)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao fǎnfǎnfùfùde kū de māma xǐng-le."
    glossedTokens := [("Bǎobao", "baby"), ("fǎnfǎnfùfùde", "repeatedly"), ("kū", "cry"), ("de", "DE"), ("māma", "mother"), ("xǐng-le", "awake-PFV")]
    glossedWords := [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['f', 'ǎ', 'n', 'f', 'ǎ', 'n', 'f', 'ù', 'f', 'ù', 'd', 'e'], ['r', 'e', 'p', 'e', 'a', 't', 'e', 'd', 'l', 'y'], [⟨['f', 'ǎ', 'n', 'f', 'ǎ', 'n', 'f', 'ù', 'f', 'ù', 'd', 'e'], ['r', 'e', 'p', 'e', 'a', 't', 'e', 'd', 'l', 'y'], none⟩]⟩, ⟨['k', 'ū'], ['c', 'r', 'y'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['m', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['x', 'ǐ', 'n', 'g', '-', 'l', 'e'], ['a', 'w', 'a', 'k', 'e', '-', 'P', 'F', 'V'], [⟨['x', 'ǐ', 'n', 'g'], ['a', 'w', 'a', 'k', 'e'], none⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A V-de resultative modified by 'repeatedly'."
    judgment := .acceptable
    contrasts := []
    readings := [("the whole resultative is modified: repeated wakings", .acceptable), ("V1 alone is modified: the baby cried repeatedly until Mother woke once", .questionable)]
    paperFeatures := [] }

def ex_42 : Datum :=
  { id := "tay2024_42"
    source := ⟨"tay-2024", "(42), (44)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao fǎnfǎnfùfùde kū-xǐng-le māma."
    glossedTokens := [("Bǎobao", "baby"), ("fǎnfǎnfùfùde", "repeatedly"), ("kū-xǐng-le", "cry-awake-PFV"), ("māma", "mother")]
    glossedWords := [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['f', 'ǎ', 'n', 'f', 'ǎ', 'n', 'f', 'ù', 'f', 'ù', 'd', 'e'], ['r', 'e', 'p', 'e', 'a', 't', 'e', 'd', 'l', 'y'], [⟨['f', 'ǎ', 'n', 'f', 'ǎ', 'n', 'f', 'ù', 'f', 'ù', 'd', 'e'], ['r', 'e', 'p', 'e', 'a', 't', 'e', 'd', 'l', 'y'], none⟩]⟩, ⟨['k', 'ū', '-', 'x', 'ǐ', 'n', 'g', '-', 'l', 'e'], ['c', 'r', 'y', '-', 'a', 'w', 'a', 'k', 'e', '-', 'P', 'F', 'V'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩, ⟨['x', 'ǐ', 'n', 'g'], ['a', 'w', 'a', 'k', 'e'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['m', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A V-V resultative modified by 'repeatedly'."
    judgment := .acceptable
    contrasts := []
    readings := [("the whole resultative is modified: repeated wakings", .acceptable), ("V1 alone is modified: the baby cried repeatedly until Mother woke once", .ungrammatical)]
    paperFeatures := [] }

def ex_45 : Datum :=
  { id := "tay2024_45"
    source := ⟨"tay-2024", "(45)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao zài jiā lǐ kū de línjū xǐng-le."
    glossedTokens := [("Bǎobao", "baby"), ("zài", "at"), ("jiā", "house"), ("lǐ", "inside"), ("kū", "cry"), ("de", "DE"), ("línjū", "neighbour"), ("xǐng-le", "awake-PFV")]
    glossedWords := [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['z', 'à', 'i'], ['a', 't'], [⟨['z', 'à', 'i'], ['a', 't'], none⟩]⟩, ⟨['j', 'i', 'ā'], ['h', 'o', 'u', 's', 'e'], [⟨['j', 'i', 'ā'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['l', 'ǐ'], ['i', 'n', 's', 'i', 'd', 'e'], [⟨['l', 'ǐ'], ['i', 'n', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['k', 'ū'], ['c', 'r', 'y'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['l', 'í', 'n', 'j', 'ū'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r'], [⟨['l', 'í', 'n', 'j', 'ū'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r'], none⟩]⟩, ⟨['x', 'ǐ', 'n', 'g', '-', 'l', 'e'], ['a', 'w', 'a', 'k', 'e', '-', 'P', 'F', 'V'], [⟨['x', 'ǐ', 'n', 'g'], ['a', 'w', 'a', 'k', 'e'], none⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The baby cried at home until the neighbours woke up next door."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_46 : Datum :=
  { id := "tay2024_46"
    source := ⟨"tay-2024", "(46)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao zài jiā lǐ kū-xǐng-le línjū."
    glossedTokens := [("Bǎobao", "baby"), ("zài", "at"), ("jiā", "house"), ("lǐ", "inside"), ("kū-xǐng-le", "cry-awake-PFV"), ("línjū", "neighbour")]
    glossedWords := [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['z', 'à', 'i'], ['a', 't'], [⟨['z', 'à', 'i'], ['a', 't'], none⟩]⟩, ⟨['j', 'i', 'ā'], ['h', 'o', 'u', 's', 'e'], [⟨['j', 'i', 'ā'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['l', 'ǐ'], ['i', 'n', 's', 'i', 'd', 'e'], [⟨['l', 'ǐ'], ['i', 'n', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['k', 'ū', '-', 'x', 'ǐ', 'n', 'g', '-', 'l', 'e'], ['c', 'r', 'y', '-', 'a', 'w', 'a', 'k', 'e', '-', 'P', 'F', 'V'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩, ⟨['x', 'ǐ', 'n', 'g'], ['a', 'w', 'a', 'k', 'e'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['l', 'í', 'n', 'j', 'ū'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r'], [⟨['l', 'í', 'n', 'j', 'ū'], ['n', 'e', 'i', 'g', 'h', 'b', 'o', 'u', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The baby cried at home until the neighbours woke up next door."
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_107 : Datum :=
  { id := "tay2024_107"
    source := ⟨"tay-2024", "(107)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān shè-sǐ-le Lǐsì."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("shè-sǐ-le", "shoot-die-PFV"), ("Lǐsì", "Lisi")]
    glossedWords := [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['s', 'h', 'è', '-', 's', 'ǐ', '-', 'l', 'e'], ['s', 'h', 'o', 'o', 't', '-', 'd', 'i', 'e', '-', 'P', 'F', 'V'], [⟨['s', 'h', 'è'], ['s', 'h', 'o', 'o', 't'], none⟩, ⟨['s', 'ǐ'], ['d', 'i', 'e'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['L', 'ǐ', 's', 'ì'], ['L', 'i', 's', 'i'], [⟨['L', 'ǐ', 's', 'ì'], ['L', 'i', 's', 'i'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Zhangsan shoots Lisi, who is fatally wounded but does not die at once: the shooting and the dying overlap only at the moment the bullet makes contact."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_131 : Datum :=
  { id := "tay2024_131"
    source := ⟨"tay-2024", "(131)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Bǎobao kū-xǐng-le māma."
    glossedTokens := [("Bǎobao", "baby"), ("kū-xǐng-le", "cry-awake-PFV"), ("māma", "mother")]
    glossedWords := [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], [⟨['B', 'ǎ', 'o', 'b', 'a', 'o'], ['b', 'a', 'b', 'y'], none⟩]⟩, ⟨['k', 'ū', '-', 'x', 'ǐ', 'n', 'g', '-', 'l', 'e'], ['c', 'r', 'y', '-', 'a', 'w', 'a', 'k', 'e', '-', 'P', 'F', 'V'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩, ⟨['x', 'ǐ', 'n', 'g'], ['a', 'w', 'a', 'k', 'e'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['m', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_132 : Datum :=
  { id := "tay2024_132"
    source := ⟨"tay-2024", "(132)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wǒ qiē-suì-le yángcōng."
    glossedTokens := [("Wǒ", "I"), ("qiē-suì-le", "cut-in.pieces-PFV"), ("yángcōng", "onion")]
    glossedWords := [⟨['W', 'ǒ'], ['I'], [⟨['W', 'ǒ'], ['I'], none⟩]⟩, ⟨['q', 'i', 'ē', '-', 's', 'u', 'ì', '-', 'l', 'e'], ['c', 'u', 't', '-', 'i', 'n', '.', 'p', 'i', 'e', 'c', 'e', 's', '-', 'P', 'F', 'V'], [⟨['q', 'i', 'ē'], ['c', 'u', 't'], none⟩, ⟨['s', 'u', 'ì'], ['i', 'n', '.', 'p', 'i', 'e', 'c', 'e', 's'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['y', 'á', 'n', 'g', 'c', 'ō', 'n', 'g'], ['o', 'n', 'i', 'o', 'n'], [⟨['y', 'á', 'n', 'g', 'c', 'ō', 'n', 'g'], ['o', 'n', 'i', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_133 : Datum :=
  { id := "tay2024_133"
    source := ⟨"tay-2024", "(133)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Mìyǔ xià-hēi-le tiāndì."
    glossedTokens := [("Mìyǔ", "dense.rain"), ("xià-hēi-le", "fall-black-PFV"), ("tiāndì", "earth")]
    glossedWords := [⟨['M', 'ì', 'y', 'ǔ'], ['d', 'e', 'n', 's', 'e', '.', 'r', 'a', 'i', 'n'], [⟨['M', 'ì', 'y', 'ǔ'], ['d', 'e', 'n', 's', 'e', '.', 'r', 'a', 'i', 'n'], none⟩]⟩, ⟨['x', 'i', 'à', '-', 'h', 'ē', 'i', '-', 'l', 'e'], ['f', 'a', 'l', 'l', '-', 'b', 'l', 'a', 'c', 'k', '-', 'P', 'F', 'V'], [⟨['x', 'i', 'à'], ['f', 'a', 'l', 'l'], none⟩, ⟨['h', 'ē', 'i'], ['b', 'l', 'a', 'c', 'k'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['t', 'i', 'ā', 'n', 'd', 'ì'], ['e', 'a', 'r', 't', 'h'], [⟨['t', 'i', 'ā', 'n', 'd', 'ì'], ['e', 'a', 'r', 't', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "theme")] }

def ex_134 : Datum :=
  { id := "tay2024_134"
    source := ⟨"tay-2024", "(134)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Yīfú xǐ-lèi-le jiějiě."
    glossedTokens := [("Yīfú", "clothes"), ("xǐ-lèi-le", "wash-tired-PFV"), ("jiějiě", "elder.sister")]
    glossedWords := [⟨['Y', 'ī', 'f', 'ú'], ['c', 'l', 'o', 't', 'h', 'e', 's'], [⟨['Y', 'ī', 'f', 'ú'], ['c', 'l', 'o', 't', 'h', 'e', 's'], none⟩]⟩, ⟨['x', 'ǐ', '-', 'l', 'è', 'i', '-', 'l', 'e'], ['w', 'a', 's', 'h', '-', 't', 'i', 'r', 'e', 'd', '-', 'P', 'F', 'V'], [⟨['x', 'ǐ'], ['w', 'a', 's', 'h'], none⟩, ⟨['l', 'è', 'i'], ['t', 'i', 'r', 'e', 'd'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'i', 'ě', 'j', 'i', 'ě'], ['e', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r'], [⟨['j', 'i', 'ě', 'j', 'i', 'ě'], ['e', 'l', 'd', 'e', 'r', '.', 's', 'i', 's', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "theme")] }

def ex_137 : Datum :=
  { id := "tay2024_137"
    source := ⟨"tay-2024", "(137)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Éjūn jī-chén-le yī sōu xúnyángjiàn."
    glossedTokens := [("Éjūn", "Russian.forces"), ("jī-chén-le", "strike-sink-PFV"), ("yī", "one"), ("sōu", "CLF"), ("xúnyángjiàn", "cruiser")]
    glossedWords := [⟨['É', 'j', 'ū', 'n'], ['R', 'u', 's', 's', 'i', 'a', 'n', '.', 'f', 'o', 'r', 'c', 'e', 's'], [⟨['É', 'j', 'ū', 'n'], ['R', 'u', 's', 's', 'i', 'a', 'n', '.', 'f', 'o', 'r', 'c', 'e', 's'], none⟩]⟩, ⟨['j', 'ī', '-', 'c', 'h', 'é', 'n', '-', 'l', 'e'], ['s', 't', 'r', 'i', 'k', 'e', '-', 's', 'i', 'n', 'k', '-', 'P', 'F', 'V'], [⟨['j', 'ī'], ['s', 't', 'r', 'i', 'k', 'e'], none⟩, ⟨['c', 'h', 'é', 'n'], ['s', 'i', 'n', 'k'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['y', 'ī'], ['o', 'n', 'e'], [⟨['y', 'ī'], ['o', 'n', 'e'], none⟩]⟩, ⟨['s', 'ō', 'u'], ['C', 'L', 'F'], [⟨['s', 'ō', 'u'], ['C', 'L', 'F'], none⟩]⟩, ⟨['x', 'ú', 'n', 'y', 'á', 'n', 'g', 'j', 'i', 'à', 'n'], ['c', 'r', 'u', 'i', 's', 'e', 'r'], [⟨['x', 'ú', 'n', 'y', 'á', 'n', 'g', 'j', 'i', 'à', 'n'], ['c', 'r', 'u', 'i', 's', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_139 : Datum :=
  { id := "tay2024_139"
    source := ⟨"tay-2024", "(139)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Éjūn chōng-chén-le yī sōu xúnyángjiàn."
    glossedTokens := [("Éjūn", "Russian.forces"), ("chōng-chén-le", "rush-sink-PFV"), ("yī", "one"), ("sōu", "CLF"), ("xúnyángjiàn", "cruiser")]
    glossedWords := [⟨['É', 'j', 'ū', 'n'], ['R', 'u', 's', 's', 'i', 'a', 'n', '.', 'f', 'o', 'r', 'c', 'e', 's'], [⟨['É', 'j', 'ū', 'n'], ['R', 'u', 's', 's', 'i', 'a', 'n', '.', 'f', 'o', 'r', 'c', 'e', 's'], none⟩]⟩, ⟨['c', 'h', 'ō', 'n', 'g', '-', 'c', 'h', 'é', 'n', '-', 'l', 'e'], ['r', 'u', 's', 'h', '-', 's', 'i', 'n', 'k', '-', 'P', 'F', 'V'], [⟨['c', 'h', 'ō', 'n', 'g'], ['r', 'u', 's', 'h'], none⟩, ⟨['c', 'h', 'é', 'n'], ['s', 'i', 'n', 'k'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['y', 'ī'], ['o', 'n', 'e'], [⟨['y', 'ī'], ['o', 'n', 'e'], none⟩]⟩, ⟨['s', 'ō', 'u'], ['C', 'L', 'F'], [⟨['s', 'ō', 'u'], ['C', 'L', 'F'], none⟩]⟩, ⟨['x', 'ú', 'n', 'y', 'á', 'n', 'g', 'j', 'i', 'à', 'n'], ['c', 'r', 'u', 'i', 's', 'e', 'r'], [⟨['x', 'ú', 'n', 'y', 'á', 'n', 'g', 'j', 'i', 'à', 'n'], ['c', 'r', 'u', 'i', 's', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_146 : Datum :=
  { id := "tay2024_146"
    source := ⟨"tay-2024", "(146)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Jiàoliàn zǒu-lèi-le John."
    glossedTokens := [("Jiàoliàn", "coach"), ("zǒu-lèi-le", "walk-tired-PFV"), ("John", "John")]
    glossedWords := [⟨['J', 'i', 'à', 'o', 'l', 'i', 'à', 'n'], ['c', 'o', 'a', 'c', 'h'], [⟨['J', 'i', 'à', 'o', 'l', 'i', 'à', 'n'], ['c', 'o', 'a', 'c', 'h'], none⟩]⟩, ⟨['z', 'ǒ', 'u', '-', 'l', 'è', 'i', '-', 'l', 'e'], ['w', 'a', 'l', 'k', '-', 't', 'i', 'r', 'e', 'd', '-', 'P', 'F', 'V'], [⟨['z', 'ǒ', 'u'], ['w', 'a', 'l', 'k'], none⟩, ⟨['l', 'è', 'i'], ['t', 'i', 'r', 'e', 'd'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_148 : Datum :=
  { id := "tay2024_148"
    source := ⟨"tay-2024", "(148)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān liè-kāi-le jīdàn."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("liè-kāi-le", "crack-open-PFV"), ("jīdàn", "egg")]
    glossedWords := [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['l', 'i', 'è', '-', 'k', 'ā', 'i', '-', 'l', 'e'], ['c', 'r', 'a', 'c', 'k', '-', 'o', 'p', 'e', 'n', '-', 'P', 'F', 'V'], [⟨['l', 'i', 'è'], ['c', 'r', 'a', 'c', 'k'], none⟩, ⟨['k', 'ā', 'i'], ['o', 'p', 'e', 'n'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['j', 'ī', 'd', 'à', 'n'], ['e', 'g', 'g'], [⟨['j', 'ī', 'd', 'à', 'n'], ['e', 'g', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_149 : Datum :=
  { id := "tay2024_149"
    source := ⟨"tay-2024", "(149)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Qiēcàibǎn qiē-dùn-le wǒ de càidāo."
    glossedTokens := [("Qiēcàibǎn", "cutting.board"), ("qiē-dùn-le", "cut-dull-PFV"), ("wǒ", "1SG"), ("de", "DE"), ("càidāo", "knife")]
    glossedWords := [⟨['Q', 'i', 'ē', 'c', 'à', 'i', 'b', 'ǎ', 'n'], ['c', 'u', 't', 't', 'i', 'n', 'g', '.', 'b', 'o', 'a', 'r', 'd'], [⟨['Q', 'i', 'ē', 'c', 'à', 'i', 'b', 'ǎ', 'n'], ['c', 'u', 't', 't', 'i', 'n', 'g', '.', 'b', 'o', 'a', 'r', 'd'], none⟩]⟩, ⟨['q', 'i', 'ē', '-', 'd', 'ù', 'n', '-', 'l', 'e'], ['c', 'u', 't', '-', 'd', 'u', 'l', 'l', '-', 'P', 'F', 'V'], [⟨['q', 'i', 'ē'], ['c', 'u', 't'], none⟩, ⟨['d', 'ù', 'n'], ['d', 'u', 'l', 'l'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['w', 'ǒ'], ['1', 'S', 'G'], [⟨['w', 'ǒ'], ['1', 'S', 'G'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['c', 'à', 'i', 'd', 'ā', 'o'], ['k', 'n', 'i', 'f', 'e'], [⟨['c', 'à', 'i', 'd', 'ā', 'o'], ['k', 'n', 'i', 'f', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "pureCauser")] }

def ex_150 : Datum :=
  { id := "tay2024_150"
    source := ⟨"tay-2024", "(150)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhè bù diànyǐng kū-hóng-le wǒ de yǎnjīng."
    glossedTokens := [("Zhè", "this"), ("bù", "CLF"), ("diànyǐng", "movie"), ("kū-hóng-le", "cry-red-PFV"), ("wǒ", "1SG"), ("de", "DE"), ("yǎnjīng", "eye")]
    glossedWords := [⟨['Z', 'h', 'è'], ['t', 'h', 'i', 's'], [⟨['Z', 'h', 'è'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['b', 'ù'], ['C', 'L', 'F'], [⟨['b', 'ù'], ['C', 'L', 'F'], none⟩]⟩, ⟨['d', 'i', 'à', 'n', 'y', 'ǐ', 'n', 'g'], ['m', 'o', 'v', 'i', 'e'], [⟨['d', 'i', 'à', 'n', 'y', 'ǐ', 'n', 'g'], ['m', 'o', 'v', 'i', 'e'], none⟩]⟩, ⟨['k', 'ū', '-', 'h', 'ó', 'n', 'g', '-', 'l', 'e'], ['c', 'r', 'y', '-', 'r', 'e', 'd', '-', 'P', 'F', 'V'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩, ⟨['h', 'ó', 'n', 'g'], ['r', 'e', 'd'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['w', 'ǒ'], ['1', 'S', 'G'], [⟨['w', 'ǒ'], ['1', 'S', 'G'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['y', 'ǎ', 'n', 'j', 'ī', 'n', 'g'], ['e', 'y', 'e'], [⟨['y', 'ǎ', 'n', 'j', 'ī', 'n', 'g'], ['e', 'y', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "subjectMatter")] }

def ex_151 : Datum :=
  { id := "tay2024_151"
    source := ⟨"tay-2024", "(151)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nèi ge xiàohuà xiào-téng-le Zhāngsān de dùzi."
    glossedTokens := [("Nèi", "that"), ("ge", "CLF"), ("xiàohuà", "joke"), ("xiào-téng-le", "laugh-hurt-PFV"), ("Zhāngsān", "Zhangsan"), ("de", "DE"), ("dùzi", "belly")]
    glossedWords := [⟨['N', 'è', 'i'], ['t', 'h', 'a', 't'], [⟨['N', 'è', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['x', 'i', 'à', 'o', 'h', 'u', 'à'], ['j', 'o', 'k', 'e'], [⟨['x', 'i', 'à', 'o', 'h', 'u', 'à'], ['j', 'o', 'k', 'e'], none⟩]⟩, ⟨['x', 'i', 'à', 'o', '-', 't', 'é', 'n', 'g', '-', 'l', 'e'], ['l', 'a', 'u', 'g', 'h', '-', 'h', 'u', 'r', 't', '-', 'P', 'F', 'V'], [⟨['x', 'i', 'à', 'o'], ['l', 'a', 'u', 'g', 'h'], none⟩, ⟨['t', 'é', 'n', 'g'], ['h', 'u', 'r', 't'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['d', 'ù', 'z', 'i'], ['b', 'e', 'l', 'l', 'y'], [⟨['d', 'ù', 'z', 'i'], ['b', 'e', 'l', 'l', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "subjectMatter")] }

def ex_202 : Datum :=
  { id := "tay2024_202"
    source := ⟨"tay-2024", "(202)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wǒ qiē-dùn-le càidāo."
    glossedTokens := [("Wǒ", "I"), ("qiē-dùn-le", "cut-dull-PFV"), ("càidāo", "knife")]
    glossedWords := [⟨['W', 'ǒ'], ['I'], [⟨['W', 'ǒ'], ['I'], none⟩]⟩, ⟨['q', 'i', 'ē', '-', 'd', 'ù', 'n', '-', 'l', 'e'], ['c', 'u', 't', '-', 'd', 'u', 'l', 'l', '-', 'P', 'F', 'V'], [⟨['q', 'i', 'ē'], ['c', 'u', 't'], none⟩, ⟨['d', 'ù', 'n'], ['d', 'u', 'l', 'l'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['c', 'à', 'i', 'd', 'ā', 'o'], ['k', 'n', 'i', 'f', 'e'], [⟨['c', 'à', 'i', 'd', 'ā', 'o'], ['k', 'n', 'i', 'f', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def ex_205 : Datum :=
  { id := "tay2024_205"
    source := ⟨"tay-2024", "(205)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhè dùn fàn chī-qióng-le wǒ."
    glossedTokens := [("Zhè", "this"), ("dùn", "CLF"), ("fàn", "meal"), ("chī-qióng-le", "eat-poor-PFV"), ("wǒ", "me")]
    glossedWords := [⟨['Z', 'h', 'è'], ['t', 'h', 'i', 's'], [⟨['Z', 'h', 'è'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['d', 'ù', 'n'], ['C', 'L', 'F'], [⟨['d', 'ù', 'n'], ['C', 'L', 'F'], none⟩]⟩, ⟨['f', 'à', 'n'], ['m', 'e', 'a', 'l'], [⟨['f', 'à', 'n'], ['m', 'e', 'a', 'l'], none⟩]⟩, ⟨['c', 'h', 'ī', '-', 'q', 'i', 'ó', 'n', 'g', '-', 'l', 'e'], ['e', 'a', 't', '-', 'p', 'o', 'o', 'r', '-', 'P', 'F', 'V'], [⟨['c', 'h', 'ī'], ['e', 'a', 't'], none⟩, ⟨['q', 'i', 'ó', 'n', 'g'], ['p', 'o', 'o', 'r'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['w', 'ǒ'], ['m', 'e'], [⟨['w', 'ǒ'], ['m', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("I ate the meal", .acceptable), ("someone else ate the meal I paid for", .acceptable)]
    paperFeatures := [("externalArgument", "theme")] }

def ex_206 : Datum :=
  { id := "tay2024_206"
    source := ⟨"tay-2024", "(206)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhè shǒu gē chàng-kū-le guānzhòng."
    glossedTokens := [("Zhè", "this"), ("shǒu", "CLF"), ("gē", "song"), ("chàng-kū-le", "sing-cry-PFV"), ("guānzhòng", "audience")]
    glossedWords := [⟨['Z', 'h', 'è'], ['t', 'h', 'i', 's'], [⟨['Z', 'h', 'è'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['s', 'h', 'ǒ', 'u'], ['C', 'L', 'F'], [⟨['s', 'h', 'ǒ', 'u'], ['C', 'L', 'F'], none⟩]⟩, ⟨['g', 'ē'], ['s', 'o', 'n', 'g'], [⟨['g', 'ē'], ['s', 'o', 'n', 'g'], none⟩]⟩, ⟨['c', 'h', 'à', 'n', 'g', '-', 'k', 'ū', '-', 'l', 'e'], ['s', 'i', 'n', 'g', '-', 'c', 'r', 'y', '-', 'P', 'F', 'V'], [⟨['c', 'h', 'à', 'n', 'g'], ['s', 'i', 'n', 'g'], none⟩, ⟨['k', 'ū'], ['c', 'r', 'y'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['g', 'u', 'ā', 'n', 'z', 'h', 'ò', 'n', 'g'], ['a', 'u', 'd', 'i', 'e', 'n', 'c', 'e'], [⟨['g', 'u', 'ā', 'n', 'z', 'h', 'ò', 'n', 'g'], ['a', 'u', 'd', 'i', 'e', 'n', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("the audience sang", .acceptable), ("the performer sang", .acceptable)]
    paperFeatures := [("externalArgument", "theme")] }

def ex_216 : Datum :=
  { id := "tay2024_216"
    source := ⟨"tay-2024", "(216)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Yīfú xǐ-gānjìng-le."
    glossedTokens := [("Yīfú", "clothes"), ("xǐ-gānjìng-le", "wash-clean-PFV")]
    glossedWords := [⟨['Y', 'ī', 'f', 'ú'], ['c', 'l', 'o', 't', 'h', 'e', 's'], [⟨['Y', 'ī', 'f', 'ú'], ['c', 'l', 'o', 't', 'h', 'e', 's'], none⟩]⟩, ⟨['x', 'ǐ', '-', 'g', 'ā', 'n', 'j', 'ì', 'n', 'g', '-', 'l', 'e'], ['w', 'a', 's', 'h', '-', 'c', 'l', 'e', 'a', 'n', '-', 'P', 'F', 'V'], [⟨['x', 'ǐ'], ['w', 'a', 's', 'h'], none⟩, ⟨['g', 'ā', 'n', 'j', 'ì', 'n', 'g'], ['c', 'l', 'e', 'a', 'n'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_217 : Datum :=
  { id := "tay2024_217"
    source := ⟨"tay-2024", "(217)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wǒ de càidāo qiē-dùn-le."
    glossedTokens := [("Wǒ", "1SG"), ("de", "DE"), ("càidāo", "knife"), ("qiē-dùn-le", "cut-dull-PFV")]
    glossedWords := [⟨['W', 'ǒ'], ['1', 'S', 'G'], [⟨['W', 'ǒ'], ['1', 'S', 'G'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['c', 'à', 'i', 'd', 'ā', 'o'], ['k', 'n', 'i', 'f', 'e'], [⟨['c', 'à', 'i', 'd', 'ā', 'o'], ['k', 'n', 'i', 'f', 'e'], none⟩]⟩, ⟨['q', 'i', 'ē', '-', 'd', 'ù', 'n', '-', 'l', 'e'], ['c', 'u', 't', '-', 'd', 'u', 'l', 'l', '-', 'P', 'F', 'V'], [⟨['q', 'i', 'ē'], ['c', 'u', 't'], none⟩, ⟨['d', 'ù', 'n'], ['d', 'u', 'l', 'l'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_219 : Datum :=
  { id := "tay2024_219"
    source := ⟨"tay-2024", "(219)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān kū-lèi-le."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("kū-lèi-le", "cry-tired-PFV")]
    glossedWords := [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['k', 'ū', '-', 'l', 'è', 'i', '-', 'l', 'e'], ['c', 'r', 'y', '-', 't', 'i', 'r', 'e', 'd', '-', 'P', 'F', 'V'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩, ⟨['l', 'è', 'i'], ['t', 'i', 'r', 'e', 'd'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_221 : Datum :=
  { id := "tay2024_221"
    source := ⟨"tay-2024", "(221)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Shǒujuǎn kū-shī-le."
    glossedTokens := [("Shǒujuǎn", "handkerchief"), ("kū-shī-le", "cry-wet-PFV")]
    glossedWords := [⟨['S', 'h', 'ǒ', 'u', 'j', 'u', 'ǎ', 'n'], ['h', 'a', 'n', 'd', 'k', 'e', 'r', 'c', 'h', 'i', 'e', 'f'], [⟨['S', 'h', 'ǒ', 'u', 'j', 'u', 'ǎ', 'n'], ['h', 'a', 'n', 'd', 'k', 'e', 'r', 'c', 'h', 'i', 'e', 'f'], none⟩]⟩, ⟨['k', 'ū', '-', 's', 'h', 'ī', '-', 'l', 'e'], ['c', 'r', 'y', '-', 'w', 'e', 't', '-', 'P', 'F', 'V'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩, ⟨['s', 'h', 'ī'], ['w', 'e', 't'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Out of the blue."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def ex_224 : Datum :=
  { id := "tay2024_224"
    source := ⟨"tay-2024", "(224)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Māma kū-xǐng-le."
    glossedTokens := [("Māma", "mother"), ("kū-xǐng-le", "cry-awake-PFV")]
    glossedWords := [⟨['M', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['M', 'ā', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['k', 'ū', '-', 'x', 'ǐ', 'n', 'g', '-', 'l', 'e'], ['c', 'r', 'y', '-', 'a', 'w', 'a', 'k', 'e', '-', 'P', 'F', 'V'], [⟨['k', 'ū'], ['c', 'r', 'y'], none⟩, ⟨['x', 'ǐ', 'n', 'g'], ['a', 'w', 'a', 'k', 'e'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("Mother cries herself awake", .acceptable), ("Mother wakes from someone else crying", .unacceptable)]
    paperFeatures := [] }

def ex_330 : Datum :=
  { id := "tay2024_330"
    source := ⟨"tay-2024", "(330), (349)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān qí-lèi-le mǎ."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("qí-lèi-le", "ride-tired-PFV"), ("mǎ", "horse")]
    glossedWords := [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['q', 'í', '-', 'l', 'è', 'i', '-', 'l', 'e'], ['r', 'i', 'd', 'e', '-', 't', 'i', 'r', 'e', 'd', '-', 'P', 'F', 'V'], [⟨['q', 'í'], ['r', 'i', 'd', 'e'], none⟩, ⟨['l', 'è', 'i'], ['t', 'i', 'r', 'e', 'd'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['m', 'ǎ'], ['h', 'o', 'r', 's', 'e'], [⟨['m', 'ǎ'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A hybrid resultative, commonly described as a subject-oriented transitive resultative."
    judgment := .acceptable
    contrasts := []
    readings := [("the horse became tired", .acceptable), ("Zhangsan became tired", .variable)]
    paperFeatures := [("externalArgument", "agent")] }

def ex_668 : Datum :=
  { id := "tay2024_668"
    source := ⟨"tay-2024", "(668), (673)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān dǎ-pò-le huāpíng."
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("dǎ-pò-le", "hit-break-PFV"), ("huāpíng", "vase")]
    glossedWords := [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], [⟨['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n'], ['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n'], none⟩]⟩, ⟨['d', 'ǎ', '-', 'p', 'ò', '-', 'l', 'e'], ['h', 'i', 't', '-', 'b', 'r', 'e', 'a', 'k', '-', 'P', 'F', 'V'], [⟨['d', 'ǎ'], ['h', 'i', 't'], none⟩, ⟨['p', 'ò'], ['b', 'r', 'e', 'a', 'k'], some '-'⟩, ⟨['l', 'e'], ['P', 'F', 'V'], some '-'⟩]⟩, ⟨['h', 'u', 'ā', 'p', 'í', 'n', 'g'], ['v', 'a', 's', 'e'], [⟨['h', 'u', 'ā', 'p', 'í', 'n', 'g'], ['v', 'a', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A transitive V-V resultative whose result verb is an intransitive change-of-state verb."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("externalArgument", "agent")] }

def all : List Datum := [ex_41, ex_42, ex_45, ex_46, ex_107, ex_131, ex_132, ex_133, ex_134, ex_137, ex_139, ex_146, ex_148, ex_149, ex_150, ex_151, ex_202, ex_205, ex_206, ex_216, ex_217, ex_219, ex_221, ex_224, ex_330, ex_668]

/-- The paper's reading of the external argument of a transitive compound relative to V1. -/
inductive ExternalArgument where
  /-- agent: agent -/
  | agent
  /-- theme: theme -/
  | theme
  /-- subjectMatter: subjectMatter -/
  | subjectMatter
  /-- pureCauser: pureCauser -/
  | pureCauser
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `externalArgument`. -/
def externalArgument (e : Datum) : Option ExternalArgument :=
  e.parse? "externalArgument" [("agent", .agent), ("theme", .theme), ("subjectMatter", .subjectMatter),
    ("pureCauser", .pureCauser)]

end Tay2024.Examples
