module

public import Linglib.Data.Examples.Schema

/-!
# `Aremu2025b` — typed example data

Auto-generated from `Linglib/Data/Examples/Aremu2025b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Aremu2025b.Examples`.
-/

@[expose] public section

namespace Aremu2025b.Examples

def ex_2b : Datum :=
  { id := "aremu2025b_2b"
    source := ⟨"aremu-2025b", "(2b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Eku ni Adé pa"
    glossedTokens := [("Eku", "rat"), ("ni", "FOC"), ("Adé", "A."), ("pa", "kill")]
    glossedWords := [⟨['E', 'k', 'u'], ['r', 'a', 't'], [⟨['E', 'k', 'u'], ['r', 'a', 't'], none⟩]⟩, ⟨['n', 'i'], ['F', 'O', 'C'], [⟨['n', 'i'], ['F', 'O', 'C'], none⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['p', 'a'], ['k', 'i', 'l', 'l'], [⟨['p', 'a'], ['k', 'i', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Kí ni Adé pa? 'What did Adé kill?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object")] }

def ex_3b : Datum :=
  { id := "aremu2025b_3b"
    source := ⟨"aremu-2025b", "(3b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Tolú Adé rí rín"
    glossedTokens := [("Tolú", "T."), ("Adé", "A."), ("rí", "see"), ("rín", "FOC")]
    glossedWords := [⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nèé Adé rí-i? 'Who did Adé see?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object")] }

def ex_10b : Datum :=
  { id := "aremu2025b_10b"
    source := ⟨"aremu-2025b", "(10b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé ó jẹ ejíjẹ nẹ̀ rín"
    glossedTokens := [("Adé", "A."), ("ó", "RP"), ("jẹ", "eat"), ("ejíjẹ", "food"), ("nẹ̀", "DEF"), ("rín", "FOC")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['ó'], ['R', 'P'], [⟨['ó'], ['R', 'P'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], [⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], [⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nọ̀ọ́ jẹ ejíjẹ nẹ̀? 'Who ate the food?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject")] }

def ex_10b_noRP : Datum :=
  { id := "aremu2025b_10b_noRP"
    source := ⟨"aremu-2025b", "(10b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé jẹ ejíjẹ nẹ̀ rín"
    glossedTokens := [("Adé", "A."), ("jẹ", "eat"), ("ejíjẹ", "food"), ("nẹ̀", "DEF"), ("rín", "FOC")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], [⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], [⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nọ̀ọ́ jẹ ejíjẹ nẹ̀? 'Who ate the food?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject")] }

def ex_10b_noRin : Datum :=
  { id := "aremu2025b_10b_noRin"
    source := ⟨"aremu-2025b", "(10b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé ó jẹ ejíjẹ nẹ̀"
    glossedTokens := [("Adé", "A."), ("ó", "RP"), ("jẹ", "eat"), ("ejíjẹ", "food"), ("nẹ̀", "DEF")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['ó'], ['R', 'P'], [⟨['ó'], ['R', 'P'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], [⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], [⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nọ̀ọ́ jẹ ejíjẹ nẹ̀? 'Who ate the food?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject")] }

def ex_10c : Datum :=
  { id := "aremu2025b_10c"
    source := ⟨"aremu-2025b", "(10c)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé jẹ ejíjẹ nẹ̀"
    glossedTokens := [("Adé", "A."), ("jẹ", "eat"), ("ejíjẹ", "food"), ("nẹ̀", "DEF")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], [⟨['e', 'j', 'í', 'j', 'ẹ'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], [⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nọ̀ọ́ jẹ ejíjẹ nẹ̀? 'Who ate the food?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject")] }

def ex_16a : Datum :=
  { id := "aremu2025b_16a"
    source := ⟨"aremu-2025b", "(16a)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Èmi ni mo na Akin"
    glossedTokens := [("Èmi", "1SG"), ("ni", "FOC"), ("mo", "1SG"), ("na", "beat"), ("Akin", "Akin")]
    glossedWords := [⟨['È', 'm', 'i'], ['1', 'S', 'G'], [⟨['È', 'm', 'i'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'i'], ['F', 'O', 'C'], [⟨['n', 'i'], ['F', 'O', 'C'], none⟩]⟩, ⟨['m', 'o'], ['1', 'S', 'G'], [⟨['m', 'o'], ['1', 'S', 'G'], none⟩]⟩, ⟨['n', 'a'], ['b', 'e', 'a', 't'], [⟨['n', 'a'], ['b', 'e', 'a', 't'], none⟩]⟩, ⟨['A', 'k', 'i', 'n'], ['A', 'k', 'i', 'n'], [⟨['A', 'k', 'i', 'n'], ['A', 'k', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Subject focus."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject"), ("person", "first")] }

def ex_16b : Datum :=
  { id := "aremu2025b_16b"
    source := ⟨"aremu-2025b", "(16b)"⟩
    reportedIn := none
    language := "yoru1245"
    primaryText := "Ìwo ni o na Akin"
    glossedTokens := [("Ìwo", "2SG"), ("ni", "FOC"), ("o", "2SG"), ("na", "beat"), ("Akin", "Akin")]
    glossedWords := [⟨['Ì', 'w', 'o'], ['2', 'S', 'G'], [⟨['Ì', 'w', 'o'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'i'], ['F', 'O', 'C'], [⟨['n', 'i'], ['F', 'O', 'C'], none⟩]⟩, ⟨['o'], ['2', 'S', 'G'], [⟨['o'], ['2', 'S', 'G'], none⟩]⟩, ⟨['n', 'a'], ['b', 'e', 'a', 't'], [⟨['n', 'a'], ['b', 'e', 'a', 't'], none⟩]⟩, ⟨['A', 'k', 'i', 'n'], ['A', 'k', 'i', 'n'], [⟨['A', 'k', 'i', 'n'], ['A', 'k', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Subject focus."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject"), ("person", "second")] }

def ex_22b : Datum :=
  { id := "aremu2025b_22b"
    source := ⟨"aremu-2025b", "(22b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Tolú Adé rí rín"
    glossedTokens := [("Tolú", "T."), ("Adé", "A."), ("rí", "see"), ("rín", "FOC")]
    glossedWords := [⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nèé Adé rí-i? 'Who did Adé see?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object")] }

def ex_22b_RP : Datum :=
  { id := "aremu2025b_22b_RP"
    source := ⟨"aremu-2025b", "(22b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Tolú Adé rí ó rín"
    glossedTokens := [("Tolú", "T."), ("Adé", "A."), ("rí", "see"), ("ó", "RP"), ("rín", "FOC")]
    glossedWords := [⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['ó'], ['R', 'P'], [⟨['ó'], ['R', 'P'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nèé Adé rí-i? 'Who did Adé see?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object")] }

def ex_22b_noRin : Datum :=
  { id := "aremu2025b_22b_noRin"
    source := ⟨"aremu-2025b", "(22b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Tolú Adé rí"
    glossedTokens := [("Tolú", "T."), ("Adé", "A."), ("rí", "see")]
    glossedWords := [⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nèé Adé rí-i? 'Who did Adé see?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object")] }

def ex_22c : Datum :=
  { id := "aremu2025b_22c"
    source := ⟨"aremu-2025b", "(22c)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé rí Tolú"
    glossedTokens := [("Adé", "A."), ("rí", "see"), ("Tolú", "T.")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nèé Adé rí-i? 'Who did Adé see?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object")] }

def ex_22c_rin : Datum :=
  { id := "aremu2025b_22c_rin"
    source := ⟨"aremu-2025b", "(22c)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé rí Tolú rín"
    glossedTokens := [("Adé", "A."), ("rí", "see"), ("Tolú", "T."), ("rín", "FOC")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Nèé Adé rí-i? 'Who did Adé see?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object")] }

def ex_27b : Datum :=
  { id := "aremu2025b_27b"
    source := ⟨"aremu-2025b", "(27b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Àná Ayọ̀ rí Tolú rín"
    glossedTokens := [("Àná", "yesterday"), ("Ayọ̀", "A."), ("rí", "see"), ("Tolú", "T"), ("rín", "FOC")]
    glossedWords := [⟨['À', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['À', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['A', 'y', 'ọ', '̀'], ['A', '.'], [⟨['A', 'y', 'ọ', '̀'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['T', 'o', 'l', 'ú'], ['T'], [⟨['T', 'o', 'l', 'ú'], ['T'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Ugbo Ayọ̀ rí Tolú? 'When did Adé see Tolú?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "adjunct"), ("fronted", "adjunct")] }

def ex_27b_noRin : Datum :=
  { id := "aremu2025b_27b_noRin"
    source := ⟨"aremu-2025b", "(27b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Àná Ayọ̀ rí Tolú"
    glossedTokens := [("Àná", "yesterday"), ("Ayọ̀", "A."), ("rí", "see"), ("Tolú", "T")]
    glossedWords := [⟨['À', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['À', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['A', 'y', 'ọ', '̀'], ['A', '.'], [⟨['A', 'y', 'ọ', '̀'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['T', 'o', 'l', 'ú'], ['T'], [⟨['T', 'o', 'l', 'ú'], ['T'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Ugbo Ayọ̀ rí Tolú? 'When did Adé see Tolú?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "adjunct"), ("fronted", "adjunct")] }

def ex_27c : Datum :=
  { id := "aremu2025b_27c"
    source := ⟨"aremu-2025b", "(27c)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé rí Tolú ni àná"
    glossedTokens := [("Adé", "A."), ("rí", "see"), ("Tolú", "T."), ("ni", "at"), ("àná", "yesterday")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩, ⟨['n', 'i'], ['a', 't'], [⟨['n', 'i'], ['a', 't'], none⟩]⟩, ⟨['à', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['à', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Ugbo Ayọ̀ rí Tolú? 'When did Adé see Tolú?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "adjunct")] }

def ex_27c_rin : Datum :=
  { id := "aremu2025b_27c_rin"
    source := ⟨"aremu-2025b", "(27c)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé rí Tolú ni àná rín"
    glossedTokens := [("Adé", "A."), ("rí", "see"), ("Tolú", "T."), ("ni", "at"), ("àná", "yesterday"), ("rín", "FOC")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'í'], ['s', 'e', 'e'], [⟨['r', 'í'], ['s', 'e', 'e'], none⟩]⟩, ⟨['T', 'o', 'l', 'ú'], ['T', '.'], [⟨['T', 'o', 'l', 'ú'], ['T', '.'], none⟩]⟩, ⟨['n', 'i'], ['a', 't'], [⟨['n', 'i'], ['a', 't'], none⟩]⟩, ⟨['à', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['à', 'n', 'á'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Ugbo Ayọ̀ rí Tolú? 'When did Adé see Tolú?'"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "adjunct")] }

def ex_29a : Datum :=
  { id := "aremu2025b_29a"
    source := ⟨"aremu-2025b", "(29a)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé rà ìwé"
    glossedTokens := [("Adé", "A."), ("rà", "buy"), ("ìwé", "book")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'à'], ['b', 'u', 'y'], [⟨['r', 'à'], ['b', 'u', 'y'], none⟩]⟩, ⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], [⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: What did Adé do?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "vp")] }

def ex_29a_rin : Datum :=
  { id := "aremu2025b_29a_rin"
    source := ⟨"aremu-2025b", "(29a)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé rà ìwé rín"
    glossedTokens := [("Adé", "A."), ("rà", "buy"), ("ìwé", "book"), ("rín", "FOC")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'à'], ['b', 'u', 'y'], [⟨['r', 'à'], ['b', 'u', 'y'], none⟩]⟩, ⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], [⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: What did Adé do?"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "vp")] }

def ex_29b : Datum :=
  { id := "aremu2025b_29b"
    source := ⟨"aremu-2025b", "(29b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Rí-rà Adé rà ìwé rín"
    glossedTokens := [("Rí-rà", "NMZL-buy"), ("Adé", "A."), ("rà", "buy"), ("ìwé", "book"), ("rín", "FOC")]
    glossedWords := [⟨['R', 'í', '-', 'r', 'à'], ['N', 'M', 'Z', 'L', '-', 'b', 'u', 'y'], [⟨['R', 'í'], ['N', 'M', 'Z', 'L'], none⟩, ⟨['r', 'à'], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'à'], ['b', 'u', 'y'], [⟨['r', 'à'], ['b', 'u', 'y'], none⟩]⟩, ⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], [⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Verb focus, the fronted verb nominalized by partial reduplication and a copy left in place."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "verb"), ("fronted", "verb")] }

def ex_29b_noRin : Datum :=
  { id := "aremu2025b_29b_noRin"
    source := ⟨"aremu-2025b", "(29b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Rí-rà Adé rà ìwé"
    glossedTokens := [("Rí-rà", "NMZL-buy"), ("Adé", "A."), ("rà", "buy"), ("ìwé", "book")]
    glossedWords := [⟨['R', 'í', '-', 'r', 'à'], ['N', 'M', 'Z', 'L', '-', 'b', 'u', 'y'], [⟨['R', 'í'], ['N', 'M', 'Z', 'L'], none⟩, ⟨['r', 'à'], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['r', 'à'], ['b', 'u', 'y'], [⟨['r', 'à'], ['b', 'u', 'y'], none⟩]⟩, ⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], [⟨['ì', 'w', 'é'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Verb focus, the fronted verb nominalized by partial reduplication and a copy left in place."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "verb"), ("fronted", "verb")] }

def ex_31a : Datum :=
  { id := "aremu2025b_31a"
    source := ⟨"aremu-2025b", "(31a)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé ó jẹ ejíje nẹ̀ rín kìí se Bọ́lá"
    glossedTokens := [("Adé", "A."), ("ó", "RP"), ("jẹ", "eat"), ("ejíje", "food"), ("nẹ̀", "DEF"), ("rín", "FOC"), ("kìí", "NEG"), ("se", "COP"), ("Bọ́lá", "B.")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['ó'], ['R', 'P'], [⟨['ó'], ['R', 'P'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['e', 'j', 'í', 'j', 'e'], ['f', 'o', 'o', 'd'], [⟨['e', 'j', 'í', 'j', 'e'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], [⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩, ⟨['k', 'ì', 'í'], ['N', 'E', 'G'], [⟨['k', 'ì', 'í'], ['N', 'E', 'G'], none⟩]⟩, ⟨['s', 'e'], ['C', 'O', 'P'], [⟨['s', 'e'], ['C', 'O', 'P'], none⟩]⟩, ⟨['B', 'ọ', '́', 'l', 'á'], ['B', '.'], [⟨['B', 'ọ', '́', 'l', 'á'], ['B', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Contrastive subject focus."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("fronted", "subject"), ("continuation", "contrastive")] }

def ex_31b : Datum :=
  { id := "aremu2025b_31b"
    source := ⟨"aremu-2025b", "(31b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé jẹ ejíje nẹ̀ kìí se Bọ́lá"
    glossedTokens := [("Adé", "A."), ("jẹ", "eat"), ("ejíje", "food"), ("nẹ̀", "DEF"), ("kìí", "NEG"), ("se", "COP"), ("Bọ́lá", "B.")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['e', 'j', 'í', 'j', 'e'], ['f', 'o', 'o', 'd'], [⟨['e', 'j', 'í', 'j', 'e'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], [⟨['n', 'ẹ', '̀'], ['D', 'E', 'F'], none⟩]⟩, ⟨['k', 'ì', 'í'], ['N', 'E', 'G'], [⟨['k', 'ì', 'í'], ['N', 'E', 'G'], none⟩]⟩, ⟨['s', 'e'], ['C', 'O', 'P'], [⟨['s', 'e'], ['C', 'O', 'P'], none⟩]⟩, ⟨['B', 'ọ', '́', 'l', 'á'], ['B', '.'], [⟨['B', 'ọ', '́', 'l', 'á'], ['B', '.'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Labelled new information subject focus."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "subject"), ("continuation", "contrastive")] }

def ex_32a : Datum :=
  { id := "aremu2025b_32a"
    source := ⟨"aremu-2025b", "(32a)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Ìrẹsì Adé jẹ rín kìí se ẹ̀wà"
    glossedTokens := [("Ìrẹsì", "rice"), ("Adé", "A."), ("jẹ", "eat"), ("rín", "FOC"), ("kìí", "NEG"), ("se", "COP"), ("ẹ̀wà", "beans")]
    glossedWords := [⟨['Ì', 'r', 'ẹ', 's', 'ì'], ['r', 'i', 'c', 'e'], [⟨['Ì', 'r', 'ẹ', 's', 'ì'], ['r', 'i', 'c', 'e'], none⟩]⟩, ⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['r', 'í', 'n'], ['F', 'O', 'C'], [⟨['r', 'í', 'n'], ['F', 'O', 'C'], none⟩]⟩, ⟨['k', 'ì', 'í'], ['N', 'E', 'G'], [⟨['k', 'ì', 'í'], ['N', 'E', 'G'], none⟩]⟩, ⟨['s', 'e'], ['C', 'O', 'P'], [⟨['s', 'e'], ['C', 'O', 'P'], none⟩]⟩, ⟨['ẹ', '̀', 'w', 'à'], ['b', 'e', 'a', 'n', 's'], [⟨['ẹ', '̀', 'w', 'à'], ['b', 'e', 'a', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Contrastive object focus."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("fronted", "object"), ("continuation", "contrastive")] }

def ex_32b : Datum :=
  { id := "aremu2025b_32b"
    source := ⟨"aremu-2025b", "(32b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé jẹ ìrẹsì"
    glossedTokens := [("Adé", "A."), ("jẹ", "eat"), ("ìrẹsì", "rice")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['ì', 'r', 'ẹ', 's', 'ì'], ['r', 'i', 'c', 'e'], [⟨['ì', 'r', 'ẹ', 's', 'ì'], ['r', 'i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "New information object focus."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object")] }

def ex_32b_contrast : Datum :=
  { id := "aremu2025b_32b_contrast"
    source := ⟨"aremu-2025b", "(32b)"⟩
    reportedIn := none
    language := "ikal1241"
    primaryText := "Adé jẹ ìrẹsì kìí se ẹ̀wà"
    glossedTokens := [("Adé", "A."), ("jẹ", "eat"), ("ìrẹsì", "rice"), ("kìí", "NEG"), ("se", "COP"), ("ẹ̀wà", "beans")]
    glossedWords := [⟨['A', 'd', 'é'], ['A', '.'], [⟨['A', 'd', 'é'], ['A', '.'], none⟩]⟩, ⟨['j', 'ẹ'], ['e', 'a', 't'], [⟨['j', 'ẹ'], ['e', 'a', 't'], none⟩]⟩, ⟨['ì', 'r', 'ẹ', 's', 'ì'], ['r', 'i', 'c', 'e'], [⟨['ì', 'r', 'ẹ', 's', 'ì'], ['r', 'i', 'c', 'e'], none⟩]⟩, ⟨['k', 'ì', 'í'], ['N', 'E', 'G'], [⟨['k', 'ì', 'í'], ['N', 'E', 'G'], none⟩]⟩, ⟨['s', 'e'], ['C', 'O', 'P'], [⟨['s', 'e'], ['C', 'O', 'P'], none⟩]⟩, ⟨['ẹ', '̀', 'w', 'à'], ['b', 'e', 'a', 'n', 's'], [⟨['ẹ', '̀', 'w', 'à'], ['b', 'e', 'a', 'n', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "New information object focus."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("focus", "object"), ("continuation", "contrastive")] }

def all : List Datum := [ex_2b, ex_3b, ex_10b, ex_10b_noRP, ex_10b_noRin, ex_10c, ex_16a, ex_16b, ex_22b, ex_22b_RP, ex_22b_noRin, ex_22c, ex_22c_rin, ex_27b, ex_27b_noRin, ex_27c, ex_27c_rin, ex_29a, ex_29a_rin, ex_29b, ex_29b_noRin, ex_31a, ex_31b, ex_32a, ex_32b, ex_32b_contrast]

end Aremu2025b.Examples
