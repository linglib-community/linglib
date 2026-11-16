module

public import Linglib.Data.Examples.Schema

/-!
# `WangSun2026` — typed example data

Auto-generated from `Linglib/Data/Examples/WangSun2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WangSun2026.Examples`.
-/

@[expose] public section

namespace WangSun2026.Examples

def ex_1 : Datum :=
  { id := "wangsun2026_1"
    source := ⟨"wang-sun-2026", "(4c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī hěn cōngming de gè xuéshēng"
    glossedTokens := [("yī", "one"), ("hěn", "very"), ("cōngming", "clever"), ("de", "DE"), ("gè", "CL"), ("xuéshēng", "student")]
    glossedWords := [⟨[['y', 'ī']], [['o', 'n', 'e']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['c', 'ō', 'n', 'g', 'm', 'i', 'n', 'g']], [['c', 'l', 'e', 'v', 'e', 'r']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩, ⟨[['x', 'u', 'é', 's', 'h', 'ē', 'n', 'g']], [['s', 't', 'u', 'd', 'e', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Num _ Cl")] }

def ex_2 : Datum :=
  { id := "wangsun2026_2"
    source := ⟨"wang-sun-2026", "(8a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yí gè cōngming (de) xuéshēng"
    glossedTokens := [("yí", "one"), ("gè", "CL"), ("cōngming", "clever"), ("(de)", "DE"), ("xuéshēng", "student")]
    glossedWords := [⟨[['y', 'í']], [['o', 'n', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩, ⟨[['c', 'ō', 'n', 'g', 'm', 'i', 'n', 'g']], [['c', 'l', 'e', 'v', 'e', 'r']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['x', 'u', 'é', 's', 'h', 'ē', 'n', 'g']], [['s', 't', 'u', 'd', 'e', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "bare"), ("position", "Cl _ N")] }

def ex_3 : Datum :=
  { id := "wangsun2026_3"
    source := ⟨"wang-sun-2026", "(29a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī hěn dà (de) zhāng zhuōzi"
    glossedTokens := [("yī", "one"), ("hěn", "very"), ("dà", "big"), ("(de)", "DE"), ("zhāng", "CL"), ("zhuōzi", "table")]
    glossedWords := [⟨[['y', 'ī']], [['o', 'n', 'e']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['z', 'h', 'ā', 'n', 'g']], [['C', 'L']]⟩, ⟨[['z', 'h', 'u', 'ō', 'z', 'i']], [['t', 'a', 'b', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Num _ Cl")] }

def ex_4 : Datum :=
  { id := "wangsun2026_4"
    source := ⟨"wang-sun-2026", "(29b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yí dà zhāng zhuōzi"
    glossedTokens := [("yí", "one"), ("dà", "big"), ("zhāng", "CL"), ("zhuōzi", "table")]
    glossedWords := [⟨[['y', 'í']], [['o', 'n', 'e']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['z', 'h', 'ā', 'n', 'g']], [['C', 'L']]⟩, ⟨[['z', 'h', 'u', 'ō', 'z', 'i']], [['t', 'a', 'b', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "bare"), ("position", "Num _ Cl")] }

def ex_5 : Datum :=
  { id := "wangsun2026_5"
    source := ⟨"wang-sun-2026", "(28a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī zhāng hěn dà de zhuōzi"
    glossedTokens := [("yī", "one"), ("zhāng", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("zhuōzi", "table")]
    glossedWords := [⟨[['y', 'ī']], [['o', 'n', 'e']]⟩, ⟨[['z', 'h', 'ā', 'n', 'g']], [['C', 'L']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['z', 'h', 'u', 'ō', 'z', 'i']], [['t', 'a', 'b', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Cl _ N")] }

def ex_6 : Datum :=
  { id := "wangsun2026_6"
    source := ⟨"wang-sun-2026", "(5c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Gè píngguǒ, Zhāngsān chī-le sān"
    glossedTokens := [("Gè", "CL"), ("píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("sān", "three")]
    glossedWords := [⟨[['G', 'è']], [['C', 'L']]⟩, ⟨[['p', 'í', 'n', 'g', 'g', 'u', 'ǒ']], [['a', 'p', 'p', 'l', 'e']]⟩, ⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['c', 'h', 'ī'], ['l', 'e']], [['e', 'a', 't'], ['P', 'F', 'V']]⟩, ⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "Cl N")] }

def ex_7 : Datum :=
  { id := "wangsun2026_7"
    source := ⟨"wang-sun-2026", "(13b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ, Zhāngsān chī-le sān gè"
    glossedTokens := [("Píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("sān", "three"), ("gè", "CL")]
    glossedWords := [⟨[['P', 'í', 'n', 'g', 'g', 'u', 'ǒ']], [['a', 'p', 'p', 'l', 'e']]⟩, ⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'a', 'n']]⟩, ⟨[['c', 'h', 'ī'], ['l', 'e']], [['e', 'a', 't'], ['P', 'F', 'V']]⟩, ⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "N")] }

def ex_8 : Datum :=
  { id := "wangsun2026_8"
    source := ⟨"wang-sun-2026", "(14a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Sān gè, Zhāngsān chī-le píngguǒ"
    glossedTokens := [("Sān", "three"), ("gè", "CL"), ("Zhāngsān", "Zhāngsān"), ("chī-le", "eat-PFV"), ("píngguǒ", "apple")]
    glossedWords := [⟨[['S', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩, ⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']]⟩, ⟨[['c', 'h', 'ī'], ['l', 'e']], [['e', 'a', 't'], ['P', 'F', 'V']]⟩, ⟨[['p', 'í', 'n', 'g', 'g', 'u', 'ǒ']], [['a', 'p', 'p', 'l', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "Num Cl")] }

def ex_9 : Datum :=
  { id := "wangsun2026_9"
    source := ⟨"wang-sun-2026", "(39a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān mǎi-le jǐ zhāng hěn dà de zhuōzi?"
    glossedTokens := [("Zhāngsān", "Zhangsān"), ("mǎi-le", "buy-PFV"), ("jǐ", "how-many"), ("zhāng", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("zhuōzi", "table")]
    glossedWords := [⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'ā', 'n']]⟩, ⟨[['m', 'ǎ', 'i'], ['l', 'e']], [['b', 'u', 'y'], ['P', 'F', 'V']]⟩, ⟨[['j', 'ǐ']], [['h', 'o', 'w'], ['m', 'a', 'n', 'y']]⟩, ⟨[['z', 'h', 'ā', 'n', 'g']], [['C', 'L']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['z', 'h', 'u', 'ō', 'z', 'i']], [['t', 'a', 'b', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "numeral"), ("modifier", "post-classifier")] }

def ex_10 : Datum :=
  { id := "wangsun2026_10"
    source := ⟨"wang-sun-2026", "(39b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān mǎi-le hěn dà de jǐ zhāng zhuōzi?"
    glossedTokens := [("Zhāngsān", "Zhangsān"), ("mǎi-le", "buy-PFV"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("jǐ", "how-many"), ("zhāng", "CL"), ("zhuōzi", "table")]
    glossedWords := [⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'ā', 'n']]⟩, ⟨[['m', 'ǎ', 'i'], ['l', 'e']], [['b', 'u', 'y'], ['P', 'F', 'V']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['j', 'ǐ']], [['h', 'o', 'w'], ['m', 'a', 'n', 'y']]⟩, ⟨[['z', 'h', 'ā', 'n', 'g']], [['C', 'L']]⟩, ⟨[['z', 'h', 'u', 'ō', 'z', 'i']], [['t', 'a', 'b', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("wh", "numeral"), ("modifier", "pre-nominal")] }

def ex_11 : Datum :=
  { id := "wangsun2026_11"
    source := ⟨"wang-sun-2026", "(33a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "sān bēi jiǔ"
    glossedTokens := [("sān", "three"), ("bēi", "glass"), ("jiǔ", "liquor")]
    glossedWords := [⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['b', 'ē', 'i']], [['g', 'l', 'a', 's', 's']]⟩, ⟨[['j', 'i', 'ǔ']], [['l', 'i', 'q', 'u', 'o', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "none"), ("reading", "sortal")] }

def ex_12 : Datum :=
  { id := "wangsun2026_12"
    source := ⟨"wang-sun-2026", "(33b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "sān bēi de jiǔ"
    glossedTokens := [("sān", "three"), ("bēi", "glass"), ("de", "DE"), ("jiǔ", "liquor")]
    glossedWords := [⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['b', 'ē', 'i']], [['g', 'l', 'a', 's', 's']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['j', 'i', 'ǔ']], [['l', 'i', 'q', 'u', 'o', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "de"), ("reading", "mensural")] }

def ex_13 : Datum :=
  { id := "wangsun2026_13"
    source := ⟨"wang-sun-2026", "(31)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "nà hěn dà de yī zhāng zhuōzi"
    glossedTokens := [("nà", "that"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("yī", "one"), ("zhāng", "CL"), ("zhuōzi", "table")]
    glossedWords := [⟨[['n', 'à']], [['t', 'h', 'a', 't']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['y', 'ī']], [['o', 'n', 'e']]⟩, ⟨[['z', 'h', 'ā', 'n', 'g']], [['C', 'L']]⟩, ⟨[['z', 'h', 'u', 'ō', 'z', 'i']], [['t', 'a', 'b', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "de-marked"), ("position", "D _ Num")] }

def ex_14 : Datum :=
  { id := "wangsun2026_14"
    source := ⟨"wang-sun-2026", "(37a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "hěn míngguì de sān gè bēizi de jiǔ"
    glossedTokens := [("hěn", "very"), ("míngguì", "expensive"), ("de", "DE"), ("sān", "three"), ("gè", "CL"), ("bēizi", "glass"), ("de", "DE"), ("jiǔ", "liquor")]
    glossedWords := [⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['m', 'í', 'n', 'g', 'g', 'u', 'ì']], [['e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩, ⟨[['b', 'ē', 'i', 'z', 'i']], [['g', 'l', 'a', 's', 's']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['j', 'i', 'ǔ']], [['l', 'i', 'q', 'u', 'o', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "two de-marked"), ("target", "D")] }

def ex_15 : Datum :=
  { id := "wangsun2026_15"
    source := ⟨"wang-sun-2026", "(37b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "hěn dà de sān gè bēizi de jiǔ"
    glossedTokens := [("hěn", "very"), ("dà", "big"), ("de", "DE"), ("sān", "three"), ("gè", "CL"), ("bēizi", "glass"), ("de", "DE"), ("jiǔ", "liquor")]
    glossedWords := [⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩, ⟨[['b', 'ē', 'i', 'z', 'i']], [['g', 'l', 'a', 's', 's']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['j', 'i', 'ǔ']], [['l', 'i', 'q', 'u', 'o', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "nested de-marked")] }

def ex_16 : Datum :=
  { id := "wangsun2026_16"
    source := ⟨"wang-sun-2026", "(43a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Sān gè píngguǒ, Zhāngsān chī-le."
    glossedTokens := [("Sān", "three"), ("gè", "CL"), ("píngguǒ", "apple"), ("Zhāngsān", "Zhangsān"), ("chī-le", "eat-PFV")]
    glossedWords := [⟨[['S', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩, ⟨[['p', 'í', 'n', 'g', 'g', 'u', 'ǒ']], [['a', 'p', 'p', 'l', 'e']]⟩, ⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'ā', 'n']]⟩, ⟨[['c', 'h', 'ī'], ['l', 'e']], [['e', 'a', 't'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topicalisation", "D")] }

def ex_17 : Datum :=
  { id := "wangsun2026_17"
    source := ⟨"wang-sun-2026", "(44a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ, Zhāngsān chī-le sān gè hěn dà de."
    glossedTokens := [("Píngguǒ", "apple"), ("Zhāngsān", "Zhangsān"), ("chī-le", "eat-PFV"), ("sān", "three"), ("gè", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE")]
    glossedWords := [⟨[['P', 'í', 'n', 'g', 'g', 'u', 'ǒ']], [['a', 'p', 'p', 'l', 'e']]⟩, ⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'ā', 'n']]⟩, ⟨[['c', 'h', 'ī'], ['l', 'e']], [['e', 'a', 't'], ['P', 'F', 'V']]⟩, ⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topicalisation", "N"), ("modifier", "2-part of Cl")] }

def ex_18 : Datum :=
  { id := "wangsun2026_18"
    source := ⟨"wang-sun-2026", "(44b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ, Zhāngsān chī-le hěn dà de sān gè."
    glossedTokens := [("Píngguǒ", "apple"), ("Zhāngsān", "Zhangsān"), ("chī-le", "eat-PFV"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("sān", "three"), ("gè", "CL")]
    glossedWords := [⟨[['P', 'í', 'n', 'g', 'g', 'u', 'ǒ']], [['a', 'p', 'p', 'l', 'e']]⟩, ⟨[['Z', 'h', 'ā', 'n', 'g', 's', 'ā', 'n']], [['Z', 'h', 'a', 'n', 'g', 's', 'ā', 'n']]⟩, ⟨[['c', 'h', 'ī'], ['l', 'e']], [['e', 'a', 't'], ['P', 'F', 'V']]⟩, ⟨[['h', 'ě', 'n']], [['v', 'e', 'r', 'y']]⟩, ⟨[['d', 'à']], [['b', 'i', 'g']]⟩, ⟨[['d', 'e']], [['D', 'E']]⟩, ⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['g', 'è']], [['C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("topicalisation", "N"), ("modifier", "2-part of D")] }

def ex_19 : Datum :=
  { id := "wangsun2026_19"
    source := ⟨"wang-sun-2026", "(45a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ bǐ yīngtáo duō sān kē."
    glossedTokens := [("Píngguǒ", "apple"), ("bǐ", "than"), ("yīngtáo", "cherry"), ("duō", "much"), ("sān", "three"), ("kē", "CL")]
    glossedWords := [⟨[['P', 'í', 'n', 'g', 'g', 'u', 'ǒ']], [['a', 'p', 'p', 'l', 'e']]⟩, ⟨[['b', 'ǐ']], [['t', 'h', 'a', 'n']]⟩, ⟨[['y', 'ī', 'n', 'g', 't', 'á', 'o']], [['c', 'h', 'e', 'r', 'r', 'y']]⟩, ⟨[['d', 'u', 'ō']], [['m', 'u', 'c', 'h']]⟩, ⟨[['s', 'ā', 'n']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['k', 'ē']], [['C', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "measure"), ("noun", "absent")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19]

end WangSun2026.Examples
