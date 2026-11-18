module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Jenks2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Jenks2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jenks2018.Examples`.
-/

@[expose] public section

namespace Jenks2018.Examples

def ex_10a : Datum :=
  { id := "jenks2018_10a"
    source := ⟨"chen-2004", "p. 1165"⟩
    reportedIn := some ⟨"jenks-2018", "(10a)"⟩
    language := "mand1415"
    primaryText := "Yueliang sheng shang lai le."
    glossedTokens := [("Yueliang", "moon"), ("sheng", "rise"), ("shang", "up"), ("lai", "come"), ("le", "LE")]
    glossedWords := [⟨['Y', 'u', 'e', 'l', 'i', 'a', 'n', 'g'], ['m', 'o', 'o', 'n'], [⟨['Y', 'u', 'e', 'l', 'i', 'a', 'n', 'g'], ['m', 'o', 'o', 'n'], none⟩]⟩, ⟨['s', 'h', 'e', 'n', 'g'], ['r', 'i', 's', 'e'], [⟨['s', 'h', 'e', 'n', 'g'], ['r', 'i', 's', 'e'], none⟩]⟩, ⟨['s', 'h', 'a', 'n', 'g'], ['u', 'p'], [⟨['s', 'h', 'a', 'n', 'g'], ['u', 'p'], none⟩]⟩, ⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], [⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_10b_bare : Datum :=
  { id := "jenks2018_10b_bare"
    source := ⟨"jenks-2018", "(10b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Taiwan (de) zongtong hen shengqi."
    glossedTokens := [("Taiwan", "Taiwan"), ("(de)", "MOD"), ("zongtong", "president"), ("hen", "very"), ("shengqi", "angry")]
    glossedWords := [⟨['T', 'a', 'i', 'w', 'a', 'n'], ['T', 'a', 'i', 'w', 'a', 'n'], [⟨['T', 'a', 'i', 'w', 'a', 'n'], ['T', 'a', 'i', 'w', 'a', 'n'], none⟩]⟩, ⟨['(', 'd', 'e', ')'], ['M', 'O', 'D'], [⟨['d', 'e'], ['M', 'O', 'D'], none⟩]⟩, ⟨['z', 'o', 'n', 'g', 't', 'o', 'n', 'g'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], [⟨['z', 'o', 'n', 'g', 't', 'o', 'n', 'g'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['s', 'h', 'e', 'n', 'g', 'q', 'i'], ['a', 'n', 'g', 'r', 'y'], [⟨['s', 'h', 'e', 'n', 'g', 'q', 'i'], ['a', 'n', 'g', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 3, "definite", none⟩]
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_10b_na : Datum :=
  { id := "jenks2018_10b_na"
    source := ⟨"jenks-2018", "(10b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na ge Taiwan (de) zongtong hen shengqi."
    glossedTokens := [("Na", "that"), ("ge", "CLF"), ("Taiwan", "Taiwan"), ("(de)", "MOD"), ("zongtong", "president"), ("hen", "very"), ("shengqi", "angry")]
    glossedWords := [⟨['N', 'a'], ['t', 'h', 'a', 't'], [⟨['N', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['T', 'a', 'i', 'w', 'a', 'n'], ['T', 'a', 'i', 'w', 'a', 'n'], [⟨['T', 'a', 'i', 'w', 'a', 'n'], ['T', 'a', 'i', 'w', 'a', 'n'], none⟩]⟩, ⟨['(', 'd', 'e', ')'], ['M', 'O', 'D'], [⟨['d', 'e'], ['M', 'O', 'D'], none⟩]⟩, ⟨['z', 'o', 'n', 'g', 't', 'o', 'n', 'g'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], [⟨['z', 'o', 'n', 'g', 't', 'o', 'n', 'g'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['s', 'h', 'e', 'n', 'g', 'q', 'i'], ['a', 'n', 'g', 'r', 'y'], [⟨['s', 'h', 'e', 'n', 'g', 'q', 'i'], ['a', 'n', 'g', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨0, 5, "definite", none⟩, ⟨0, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_10b_zhe : Datum :=
  { id := "jenks2018_10b_zhe"
    source := ⟨"jenks-2018", "(10b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Zhe ge Taiwan (de) zongtong hen shengqi."
    glossedTokens := [("Zhe", "this"), ("ge", "CLF"), ("Taiwan", "Taiwan"), ("(de)", "MOD"), ("zongtong", "president"), ("hen", "very"), ("shengqi", "angry")]
    glossedWords := [⟨['Z', 'h', 'e'], ['t', 'h', 'i', 's'], [⟨['Z', 'h', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['T', 'a', 'i', 'w', 'a', 'n'], ['T', 'a', 'i', 'w', 'a', 'n'], [⟨['T', 'a', 'i', 'w', 'a', 'n'], ['T', 'a', 'i', 'w', 'a', 'n'], none⟩]⟩, ⟨['(', 'd', 'e', ')'], ['M', 'O', 'D'], [⟨['d', 'e'], ['M', 'O', 'D'], none⟩]⟩, ⟨['z', 'o', 'n', 'g', 't', 'o', 'n', 'g'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], [⟨['z', 'o', 'n', 'g', 't', 'o', 'n', 'g'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['s', 'h', 'e', 'n', 'g', 'q', 'i'], ['a', 'n', 'g', 'r', 'y'], [⟨['s', 'h', 'e', 'n', 'g', 'q', 'i'], ['a', 'n', 'g', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨0, 5, "definite", none⟩, ⟨0, 1, "determiner", some "zhe"⟩]
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_11a : Datum :=
  { id := "jenks2018_11a"
    source := ⟨"cheng-sybesma-1999", ""⟩
    reportedIn := some ⟨"jenks-2018", "(11a)"⟩
    language := "mand1415"
    primaryText := "Hufei he-wan-le tang."
    glossedTokens := [("Hufei", "Hufei"), ("he-wan-le", "drink-finish-LE"), ("tang", "soup")]
    glossedWords := [⟨['H', 'u', 'f', 'e', 'i'], ['H', 'u', 'f', 'e', 'i'], [⟨['H', 'u', 'f', 'e', 'i'], ['H', 'u', 'f', 'e', 'i'], none⟩]⟩, ⟨['h', 'e', '-', 'w', 'a', 'n', '-', 'l', 'e'], ['d', 'r', 'i', 'n', 'k', '-', 'f', 'i', 'n', 'i', 's', 'h', '-', 'L', 'E'], [⟨['h', 'e'], ['d', 'r', 'i', 'n', 'k'], none⟩, ⟨['w', 'a', 'n'], ['f', 'i', 'n', 'i', 's', 'h'], some '-'⟩, ⟨['l', 'e'], ['L', 'E'], some '-'⟩]⟩, ⟨['t', 'a', 'n', 'g'], ['s', 'o', 'u', 'p'], [⟨['t', 'a', 'n', 'g'], ['s', 'o', 'u', 'p'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "definite", none⟩]
    paperFeatures := [("section", "3.1"), ("environment", "immediateSituation"), ("position", "object")] }

def ex_11b : Datum :=
  { id := "jenks2018_11b"
    source := ⟨"cheng-sybesma-1999", "p. 510"⟩
    reportedIn := some ⟨"jenks-2018", "(11b)"⟩
    language := "mand1415"
    primaryText := "Gou yao guo malu."
    glossedTokens := [("Gou", "dog"), ("yao", "want"), ("guo", "cross"), ("malu", "road")]
    glossedWords := [⟨['G', 'o', 'u'], ['d', 'o', 'g'], [⟨['G', 'o', 'u'], ['d', 'o', 'g'], none⟩]⟩, ⟨['y', 'a', 'o'], ['w', 'a', 'n', 't'], [⟨['y', 'a', 'o'], ['w', 'a', 'n', 't'], none⟩]⟩, ⟨['g', 'u', 'o'], ['c', 'r', 'o', 's', 's'], [⟨['g', 'u', 'o'], ['c', 'r', 'o', 's', 's'], none⟩]⟩, ⟨['m', 'a', 'l', 'u'], ['r', 'o', 'a', 'd'], [⟨['m', 'a', 'l', 'u'], ['r', 'o', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "3.1"), ("environment", "immediateSituation"), ("position", "subject")] }

def ex_14a : Datum :=
  { id := "jenks2018_14a"
    source := ⟨"jenks-2018", "(14a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Chezi bei jingcha lanjie le yinwei mei you tiezhi zai paizhao shang."
    glossedTokens := [("Chezi", "car"), ("bei", "PASS"), ("jingcha", "police"), ("lanjie", "intercept"), ("le", "LE"), ("yinwei", "because"), ("mei", "NEG"), ("you", "have"), ("tiezhi", "sticker"), ("zai", "at"), ("paizhao", "license.plate"), ("shang", "on")]
    glossedWords := [⟨['C', 'h', 'e', 'z', 'i'], ['c', 'a', 'r'], [⟨['C', 'h', 'e', 'z', 'i'], ['c', 'a', 'r'], none⟩]⟩, ⟨['b', 'e', 'i'], ['P', 'A', 'S', 'S'], [⟨['b', 'e', 'i'], ['P', 'A', 'S', 'S'], none⟩]⟩, ⟨['j', 'i', 'n', 'g', 'c', 'h', 'a'], ['p', 'o', 'l', 'i', 'c', 'e'], [⟨['j', 'i', 'n', 'g', 'c', 'h', 'a'], ['p', 'o', 'l', 'i', 'c', 'e'], none⟩]⟩, ⟨['l', 'a', 'n', 'j', 'i', 'e'], ['i', 'n', 't', 'e', 'r', 'c', 'e', 'p', 't'], [⟨['l', 'a', 'n', 'j', 'i', 'e'], ['i', 'n', 't', 'e', 'r', 'c', 'e', 'p', 't'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['y', 'i', 'n', 'w', 'e', 'i'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], [⟨['y', 'i', 'n', 'w', 'e', 'i'], ['b', 'e', 'c', 'a', 'u', 's', 'e'], none⟩]⟩, ⟨['m', 'e', 'i'], ['N', 'E', 'G'], [⟨['m', 'e', 'i'], ['N', 'E', 'G'], none⟩]⟩, ⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], [⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['t', 'i', 'e', 'z', 'h', 'i'], ['s', 't', 'i', 'c', 'k', 'e', 'r'], [⟨['t', 'i', 'e', 'z', 'h', 'i'], ['s', 't', 'i', 'c', 'k', 'e', 'r'], none⟩]⟩, ⟨['z', 'a', 'i'], ['a', 't'], [⟨['z', 'a', 'i'], ['a', 't'], none⟩]⟩, ⟨['p', 'a', 'i', 'z', 'h', 'a', 'o'], ['l', 'i', 'c', 'e', 'n', 's', 'e', '.', 'p', 'l', 'a', 't', 'e'], [⟨['p', 'a', 'i', 'z', 'h', 'a', 'o'], ['l', 'i', 'c', 'e', 'n', 's', 'e', '.', 'p', 'l', 'a', 't', 'e'], none⟩]⟩, ⟨['s', 'h', 'a', 'n', 'g'], ['o', 'n'], [⟨['s', 'h', 'a', 'n', 'g'], ['o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "definite", none⟩]
    paperFeatures := [("section", "3.1"), ("environment", "partWholeBridging"), ("position", "object")] }

def ex_14b_bare : Datum :=
  { id := "jenks2018_14b_bare"
    source := ⟨"jenks-2018", "(14b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Paul renwei na shou shi hen youmei, jishi ta bu renshi shiren."
    glossedTokens := [("Paul", "Paul"), ("renwei", "think"), ("na", "that"), ("shou", "CLF"), ("shi", "poem"), ("hen", "very"), ("youmei", "beautiful"), ("jishi", "although"), ("ta", "he"), ("bu", "NEG"), ("renshi", "know"), ("shiren", "poet")]
    glossedWords := [⟨['P', 'a', 'u', 'l'], ['P', 'a', 'u', 'l'], [⟨['P', 'a', 'u', 'l'], ['P', 'a', 'u', 'l'], none⟩]⟩, ⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], [⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'h', 'o', 'u'], ['C', 'L', 'F'], [⟨['s', 'h', 'o', 'u'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'h', 'i'], ['p', 'o', 'e', 'm'], [⟨['s', 'h', 'i'], ['p', 'o', 'e', 'm'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['y', 'o', 'u', 'm', 'e', 'i'], ['b', 'e', 'a', 'u', 't', 'i', 'f', 'u', 'l'], [⟨['y', 'o', 'u', 'm', 'e', 'i'], ['b', 'e', 'a', 'u', 't', 'i', 'f', 'u', 'l'], none⟩]⟩, ⟨['j', 'i', 's', 'h', 'i'], ['a', 'l', 't', 'h', 'o', 'u', 'g', 'h'], [⟨['j', 'i', 's', 'h', 'i'], ['a', 'l', 't', 'h', 'o', 'u', 'g', 'h'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['b', 'u'], ['N', 'E', 'G'], [⟨['b', 'u'], ['N', 'E', 'G'], none⟩]⟩, ⟨['r', 'e', 'n', 's', 'h', 'i'], ['k', 'n', 'o', 'w'], [⟨['r', 'e', 'n', 's', 'h', 'i'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['s', 'h', 'i', 'r', 'e', 'n'], ['p', 'o', 'e', 't'], [⟨['s', 'h', 'i', 'r', 'e', 'n'], ['p', 'o', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨11, 1, "definite", none⟩]
    paperFeatures := [("section", "3.1"), ("environment", "producerBridging"), ("position", "object")] }

def ex_14b_dem : Datum :=
  { id := "jenks2018_14b_dem"
    source := ⟨"jenks-2018", "(14b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Paul renwei na shou shi hen youmei, jishi ta bu renshi na wei shiren."
    glossedTokens := [("Paul", "Paul"), ("renwei", "think"), ("na", "that"), ("shou", "CLF"), ("shi", "poem"), ("hen", "very"), ("youmei", "beautiful"), ("jishi", "although"), ("ta", "he"), ("bu", "NEG"), ("renshi", "know"), ("na", "that"), ("wei", "CLF"), ("shiren", "poet")]
    glossedWords := [⟨['P', 'a', 'u', 'l'], ['P', 'a', 'u', 'l'], [⟨['P', 'a', 'u', 'l'], ['P', 'a', 'u', 'l'], none⟩]⟩, ⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], [⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'h', 'o', 'u'], ['C', 'L', 'F'], [⟨['s', 'h', 'o', 'u'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'h', 'i'], ['p', 'o', 'e', 'm'], [⟨['s', 'h', 'i'], ['p', 'o', 'e', 'm'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['y', 'o', 'u', 'm', 'e', 'i'], ['b', 'e', 'a', 'u', 't', 'i', 'f', 'u', 'l'], [⟨['y', 'o', 'u', 'm', 'e', 'i'], ['b', 'e', 'a', 'u', 't', 'i', 'f', 'u', 'l'], none⟩]⟩, ⟨['j', 'i', 's', 'h', 'i'], ['a', 'l', 't', 'h', 'o', 'u', 'g', 'h'], [⟨['j', 'i', 's', 'h', 'i'], ['a', 'l', 't', 'h', 'o', 'u', 'g', 'h'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['b', 'u'], ['N', 'E', 'G'], [⟨['b', 'u'], ['N', 'E', 'G'], none⟩]⟩, ⟨['r', 'e', 'n', 's', 'h', 'i'], ['k', 'n', 'o', 'w'], [⟨['r', 'e', 'n', 's', 'h', 'i'], ['k', 'n', 'o', 'w'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['w', 'e', 'i'], ['C', 'L', 'F'], [⟨['w', 'e', 'i'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'h', 'i', 'r', 'e', 'n'], ['p', 'o', 'e', 't'], [⟨['s', 'h', 'i', 'r', 'e', 'n'], ['p', 'o', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨11, 3, "definite", none⟩, ⟨11, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.1"), ("environment", "producerBridging"), ("position", "object")] }

def ex_15b_bare : Datum :=
  { id := "jenks2018_15b_bare"
    source := ⟨"jenks-2018", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo zuotian yudao nansheng."
    glossedTokens := [("Wo", "I"), ("zuotian", "yesterday"), ("yudao", "meet"), ("nansheng", "boy")]
    glossedWords := [⟨['W', 'o'], ['I'], [⟨['W', 'o'], ['I'], none⟩]⟩, ⟨['z', 'u', 'o', 't', 'i', 'a', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['z', 'u', 'o', 't', 'i', 'a', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['y', 'u', 'd', 'a', 'o'], ['m', 'e', 'e', 't'], [⟨['y', 'u', 'd', 'a', 'o'], ['m', 'e', 'e', 't'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "definite", none⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "object")] }

def ex_15b_dem : Datum :=
  { id := "jenks2018_15b_dem"
    source := ⟨"jenks-2018", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo zuotian yudao na ge nansheng."
    glossedTokens := [("Wo", "I"), ("zuotian", "yesterday"), ("yudao", "meet"), ("na", "that"), ("ge", "CLF"), ("nansheng", "boy")]
    glossedWords := [⟨['W', 'o'], ['I'], [⟨['W', 'o'], ['I'], none⟩]⟩, ⟨['z', 'u', 'o', 't', 'i', 'a', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['z', 'u', 'o', 't', 'i', 'a', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['y', 'u', 'd', 'a', 'o'], ['m', 'e', 'e', 't'], [⟨['y', 'u', 'd', 'a', 'o'], ['m', 'e', 'e', 't'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 3, "definite", none⟩, ⟨3, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "object")] }

def ex_15c_bare : Datum :=
  { id := "jenks2018_15c_bare"
    source := ⟨"jenks-2018", "(15c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo dai gei nansheng yi ge liwu."
    glossedTokens := [("Wo", "I"), ("dai", "bring"), ("gei", "give"), ("nansheng", "boy"), ("yi", "one"), ("ge", "CLF"), ("liwu", "gift")]
    glossedWords := [⟨['W', 'o'], ['I'], [⟨['W', 'o'], ['I'], none⟩]⟩, ⟨['d', 'a', 'i'], ['b', 'r', 'i', 'n', 'g'], [⟨['d', 'a', 'i'], ['b', 'r', 'i', 'n', 'g'], none⟩]⟩, ⟨['g', 'e', 'i'], ['g', 'i', 'v', 'e'], [⟨['g', 'e', 'i'], ['g', 'i', 'v', 'e'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['y', 'i'], ['o', 'n', 'e'], [⟨['y', 'i'], ['o', 'n', 'e'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['l', 'i', 'w', 'u'], ['g', 'i', 'f', 't'], [⟨['l', 'i', 'w', 'u'], ['g', 'i', 'f', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨3, 1, "definite", none⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "indirectObject")] }

def ex_15c_dem : Datum :=
  { id := "jenks2018_15c_dem"
    source := ⟨"jenks-2018", "(15c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo dai gei na ge nansheng yi ge liwu."
    glossedTokens := [("Wo", "I"), ("dai", "bring"), ("gei", "give"), ("na", "that"), ("ge", "CLF"), ("nansheng", "boy"), ("yi", "one"), ("ge", "CLF"), ("liwu", "gift")]
    glossedWords := [⟨['W', 'o'], ['I'], [⟨['W', 'o'], ['I'], none⟩]⟩, ⟨['d', 'a', 'i'], ['b', 'r', 'i', 'n', 'g'], [⟨['d', 'a', 'i'], ['b', 'r', 'i', 'n', 'g'], none⟩]⟩, ⟨['g', 'e', 'i'], ['g', 'i', 'v', 'e'], [⟨['g', 'e', 'i'], ['g', 'i', 'v', 'e'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['y', 'i'], ['o', 'n', 'e'], [⟨['y', 'i'], ['o', 'n', 'e'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['l', 'i', 'w', 'u'], ['g', 'i', 'f', 't'], [⟨['l', 'i', 'w', 'u'], ['g', 'i', 'f', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 3, "definite", none⟩, ⟨3, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "indirectObject")] }

def ex_15d_bare : Datum :=
  { id := "jenks2018_15d_bare"
    source := ⟨"jenks-2018", "(15d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Nansheng kanqilai you er-shi sui zuoyou."
    glossedTokens := [("Nansheng", "boy"), ("kanqilai", "look"), ("you", "have"), ("er-shi", "two-ten"), ("sui", "year"), ("zuoyou", "or.so")]
    glossedWords := [⟨['N', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['N', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['k', 'a', 'n', 'q', 'i', 'l', 'a', 'i'], ['l', 'o', 'o', 'k'], [⟨['k', 'a', 'n', 'q', 'i', 'l', 'a', 'i'], ['l', 'o', 'o', 'k'], none⟩]⟩, ⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], [⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['e', 'r', '-', 's', 'h', 'i'], ['t', 'w', 'o', '-', 't', 'e', 'n'], [⟨['e', 'r'], ['t', 'w', 'o'], none⟩, ⟨['s', 'h', 'i'], ['t', 'e', 'n'], some '-'⟩]⟩, ⟨['s', 'u', 'i'], ['y', 'e', 'a', 'r'], [⟨['s', 'u', 'i'], ['y', 'e', 'a', 'r'], none⟩]⟩, ⟨['z', 'u', 'o', 'y', 'o', 'u'], ['o', 'r', '.', 's', 'o'], [⟨['z', 'u', 'o', 'y', 'o', 'u'], ['o', 'r', '.', 's', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "subject"), ("topic", "continuing")] }

def ex_15d_dem : Datum :=
  { id := "jenks2018_15d_dem"
    source := ⟨"jenks-2018", "(15d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na ge nansheng kanqilai you er-shi sui zuoyou."
    glossedTokens := [("Na", "that"), ("ge", "CLF"), ("nansheng", "boy"), ("kanqilai", "look"), ("you", "have"), ("er-shi", "two-ten"), ("sui", "year"), ("zuoyou", "or.so")]
    glossedWords := [⟨['N', 'a'], ['t', 'h', 'a', 't'], [⟨['N', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['k', 'a', 'n', 'q', 'i', 'l', 'a', 'i'], ['l', 'o', 'o', 'k'], [⟨['k', 'a', 'n', 'q', 'i', 'l', 'a', 'i'], ['l', 'o', 'o', 'k'], none⟩]⟩, ⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], [⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['e', 'r', '-', 's', 'h', 'i'], ['t', 'w', 'o', '-', 't', 'e', 'n'], [⟨['e', 'r'], ['t', 'w', 'o'], none⟩, ⟨['s', 'h', 'i'], ['t', 'e', 'n'], some '-'⟩]⟩, ⟨['s', 'u', 'i'], ['y', 'e', 'a', 'r'], [⟨['s', 'u', 'i'], ['y', 'e', 'a', 'r'], none⟩]⟩, ⟨['z', 'u', 'o', 'y', 'o', 'u'], ['o', 'r', '.', 's', 'o'], [⟨['z', 'u', 'o', 'y', 'o', 'u'], ['o', 'r', '.', 's', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 3, "definite", none⟩, ⟨0, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "subject"), ("topic", "continuing")] }

def ex_15e_bare : Datum :=
  { id := "jenks2018_15e_bare"
    source := ⟨"jenks-2018", "(15e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo bu renwei nansheng hen youqu."
    glossedTokens := [("Wo", "I"), ("bu", "NEG"), ("renwei", "think"), ("nansheng", "boy"), ("hen", "very"), ("youqu", "interesting")]
    glossedWords := [⟨['W', 'o'], ['I'], [⟨['W', 'o'], ['I'], none⟩]⟩, ⟨['b', 'u'], ['N', 'E', 'G'], [⟨['b', 'u'], ['N', 'E', 'G'], none⟩]⟩, ⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], [⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['y', 'o', 'u', 'q', 'u'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], [⟨['y', 'o', 'u', 'q', 'u'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    spans := [⟨3, 1, "definite", none⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("topic", "continuing")] }

def ex_15e_dem : Datum :=
  { id := "jenks2018_15e_dem"
    source := ⟨"jenks-2018", "(15e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo bu renwei na ge nansheng hen youqu."
    glossedTokens := [("Wo", "I"), ("bu", "NEG"), ("renwei", "think"), ("na", "that"), ("ge", "CLF"), ("nansheng", "boy"), ("hen", "very"), ("youqu", "interesting")]
    glossedWords := [⟨['W', 'o'], ['I'], [⟨['W', 'o'], ['I'], none⟩]⟩, ⟨['b', 'u'], ['N', 'E', 'G'], [⟨['b', 'u'], ['N', 'E', 'G'], none⟩]⟩, ⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], [⟨['r', 'e', 'n', 'w', 'e', 'i'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], [⟨['h', 'e', 'n'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['y', 'o', 'u', 'q', 'u'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], [⟨['y', 'o', 'u', 'q', 'u'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 3, "definite", none⟩, ⟨3, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("topic", "continuing")] }

def ex_16b : Datum :=
  { id := "jenks2018_16b"
    source := ⟨"jenks-2018", "(16b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Jingcha huaiyi na ge nuren nashihou shou le shang."
    glossedTokens := [("Jingcha", "police"), ("huaiyi", "suspect"), ("na", "that"), ("ge", "CLF"), ("nuren", "woman"), ("nashihou", "at.that.moment"), ("shou", "suffer"), ("le", "LE"), ("shang", "injury")]
    glossedWords := [⟨['J', 'i', 'n', 'g', 'c', 'h', 'a'], ['p', 'o', 'l', 'i', 'c', 'e'], [⟨['J', 'i', 'n', 'g', 'c', 'h', 'a'], ['p', 'o', 'l', 'i', 'c', 'e'], none⟩]⟩, ⟨['h', 'u', 'a', 'i', 'y', 'i'], ['s', 'u', 's', 'p', 'e', 'c', 't'], [⟨['h', 'u', 'a', 'i', 'y', 'i'], ['s', 'u', 's', 'p', 'e', 'c', 't'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['n', 'u', 'r', 'e', 'n'], ['w', 'o', 'm', 'a', 'n'], [⟨['n', 'u', 'r', 'e', 'n'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['n', 'a', 's', 'h', 'i', 'h', 'o', 'u'], ['a', 't', '.', 't', 'h', 'a', 't', '.', 'm', 'o', 'm', 'e', 'n', 't'], [⟨['n', 'a', 's', 'h', 'i', 'h', 'o', 'u'], ['a', 't', '.', 't', 'h', 'a', 't', '.', 'm', 'o', 'm', 'e', 'n', 't'], none⟩]⟩, ⟨['s', 'h', 'o', 'u'], ['s', 'u', 'f', 'f', 'e', 'r'], [⟨['s', 'h', 'o', 'u'], ['s', 'u', 'f', 'f', 'e', 'r'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['s', 'h', 'a', 'n', 'g'], ['i', 'n', 'j', 'u', 'r', 'y'], [⟨['s', 'h', 'a', 'n', 'g'], ['i', 'n', 'j', 'u', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 3, "definite", none⟩, ⟨2, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject")] }

def ex_16c : Datum :=
  { id := "jenks2018_16c"
    source := ⟨"jenks-2018", "(16c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Jingcha huaiyi nuren nashihou shou le shang."
    glossedTokens := [("Jingcha", "police"), ("huaiyi", "suspect"), ("nuren", "woman"), ("nashihou", "at.that.moment"), ("shou", "suffer"), ("le", "LE"), ("shang", "injury")]
    glossedWords := [⟨['J', 'i', 'n', 'g', 'c', 'h', 'a'], ['p', 'o', 'l', 'i', 'c', 'e'], [⟨['J', 'i', 'n', 'g', 'c', 'h', 'a'], ['p', 'o', 'l', 'i', 'c', 'e'], none⟩]⟩, ⟨['h', 'u', 'a', 'i', 'y', 'i'], ['s', 'u', 's', 'p', 'e', 'c', 't'], [⟨['h', 'u', 'a', 'i', 'y', 'i'], ['s', 'u', 's', 'p', 'e', 'c', 't'], none⟩]⟩, ⟨['n', 'u', 'r', 'e', 'n'], ['w', 'o', 'm', 'a', 'n'], [⟨['n', 'u', 'r', 'e', 'n'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩, ⟨['n', 'a', 's', 'h', 'i', 'h', 'o', 'u'], ['a', 't', '.', 't', 'h', 'a', 't', '.', 'm', 'o', 'm', 'e', 'n', 't'], [⟨['n', 'a', 's', 'h', 'i', 'h', 'o', 'u'], ['a', 't', '.', 't', 'h', 'a', 't', '.', 'm', 'o', 'm', 'e', 'n', 't'], none⟩]⟩, ⟨['s', 'h', 'o', 'u'], ['s', 'u', 'f', 'f', 'e', 'r'], [⟨['s', 'h', 'o', 'u'], ['s', 'u', 'f', 'f', 'e', 'r'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['s', 'h', 'a', 'n', 'g'], ['i', 'n', 'j', 'u', 'r', 'y'], [⟨['s', 'h', 'a', 'n', 'g'], ['i', 'n', 'j', 'u', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("definite", .unacceptable)]
    spans := [⟨2, 1, "definite", none⟩]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject")] }

def ex_18b : Datum :=
  { id := "jenks2018_18b"
    source := ⟨"cheng-huang-1996", "p. 130, (22d)"⟩
    reportedIn := some ⟨"jenks-2018", "(18b)"⟩
    language := "mand1415"
    primaryText := "Ni jiao shei jinlai, wo dou jian na ge ren."
    glossedTokens := [("Ni", "you"), ("jiao", "ask"), ("shei", "who"), ("jinlai", "enter"), ("wo", "I"), ("dou", "all"), ("jian", "see"), ("na", "that"), ("ge", "CLF"), ("ren", "person")]
    glossedWords := [⟨['N', 'i'], ['y', 'o', 'u'], [⟨['N', 'i'], ['y', 'o', 'u'], none⟩]⟩, ⟨['j', 'i', 'a', 'o'], ['a', 's', 'k'], [⟨['j', 'i', 'a', 'o'], ['a', 's', 'k'], none⟩]⟩, ⟨['s', 'h', 'e', 'i'], ['w', 'h', 'o'], [⟨['s', 'h', 'e', 'i'], ['w', 'h', 'o'], none⟩]⟩, ⟨['j', 'i', 'n', 'l', 'a', 'i'], ['e', 'n', 't', 'e', 'r'], [⟨['j', 'i', 'n', 'l', 'a', 'i'], ['e', 'n', 't', 'e', 'r'], none⟩]⟩, ⟨['w', 'o'], ['I'], [⟨['w', 'o'], ['I'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['j', 'i', 'a', 'n'], ['s', 'e', 'e'], [⟨['j', 'i', 'a', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨7, 3, "definite", none⟩, ⟨7, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object")] }

def ex_19 : Datum :=
  { id := "jenks2018_19"
    source := ⟨"jenks-2018", "(19)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ni jiao shei jinlai, wo dou jian ren."
    glossedTokens := [("Ni", "you"), ("jiao", "ask"), ("shei", "who"), ("jinlai", "enter"), ("wo", "I"), ("dou", "all"), ("jian", "see"), ("ren", "person")]
    glossedWords := [⟨['N', 'i'], ['y', 'o', 'u'], [⟨['N', 'i'], ['y', 'o', 'u'], none⟩]⟩, ⟨['j', 'i', 'a', 'o'], ['a', 's', 'k'], [⟨['j', 'i', 'a', 'o'], ['a', 's', 'k'], none⟩]⟩, ⟨['s', 'h', 'e', 'i'], ['w', 'h', 'o'], [⟨['s', 'h', 'e', 'i'], ['w', 'h', 'o'], none⟩]⟩, ⟨['j', 'i', 'n', 'l', 'a', 'i'], ['e', 'n', 't', 'e', 'r'], [⟨['j', 'i', 'n', 'l', 'a', 'i'], ['e', 'n', 't', 'e', 'r'], none⟩]⟩, ⟨['w', 'o'], ['I'], [⟨['w', 'o'], ['I'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['j', 'i', 'a', 'n'], ['s', 'e', 'e'], [⟨['j', 'i', 'a', 'n'], ['s', 'e', 'e'], none⟩]⟩, ⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], [⟨['r', 'e', 'n'], ['p', 'e', 'r', 's', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨7, 1, "definite", none⟩]
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object")] }

def ex_20_bare : Datum :=
  { id := "jenks2018_20_bare"
    source := ⟨"jenks-2018", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge [you yi zhi shuiniu de] nongfu dou hui da shuiniu."
    glossedTokens := [("Mei", "every"), ("ge", "CLF"), ("[you", "have"), ("yi", "one"), ("zhi", "CLF"), ("shuiniu", "buffalo"), ("de]", "REL"), ("nongfu", "farmer"), ("dou", "all"), ("hui", "will"), ("da", "hit"), ("shuiniu", "buffalo")]
    glossedWords := [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['[', 'y', 'o', 'u'], ['h', 'a', 'v', 'e'], [⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['y', 'i'], ['o', 'n', 'e'], [⟨['y', 'i'], ['o', 'n', 'e'], none⟩]⟩, ⟨['z', 'h', 'i'], ['C', 'L', 'F'], [⟨['z', 'h', 'i'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], [⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], none⟩]⟩, ⟨['d', 'e', ']'], ['R', 'E', 'L'], [⟨['d', 'e'], ['R', 'E', 'L'], none⟩]⟩, ⟨['n', 'o', 'n', 'g', 'f', 'u'], ['f', 'a', 'r', 'm', 'e', 'r'], [⟨['n', 'o', 'n', 'g', 'f', 'u'], ['f', 'a', 'r', 'm', 'e', 'r'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], [⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['d', 'a'], ['h', 'i', 't'], [⟨['d', 'a'], ['h', 'i', 't'], none⟩]⟩, ⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], [⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨11, 1, "definite", none⟩]
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object")] }

def ex_20_dem : Datum :=
  { id := "jenks2018_20_dem"
    source := ⟨"jenks-2018", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge [you yi zhi shuiniu de] nongfu dou hui da na zhi shuiniu."
    glossedTokens := [("Mei", "every"), ("ge", "CLF"), ("[you", "have"), ("yi", "one"), ("zhi", "CLF"), ("shuiniu", "buffalo"), ("de]", "REL"), ("nongfu", "farmer"), ("dou", "all"), ("hui", "will"), ("da", "hit"), ("na", "that"), ("zhi", "CLF"), ("shuiniu", "buffalo")]
    glossedWords := [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['[', 'y', 'o', 'u'], ['h', 'a', 'v', 'e'], [⟨['y', 'o', 'u'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['y', 'i'], ['o', 'n', 'e'], [⟨['y', 'i'], ['o', 'n', 'e'], none⟩]⟩, ⟨['z', 'h', 'i'], ['C', 'L', 'F'], [⟨['z', 'h', 'i'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], [⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], none⟩]⟩, ⟨['d', 'e', ']'], ['R', 'E', 'L'], [⟨['d', 'e'], ['R', 'E', 'L'], none⟩]⟩, ⟨['n', 'o', 'n', 'g', 'f', 'u'], ['f', 'a', 'r', 'm', 'e', 'r'], [⟨['n', 'o', 'n', 'g', 'f', 'u'], ['f', 'a', 'r', 'm', 'e', 'r'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], [⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['d', 'a'], ['h', 'i', 't'], [⟨['d', 'a'], ['h', 'i', 't'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['z', 'h', 'i'], ['C', 'L', 'F'], [⟨['z', 'h', 'i'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], [⟨['s', 'h', 'u', 'i', 'n', 'i', 'u'], ['b', 'u', 'f', 'f', 'a', 'l', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨11, 3, "definite", none⟩, ⟨11, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object")] }

def ex_28_bare : Datum :=
  { id := "jenks2018_28_bare"
    source := ⟨"jenks-2018", "(28)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Obama mei dao yi ge chengshi ta dou gen shizhang jianmian."
    glossedTokens := [("Obama", "Obama"), ("mei", "every"), ("dao", "arrive"), ("yi", "one"), ("ge", "CLF"), ("chengshi", "city"), ("ta", "he"), ("dou", "all"), ("gen", "with"), ("shizhang", "mayor"), ("jianmian", "meet")]
    glossedWords := [⟨['O', 'b', 'a', 'm', 'a'], ['O', 'b', 'a', 'm', 'a'], [⟨['O', 'b', 'a', 'm', 'a'], ['O', 'b', 'a', 'm', 'a'], none⟩]⟩, ⟨['m', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['m', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['d', 'a', 'o'], ['a', 'r', 'r', 'i', 'v', 'e'], [⟨['d', 'a', 'o'], ['a', 'r', 'r', 'i', 'v', 'e'], none⟩]⟩, ⟨['y', 'i'], ['o', 'n', 'e'], [⟨['y', 'i'], ['o', 'n', 'e'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['c', 'h', 'e', 'n', 'g', 's', 'h', 'i'], ['c', 'i', 't', 'y'], [⟨['c', 'h', 'e', 'n', 'g', 's', 'h', 'i'], ['c', 'i', 't', 'y'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['g', 'e', 'n'], ['w', 'i', 't', 'h'], [⟨['g', 'e', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['s', 'h', 'i', 'z', 'h', 'a', 'n', 'g'], ['m', 'a', 'y', 'o', 'r'], [⟨['s', 'h', 'i', 'z', 'h', 'a', 'n', 'g'], ['m', 'a', 'y', 'o', 'r'], none⟩]⟩, ⟨['j', 'i', 'a', 'n', 'm', 'i', 'a', 'n'], ['m', 'e', 'e', 't'], [⟨['j', 'i', 'a', 'n', 'm', 'i', 'a', 'n'], ['m', 'e', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 1, "definite", none⟩]
    paperFeatures := [("section", "4.3"), ("environment", "largerSituation"), ("position", "object")] }

def ex_28_dem : Datum :=
  { id := "jenks2018_28_dem"
    source := ⟨"jenks-2018", "(28)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Obama mei dao yi ge chengshi ta dou gen zhe wei shizhang jianmian."
    glossedTokens := [("Obama", "Obama"), ("mei", "every"), ("dao", "arrive"), ("yi", "one"), ("ge", "CLF"), ("chengshi", "city"), ("ta", "he"), ("dou", "all"), ("gen", "with"), ("zhe", "this"), ("wei", "CLF"), ("shizhang", "mayor"), ("jianmian", "meet")]
    glossedWords := [⟨['O', 'b', 'a', 'm', 'a'], ['O', 'b', 'a', 'm', 'a'], [⟨['O', 'b', 'a', 'm', 'a'], ['O', 'b', 'a', 'm', 'a'], none⟩]⟩, ⟨['m', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['m', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['d', 'a', 'o'], ['a', 'r', 'r', 'i', 'v', 'e'], [⟨['d', 'a', 'o'], ['a', 'r', 'r', 'i', 'v', 'e'], none⟩]⟩, ⟨['y', 'i'], ['o', 'n', 'e'], [⟨['y', 'i'], ['o', 'n', 'e'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['c', 'h', 'e', 'n', 'g', 's', 'h', 'i'], ['c', 'i', 't', 'y'], [⟨['c', 'h', 'e', 'n', 'g', 's', 'h', 'i'], ['c', 'i', 't', 'y'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['g', 'e', 'n'], ['w', 'i', 't', 'h'], [⟨['g', 'e', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['z', 'h', 'e'], ['t', 'h', 'i', 's'], [⟨['z', 'h', 'e'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['w', 'e', 'i'], ['C', 'L', 'F'], [⟨['w', 'e', 'i'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'h', 'i', 'z', 'h', 'a', 'n', 'g'], ['m', 'a', 'y', 'o', 'r'], [⟨['s', 'h', 'i', 'z', 'h', 'a', 'n', 'g'], ['m', 'a', 'y', 'o', 'r'], none⟩]⟩, ⟨['j', 'i', 'a', 'n', 'm', 'i', 'a', 'n'], ['m', 'e', 'e', 't'], [⟨['j', 'i', 'a', 'n', 'm', 'i', 'a', 'n'], ['m', 'e', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨9, 3, "definite", none⟩, ⟨9, 1, "determiner", some "zhe"⟩]
    paperFeatures := [("section", "4.3"), ("environment", "largerSituation"), ("position", "object")] }

def ex_49_bare : Datum :=
  { id := "jenks2018_49_bare"
    source := ⟨"jenks-2018", "(49)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge mai le fangzi de ren dou xuyao xiuli wuding."
    glossedTokens := [("Mei", "every"), ("ge", "CLF"), ("mai", "buy"), ("le", "LE"), ("fangzi", "house"), ("de", "DE"), ("ren", "people"), ("dou", "all"), ("xuyao", "need"), ("xiuli", "fix"), ("wuding", "roof")]
    glossedWords := [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['m', 'a', 'i'], ['b', 'u', 'y'], [⟨['m', 'a', 'i'], ['b', 'u', 'y'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['f', 'a', 'n', 'g', 'z', 'i'], ['h', 'o', 'u', 's', 'e'], [⟨['f', 'a', 'n', 'g', 'z', 'i'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['r', 'e', 'n'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['r', 'e', 'n'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['x', 'u', 'y', 'a', 'o'], ['n', 'e', 'e', 'd'], [⟨['x', 'u', 'y', 'a', 'o'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['x', 'i', 'u', 'l', 'i'], ['f', 'i', 'x'], [⟨['x', 'i', 'u', 'l', 'i'], ['f', 'i', 'x'], none⟩]⟩, ⟨['w', 'u', 'd', 'i', 'n', 'g'], ['r', 'o', 'o', 'f'], [⟨['w', 'u', 'd', 'i', 'n', 'g'], ['r', 'o', 'o', 'f'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨10, 1, "definite", none⟩]
    paperFeatures := [("section", "5.2"), ("environment", "partWholeBridging"), ("position", "object")] }

def ex_49_dem : Datum :=
  { id := "jenks2018_49_dem"
    source := ⟨"jenks-2018", "(49)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge mai le fangzi de ren dou xuyao xiuli na ge wuding."
    glossedTokens := [("Mei", "every"), ("ge", "CLF"), ("mai", "buy"), ("le", "LE"), ("fangzi", "house"), ("de", "DE"), ("ren", "people"), ("dou", "all"), ("xuyao", "need"), ("xiuli", "fix"), ("na", "that"), ("ge", "CLF"), ("wuding", "roof")]
    glossedWords := [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], [⟨['M', 'e', 'i'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['m', 'a', 'i'], ['b', 'u', 'y'], [⟨['m', 'a', 'i'], ['b', 'u', 'y'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['f', 'a', 'n', 'g', 'z', 'i'], ['h', 'o', 'u', 's', 'e'], [⟨['f', 'a', 'n', 'g', 'z', 'i'], ['h', 'o', 'u', 's', 'e'], none⟩]⟩, ⟨['d', 'e'], ['D', 'E'], [⟨['d', 'e'], ['D', 'E'], none⟩]⟩, ⟨['r', 'e', 'n'], ['p', 'e', 'o', 'p', 'l', 'e'], [⟨['r', 'e', 'n'], ['p', 'e', 'o', 'p', 'l', 'e'], none⟩]⟩, ⟨['d', 'o', 'u'], ['a', 'l', 'l'], [⟨['d', 'o', 'u'], ['a', 'l', 'l'], none⟩]⟩, ⟨['x', 'u', 'y', 'a', 'o'], ['n', 'e', 'e', 'd'], [⟨['x', 'u', 'y', 'a', 'o'], ['n', 'e', 'e', 'd'], none⟩]⟩, ⟨['x', 'i', 'u', 'l', 'i'], ['f', 'i', 'x'], [⟨['x', 'i', 'u', 'l', 'i'], ['f', 'i', 'x'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['w', 'u', 'd', 'i', 'n', 'g'], ['r', 'o', 'o', 'f'], [⟨['w', 'u', 'd', 'i', 'n', 'g'], ['r', 'o', 'o', 'f'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨10, 3, "definite", none⟩, ⟨10, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "5.2"), ("environment", "partWholeBridging"), ("position", "object")] }

def ex_51B_bare : Datum :=
  { id := "jenks2018_51B_bare"
    source := ⟨"jenks-2018", "(51B)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mao sha le (ta)."
    glossedTokens := [("Mao", "cat"), ("sha", "killed"), ("le", "LE"), ("(ta)", "it")]
    glossedWords := [⟨['M', 'a', 'o'], ['c', 'a', 't'], [⟨['M', 'a', 'o'], ['c', 'a', 't'], none⟩]⟩, ⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l', 'e', 'd'], [⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l', 'e', 'd'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['(', 't', 'a', ')'], ['i', 't'], [⟨['t', 'a'], ['i', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "subject"), ("topic", "nontopic")] }

def ex_51B_dem : Datum :=
  { id := "jenks2018_51B_dem"
    source := ⟨"jenks-2018", "(51B)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na zhi mao sha le (ta)."
    glossedTokens := [("Na", "that"), ("zhi", "CLF"), ("mao", "cat"), ("sha", "killed"), ("le", "LE"), ("(ta)", "it")]
    glossedWords := [⟨['N', 'a'], ['t', 'h', 'a', 't'], [⟨['N', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['z', 'h', 'i'], ['C', 'L', 'F'], [⟨['z', 'h', 'i'], ['C', 'L', 'F'], none⟩]⟩, ⟨['m', 'a', 'o'], ['c', 'a', 't'], [⟨['m', 'a', 'o'], ['c', 'a', 't'], none⟩]⟩, ⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l', 'e', 'd'], [⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l', 'e', 'd'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩, ⟨['(', 't', 'a', ')'], ['i', 't'], [⟨['t', 'a'], ['i', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 3, "definite", none⟩, ⟨0, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "subject"), ("topic", "nontopic")] }

def ex_51Bp_bare : Datum :=
  { id := "jenks2018_51Bp_bare"
    source := ⟨"jenks-2018", "(51B′)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ta bei mao sha le."
    glossedTokens := [("Ta", "it"), ("bei", "PASS"), ("mao", "cat"), ("sha", "kill"), ("le", "LE")]
    glossedWords := [⟨['T', 'a'], ['i', 't'], [⟨['T', 'a'], ['i', 't'], none⟩]⟩, ⟨['b', 'e', 'i'], ['P', 'A', 'S', 'S'], [⟨['b', 'e', 'i'], ['P', 'A', 'S', 'S'], none⟩]⟩, ⟨['m', 'a', 'o'], ['c', 'a', 't'], [⟨['m', 'a', 'o'], ['c', 'a', 't'], none⟩]⟩, ⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l'], [⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨2, 1, "definite", none⟩]
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "object"), ("topic", "nontopic")] }

def ex_51Bp_dem : Datum :=
  { id := "jenks2018_51Bp_dem"
    source := ⟨"jenks-2018", "(51B′)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ta bei na zhi mao sha le."
    glossedTokens := [("Ta", "it"), ("bei", "PASS"), ("na", "that"), ("zhi", "CLF"), ("mao", "cat"), ("sha", "kill"), ("le", "LE")]
    glossedWords := [⟨['T', 'a'], ['i', 't'], [⟨['T', 'a'], ['i', 't'], none⟩]⟩, ⟨['b', 'e', 'i'], ['P', 'A', 'S', 'S'], [⟨['b', 'e', 'i'], ['P', 'A', 'S', 'S'], none⟩]⟩, ⟨['n', 'a'], ['t', 'h', 'a', 't'], [⟨['n', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['z', 'h', 'i'], ['C', 'L', 'F'], [⟨['z', 'h', 'i'], ['C', 'L', 'F'], none⟩]⟩, ⟨['m', 'a', 'o'], ['c', 'a', 't'], [⟨['m', 'a', 'o'], ['c', 'a', 't'], none⟩]⟩, ⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l'], [⟨['s', 'h', 'a'], ['k', 'i', 'l', 'l'], none⟩]⟩, ⟨['l', 'e'], ['L', 'E'], [⟨['l', 'e'], ['L', 'E'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨2, 3, "definite", none⟩, ⟨2, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "object"), ("topic", "nontopic")] }

def ex_52b_bare : Datum :=
  { id := "jenks2018_52b_bare"
    source := ⟨"jenks-2018", "(52b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Nansheng, wo hen bu xihuan."
    glossedTokens := [("Nansheng", "boy"), ("wo", "I"), ("hen", "really"), ("bu", "not"), ("xihuan", "like")]
    glossedWords := [⟨['N', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['N', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['w', 'o'], ['I'], [⟨['w', 'o'], ['I'], none⟩]⟩, ⟨['h', 'e', 'n'], ['r', 'e', 'a', 'l', 'l', 'y'], [⟨['h', 'e', 'n'], ['r', 'e', 'a', 'l', 'l', 'y'], none⟩]⟩, ⟨['b', 'u'], ['n', 'o', 't'], [⟨['b', 'u'], ['n', 'o', 't'], none⟩]⟩, ⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], [⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "leftDislocated"), ("topic", "new")] }

def ex_52b_dem : Datum :=
  { id := "jenks2018_52b_dem"
    source := ⟨"jenks-2018", "(52b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na ge nansheng, wo hen bu xihuan."
    glossedTokens := [("Na", "that"), ("ge", "CLF"), ("nansheng", "boy"), ("wo", "I"), ("hen", "really"), ("bu", "not"), ("xihuan", "like")]
    glossedWords := [⟨['N', 'a'], ['t', 'h', 'a', 't'], [⟨['N', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'e'], ['C', 'L', 'F'], [⟨['g', 'e'], ['C', 'L', 'F'], none⟩]⟩, ⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['n', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['w', 'o'], ['I'], [⟨['w', 'o'], ['I'], none⟩]⟩, ⟨['h', 'e', 'n'], ['r', 'e', 'a', 'l', 'l', 'y'], [⟨['h', 'e', 'n'], ['r', 'e', 'a', 'l', 'l', 'y'], none⟩]⟩, ⟨['b', 'u'], ['n', 'o', 't'], [⟨['b', 'u'], ['n', 'o', 't'], none⟩]⟩, ⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], [⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 3, "definite", none⟩, ⟨0, 1, "determiner", some "na"⟩]
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "leftDislocated"), ("topic", "new")] }

def ex_53 : Datum :=
  { id := "jenks2018_53"
    source := ⟨"jenks-2018", "(53)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Nansheng ne, wo hen bu xihuan."
    glossedTokens := [("Nansheng", "boy"), ("ne", "CT"), ("wo", "I"), ("hen", "really"), ("bu", "not"), ("xihuan", "like")]
    glossedWords := [⟨['N', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], [⟨['N', 'a', 'n', 's', 'h', 'e', 'n', 'g'], ['b', 'o', 'y'], none⟩]⟩, ⟨['n', 'e'], ['C', 'T'], [⟨['n', 'e'], ['C', 'T'], none⟩]⟩, ⟨['w', 'o'], ['I'], [⟨['w', 'o'], ['I'], none⟩]⟩, ⟨['h', 'e', 'n'], ['r', 'e', 'a', 'l', 'l', 'y'], [⟨['h', 'e', 'n'], ['r', 'e', 'a', 'l', 'l', 'y'], none⟩]⟩, ⟨['b', 'u'], ['n', 'o', 't'], [⟨['b', 'u'], ['n', 'o', 't'], none⟩]⟩, ⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], [⟨['x', 'i', 'h', 'u', 'a', 'n'], ['l', 'i', 'k', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "leftDislocated"), ("topic", "continuing")] }

def ex_54a : Datum :=
  { id := "jenks2018_54a"
    source := ⟨"jenks-2018", "(54a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Lou5baan2 haa6zau3 lei5 gim2caa4 gung1zok3."
    glossedTokens := [("Lou5baan2", "boss"), ("haa6zau3", "afternoon"), ("lei5", "come"), ("gim2caa4", "inspect"), ("gung1zok3", "work")]
    glossedWords := [⟨['L', 'o', 'u', '5', 'b', 'a', 'a', 'n', '2'], ['b', 'o', 's', 's'], [⟨['L', 'o', 'u', '5', 'b', 'a', 'a', 'n', '2'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['h', 'a', 'a', '6', 'z', 'a', 'u', '3'], ['a', 'f', 't', 'e', 'r', 'n', 'o', 'o', 'n'], [⟨['h', 'a', 'a', '6', 'z', 'a', 'u', '3'], ['a', 'f', 't', 'e', 'r', 'n', 'o', 'o', 'n'], none⟩]⟩, ⟨['l', 'e', 'i', '5'], ['c', 'o', 'm', 'e'], [⟨['l', 'e', 'i', '5'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['g', 'i', 'm', '2', 'c', 'a', 'a', '4'], ['i', 'n', 's', 'p', 'e', 'c', 't'], [⟨['g', 'i', 'm', '2', 'c', 'a', 'a', '4'], ['i', 'n', 's', 'p', 'e', 'c', 't'], none⟩]⟩, ⟨['g', 'u', 'n', 'g', '1', 'z', 'o', 'k', '3'], ['w', 'o', 'r', 'k'], [⟨['g', 'u', 'n', 'g', '1', 'z', 'o', 'k', '3'], ['w', 'o', 'r', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_54b : Datum :=
  { id := "jenks2018_54b"
    source := ⟨"jenks-2018", "(54b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Zung2tung2 gam1maan5 baat3 dim2 soeng5 din6si6."
    glossedTokens := [("Zung2tung2", "president"), ("gam1maan5", "tonight"), ("baat3", "eight"), ("dim2", "o'clock"), ("soeng5", "get.on"), ("din6si6", "television")]
    glossedWords := [⟨['Z', 'u', 'n', 'g', '2', 't', 'u', 'n', 'g', '2'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], [⟨['Z', 'u', 'n', 'g', '2', 't', 'u', 'n', 'g', '2'], ['p', 'r', 'e', 's', 'i', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['g', 'a', 'm', '1', 'm', 'a', 'a', 'n', '5'], ['t', 'o', 'n', 'i', 'g', 'h', 't'], [⟨['g', 'a', 'm', '1', 'm', 'a', 'a', 'n', '5'], ['t', 'o', 'n', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['b', 'a', 'a', 't', '3'], ['e', 'i', 'g', 'h', 't'], [⟨['b', 'a', 'a', 't', '3'], ['e', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['d', 'i', 'm', '2'], ['o', '\'', 'c', 'l', 'o', 'c', 'k'], [⟨['d', 'i', 'm', '2'], ['o', '\'', 'c', 'l', 'o', 'c', 'k'], none⟩]⟩, ⟨['s', 'o', 'e', 'n', 'g', '5'], ['g', 'e', 't', '.', 'o', 'n'], [⟨['s', 'o', 'e', 'n', 'g', '5'], ['g', 'e', 't', '.', 'o', 'n'], none⟩]⟩, ⟨['d', 'i', 'n', '6', 's', 'i', '6'], ['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', 'n'], [⟨['d', 'i', 'n', '6', 's', 'i', '6'], ['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "definite", none⟩]
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_55b_clf : Datum :=
  { id := "jenks2018_55b_clf"
    source := ⟨"jenks-2018", "(55b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Keoi5 m4 jing6wai4 go3 zing3zi6gaa1 hou2 jau5ceoi3."
    glossedTokens := [("Keoi5", "3SG"), ("m4", "NOT"), ("jing6wai4", "think"), ("go3", "CLF"), ("zing3zi6gaa1", "politician"), ("hou2", "very"), ("jau5ceoi3", "interesting")]
    glossedWords := [⟨['K', 'e', 'o', 'i', '5'], ['3', 'S', 'G'], [⟨['K', 'e', 'o', 'i', '5'], ['3', 'S', 'G'], none⟩]⟩, ⟨['m', '4'], ['N', 'O', 'T'], [⟨['m', '4'], ['N', 'O', 'T'], none⟩]⟩, ⟨['j', 'i', 'n', 'g', '6', 'w', 'a', 'i', '4'], ['t', 'h', 'i', 'n', 'k'], [⟨['j', 'i', 'n', 'g', '6', 'w', 'a', 'i', '4'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['g', 'o', '3'], ['C', 'L', 'F'], [⟨['g', 'o', '3'], ['C', 'L', 'F'], none⟩]⟩, ⟨['z', 'i', 'n', 'g', '3', 'z', 'i', '6', 'g', 'a', 'a', '1'], ['p', 'o', 'l', 'i', 't', 'i', 'c', 'i', 'a', 'n'], [⟨['z', 'i', 'n', 'g', '3', 'z', 'i', '6', 'g', 'a', 'a', '1'], ['p', 'o', 'l', 'i', 't', 'i', 'c', 'i', 'a', 'n'], none⟩]⟩, ⟨['h', 'o', 'u', '2'], ['v', 'e', 'r', 'y'], [⟨['h', 'o', 'u', '2'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['j', 'a', 'u', '5', 'c', 'e', 'o', 'i', '3'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], [⟨['j', 'a', 'u', '5', 'c', 'e', 'o', 'i', '3'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨3, 2, "definite", none⟩, ⟨3, 0, "determiner", some "clfN"⟩]
    paperFeatures := [("section", "6.1"), ("environment", "anaphoric"), ("position", "embeddedSubject")] }

def ex_55b_dem : Datum :=
  { id := "jenks2018_55b_dem"
    source := ⟨"jenks-2018", "(55b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Keoi5 m4 jing6wai4 go2 go3 zing3zi6gaa1 hou2 jau5ceoi3."
    glossedTokens := [("Keoi5", "3SG"), ("m4", "NOT"), ("jing6wai4", "think"), ("go2", "that"), ("go3", "CLF"), ("zing3zi6gaa1", "politician"), ("hou2", "very"), ("jau5ceoi3", "interesting")]
    glossedWords := [⟨['K', 'e', 'o', 'i', '5'], ['3', 'S', 'G'], [⟨['K', 'e', 'o', 'i', '5'], ['3', 'S', 'G'], none⟩]⟩, ⟨['m', '4'], ['N', 'O', 'T'], [⟨['m', '4'], ['N', 'O', 'T'], none⟩]⟩, ⟨['j', 'i', 'n', 'g', '6', 'w', 'a', 'i', '4'], ['t', 'h', 'i', 'n', 'k'], [⟨['j', 'i', 'n', 'g', '6', 'w', 'a', 'i', '4'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['g', 'o', '2'], ['t', 'h', 'a', 't'], [⟨['g', 'o', '2'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'o', '3'], ['C', 'L', 'F'], [⟨['g', 'o', '3'], ['C', 'L', 'F'], none⟩]⟩, ⟨['z', 'i', 'n', 'g', '3', 'z', 'i', '6', 'g', 'a', 'a', '1'], ['p', 'o', 'l', 'i', 't', 'i', 'c', 'i', 'a', 'n'], [⟨['z', 'i', 'n', 'g', '3', 'z', 'i', '6', 'g', 'a', 'a', '1'], ['p', 'o', 'l', 'i', 't', 'i', 'c', 'i', 'a', 'n'], none⟩]⟩, ⟨['h', 'o', 'u', '2'], ['v', 'e', 'r', 'y'], [⟨['h', 'o', 'u', '2'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['j', 'a', 'u', '5', 'c', 'e', 'o', 'i', '3'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], [⟨['j', 'a', 'u', '5', 'c', 'e', 'o', 'i', '3'], ['i', 'n', 't', 'e', 'r', 'e', 's', 't', 'i', 'n', 'g'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    spans := [⟨3, 3, "definite", none⟩, ⟨3, 1, "determiner", some "go"⟩]
    paperFeatures := [("section", "6.1"), ("environment", "anaphoric"), ("position", "embeddedSubject")] }

def ex_56 : Datum :=
  { id := "jenks2018_56"
    source := ⟨"jenks-2018", "(56)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Mui5 go3 jau5 jat1 zek3 maa5 ge3 nung4fu1 daa2 zek3 maa5."
    glossedTokens := [("Mui5", "every"), ("go3", "CLF"), ("jau5", "have"), ("jat1", "one"), ("zek3", "CLF"), ("maa5", "horse"), ("ge3", "REL"), ("nung4fu1", "farmer"), ("daa2", "hit"), ("zek3", "CLF"), ("maa5", "horse")]
    glossedWords := [⟨['M', 'u', 'i', '5'], ['e', 'v', 'e', 'r', 'y'], [⟨['M', 'u', 'i', '5'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['g', 'o', '3'], ['C', 'L', 'F'], [⟨['g', 'o', '3'], ['C', 'L', 'F'], none⟩]⟩, ⟨['j', 'a', 'u', '5'], ['h', 'a', 'v', 'e'], [⟨['j', 'a', 'u', '5'], ['h', 'a', 'v', 'e'], none⟩]⟩, ⟨['j', 'a', 't', '1'], ['o', 'n', 'e'], [⟨['j', 'a', 't', '1'], ['o', 'n', 'e'], none⟩]⟩, ⟨['z', 'e', 'k', '3'], ['C', 'L', 'F'], [⟨['z', 'e', 'k', '3'], ['C', 'L', 'F'], none⟩]⟩, ⟨['m', 'a', 'a', '5'], ['h', 'o', 'r', 's', 'e'], [⟨['m', 'a', 'a', '5'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩, ⟨['g', 'e', '3'], ['R', 'E', 'L'], [⟨['g', 'e', '3'], ['R', 'E', 'L'], none⟩]⟩, ⟨['n', 'u', 'n', 'g', '4', 'f', 'u', '1'], ['f', 'a', 'r', 'm', 'e', 'r'], [⟨['n', 'u', 'n', 'g', '4', 'f', 'u', '1'], ['f', 'a', 'r', 'm', 'e', 'r'], none⟩]⟩, ⟨['d', 'a', 'a', '2'], ['h', 'i', 't'], [⟨['d', 'a', 'a', '2'], ['h', 'i', 't'], none⟩]⟩, ⟨['z', 'e', 'k', '3'], ['C', 'L', 'F'], [⟨['z', 'e', 'k', '3'], ['C', 'L', 'F'], none⟩]⟩, ⟨['m', 'a', 'a', '5'], ['h', 'o', 'r', 's', 'e'], [⟨['m', 'a', 'a', '5'], ['h', 'o', 'r', 's', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨9, 2, "definite", none⟩, ⟨9, 0, "determiner", some "clfN"⟩]
    paperFeatures := [("section", "6.1"), ("environment", "donkey"), ("position", "object")] }

def ex_59 : Datum :=
  { id := "jenks2018_59"
    source := ⟨"jenks-2018", "(59)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Hai2 Ou3baa1maa2 heoi3 gwo3 ge3 mui5 jat1 go3 sing4si5, keoi5 dou1 tung4 go3 si5zoeng2 gin3 gwo3 min6."
    glossedTokens := [("Hai2", "be.at"), ("Ou3baa1maa2", "Obama"), ("heoi3", "go"), ("gwo3", "PFV"), ("ge3", "POSS"), ("mui5", "every"), ("jat1", "one"), ("go3", "CLF"), ("sing4si5", "city"), ("keoi5", "she/he"), ("dou1", "all"), ("tung4", "with"), ("go3", "CLF"), ("si5zoeng2", "mayor"), ("gin3", "see"), ("gwo3", "PFV"), ("min6", "face")]
    glossedWords := [⟨['H', 'a', 'i', '2'], ['b', 'e', '.', 'a', 't'], [⟨['H', 'a', 'i', '2'], ['b', 'e', '.', 'a', 't'], none⟩]⟩, ⟨['O', 'u', '3', 'b', 'a', 'a', '1', 'm', 'a', 'a', '2'], ['O', 'b', 'a', 'm', 'a'], [⟨['O', 'u', '3', 'b', 'a', 'a', '1', 'm', 'a', 'a', '2'], ['O', 'b', 'a', 'm', 'a'], none⟩]⟩, ⟨['h', 'e', 'o', 'i', '3'], ['g', 'o'], [⟨['h', 'e', 'o', 'i', '3'], ['g', 'o'], none⟩]⟩, ⟨['g', 'w', 'o', '3'], ['P', 'F', 'V'], [⟨['g', 'w', 'o', '3'], ['P', 'F', 'V'], none⟩]⟩, ⟨['g', 'e', '3'], ['P', 'O', 'S', 'S'], [⟨['g', 'e', '3'], ['P', 'O', 'S', 'S'], none⟩]⟩, ⟨['m', 'u', 'i', '5'], ['e', 'v', 'e', 'r', 'y'], [⟨['m', 'u', 'i', '5'], ['e', 'v', 'e', 'r', 'y'], none⟩]⟩, ⟨['j', 'a', 't', '1'], ['o', 'n', 'e'], [⟨['j', 'a', 't', '1'], ['o', 'n', 'e'], none⟩]⟩, ⟨['g', 'o', '3'], ['C', 'L', 'F'], [⟨['g', 'o', '3'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'i', 'n', 'g', '4', 's', 'i', '5'], ['c', 'i', 't', 'y'], [⟨['s', 'i', 'n', 'g', '4', 's', 'i', '5'], ['c', 'i', 't', 'y'], none⟩]⟩, ⟨['k', 'e', 'o', 'i', '5'], ['s', 'h', 'e', '/', 'h', 'e'], [⟨['k', 'e', 'o', 'i', '5'], ['s', 'h', 'e', '/', 'h', 'e'], none⟩]⟩, ⟨['d', 'o', 'u', '1'], ['a', 'l', 'l'], [⟨['d', 'o', 'u', '1'], ['a', 'l', 'l'], none⟩]⟩, ⟨['t', 'u', 'n', 'g', '4'], ['w', 'i', 't', 'h'], [⟨['t', 'u', 'n', 'g', '4'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['g', 'o', '3'], ['C', 'L', 'F'], [⟨['g', 'o', '3'], ['C', 'L', 'F'], none⟩]⟩, ⟨['s', 'i', '5', 'z', 'o', 'e', 'n', 'g', '2'], ['m', 'a', 'y', 'o', 'r'], [⟨['s', 'i', '5', 'z', 'o', 'e', 'n', 'g', '2'], ['m', 'a', 'y', 'o', 'r'], none⟩]⟩, ⟨['g', 'i', 'n', '3'], ['s', 'e', 'e'], [⟨['g', 'i', 'n', '3'], ['s', 'e', 'e'], none⟩]⟩, ⟨['g', 'w', 'o', '3'], ['P', 'F', 'V'], [⟨['g', 'w', 'o', '3'], ['P', 'F', 'V'], none⟩]⟩, ⟨['m', 'i', 'n', '6'], ['f', 'a', 'c', 'e'], [⟨['m', 'i', 'n', '6'], ['f', 'a', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨12, 2, "definite", none⟩, ⟨12, 0, "determiner", some "clfN"⟩]
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("position", "object")] }

def all : List Datum := [ex_10a, ex_10b_bare, ex_10b_na, ex_10b_zhe, ex_11a, ex_11b, ex_14a, ex_14b_bare, ex_14b_dem, ex_15b_bare, ex_15b_dem, ex_15c_bare, ex_15c_dem, ex_15d_bare, ex_15d_dem, ex_15e_bare, ex_15e_dem, ex_16b, ex_16c, ex_18b, ex_19, ex_20_bare, ex_20_dem, ex_28_bare, ex_28_dem, ex_49_bare, ex_49_dem, ex_51B_bare, ex_51B_dem, ex_51Bp_bare, ex_51Bp_dem, ex_52b_bare, ex_52b_dem, ex_53, ex_54a, ex_54b, ex_55b_clf, ex_55b_dem, ex_56, ex_59]

/-- The definite environments the paper tests. -/
inductive Environment where
  /-- largerSituation: a larger-situation definite, unique by world knowledge -/
  | largerSituation
  /-- immediateSituation: an immediate-situation definite, unique in the utterance context -/
  | immediateSituation
  /-- partWholeBridging: a definite bridged to an antecedent that contains its referent -/
  | partWholeBridging
  /-- producerBridging: a definite bridged to the product of its referent -/
  | producerBridging
  /-- anaphoric: a definite anaphoric to an antecedent in a narrative sequence -/
  | anaphoric
  /-- donkey: a definite covarying with an indefinite that does not c-command it -/
  | donkey
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `environment`. -/
def environment (e : Datum) : Option Environment :=
  e.parse? "environment" [("largerSituation", .largerSituation), ("immediateSituation", .immediateSituation),
    ("partWholeBridging", .partWholeBridging), ("producerBridging", .producerBridging),
    ("anaphoric", .anaphoric), ("donkey", .donkey)]

/-- The discourse status the paper assigns the definite, where it assigns one. -/
inductive Topic where
  /-- continuing: a continuing topic, a contrastive one included -/
  | continuing
  /-- new: a new topic, as under left-dislocation -/
  | new
  /-- nontopic: a noun phrase outside the topic situation of the question under discussion -/
  | nontopic
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `topic`. -/
def topic (e : Datum) : Option Topic :=
  e.parse? "topic" [("continuing", .continuing), ("new", .new), ("nontopic", .nontopic)]

/-- The reading of the noun phrase under test that the paper judges apart from the sentence. -/
inductive Reading where
  /-- definite: the noun phrase refers back to the antecedent -/
  | definite
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .definite => "definite"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- definite: the definite noun phrase under test -/
  | definite
  /-- determiner: the determiner heading the noun phrase under test -/
  | determiner
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("definite", .definite), ("determiner", .determiner)]

/-- The determiners heading the noun phrases under test. -/
inductive Lexeme where
  /-- na: Mandarin na 'that' -/
  | na
  /-- zhe: Mandarin zhe 'this' -/
  | zhe
  /-- go: Cantonese go2 'that' -/
  | go
  /-- clfN: the Cantonese definite article exponed by a classifier phrase, [Clf-N] -/
  | clfN
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("na", .na), ("zhe", .zhe), ("go", .go), ("clfN", .clfN)])

end Jenks2018.Examples
