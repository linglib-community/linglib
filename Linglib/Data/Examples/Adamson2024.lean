module

public import Linglib.Data.Examples.Schema

/-!
# `Adamson2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Adamson2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Adamson2024.Examples`.
-/

@[expose] public section

namespace Adamson2024.Examples

def ex_39a : Datum :=
  { id := "adamson2024_39a"
    source := ⟨"adamson-2024", "(39a)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "a bina-naa"
    glossedTokens := [("a", "ART.I.SG"), ("bina-naa", "spleen-1SG")]
    glossedWords := [⟨[['a']], [['A', 'R', 'T', '.', 'I', '.', 'S', 'G']]⟩, ⟨[['b', 'i', 'n', 'a'], ['n', 'a', 'a']], [['s', 'p', 'l', 'e', 'e', 'n'], ['1', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "inalienable"), ("gender", "I")] }

def ex_39b : Datum :=
  { id := "adamson2024_39b"
    source := ⟨"adamson-2024", "(39b)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "o bina"
    glossedTokens := [("o", "ART.II.SG"), ("bina", "spleen")]
    glossedWords := [⟨[['o']], [['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['b', 'i', 'n', 'a']], [['s', 'p', 'l', 'e', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "none"), ("gender", "II")] }

def ex_40a : Datum :=
  { id := "adamson2024_40a"
    source := ⟨"adamson-2024", "(40a)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "a vuha-naa"
    glossedTokens := [("a", "ART.I.SG"), ("vuha-naa", "heart-1SG")]
    glossedWords := [⟨[['a']], [['A', 'R', 'T', '.', 'I', '.', 'S', 'G']]⟩, ⟨[['v', 'u', 'h', 'a'], ['n', 'a', 'a']], [['h', 'e', 'a', 'r', 't'], ['1', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "inalienable"), ("gender", "I")] }

def ex_40b : Datum :=
  { id := "adamson2024_40b"
    source := ⟨"adamson-2024", "(40b)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "o vuha"
    glossedTokens := [("o", "ART.II.SG"), ("vuha", "heart")]
    glossedWords := [⟨[['o']], [['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['v', 'u', 'h', 'a']], [['h', 'e', 'a', 'r', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "none"), ("gender", "II")] }

def ex_44a : Datum :=
  { id := "adamson2024_44a"
    source := ⟨"adamson-2024", "(44a)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "a revasin-naa"
    glossedTokens := [("a", "ART.I.SG"), ("revasin-naa", "blood-1SG")]
    glossedWords := [⟨[['a']], [['A', 'R', 'T', '.', 'I', '.', 'S', 'G']]⟩, ⟨[['r', 'e', 'v', 'a', 's', 'i', 'n'], ['n', 'a', 'a']], [['b', 'l', 'o', 'o', 'd'], ['1', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "inalienable"), ("gender", "I")] }

def ex_44b : Datum :=
  { id := "adamson2024_44b"
    source := ⟨"adamson-2024", "(44b)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "o revasin te-naa"
    glossedTokens := [("o", "ART.II.SG"), ("revasin", "blood"), ("te-naa", "of-1SG")]
    glossedWords := [⟨[['o']], [['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['r', 'e', 'v', 'a', 's', 'i', 'n']], [['b', 'l', 'o', 'o', 'd']]⟩, ⟨[['t', 'e'], ['n', 'a', 'a']], [['o', 'f'], ['1', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "alienable"), ("gender", "II")] }

def ex_45b : Datum :=
  { id := "adamson2024_45b"
    source := ⟨"adamson-2024", "(45b)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "O ihu-na te-naa to gono e Leona."
    glossedTokens := [("O", "ART.II.SG"), ("ihu-na", "nose-DEREL"), ("te-naa", "of-1SG"), ("to", "TOP"), ("gono", "get"), ("e", "ART.PROP"), ("Leona", "Leona")]
    glossedWords := [⟨[['O']], [['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['i', 'h', 'u'], ['n', 'a']], [['n', 'o', 's', 'e'], ['D', 'E', 'R', 'E', 'L']]⟩, ⟨[['t', 'e'], ['n', 'a', 'a']], [['o', 'f'], ['1', 'S', 'G']]⟩, ⟨[['t', 'o']], [['T', 'O', 'P']]⟩, ⟨[['g', 'o', 'n', 'o']], [['g', 'e', 't']]⟩, ⟨[['e']], [['A', 'R', 'T', '.', 'P', 'R', 'O', 'P']]⟩, ⟨[['L', 'e', 'o', 'n', 'a']], [['L', 'e', 'o', 'n', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "alienable"), ("gender", "II"), ("alienator", "-na")] }

def ex_46 : Datum :=
  { id := "adamson2024_46"
    source := ⟨"adamson-2024", "(46)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "Koroto o moo guu."
    glossedTokens := [("Koroto", "draw"), ("o", "ART.II.SG"), ("moo", "leg"), ("guu", "pig")]
    glossedWords := [⟨[['K', 'o', 'r', 'o', 't', 'o']], [['d', 'r', 'a', 'w']]⟩, ⟨[['o']], [['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['m', 'o', 'o']], [['l', 'e', 'g']]⟩, ⟨[['g', 'u', 'u']], [['p', 'i', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "compound"), ("gender", "II")] }

def ex_48 : Datum :=
  { id := "adamson2024_48"
    source := ⟨"adamson-2024", "(48)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "a hena n-o toro"
    glossedTokens := [("a", "ART.I.SG"), ("hena", "name"), ("n-o", "3SG-ART.II.SG"), ("toro", "ship")]
    glossedWords := [⟨[['a']], [['A', 'R', 'T', '.', 'I', '.', 'S', 'G']]⟩, ⟨[['h', 'e', 'n', 'a']], [['n', 'a', 'm', 'e']]⟩, ⟨[['n'], ['o']], [['3', 'S', 'G'], ['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['t', 'o', 'r', 'o']], [['s', 'h', 'i', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "inalienable"), ("gender", "I"), ("possessorGender", "II")] }

def ex_50 : Datum :=
  { id := "adamson2024_50"
    source := ⟨"adamson-2024", "(50)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "e sina-na-e"
    glossedTokens := [("e", "ART.PROP.SG"), ("sina", "mother"), ("-na-e", "3SG")]
    glossedWords := [⟨[['e']], [['A', 'R', 'T', '.', 'P', 'R', 'O', 'P', '.', 'S', 'G']]⟩, ⟨[['s', 'i', 'n', 'a']], [['m', 'o', 't', 'h', 'e', 'r']]⟩, ⟨[[], ['n', 'a'], ['e']], [['3', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "inalienable"), ("article", "proprial")] }

def ex_51 : Datum :=
  { id := "adamson2024_51"
    source := ⟨"adamson-2024", "(51)"⟩
    reportedIn := none
    language := "teop1238"
    primaryText := "o sina-na o beera"
    glossedTokens := [("o", "ART.II.SG"), ("sina-na", "mother-DEREL"), ("o", "ART.II.SG"), ("beera", "big")]
    glossedWords := [⟨[['o']], [['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['s', 'i', 'n', 'a'], ['n', 'a']], [['m', 'o', 't', 'h', 'e', 'r'], ['D', 'E', 'R', 'E', 'L']]⟩, ⟨[['o']], [['A', 'R', 'T', '.', 'I', 'I', '.', 'S', 'G']]⟩, ⟨[['b', 'e', 'e', 'r', 'a']], [['b', 'i', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("possession", "none"), ("gender", "II"), ("alienator", "-na")] }

def ex_52 : Datum :=
  { id := "adamson2024_52"
    source := ⟨"adamson-2024", "(52)"⟩
    reportedIn := none
    language := "jara1276"
    primaryText := "Okomobi mano"
    glossedTokens := [("Okomobi", "name(M)"), ("mano", "arm.M")]
    glossedWords := [⟨[['O', 'k', 'o', 'm', 'o', 'b', 'i']], [['n', 'a', 'm', 'e', '(', 'M', ')']]⟩, ⟨[['m', 'a', 'n', 'o']], [['a', 'r', 'm', '.', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jane mani", .acceptable)]
    readings := []
    paperFeatures := [("possession", "inalienable"), ("agreement", "possessor")] }

def ex_53 : Datum :=
  { id := "adamson2024_53"
    source := ⟨"adamson-2024", "(53)"⟩
    reportedIn := none
    language := "jara1276"
    primaryText := "otaa mano"
    glossedTokens := [("otaa", "1PL.EXCL"), ("mano", "arm.M")]
    glossedWords := [⟨[['o', 't', 'a', 'a']], [['1', 'P', 'L', '.', 'E', 'X', 'C', 'L']]⟩, ⟨[['m', 'a', 'n', 'o']], [['a', 'r', 'm', '.', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("mee mani", .acceptable)]
    readings := []
    paperFeatures := [("possession", "inalienable"), ("agreement", "possessor")] }

def ex_64 : Datum :=
  { id := "adamson2024_64"
    source := ⟨"adamson-2024", "(64)"⟩
    reportedIn := none
    language := "jara1276"
    primaryText := "Okomobi teme"
    glossedTokens := [("Okomobi", "name(M)"), ("teme", "foot.M")]
    glossedWords := [⟨[['O', 'k', 'o', 'm', 'o', 'b', 'i']], [['n', 'a', 'm', 'e', '(', 'M', ')']]⟩, ⟨[['t', 'e', 'm', 'e']], [['f', 'o', 'o', 't', '.', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Okomobi kaa tao.kana", .acceptable)]
    readings := []
    paperFeatures := [("possession", "inalienable"), ("marker", "juxtaposition")] }

def ex_70 : Datum :=
  { id := "adamson2024_70"
    source := ⟨"adamson-2024", "(70)"⟩
    reportedIn := none
    language := "jara1276"
    primaryText := "Jaki efe so to-sa-ka bofe jaa"
    glossedTokens := [("Jaki", "toucan(M)"), ("efe", "feather.M"), ("so", "lie"), ("to-sa-ka", "away-cleanly-DEC.M"), ("bofe", "ground(F)"), ("jaa", "PERI")]
    glossedWords := [⟨[['J', 'a', 'k', 'i']], [['t', 'o', 'u', 'c', 'a', 'n', '(', 'M', ')']]⟩, ⟨[['e', 'f', 'e']], [['f', 'e', 'a', 't', 'h', 'e', 'r', '.', 'M']]⟩, ⟨[['s', 'o']], [['l', 'i', 'e']]⟩, ⟨[['t', 'o'], ['s', 'a'], ['k', 'a']], [['a', 'w', 'a', 'y'], ['c', 'l', 'e', 'a', 'n', 'l', 'y'], ['D', 'E', 'C', '.', 'M']]⟩, ⟨[['b', 'o', 'f', 'e']], [['g', 'r', 'o', 'u', 'n', 'd', '(', 'F', ')']]⟩, ⟨[['j', 'a', 'a']], [['P', 'E', 'R', 'I']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jaki mee afe so to-sa-ke bofe jaa", .acceptable)]
    readings := []
    paperFeatures := [("agreement", "possessor"), ("target", "declarative")] }

def ex_71 : Datum :=
  { id := "adamson2024_71"
    source := ⟨"adamson-2024", "(71)"⟩
    reportedIn := none
    language := "jara1276"
    primaryText := "Okomobi mano bako"
    glossedTokens := [("Okomobi", "name(M)"), ("mano", "arm.M"), ("bako", "inside.M")]
    glossedWords := [⟨[['O', 'k', 'o', 'm', 'o', 'b', 'i']], [['n', 'a', 'm', 'e', '(', 'M', ')']]⟩, ⟨[['m', 'a', 'n', 'o']], [['a', 'r', 'm', '.', 'M']]⟩, ⟨[['b', 'a', 'k', 'o']], [['i', 'n', 's', 'i', 'd', 'e', '.', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jane mani baki", .acceptable)]
    readings := []
    paperFeatures := [("construction", "complex possessor"), ("pattern", "match")] }

def ex_73 : Datum :=
  { id := "adamson2024_73"
    source := ⟨"adamson-2024", "(73)"⟩
    reportedIn := none
    language := "jara1276"
    primaryText := "o-mano baki"
    glossedTokens := [("o-", "1SG"), ("mano", "arm.M"), ("baki", "inside.F")]
    glossedWords := [⟨[['o'], []], [['1', 'S', 'G']]⟩, ⟨[['m', 'a', 'n', 'o']], [['a', 'r', 'm', '.', 'M']]⟩, ⟨[['b', 'a', 'k', 'i']], [['i', 'n', 's', 'i', 'd', 'e', '.', 'F']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("ti-mano baki", .acceptable)]
    readings := []
    paperFeatures := [("construction", "complex possessor"), ("pattern", "mismatch")] }

def ex_75a : Datum :=
  { id := "adamson2024_75a"
    source := ⟨"adamson-2024", "(75a)"⟩
    reportedIn := none
    language := "jara1276"
    primaryText := "ee teme bite"
    glossedTokens := [("ee", "1.INCL.POSS"), ("teme", "foot.M"), ("bite", "small.F")]
    glossedWords := [⟨[['e', 'e']], [['1', '.', 'I', 'N', 'C', 'L', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['t', 'e', 'm', 'e']], [['f', 'o', 'o', 't', '.', 'M']]⟩, ⟨[['b', 'i', 't', 'e']], [['s', 'm', 'a', 'l', 'l', '.', 'F']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("ee teme biti", .ungrammatical)]
    readings := []
    paperFeatures := [("agreement", "attributive"), ("gender", "feminine")] }

def ex_80 : Datum :=
  { id := "adamson2024_80"
    source := ⟨"adamson-2024", "(80)"⟩
    reportedIn := none
    language := "yany1243"
    primaryText := "nja-ganjmaḍa niya-wini"
    glossedTokens := [("nja-ganjmaḍa", "HM-two"), ("niya-wini", "his-name")]
    glossedWords := [⟨[['n', 'j', 'a'], ['g', 'a', 'n', 'j', 'm', 'a', 'ḍ', 'a']], [['H', 'M'], ['t', 'w', 'o']]⟩, ⟨[['n', 'i', 'y', 'a'], ['w', 'i', 'n', 'i']], [['h', 'i', 's'], ['n', 'a', 'm', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("∅-djagaḍa ni-wini", .acceptable), ("řa-maŋadji nanda-wini", .acceptable)]
    readings := []
    paperFeatures := [("possession", "inalienable"), ("mechanism", "inherited gender")] }

def ex_88 : Datum :=
  { id := "adamson2024_88"
    source := ⟨"adamson-2024", "(88)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1622"
    primaryText := "igih u-pe waninggap k-a."
    glossedTokens := [("igih", "name"), ("u-pe", "II-DIST"), ("waninggap", "good"), ("k-a", "PRS.NEUT-3.A")]
    glossedWords := [⟨[['i', 'g', 'i', 'h']], [['n', 'a', 'm', 'e']]⟩, ⟨[['u'], ['p', 'e']], [['I', 'I'], ['D', 'I', 'S', 'T']]⟩, ⟨[['w', 'a', 'n', 'i', 'n', 'g', 'g', 'a', 'p']], [['g', 'o', 'o', 'd']]⟩, ⟨[['k'], ['a']], [['P', 'R', 'S', '.', 'N', 'E', 'U', 'T'], ['3', '.', 'A']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("igih e-pe waninggap k-a.", .acceptable), ("igih i-pe waninggap k-a.", .acceptable)]
    readings := []
    paperFeatures := [("possession", "inalienable"), ("mechanism", "inherited gender")] }

def ex_89 : Datum :=
  { id := "adamson2024_89"
    source := ⟨"adamson-2024", "(89)"⟩
    reportedIn := none
    language := "nucl1622"
    primaryText := "basik hu nanuh"
    glossedTokens := [("basik", "pig(II)"), ("hu", "like.II"), ("nanuh", "face.II")]
    glossedWords := [⟨[['b', 'a', 's', 'i', 'k']], [['p', 'i', 'g', '(', 'I', 'I', ')']]⟩, ⟨[['h', 'u']], [['l', 'i', 'k', 'e', '.', 'I', 'I']]⟩, ⟨[['n', 'a', 'n', 'u', 'h']], [['f', 'a', 'c', 'e', '.', 'I', 'I']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("basik hi nanih", .acceptable)]
    readings := []
    paperFeatures := [("possession", "inalienable"), ("mechanism", "inherited gender")] }

def ex_100 : Datum :=
  { id := "adamson2024_100"
    source := ⟨"adamson-2024", "(100)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "ossa"
    glossedTokens := [("ossa", "bone.F.PL")]
    glossedWords := [⟨[['o', 's', 's', 'a']], [['b', 'o', 'n', 'e', '.', 'F', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("osso", .acceptable), ("ossi", .acceptable)]
    readings := []
    paperFeatures := [("number", "on n"), ("gender", "feminine")] }

def all : List Datum := [ex_39a, ex_39b, ex_40a, ex_40b, ex_44a, ex_44b, ex_45b, ex_46, ex_48, ex_50, ex_51, ex_52, ex_53, ex_64, ex_70, ex_71, ex_73, ex_75a, ex_80, ex_88, ex_89, ex_100]

end Adamson2024.Examples
