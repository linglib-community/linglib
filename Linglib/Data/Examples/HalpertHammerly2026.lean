module

public import Linglib.Data.Examples.Schema

/-!
# `HalpertHammerly2026` — typed example data

Auto-generated from `Linglib/Data/Examples/HalpertHammerly2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HalpertHammerly2026.Examples`.
-/

@[expose] public section

namespace HalpertHammerly2026.Examples

def ex8a : Datum :=
  { id := "halperthammerly2026_ex8a"
    source := ⟨"wasike-2006", "p. 235"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(8a)"⟩
    language := "buku1249"
    primaryText := "Naliaka a-li mu-nju"
    glossedTokens := [("Naliaka", "1Naliaka"), ("a-li", "1SM-be"), ("mu-nju", "18-house")]
    glossedWords := [⟨[['N', 'a', 'l', 'i', 'a', 'k', 'a']], [['1', 'N', 'a', 'l', 'i', 'a', 'k', 'a']]⟩, ⟨[['a'], ['l', 'i']], [['1', 'S', 'M'], ['b', 'e']]⟩, ⟨[['m', 'u'], ['n', 'j', 'u']], [['1', '8'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "alternativeAgreement"), ("class", "1")] }

def ex8b : Datum :=
  { id := "halperthammerly2026_ex8b"
    source := ⟨"wasike-2006", "p. 236"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(8b)"⟩
    language := "buku1249"
    primaryText := "Naani o-o-li mu-nju"
    glossedTokens := [("Naani", "1who"), ("o-o-li", "1C-1AA-be"), ("mu-nju", "18-house")]
    glossedWords := [⟨[['N', 'a', 'a', 'n', 'i']], [['1', 'w', 'h', 'o']]⟩, ⟨[['o'], ['o'], ['l', 'i']], [['1', 'C'], ['1', 'A', 'A'], ['b', 'e']]⟩, ⟨[['m', 'u'], ['n', 'j', 'u']], [['1', '8'], ['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "alternativeAgreement"), ("class", "1")] }

def ex8c : Datum :=
  { id := "halperthammerly2026_ex8c"
    source := ⟨"diercks-2010", "p. 133"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(8c)"⟩
    language := "buku1249"
    primaryText := "Nise/niwe o-w-onak-e ku-mu-lyango kuno"
    glossedTokens := [("Nise/niwe", "1SG.PRO/2SG.PRO"), ("o-w-onak-e", "1C-1AA-damage-PST"), ("ku-mu-lyango", "3-3-door"), ("kuno", "3-DEM")]
    glossedWords := [⟨[['N', 'i', 's', 'e', '/', 'n', 'i', 'w', 'e']], [['1', 'S', 'G', '.', 'P', 'R', 'O', '/', '2', 'S', 'G', '.', 'P', 'R', 'O']]⟩, ⟨[['o'], ['w'], ['o', 'n', 'a', 'k'], ['e']], [['1', 'C'], ['1', 'A', 'A'], ['d', 'a', 'm', 'a', 'g', 'e'], ['P', 'S', 'T']]⟩, ⟨[['k', 'u'], ['m', 'u'], ['l', 'y', 'a', 'n', 'g', 'o']], [['3'], ['3'], ['d', 'o', 'o', 'r']]⟩, ⟨[['k', 'u', 'n', 'o']], [['3'], ['D', 'E', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "alternativeAgreement"), ("person", "local")] }

def ex9a : Datum :=
  { id := "halperthammerly2026_ex9a"
    source := ⟨"diercks-2010", "p. 117"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(9a)"⟩
    language := "buku1249"
    primaryText := "si-si-ndu sy-a-kwa"
    glossedTokens := [("si-si-ndu", "7-7-thing"), ("sy-a-kwa", "7SM-PST-fall")]
    glossedWords := [⟨[['s', 'i'], ['s', 'i'], ['n', 'd', 'u']], [['7'], ['7'], ['t', 'h', 'i', 'n', 'g']]⟩, ⟨[['s', 'y'], ['a'], ['k', 'w', 'a']], [['7', 'S', 'M'], ['P', 'S', 'T'], ['f', 'a', 'l', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "alternativeAgreement"), ("class", "7")] }

def ex9b : Datum :=
  { id := "halperthammerly2026_ex9b"
    source := ⟨"diercks-2010", "p. 117"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(9b)"⟩
    language := "buku1249"
    primaryText := "si-si-ndu si-sy-a-kwa"
    glossedTokens := [("si-si-ndu", "7-7-thing"), ("si-sy-a-kwa", "7C-7SM-PST-fall")]
    glossedWords := [⟨[['s', 'i'], ['s', 'i'], ['n', 'd', 'u']], [['7'], ['7'], ['t', 'h', 'i', 'n', 'g']]⟩, ⟨[['s', 'i'], ['s', 'y'], ['a'], ['k', 'w', 'a']], [['7', 'C'], ['7', 'S', 'M'], ['P', 'S', 'T'], ['f', 'a', 'l', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "alternativeAgreement"), ("class", "7")] }

def ex10a : Datum :=
  { id := "halperthammerly2026_ex10a"
    source := ⟨"halpert-hammerly-2026", "(10a)"⟩
    reportedIn := none
    language := "zulu1248"
    primaryText := "Yi-mina o-khuluma-yo"
    glossedTokens := [("Yi-mina", "COP-1SG.PRO"), ("o-khuluma-yo", "1SM.REL-speak-DJ.REL")]
    glossedWords := [⟨[['Y', 'i'], ['m', 'i', 'n', 'a']], [['C', 'O', 'P'], ['1', 'S', 'G', '.', 'P', 'R', 'O']]⟩, ⟨[['o'], ['k', 'h', 'u', 'l', 'u', 'm', 'a'], ['y', 'o']], [['1', 'S', 'M', '.', 'R', 'E', 'L'], ['s', 'p', 'e', 'a', 'k'], ['D', 'J', '.', 'R', 'E', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "personReduction"), ("class", "1")] }

def ex10b : Datum :=
  { id := "halperthammerly2026_ex10b"
    source := ⟨"halpert-hammerly-2026", "(10b)"⟩
    reportedIn := none
    language := "zulu1248"
    primaryText := "Nina ni-ba-hle"
    glossedTokens := [("Nina", "2PL.PRO"), ("ni-ba-hle", "2PL-2SM-good")]
    glossedWords := [⟨[['N', 'i', 'n', 'a']], [['2', 'P', 'L', '.', 'P', 'R', 'O']]⟩, ⟨[['n', 'i'], ['b', 'a'], ['h', 'l', 'e']], [['2', 'P', 'L'], ['2', 'S', 'M'], ['g', 'o', 'o', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "personReduction"), ("class", "2")] }

def ex11a : Datum :=
  { id := "halperthammerly2026_ex11a"
    source := ⟨"riedel-taji-2022", "(28)"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(11a)"⟩
    language := "yaoo1241"
    primaryText := "Chi-lundamisi nga-ni-a-lila"
    glossedTokens := [("Chi-lundamisi", "7-last.initiate"), ("nga-ni-a-lila", "NEG-PST-1SM-cry")]
    glossedWords := [⟨[['C', 'h', 'i'], ['l', 'u', 'n', 'd', 'a', 'm', 'i', 's', 'i']], [['7'], ['l', 'a', 's', 't', '.', 'i', 'n', 'i', 't', 'i', 'a', 't', 'e']]⟩, ⟨[['n', 'g', 'a'], ['n', 'i'], ['a'], ['l', 'i', 'l', 'a']], [['N', 'E', 'G'], ['P', 'S', 'T'], ['1', 'S', 'M'], ['c', 'r', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "animacyAgreement"), ("class", "7"), ("core", "human")] }

def ex11b : Datum :=
  { id := "halperthammerly2026_ex11b"
    source := ⟨"riedel-taji-2022", "(28)"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(11b)"⟩
    language := "yaoo1241"
    primaryText := "Chi-lundamisi nga-ni-chi-lila"
    glossedTokens := [("Chi-lundamisi", "7-last.initiate"), ("nga-ni-chi-lila", "NEG-PST-7SM-cry")]
    glossedWords := [⟨[['C', 'h', 'i'], ['l', 'u', 'n', 'd', 'a', 'm', 'i', 's', 'i']], [['7'], ['l', 'a', 's', 't', '.', 'i', 'n', 'i', 't', 'i', 'a', 't', 'e']]⟩, ⟨[['n', 'g', 'a'], ['n', 'i'], ['c', 'h', 'i'], ['l', 'i', 'l', 'a']], [['N', 'E', 'G'], ['P', 'S', 'T'], ['7', 'S', 'M'], ['c', 'r', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "animacyAgreement"), ("class", "7"), ("core", "human")] }

def ex12a : Datum :=
  { id := "halperthammerly2026_ex12a"
    source := ⟨"riedel-taji-2022", "(35)"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(12a)"⟩
    language := "yaoo1241"
    primaryText := "A-ku-m-l-isy-a mbaka jwao"
    glossedTokens := [("A-ku-m-l-isy-a", "1SM-PRES-1OM-eat-CAUS-FV"), ("mbaka", "9cat"), ("jwao", "1POSS.3SG")]
    glossedWords := [⟨[['A'], ['k', 'u'], ['m'], ['l'], ['i', 's', 'y'], ['a']], [['1', 'S', 'M'], ['P', 'R', 'E', 'S'], ['1', 'O', 'M'], ['e', 'a', 't'], ['C', 'A', 'U', 'S'], ['F', 'V']]⟩, ⟨[['m', 'b', 'a', 'k', 'a']], [['9', 'c', 'a', 't']]⟩, ⟨[['j', 'w', 'a', 'o']], [['1', 'P', 'O', 'S', 'S', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "animacyAgreement"), ("class", "9"), ("core", "animal")] }

def ex12b : Datum :=
  { id := "halperthammerly2026_ex12b"
    source := ⟨"riedel-taji-2022", "(35)"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(12b)"⟩
    language := "yaoo1241"
    primaryText := "A-ku-ji-l-isy-a mbaka"
    glossedTokens := [("A-ku-ji-l-isy-a", "1SM-PRES-9OM-eat-CAUS-FV"), ("mbaka", "9cat")]
    glossedWords := [⟨[['A'], ['k', 'u'], ['j', 'i'], ['l'], ['i', 's', 'y'], ['a']], [['1', 'S', 'M'], ['P', 'R', 'E', 'S'], ['9', 'O', 'M'], ['e', 'a', 't'], ['C', 'A', 'U', 'S'], ['F', 'V']]⟩, ⟨[['m', 'b', 'a', 'k', 'a']], [['9', 'c', 'a', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "animacyAgreement"), ("class", "9"), ("core", "animal")] }

def ex13a : Datum :=
  { id := "halperthammerly2026_ex13a"
    source := ⟨"contini-morava-2008", "(1)"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(13a)"⟩
    language := "swah1253"
    primaryText := "Ki-su ch-ake ki-meanguka"
    glossedTokens := [("Ki-su", "7-knife"), ("ch-ake", "7-1SG.POSS"), ("ki-meanguka", "7SM-has.fallen")]
    glossedWords := [⟨[['K', 'i'], ['s', 'u']], [['7'], ['k', 'n', 'i', 'f', 'e']]⟩, ⟨[['c', 'h'], ['a', 'k', 'e']], [['7'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['k', 'i'], ['m', 'e', 'a', 'n', 'g', 'u', 'k', 'a']], [['7', 'S', 'M'], ['h', 'a', 's', '.', 'f', 'a', 'l', 'l', 'e', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "animacyAgreement"), ("class", "7"), ("core", "inanimate")] }

def ex13b : Datum :=
  { id := "halperthammerly2026_ex13b"
    source := ⟨"contini-morava-2008", "(1)"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(13b)"⟩
    language := "swah1253"
    primaryText := "Ki-ongozi w-ake a-meanguka"
    glossedTokens := [("Ki-ongozi", "7-leader"), ("w-ake", "1-1SG.POSS"), ("a-meanguka", "1SM-has.fallen")]
    glossedWords := [⟨[['K', 'i'], ['o', 'n', 'g', 'o', 'z', 'i']], [['7'], ['l', 'e', 'a', 'd', 'e', 'r']]⟩, ⟨[['w'], ['a', 'k', 'e']], [['1'], ['1', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['a'], ['m', 'e', 'a', 'n', 'g', 'u', 'k', 'a']], [['1', 'S', 'M'], ['h', 'a', 's', '.', 'f', 'a', 'l', 'l', 'e', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "animacyAgreement"), ("class", "7"), ("core", "human")] }

def ex14a : Datum :=
  { id := "halperthammerly2026_ex14a"
    source := ⟨"hualde-1989", "p. 182"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(14a)"⟩
    language := "nyat1246"
    primaryText := "N-a-mʊ-onaa mwalimu"
    glossedTokens := [("N-a-mʊ-onaa", "1SM-PAST1-1OM-see"), ("mwalimu", "1teacher")]
    glossedWords := [⟨[['N'], ['a'], ['m', 'ʊ'], ['o', 'n', 'a', 'a']], [['1', 'S', 'M'], ['P', 'A', 'S', 'T', '1'], ['1', 'O', 'M'], ['s', 'e', 'e']]⟩, ⟨[['m', 'w', 'a', 'l', 'i', 'm', 'u']], [['1', 't', 'e', 'a', 'c', 'h', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "objectDoubling"), ("core", "human")] }

def ex14b : Datum :=
  { id := "halperthammerly2026_ex14b"
    source := ⟨"hualde-1989", "p. 182"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(14b)"⟩
    language := "nyat1246"
    primaryText := "N-a-kɪ-onaa kɪtabu"
    glossedTokens := [("N-a-kɪ-onaa", "1SM-PAST1-7OM-see"), ("kɪtabu", "7book")]
    glossedWords := [⟨[['N'], ['a'], ['k', 'ɪ'], ['o', 'n', 'a', 'a']], [['1', 'S', 'M'], ['P', 'A', 'S', 'T', '1'], ['7', 'O', 'M'], ['s', 'e', 'e']]⟩, ⟨[['k', 'ɪ', 't', 'a', 'b', 'u']], [['7', 'b', 'o', 'o', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("phenomenon", "objectDoubling"), ("core", "inanimate")] }

def ex15 : Datum :=
  { id := "halperthammerly2026_ex15"
    source := ⟨"taraldsen-et-al-2018", "p. 1345"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(15)"⟩
    language := "xhos1239"
    primaryText := "U-m-ntwana no-m-fazi ba-ya-dlala"
    glossedTokens := [("U-m-ntwana", "1-1-child"), ("no-m-fazi", "and.1-1-woman"), ("ba-ya-dlala", "SM2-DJ-play")]
    glossedWords := [⟨[['U'], ['m'], ['n', 't', 'w', 'a', 'n', 'a']], [['1'], ['1'], ['c', 'h', 'i', 'l', 'd']]⟩, ⟨[['n', 'o'], ['m'], ['f', 'a', 'z', 'i']], [['a', 'n', 'd', '.', '1'], ['1'], ['w', 'o', 'm', 'a', 'n']]⟩, ⟨[['b', 'a'], ['y', 'a'], ['d', 'l', 'a', 'l', 'a']], [['S', 'M', '2'], ['D', 'J'], ['p', 'l', 'a', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "conjunctAgreement"), ("class", "1"), ("core", "human")] }

def ex16 : Datum :=
  { id := "halperthammerly2026_ex16"
    source := ⟨"taraldsen-et-al-2018", "p. 1346"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(16)"⟩
    language := "xhos1239"
    primaryText := "U-m-Xhosa no-m-Zulu ba-sebenza ndawonye"
    glossedTokens := [("U-m-Xhosa", "1-1-Xhosa"), ("no-m-Zulu", "and.1-1-Zulu"), ("ba-sebenza", "SM2-work"), ("ndawonye", "together")]
    glossedWords := [⟨[['U'], ['m'], ['X', 'h', 'o', 's', 'a']], [['1'], ['1'], ['X', 'h', 'o', 's', 'a']]⟩, ⟨[['n', 'o'], ['m'], ['Z', 'u', 'l', 'u']], [['a', 'n', 'd', '.', '1'], ['1'], ['Z', 'u', 'l', 'u']]⟩, ⟨[['b', 'a'], ['s', 'e', 'b', 'e', 'n', 'z', 'a']], [['S', 'M', '2'], ['w', 'o', 'r', 'k']]⟩, ⟨[['n', 'd', 'a', 'w', 'o', 'n', 'y', 'e']], [['t', 'o', 'g', 'e', 't', 'h', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("U-m-Xhosa no-m-Zulu a-sebenza ndawonye.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "conjunctAgreement"), ("class", "1"), ("core", "human")] }

def ex17 : Datum :=
  { id := "halperthammerly2026_ex17"
    source := ⟨"taraldsen-et-al-2018", "p. 1347"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(17)"⟩
    language := "xhos1239"
    primaryText := "I-li-tye ne-qanda zi-khataza i-n-taka"
    glossedTokens := [("I-li-tye", "5-5-stone"), ("ne-qanda", "and.5-egg"), ("zi-khataza", "SM8.10-annoy"), ("i-n-taka", "9-9-bird")]
    glossedWords := [⟨[['I'], ['l', 'i'], ['t', 'y', 'e']], [['5'], ['5'], ['s', 't', 'o', 'n', 'e']]⟩, ⟨[['n', 'e'], ['q', 'a', 'n', 'd', 'a']], [['a', 'n', 'd', '.', '5'], ['e', 'g', 'g']]⟩, ⟨[['z', 'i'], ['k', 'h', 'a', 't', 'a', 'z', 'a']], [['S', 'M', '8', '.', '1', '0'], ['a', 'n', 'n', 'o', 'y']]⟩, ⟨[['i'], ['n'], ['t', 'a', 'k', 'a']], [['9'], ['9'], ['b', 'i', 'r', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("I-li-tye ne-qanda a-khataza i-n-taka", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.3"), ("phenomenon", "conjunctAgreement"), ("class", "5"), ("core", "inanimate")] }

def ex20a : Datum :=
  { id := "halperthammerly2026_ex20a"
    source := ⟨"msaka-2019", "p. 74"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(20a)"⟩
    language := "nyan1308"
    primaryText := "gonth-a"
    glossedTokens := [("gonth-a", "deaf-VFV")]
    glossedWords := [⟨[['g', 'o', 'n', 't', 'h'], ['a']], [['d', 'e', 'a', 'f'], ['V', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "finalVowel"), ("vowel", "a")] }

def ex20b : Datum :=
  { id := "halperthammerly2026_ex20b"
    source := ⟨"msaka-2019", "p. 74"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(20b)"⟩
    language := "nyan1308"
    primaryText := "gónth-i"
    glossedTokens := [("gónth-i", "deaf-NFV")]
    glossedWords := [⟨[['g', 'ó', 'n', 't', 'h'], ['i']], [['d', 'e', 'a', 'f'], ['N', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "finalVowel"), ("vowel", "i")] }

def ex21a : Datum :=
  { id := "halperthammerly2026_ex21a"
    source := ⟨"mletshe-2019", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(21a)"⟩
    language := "xhos1239"
    primaryText := "u-m-thiml-i"
    glossedTokens := [("u-m-thiml-i", "CL1-CL1-sneeze-NFV.ANIM")]
    glossedWords := [⟨[['u'], ['m'], ['t', 'h', 'i', 'm', 'l'], ['i']], [['C', 'L', '1'], ['C', 'L', '1'], ['s', 'n', 'e', 'e', 'z', 'e'], ['N', 'F', 'V', '.', 'A', 'N', 'I', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "finalVowel"), ("vowel", "i"), ("class", "1")] }

def ex21b : Datum :=
  { id := "halperthammerly2026_ex21b"
    source := ⟨"mletshe-2019", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(21b)"⟩
    language := "xhos1239"
    primaryText := "u-m-thiml-o"
    glossedTokens := [("u-m-thiml-o", "CL3-CL3-sneeze-NFV.INAN")]
    glossedWords := [⟨[['u'], ['m'], ['t', 'h', 'i', 'm', 'l'], ['o']], [['C', 'L', '3'], ['C', 'L', '3'], ['s', 'n', 'e', 'e', 'z', 'e'], ['N', 'F', 'V', '.', 'I', 'N', 'A', 'N']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "finalVowel"), ("vowel", "o"), ("class", "3")] }

def ex23 : Datum :=
  { id := "halperthammerly2026_ex23"
    source := ⟨"mletshe-2019", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(23)"⟩
    language := "xhos1239"
    primaryText := "i-si-thiml-i"
    glossedTokens := [("i-si-thiml-i", "CL7-CL7-sneeze-NFV.ANIM")]
    glossedWords := [⟨[['i'], ['s', 'i'], ['t', 'h', 'i', 'm', 'l'], ['i']], [['C', 'L', '7'], ['C', 'L', '7'], ['s', 'n', 'e', 'e', 'z', 'e'], ['N', 'F', 'V', '.', 'A', 'N', 'I', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("phenomenon", "finalVowel"), ("vowel", "i"), ("class", "7")] }

def ex24a : Datum :=
  { id := "halperthammerly2026_ex24a"
    source := ⟨"dechaine-et-al-2014", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(24a)"⟩
    language := "shon1251"
    primaryText := "mu-kómáná"
    glossedTokens := [("mu-kómáná", "CL1-boy")]
    glossedWords := [⟨[['m', 'u'], ['k', 'ó', 'm', 'á', 'n', 'á']], [['C', 'L', '1'], ['b', 'o', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "stacking"), ("class", "1")] }

def ex24b : Datum :=
  { id := "halperthammerly2026_ex24b"
    source := ⟨"dechaine-et-al-2014", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(24b)"⟩
    language := "shon1251"
    primaryText := "ka-mu-kómáná"
    glossedTokens := [("ka-mu-kómáná", "CL12-CL1-boy")]
    glossedWords := [⟨[['k', 'a'], ['m', 'u'], ['k', 'ó', 'm', 'á', 'n', 'á']], [['C', 'L', '1', '2'], ['C', 'L', '1'], ['b', 'o', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "stacking"), ("class", "12")] }

def ex27a : Datum :=
  { id := "halperthammerly2026_ex27a"
    source := ⟨"mletshe-2019", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(27a)"⟩
    language := "xhos1239"
    primaryText := "u-m-khohlel-i"
    glossedTokens := [("u-m-khohlel-i", "CL1-CL1-cough-NFV.ANIM")]
    glossedWords := [⟨[['u'], ['m'], ['k', 'h', 'o', 'h', 'l', 'e', 'l'], ['i']], [['C', 'L', '1'], ['C', 'L', '1'], ['c', 'o', 'u', 'g', 'h'], ['N', 'F', 'V', '.', 'A', 'N', 'I', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "stacking"), ("vowel", "i"), ("class", "1")] }

def ex27b : Datum :=
  { id := "halperthammerly2026_ex27b"
    source := ⟨"mletshe-2019", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(27b)"⟩
    language := "xhos1239"
    primaryText := "i-si-khohlel-i"
    glossedTokens := [("i-si-khohlel-i", "CL7-CL7-cough-NFV.ANIM")]
    glossedWords := [⟨[['i'], ['s', 'i'], ['k', 'h', 'o', 'h', 'l', 'e', 'l'], ['i']], [['C', 'L', '7'], ['C', 'L', '7'], ['c', 'o', 'u', 'g', 'h'], ['N', 'F', 'V', '.', 'A', 'N', 'I', 'M']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "stacking"), ("vowel", "i"), ("class", "7")] }

def ex27c : Datum :=
  { id := "halperthammerly2026_ex27c"
    source := ⟨"mletshe-2019", ""⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(27c)"⟩
    language := "xhos1239"
    primaryText := "i-si-khohlel-a"
    glossedTokens := [("i-si-khohlel-a", "CL7-CL7-cough-NFV.INAN")]
    glossedWords := [⟨[['i'], ['s', 'i'], ['k', 'h', 'o', 'h', 'l', 'e', 'l'], ['a']], [['C', 'L', '7'], ['C', 'L', '7'], ['c', 'o', 'u', 'g', 'h'], ['N', 'F', 'V', '.', 'I', 'N', 'A', 'N']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "stacking"), ("vowel", "a"), ("class", "7")] }

def exfn14i : Datum :=
  { id := "halperthammerly2026_exfn14i"
    source := ⟨"xala-1996", "p. 50"⟩
    reportedIn := some ⟨"halpert-hammerly-2026", "(fn. 14 (i))"⟩
    language := "zulu1248"
    primaryText := "ubu-n-ja"
    glossedTokens := [("ubu-n-ja", "14-9-dog")]
    glossedWords := [⟨[['u', 'b', 'u'], ['n'], ['j', 'a']], [['1', '4'], ['9'], ['d', 'o', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("phenomenon", "stacking"), ("class", "14")] }

def all : List Datum := [ex8a, ex8b, ex8c, ex9a, ex9b, ex10a, ex10b, ex11a, ex11b, ex12a, ex12b, ex13a, ex13b, ex14a, ex14b, ex15, ex16, ex17, ex20a, ex20b, ex21a, ex21b, ex23, ex24a, ex24b, ex27a, ex27b, ex27c, exfn14i]

end HalpertHammerly2026.Examples
