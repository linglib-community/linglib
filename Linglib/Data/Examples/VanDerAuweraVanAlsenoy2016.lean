module

public import Linglib.Data.Examples.Schema

/-!
# `VanDerAuweraVanAlsenoy2016` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerAuweraVanAlsenoy2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerAuweraVanAlsenoy2016.Examples`.
-/

@[expose] public section

namespace VanDerAuweraVanAlsenoy2016.Examples

def ex_1a : Datum :=
  { id := "vanderauweravanalsenoy2016_1a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I ain't never been to jail"
    glossedTokens := []
    context := "Non-standard English."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("exponents", "clausal negator + negative adverb")] }

def ex_2 : Datum :=
  { id := "vanderauweravanalsenoy2016_2"
    source := ⟨"de-swart-2010", "p. 46"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(2)"⟩
    language := "stan1288"
    primaryText := "Nadie ha dicho nada"
    glossedTokens := [("Nadie", "nobody"), ("ha", "has"), ("dicho", "said"), ("nada", "nothing")]
    glossedWords := [⟨[['N', 'a', 'd', 'i', 'e']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['h', 'a']], [['h', 'a', 's']]⟩, ⟨[['d', 'i', 'c', 'h', 'o']], [['s', 'a', 'i', 'd']]⟩, ⟨[['n', 'a', 'd', 'a']], [['n', 'o', 't', 'h', 'i', 'n', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "negative spread")] }

def ex_3a : Datum :=
  { id := "vanderauweravanalsenoy2016_3a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(3a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je n'ai rien entendu"
    glossedTokens := [("Je", "I"), ("n'ai", "NEG.have"), ("rien", "nothing"), ("entendu", "heard")]
    glossedWords := [⟨[['J', 'e']], [['I']]⟩, ⟨[['n', '\'', 'a', 'i']], [['N', 'E', 'G', '.', 'h', 'a', 'v', 'e']]⟩, ⟨[['r', 'i', 'e', 'n']], [['n', 'o', 't', 'h', 'i', 'n', 'g']]⟩, ⟨[['e', 'n', 't', 'e', 'n', 'd', 'u']], [['h', 'e', 'a', 'r', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "negative"), ("negator", "ne")] }

def ex_3e : Datum :=
  { id := "vanderauweravanalsenoy2016_3e"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(3e)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai rien entendu"
    glossedTokens := [("J'ai", "I.have"), ("rien", "nothing"), ("entendu", "heard")]
    glossedWords := [⟨[['J', '\'', 'a', 'i']], [['I', '.', 'h', 'a', 'v', 'e']]⟩, ⟨[['r', 'i', 'e', 'n']], [['n', 'o', 't', 'h', 'i', 'n', 'g']]⟩, ⟨[['e', 'n', 't', 'e', 'n', 'd', 'u']], [['h', 'e', 'a', 'r', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := "Intended with a positive reading of rien."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "negative")] }

def ex_14a : Datum :=
  { id := "vanderauweravanalsenoy2016_14a"
    source := ⟨"haspelmath-1997", "(431a)"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(14a)"⟩
    language := "poli1260"
    primaryText := "Nikt nie przyszedł"
    glossedTokens := [("Nikt", "nobody"), ("nie", "NEG"), ("przyszedł", "came")]
    glossedWords := [⟨[['N', 'i', 'k', 't']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['n', 'i', 'e']], [['N', 'E', 'G']]⟩, ⟨[['p', 'r', 'z', 'y', 's', 'z', 'e', 'd', 'ł']], [['c', 'a', 'm', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("position", "preverbal")] }

def ex_14b : Datum :=
  { id := "vanderauweravanalsenoy2016_14b"
    source := ⟨"haspelmath-1997", "(431b)"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(14b)"⟩
    language := "poli1260"
    primaryText := "Nie widziałam nikogo"
    glossedTokens := [("Nie", "NEG"), ("widziałam", "saw"), ("nikogo", "nobody")]
    glossedWords := [⟨[['N', 'i', 'e']], [['N', 'E', 'G']]⟩, ⟨[['w', 'i', 'd', 'z', 'i', 'a', 'ł', 'a', 'm']], [['s', 'a', 'w']]⟩, ⟨[['n', 'i', 'k', 'o', 'g', 'o']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("position", "postverbal")] }

def ex_15a : Datum :=
  { id := "vanderauweravanalsenoy2016_15a"
    source := ⟨"haspelmath-1997", "(433a)"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(15a)"⟩
    language := "stan1288"
    primaryText := "Nadie vino"
    glossedTokens := [("Nadie", "nobody"), ("vino", "came")]
    glossedWords := [⟨[['N', 'a', 'd', 'i', 'e']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['v', 'i', 'n', 'o']], [['c', 'a', 'm', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "absent")] }

def ex_15b : Datum :=
  { id := "vanderauweravanalsenoy2016_15b"
    source := ⟨"haspelmath-1997", "(433b)"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(15b)"⟩
    language := "stan1288"
    primaryText := "No vi a nadie"
    glossedTokens := [("No", "NEG"), ("vi", "saw"), ("a", "to"), ("nadie", "nobody")]
    glossedWords := [⟨[['N', 'o']], [['N', 'E', 'G']]⟩, ⟨[['v', 'i']], [['s', 'a', 'w']]⟩, ⟨[['a']], [['t', 'o']]⟩, ⟨[['n', 'a', 'd', 'i', 'e']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "obligatory")] }

def ex_16a : Datum :=
  { id := "vanderauweravanalsenoy2016_16a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(16a)"⟩
    reportedIn := none
    language := "cent2050"
    primaryText := "ndú-má lèzə̂-nyí"
    glossedTokens := [("ndú-má", "who-NEG"), ("lèzə̂-nyí", "went-NEG")]
    glossedWords := [⟨[['n', 'd', 'ú'], ['m', 'á']], [['w', 'h', 'o'], ['N', 'E', 'G']]⟩, ⟨[['l', 'è', 'z', 'ə', '̂'], ['n', 'y', 'í']], [['w', 'e', 'n', 't'], ['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("negator", "postverbal")] }

def ex_20a : Datum :=
  { id := "vanderauweravanalsenoy2016_20a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(20a)"⟩
    reportedIn := none
    language := "cham1312"
    primaryText := "ni unu istaba guini gi paingi"
    glossedTokens := [("ni", "NEG"), ("unu", "one"), ("istaba", "AGR.be"), ("guini", "here"), ("gi", "LOC"), ("paingi", "last.night")]
    glossedWords := [⟨[['n', 'i']], [['N', 'E', 'G']]⟩, ⟨[['u', 'n', 'u']], [['o', 'n', 'e']]⟩, ⟨[['i', 's', 't', 'a', 'b', 'a']], [['A', 'G', 'R', '.', 'b', 'e']]⟩, ⟨[['g', 'u', 'i', 'n', 'i']], [['h', 'e', 'r', 'e']]⟩, ⟨[['g', 'i']], [['L', 'O', 'C']]⟩, ⟨[['p', 'a', 'i', 'n', 'g', 'i']], [['l', 'a', 's', 't', '.', 'n', 'i', 'g', 'h', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("contact", "Spanish")] }

def ex_21a : Datum :=
  { id := "vanderauweravanalsenoy2016_21a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(21a)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "wala taxi wiʔif"
    glossedTokens := [("wala", "not.even"), ("taxi", "taxi"), ("wiʔif", "stop.PRF.3MSG")]
    glossedWords := [⟨[['w', 'a', 'l', 'a']], [['n', 'o', 't', '.', 'e', 'v', 'e', 'n']]⟩, ⟨[['t', 'a', 'x', 'i']], [['t', 'a', 'x', 'i']]⟩, ⟨[['w', 'i', 'ʔ', 'i', 'f']], [['s', 't', 'o', 'p', '.', 'P', 'R', 'F', '.', '3', 'M', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("indefinite", "wala")] }

def ex_21b : Datum :=
  { id := "vanderauweravanalsenoy2016_21b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(21b)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "miš sāmiʕ wala kilma"
    glossedTokens := [("miš", "NEG"), ("sāmiʕ", "hear.PTCP.MSG"), ("wala", "not.even"), ("kilma", "word")]
    glossedWords := [⟨[['m', 'i', 'š']], [['N', 'E', 'G']]⟩, ⟨[['s', 'ā', 'm', 'i', 'ʕ']], [['h', 'e', 'a', 'r', '.', 'P', 'T', 'C', 'P', '.', 'M', 'S', 'G']]⟩, ⟨[['w', 'a', 'l', 'a']], [['n', 'o', 't', '.', 'e', 'v', 'e', 'n']]⟩, ⟨[['k', 'i', 'l', 'm', 'a']], [['w', 'o', 'r', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "obligatory")] }

def ex_24 : Datum :=
  { id := "vanderauweravanalsenoy2016_24"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(24)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vissi ekki sjá neitt"
    glossedTokens := [("Ég", "I"), ("vissi", "did"), ("ekki", "NEG"), ("sjá", "see"), ("neitt", "nothing")]
    glossedWords := [⟨[['É', 'g']], [['I']]⟩, ⟨[['v', 'i', 's', 's', 'i']], [['d', 'i', 'd']]⟩, ⟨[['e', 'k', 'k', 'i']], [['N', 'E', 'G']]⟩, ⟨[['s', 'j', 'á']], [['s', 'e', 'e']]⟩, ⟨[['n', 'e', 'i', 't', 't']], [['n', 'o', 't', 'h', 'i', 'n', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("paradigm", "neinn")] }

def ex_25 : Datum :=
  { id := "vanderauweravanalsenoy2016_25"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(25)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Neinn sá (ekki) mig"
    glossedTokens := [("Neinn", "nobody"), ("sá", "saw"), ("(ekki)", "NEG"), ("mig", "me")]
    glossedWords := [⟨[['N', 'e', 'i', 'n', 'n']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['s', 'á']], [['s', 'a', 'w']]⟩, ⟨[['e', 'k', 'k', 'i']], [['N', 'E', 'G']]⟩, ⟨[['m', 'i', 'g']], [['m', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("paradigm", "neinn")] }

def ex_27c : Datum :=
  { id := "vanderauweravanalsenoy2016_27c"
    source := ⟨"haspelmath-1997", "(460c)"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(27c)"⟩
    language := "oldr1238"
    primaryText := "jako svoego nikto že ne xulit'"
    glossedTokens := [("jako", "because"), ("svoego", "self.ACC"), ("nikto", "nobody"), ("že", "PRT"), ("ne", "NEG"), ("xulit'", "abuses")]
    glossedWords := [⟨[['j', 'a', 'k', 'o']], [['b', 'e', 'c', 'a', 'u', 's', 'e']]⟩, ⟨[['s', 'v', 'o', 'e', 'g', 'o']], [['s', 'e', 'l', 'f', '.', 'A', 'C', 'C']]⟩, ⟨[['n', 'i', 'k', 't', 'o']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['ž', 'e']], [['P', 'R', 'T']]⟩, ⟨[['n', 'e']], [['N', 'E', 'G']]⟩, ⟨[['x', 'u', 'l', 'i', 't', '\'']], [['a', 'b', 'u', 's', 'e', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_29a : Datum :=
  { id := "vanderauweravanalsenoy2016_29a"
    source := ⟨"de-swart-2010", "p. 173"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(29a)"⟩
    language := "stan1289"
    primaryText := "Ningú (no) ha vist Joan"
    glossedTokens := [("Ningú", "nobody"), ("(no)", "NEG"), ("ha", "has"), ("vist", "seen"), ("Joan", "John")]
    glossedWords := [⟨[['N', 'i', 'n', 'g', 'ú']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['n', 'o']], [['N', 'E', 'G']]⟩, ⟨[['h', 'a']], [['h', 'a', 's']]⟩, ⟨[['v', 'i', 's', 't']], [['s', 'e', 'e', 'n']]⟩, ⟨[['J', 'o', 'a', 'n']], [['J', 'o', 'h', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_31a : Datum :=
  { id := "vanderauweravanalsenoy2016_31a"
    source := ⟨"haspelmath-1997", "(463a)"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(31a)"⟩
    language := "stan1293"
    primaryText := "Nobody don't know where it's at"
    glossedTokens := []
    context := "African American Vernacular English."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_33b : Datum :=
  { id := "vanderauweravanalsenoy2016_33b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(33b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je (n')ai vu personne"
    glossedTokens := [("Je", "I"), ("(n')ai", "NEG.have"), ("vu", "seen"), ("personne", "nobody")]
    glossedWords := [⟨[['J', 'e']], [['I']]⟩, ⟨[['n', '\'', 'a', 'i']], [['N', 'E', 'G', '.', 'h', 'a', 'v', 'e']]⟩, ⟨[['v', 'u']], [['s', 'e', 'e', 'n']]⟩, ⟨[['p', 'e', 'r', 's', 'o', 'n', 'n', 'e']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")] }

def ex_34a : Datum :=
  { id := "vanderauweravanalsenoy2016_34a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(34a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Niemand heeft mij (*nie) gezien"
    glossedTokens := [("Niemand", "nobody"), ("heeft", "has"), ("mij", "me"), ("(*nie)", "NEG"), ("gezien", "seen")]
    glossedWords := [⟨[['N', 'i', 'e', 'm', 'a', 'n', 'd']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['h', 'e', 'e', 'f', 't']], [['h', 'a', 's']]⟩, ⟨[['m', 'i', 'j']], [['m', 'e']]⟩, ⟨[['*', 'n', 'i', 'e']], [['N', 'E', 'G']]⟩, ⟨[['g', 'e', 'z', 'i', 'e', 'n']], [['s', 'e', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := "Brabantic Belgian Dutch."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "absent")] }

def ex_34b : Datum :=
  { id := "vanderauweravanalsenoy2016_34b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(34b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik heb niemand (nie) gezien"
    glossedTokens := [("Ik", "I"), ("heb", "have"), ("niemand", "nobody"), ("(nie)", "NEG"), ("gezien", "seen")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'e', 'b']], [['h', 'a', 'v', 'e']]⟩, ⟨[['n', 'i', 'e', 'm', 'a', 'n', 'd']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩, ⟨[['n', 'i', 'e']], [['N', 'E', 'G']]⟩, ⟨[['g', 'e', 'z', 'i', 'e', 'n']], [['s', 'e', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := "Brabantic Belgian Dutch."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")] }

def ex_35b : Datum :=
  { id := "vanderauweravanalsenoy2016_35b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(35b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "versad šeni cigni ver vnaxe"
    glossedTokens := [("versad", "nowhere"), ("šeni", "your"), ("cigni", "book"), ("ver", "NEG"), ("vnaxe", "1.see.3")]
    glossedWords := [⟨[['v', 'e', 'r', 's', 'a', 'd']], [['n', 'o', 'w', 'h', 'e', 'r', 'e']]⟩, ⟨[['š', 'e', 'n', 'i']], [['y', 'o', 'u', 'r']]⟩, ⟨[['c', 'i', 'g', 'n', 'i']], [['b', 'o', 'o', 'k']]⟩, ⟨[['v', 'e', 'r']], [['N', 'E', 'G']]⟩, ⟨[['v', 'n', 'a', 'x', 'e']], [['1', '.', 's', 'e', 'e', '.', '3']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("parameter", "immediate precedence")] }

def ex_37 : Datum :=
  { id := "vanderauweravanalsenoy2016_37"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(37)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "votʃ-intʃ (tʃi)-desa"
    glossedTokens := [("votʃ-intʃ", "no-what"), ("(tʃi)-desa", "(NEG)-saw")]
    glossedWords := [⟨[['v', 'o', 't', 'ʃ'], ['i', 'n', 't', 'ʃ']], [['n', 'o'], ['w', 'h', 'a', 't']]⟩, ⟨[['t', 'ʃ', 'i'], ['d', 'e', 's', 'a']], [['(', 'N', 'E', 'G', ')'], ['s', 'a', 'w']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_40b : Datum :=
  { id := "vanderauweravanalsenoy2016_40b"
    source := ⟨"de-swart-2010", "p. 187"⟩
    reportedIn := some ⟨"van-der-auwera-van-alsenoy-2016", "(40b)"⟩
    language := "wels1247"
    primaryText := "Welish i neb"
    glossedTokens := [("Welish", "saw"), ("i", "I"), ("neb", "nobody")]
    glossedWords := [⟨[['W', 'e', 'l', 'i', 's', 'h']], [['s', 'a', 'w']]⟩, ⟨[['i']], [['I']]⟩, ⟨[['n', 'e', 'b']], [['n', 'o', 'b', 'o', 'd', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := "Informal Welsh."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")] }

def ex_45 : Datum :=
  { id := "vanderauweravanalsenoy2016_45"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(45)"⟩
    reportedIn := none
    language := "east2295"
    primaryText := "Ober men ken dokh tsum keyser nit firn a yidn mit bord un peyes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("parameter", "emphasis")] }

def all : List Datum := [ex_1a, ex_2, ex_3a, ex_3e, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_20a, ex_21a, ex_21b, ex_24, ex_25, ex_27c, ex_29a, ex_31a, ex_33b, ex_34a, ex_34b, ex_35b, ex_37, ex_40b, ex_45]

end VanDerAuweraVanAlsenoy2016.Examples
