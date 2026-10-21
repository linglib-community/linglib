module

public import Linglib.Data.Examples.Schema

/-!
# `Brodkin2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Brodkin2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Brodkin2026.Examples`.
-/

@[expose] public section

namespace Brodkin2026.Examples

def ex_33a : Datum :=
  { id := "brodkin2026_33a"
    source := ⟨"brodkin-2026", "(33a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "méloᴴ uwéŋanᴴ ndi wúkuᴴ éᴴ."
    glossedTokens := [("meloʔ", "want"), ("o", "2ABS"), ("u-beŋaŋ", "1ERG-give"), ("ndi", "this"), ("buku", "book"), ("e", "here")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "short"), ("syntax", "complement")] }

def ex_33b : Datum :=
  { id := "brodkin2026_33b"
    source := ⟨"brodkin-2026", "(33b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "méloᴴ uwéŋaᴴ ĩ́ndiᴴ éᴴ."
    glossedTokens := [("meloʔ", "want"), ("o", "2ABS"), ("u-beŋaŋ", "1ERG-give"), ("ndi", "this"), ("e", "here")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "long"), ("syntax", "adjunct"), ("next", "footed")] }

def ex_36a : Datum :=
  { id := "brodkin2026_36a"
    source := ⟨"brodkin-2026", "(36a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "do anʤóroᴴ ndaŋ ŋúra wéɣaᴴ óᴴ."
    glossedTokens := [("do", "that"), ("anʤoro", "coconut"), ("ndaŋ", "not"), ("ŋura", "unripe"), ("bega", "too"), ("o", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "neg"), ("allomorph", "short"), ("syntax", "complement")] }

def ex_36b : Datum :=
  { id := "brodkin2026_36b"
    source := ⟨"brodkin-2026", "(36b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "tapi ɹo anʤóroᴴ andíaŋᴴ óᴴ."
    glossedTokens := [("tapi", "but"), ("do", "that"), ("anʤoro", "coconut"), ("ndaŋ", "not"), ("o", "there")]
    context := "De anjoro ngura bega e, … 'This coconut is too unripe, …'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "neg"), ("allomorph", "long"), ("syntax", "adjunct"), ("next", "footed")] }

def ex_40a : Datum :=
  { id := "brodkin2026_40a"
    source := ⟨"brodkin-2026", "(40a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "á ɹúaᴴ píllóaᴴ?"
    glossedTokens := [("a", "what"), ("dua", "still"), ("piŋ-loa", "ANTIP-sound")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "short"), ("syntax", "host")] }

def ex_40b : Datum :=
  { id := "brodkin2026_40b"
    source := ⟨"brodkin-2026", "(40b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ápaᴴ píllóaᴴ?"
    glossedTokens := [("a", "what"), ("piŋ-loa", "ANTIP-sound")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_41a : Datum :=
  { id := "brodkin2026_41a"
    source := ⟨"brodkin-2026", "(41a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ná násamᴴ mweŋéiᴴ?"
    glossedTokens := [("na", "which"), ("nasaŋ", "every"), ("mu-eŋei", "2ERG-be.in")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "short"), ("syntax", "host")] }

def ex_41b : Datum :=
  { id := "brodkin2026_41b"
    source := ⟨"brodkin-2026", "(41b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ínnaᴴ wémmeᴴ?"
    glossedTokens := [("na", "which"), ("bemme", "fall")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_42a : Datum :=
  { id := "brodkin2026_42a"
    source := ⟨"brodkin-2026", "(42a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "né násamᴴ mwítaᴴ?"
    glossedTokens := [("nai", "who"), ("nasaŋ", "every"), ("mu-ita", "2ERG-see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "who"), ("allomorph", "short"), ("syntax", "host")] }

def ex_42b : Datum :=
  { id := "brodkin2026_42b"
    source := ⟨"brodkin-2026", "(42b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ínneᴴ lámbaᴴ?"
    glossedTokens := [("nai", "who"), ("lamba", "go")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "who"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_56a : Datum :=
  { id := "brodkin2026_56a"
    source := ⟨"brodkin-2026", "(56a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "máã́paᴴ o míeʔᴴ?"
    glossedTokens := [("maŋ-apa", "VERBALIZER-what"), ("o", "2ABS"), ("mieʔ", "2PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "sisters"), ("affix", "verbalizer")] }

def ex_56b : Datum :=
  { id := "brodkin2026_56b"
    source := ⟨"brodkin-2026", "(56b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "máã́pa násaŋᴴ o míeʔᴴ?"
    glossedTokens := [("maŋ-apa", "VERBALIZER-what"), ("nasaŋ", "every"), ("o", "2ABS"), ("mieʔ", "2PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "host"), ("affix", "verbalizer")] }

def ex_76a : Datum :=
  { id := "brodkin2026_76a"
    source := ⟨"brodkin-2026", "(76a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ápaᴴ máppakéʔdeʔᴴ i?"
    glossedTokens := [("a", "what"), ("maŋ-pakeʔdeʔ", "AF-awaken"), ("i", "3ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_76b : Datum :=
  { id := "brodkin2026_76b"
    source := ⟨"brodkin-2026", "(76b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "á naᴴmáppakéʔdeʔᴴ i?"
    glossedTokens := [("a", "what"), ("na-maŋ-pakeʔdeʔ", "FUT-AF-awaken"), ("i", "3ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "what"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_77a : Datum :=
  { id := "brodkin2026_77a"
    source := ⟨"brodkin-2026", "(77a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ínnaᴴ kéttʃuʔᴴ?"
    glossedTokens := [("na", "which"), ("kettʃuʔ", "small")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same")] }

def ex_77b : Datum :=
  { id := "brodkin2026_77b"
    source := ⟨"brodkin-2026", "(77b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ná kaᴴrámboᴴ?"
    glossedTokens := [("na", "which"), ("karambo", "far")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "which"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_78a : Datum :=
  { id := "brodkin2026_78a"
    source := ⟨"brodkin-2026", "(78a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "nalattʃáriᴴ i índiᴴ ɣúruᴴ éᴴ."
    glossedTokens := [("na-lattʃari", "3ERG-throw.at"), ("i", "3ABS"), ("ndi", "this"), ("guru", "teacher"), ("e", "here")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "footed"), ("maxPhi", "same"), ("clause", "ditransitive")] }

def ex_78b : Datum :=
  { id := "brodkin2026_78b"
    source := ⟨"brodkin-2026", "(78b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "nalattʃáriᴴ i ndí ɣuᴴrúnnaᴴ éᴴ."
    glossedTokens := [("na-lattʃari", "3ERG-throw.at"), ("i", "3ABS"), ("ndi", "this"), ("guru-na", "teacher-3GEN"), ("e", "here")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "this_in_hand"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same"), ("clause", "ditransitive")] }

def ex_83b : Datum :=
  { id := "brodkin2026_83b"
    source := ⟨"brodkin-2026", "(83b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "néteᴴ i ɹó jaᴴrámmiŋᴴ óᴴ."
    glossedTokens := [("na-itai", "3ERG-look.for"), ("i", "3ABS"), ("do", "that"), ("ʤarammiŋ", "mirror"), ("o", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_84 : Datum :=
  { id := "brodkin2026_84"
    source := ⟨"brodkin-2026", "(84)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "nálliᴴ i ɹíʔoᴴ dirwambóŋiᴴ óᴴ."
    glossedTokens := [("na-alli", "3ERG-buy"), ("i", "3ABS"), ("do", "that"), ("diruamboŋi", "a.while.ago"), ("o", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "different")] }

def ex_86a : Datum :=
  { id := "brodkin2026_86a"
    source := ⟨"brodkin-2026", "(86a)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "natínroᴴ i ɹo ɣuᴴrúnaᴴ óᴴ."
    glossedTokens := [("na-tinro", "3ERG-chase"), ("i", "3ABS"), ("do", "that"), ("guru-na", "teacher-3GEN"), ("o", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same")] }

def ex_86b : Datum :=
  { id := "brodkin2026_86b"
    source := ⟨"brodkin-2026", "(86b)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "natínroᴴ i ɹíʔoᴴ gurúnaᴴ ikátʃoʔ óᴴ."
    glossedTokens := [("na-tinro", "3ERG-chase"), ("i", "3ABS"), ("do", "that"), ("guru-na", "teacher-3GEN"), ("ikatʃoʔ", "NAME"), ("o", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "long"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "different")] }

def ex_92 : Datum :=
  { id := "brodkin2026_92"
    source := ⟨"brodkin-2026", "(92)"⟩
    reportedIn := none
    language := "mand1442"
    primaryText := "ukiriŋaᴴ ĩ ɹó ɣuᴴrúʔuᴴ óᴴ."
    glossedTokens := [("u-kiriŋ-aŋ", "1ERG-send-APPL"), ("i", "3ABS"), ("do", "that"), ("guru-u", "teacher-1GEN"), ("o", "there")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("head", "that"), ("allomorph", "short"), ("syntax", "sisters"), ("next", "unfooted"), ("maxPhi", "same"), ("clause", "ditransitive")] }

def all : List Datum := [ex_33a, ex_33b, ex_36a, ex_36b, ex_40a, ex_40b, ex_41a, ex_41b, ex_42a, ex_42b, ex_56a, ex_56b, ex_76a, ex_76b, ex_77a, ex_77b, ex_78a, ex_78b, ex_83b, ex_84, ex_86a, ex_86b, ex_92]

end Brodkin2026.Examples
