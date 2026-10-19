module

public import Linglib.Data.Examples.Schema

/-!
# `Jablonska2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Jablonska2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jablonska2004.Examples`.
-/

@[expose] public section

namespace Jablonska2004.Examples

def ex_4a : Datum :=
  { id := "jablonska2004_4a"
    source := ⟨"jablonska-2004", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The soup cooled for an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("claim", "degree achievements pass both telicity tests")] }

def ex_4b : Datum :=
  { id := "jablonska2004_4b"
    source := ⟨"jablonska-2004", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The soup cooled in an hour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("claim", "degree achievements pass both telicity tests")] }

def ex_11a : Datum :=
  { id := "jablonska2004_11a"
    source := ⟨"jablonska-2004", "(11a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Marek po-siwi-a-ł w dwa lata."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("reading", "considerable change"), ("claim", "upward entailing to (11b)")] }

def ex_11b : Datum :=
  { id := "jablonska2004_11b"
    source := ⟨"jablonska-2004", "(11b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Marek po-siwi-a-ł w rok."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("reading", "considerable change")] }

def ex_12a : Datum :=
  { id := "jablonska2004_12a"
    source := ⟨"jablonska-2004", "(12a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Marek po-spacerował przez dwie godziny."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("reading", "delimitative"), ("claim", "entails (12b) only by varying the vague 'while'")] }

def ex_12b : Datum :=
  { id := "jablonska2004_12b"
    source := ⟨"jablonska-2004", "(12b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Marek po-spacerował przez godzinę."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("reading", "delimitative")] }

def ex_14a : Datum :=
  { id := "jablonska2004_14a"
    source := ⟨"jablonska-2004", "(14a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "kop-ną-ć kogoś w sekundę"
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "semelfactive"), ("claim", "no process part")] }

def ex_14b : Datum :=
  { id := "jablonska2004_14b"
    source := ⟨"jablonska-2004", "(14b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "rdze-wi-e-ć w pół roku"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "low -ej-"), ("claim", "no process part")] }

def ex_14c : Datum :=
  { id := "jablonska2004_14c"
    source := ⟨"jablonska-2004", "(14c)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "ufać w pół roku"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "stative"), ("claim", "no change of state")] }

def ex_14d : Datum :=
  { id := "jablonska2004_14d"
    source := ⟨"jablonska-2004", "(14d)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "kopać w pół roku"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "high -aj-"), ("claim", "no change of state")] }

def ex_17 : Datum :=
  { id := "jablonska2004_17"
    source := ⟨"jablonska-2004", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The icicle lengthened by 3 centimeters (*for two days)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("claim", "an overt degree quantizes")] }

def ex_23a : Datum :=
  { id := "jablonska2004_23a"
    source := ⟨"jablonska-2004", "(23a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ci mężczyźni po-babi-e-li jednocześnie."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "low -ej-"), ("reading", "distributive"), ("layers", "po- in Asp1")] }

def ex_23b : Datum :=
  { id := "jablonska2004_23b"
    source := ⟨"jablonska-2004", "(23b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Nagle wszyscy po-smut-ni-e-li."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "low -ej-"), ("reading", "distributive")] }

def ex_24a : Datum :=
  { id := "jablonska2004_24a"
    source := ⟨"jablonska-2004", "(24a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Po-prze-czyt-∅-ywa-łem wszystkie książki."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "high -aj-"), ("layers", "lexical prefix, Secondary Imperfective, po- in Asp3"), ("reading", "distributive")] }

def ex_24b : Datum :=
  { id := "jablonska2004_24b"
    source := ⟨"jablonska-2004", "(24b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Po-prze-czyt-a-łem wszystkie książki."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("verbalizer", "high -aj-"), ("layers", "lexical prefix, po-"), ("claim", "po- selects a [-Perf] predicate (25)")] }

def ex_28a : Datum :=
  { id := "jablonska2004_28a"
    source := ⟨"jablonska-2004", "(28a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Maria po-chowa-ła (wszystkie) zabawki."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("verbalizer", "high -aj-"), ("reading", "distributive or delimitative")] }

def ex_28b : Datum :=
  { id := "jablonska2004_28b"
    source := ⟨"jablonska-2004", "(28b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Maria po-prze-pis-ywa-ła (wszystkie) listy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("layers", "lexical prefix, Secondary Imperfective, po- in Asp3"), ("reading", "distributive or delimitative")] }

def ex_28c : Datum :=
  { id := "jablonska2004_28c"
    source := ⟨"jablonska-2004", "(28c)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Chłopcy po-śpiewa-li."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("reading", "delimitative only: the external argument is outside the scope of po-")] }

def ex_28d : Datum :=
  { id := "jablonska2004_28d"
    source := ⟨"jablonska-2004", "(28d)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Ludzie po-w-chodzi-li (przez chwilę, a potem przestali)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("reading", "distributive or delimitative")] }

def ex_28e : Datum :=
  { id := "jablonska2004_28e"
    source := ⟨"jablonska-2004", "(28e)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Marek po-o-mawia-ł swój doktorat na każdej konferencji w tym roku."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("reading", "distributive with singular subject and object")] }

def ex_33a : Datum :=
  { id := "jablonska2004_33a"
    source := ⟨"jablonska-2004", "(33a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "zacząć po-prze-pis-ywa-ć listy"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3"), ("claim", "po- above SI yields a perfective: no phasal complement")] }

def ex_33b : Datum :=
  { id := "jablonska2004_33b"
    source := ⟨"jablonska-2004", "(33b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "po-prze-pis-uj-e-sz listy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3"), ("claim", "no present-tense interpretation")] }

def ex_44 : Datum :=
  { id := "jablonska2004_44"
    source := ⟨"jablonska-2004", "(44)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Okna zostały po-za-myk-a-n-e."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3"), ("claim", "the SI morpheme sits below Voice: a verbal passive")] }

def ex_46a : Datum :=
  { id := "jablonska2004_46a"
    source := ⟨"jablonska-2004", "(46a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Marek zaczął mach-ną-ć."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("claim", "semelfactives are perfective: no phasal complement")] }

def ex_46b : Datum :=
  { id := "jablonska2004_46b"
    source := ⟨"jablonska-2004", "(46b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Zaraz mach-ni-e-sz"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.1"), ("claim", "semelfactives are perfective: no present reading")] }

def ex_52 : Datum :=
  { id := "jablonska2004_52"
    source := ⟨"jablonska-2004", "(52)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Natychmiast po-biegnię-to po lekarza."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4"), ("claim", "impersonal passive: unergative")] }

def ex_63a : Datum :=
  { id := "jablonska2004_63a"
    source := ⟨"jablonska-2004", "(63a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "po-palić"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "no attenuative reading without SI")] }

def ex_65a : Datum :=
  { id := "jablonska2004_65a"
    source := ⟨"jablonska-2004", "(65a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Maria po-dmuch-iwa-ła na zupę kiedy wszedł Jan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("reading", "progressive of an attenuative-frequentative")] }

def ex_65b : Datum :=
  { id := "jablonska2004_65b"
    source := ⟨"jablonska-2004", "(65b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Maria gr-ywa-ła na wyścigach kiedy przyjechał Jan."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("reading", "habitual only")] }

def ex_71a : Datum :=
  { id := "jablonska2004_71a"
    source := ⟨"jablonska-2004", "(71a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The situation is worsening."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "English degree achievements take the progressive")] }

def ex_80a : Datum :=
  { id := "jablonska2004_80a"
    source := ⟨"jablonska-2004", "(80a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Maria do-płynie do brzegu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("verbalizer", "directed motion")] }

def ex_80b : Datum :=
  { id := "jablonska2004_80b"
    source := ⟨"jablonska-2004", "(80b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Maria zawsze/właśnie do-pływa do brzegu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "SI only through the non-directed stem")] }

def ex_83a : Datum :=
  { id := "jablonska2004_83a"
    source := ⟨"jablonska-2004", "(83a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Kiedy wreszcie po-po-równ-ywa-li-śmy wszystkie prace, mogliśmy przystąpić do wydawania ocen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("layers", "lexical po-, Secondary Imperfective, po- in Asp3"), ("reading", "distributive")] }

def ex_83b : Datum :=
  { id := "jablonska2004_83b"
    source := ⟨"jablonska-2004", "(83b)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "Czy wszyscy uczestnicy po-po-twierdz-a-li już swój udział?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("layers", "lexical po-, Secondary Imperfective, po- in Asp3"), ("reading", "distributive")] }

def all : List Datum := [ex_4a, ex_4b, ex_11a, ex_11b, ex_12a, ex_12b, ex_14a, ex_14b, ex_14c, ex_14d, ex_17, ex_23a, ex_23b, ex_24a, ex_24b, ex_28a, ex_28b, ex_28c, ex_28d, ex_28e, ex_33a, ex_33b, ex_44, ex_46a, ex_46b, ex_52, ex_63a, ex_65a, ex_65b, ex_71a, ex_80a, ex_80b, ex_83a, ex_83b]

end Jablonska2004.Examples
