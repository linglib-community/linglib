module

public import Linglib.Data.Examples.Schema

/-!
# `HartmannZimmermann2004` — typed example data

Auto-generated from `Linglib/Data/Examples/HartmannZimmermann2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartmannZimmermann2004.Examples`.
-/

@[expose] public section

namespace HartmannZimmermann2004.Examples

def ex17b : Datum :=
  { id := "hartmannzimmermann2004_ex17b"
    source := ⟨"hartmann-zimmermann-2004", "(17b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "múdúd-gó nóŋ"
    glossedTokens := [("múdúd-gó", "die-PERF"), ("nóŋ", "who")]
    glossedWords := [⟨['m', 'ú', 'd', 'ú', 'd', '-', 'g', 'ó'], ['d', 'i', 'e', '-', 'P', 'E', 'R', 'F'], [⟨['m', 'ú', 'd', 'ú', 'd'], ['d', 'i', 'e'], none⟩, ⟨['g', 'ó'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['n', 'ó', 'ŋ'], ['w', 'h', 'o'], [⟨['n', 'ó', 'ŋ'], ['w', 'h', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "subject"), ("aspect", "perfective"), ("strategy", "postposing")] }

def ex24a : Datum :=
  { id := "hartmannzimmermann2004_ex24a"
    source := ⟨"hartmann-zimmermann-2004", "(24a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Fátíma wur-go."
    glossedTokens := [("Fátíma", "Fatima"), ("wur-go", "laugh-PERF")]
    glossedWords := [⟨['F', 'á', 't', 'í', 'm', 'a'], ['F', 'a', 't', 'i', 'm', 'a'], [⟨['F', 'á', 't', 'í', 'm', 'a'], ['F', 'a', 't', 'i', 'm', 'a'], none⟩]⟩, ⟨['w', 'u', 'r', '-', 'g', 'o'], ['l', 'a', 'u', 'g', 'h', '-', 'P', 'E', 'R', 'F'], [⟨['w', 'u', 'r'], ['l', 'a', 'u', 'g', 'h'], none⟩, ⟨['g', 'o'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "allNew"), ("aspect", "perfective"), ("strategy", "unmarked")] }

def ex24b : Datum :=
  { id := "hartmannzimmermann2004_ex24b"
    source := ⟨"hartmann-zimmermann-2004", "(24b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Mbáastám wur-gó-i."
    glossedTokens := [("Mbáastám", "she"), ("wur-gó-i", "laugh-PERF-FOC")]
    glossedWords := [⟨['M', 'b', 'á', 'a', 's', 't', 'á', 'm'], ['s', 'h', 'e'], [⟨['M', 'b', 'á', 'a', 's', 't', 'á', 'm'], ['s', 'h', 'e'], none⟩]⟩, ⟨['w', 'u', 'r', '-', 'g', 'ó', '-', 'i'], ['l', 'a', 'u', 'g', 'h', '-', 'P', 'E', 'R', 'F', '-', 'F', 'O', 'C'], [⟨['w', 'u', 'r'], ['l', 'a', 'u', 'g', 'h'], none⟩, ⟨['g', 'ó'], ['P', 'E', 'R', 'F'], some '-'⟩, ⟨['i'], ['F', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to: Mairo yaa-gó náŋ? 'What did Mairo do?'"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("strategy", "suffixI"), ("transitive", "false")] }

def ex25a : Datum :=
  { id := "hartmannzimmermann2004_ex25a"
    source := ⟨"hartmann-zimmermann-2004", "(25a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lak wai-gó lánda"
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    glossedWords := [⟨['L', 'a', 'k'], ['L', 'a', 'k', 'u'], [⟨['L', 'a', 'k'], ['L', 'a', 'k', 'u'], none⟩]⟩, ⟨['w', 'a', 'i', '-', 'g', 'ó'], ['s', 'e', 'l', 'l', '-', 'P', 'E', 'R', 'F'], [⟨['w', 'a', 'i'], ['s', 'e', 'l', 'l'], none⟩, ⟨['g', 'ó'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['l', 'á', 'n', 'd', 'a'], ['d', 'r', 'e', 's', 's'], [⟨['l', 'á', 'n', 'd', 'a'], ['d', 'r', 'e', 's', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to: What did Laku sell?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")] }

def ex25b : Datum :=
  { id := "hartmannzimmermann2004_ex25b"
    source := ⟨"hartmann-zimmermann-2004", "(25b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lak wai-gó lánda"
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    glossedWords := [⟨['L', 'a', 'k'], ['L', 'a', 'k', 'u'], [⟨['L', 'a', 'k'], ['L', 'a', 'k', 'u'], none⟩]⟩, ⟨['w', 'a', 'i', '-', 'g', 'ó'], ['s', 'e', 'l', 'l', '-', 'P', 'E', 'R', 'F'], [⟨['w', 'a', 'i'], ['s', 'e', 'l', 'l'], none⟩, ⟨['g', 'ó'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['l', 'á', 'n', 'd', 'a'], ['d', 'r', 'e', 's', 's'], [⟨['l', 'á', 'n', 'd', 'a'], ['d', 'r', 'e', 's', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to: What did Laku do?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")] }

def ex25c : Datum :=
  { id := "hartmannzimmermann2004_ex25c"
    source := ⟨"hartmann-zimmermann-2004", "(25c)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lak wai-gó lánda"
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    glossedWords := [⟨['L', 'a', 'k'], ['L', 'a', 'k', 'u'], [⟨['L', 'a', 'k'], ['L', 'a', 'k', 'u'], none⟩]⟩, ⟨['w', 'a', 'i', '-', 'g', 'ó'], ['s', 'e', 'l', 'l', '-', 'P', 'E', 'R', 'F'], [⟨['w', 'a', 'i'], ['s', 'e', 'l', 'l'], none⟩, ⟨['g', 'ó'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['l', 'á', 'n', 'd', 'a'], ['d', 'r', 'e', 's', 's'], [⟨['l', 'á', 'n', 'd', 'a'], ['d', 'r', 'e', 's', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answer to: What did Laku do at the market? Did she buy a dress or did she sell a dress?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")] }

def ex31 : Datum :=
  { id := "hartmannzimmermann2004_ex31"
    source := ⟨"hartmann-zimmermann-2004", "(31)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    glossedWords := [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], none⟩]⟩, ⟨['n'], ['P', 'R', 'O', 'G'], [⟨['n'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], [⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], [⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "allNew"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex32a : Datum :=
  { id := "hartmannzimmermann2004_ex32a"
    source := ⟨"hartmann-zimmermann-2004", "(32a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    glossedWords := [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], none⟩]⟩, ⟨['n'], ['P', 'R', 'O', 'G'], [⟨['n'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], [⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], [⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Lakú n ball náŋ? 'What is Laku writing?'"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex32b : Datum :=
  { id := "hartmannzimmermann2004_ex32b"
    source := ⟨"hartmann-zimmermann-2004", "(32b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    glossedWords := [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], none⟩]⟩, ⟨['n'], ['P', 'R', 'O', 'G'], [⟨['n'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], [⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], [⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Lakú n yaaj náŋ? 'What is Laku doing?'"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex32c : Datum :=
  { id := "hartmannzimmermann2004_ex32c"
    source := ⟨"hartmann-zimmermann-2004", "(32c)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    glossedWords := [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], [⟨['L', 'a', 'k', 'ú'], ['L', 'a', 'k', 'u'], none⟩]⟩, ⟨['n'], ['P', 'R', 'O', 'G'], [⟨['n'], ['P', 'R', 'O', 'G'], none⟩]⟩, ⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], [⟨['b', 'a', 'l', 'l'], ['w', 'r', 'i', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], [⟨['w', 'a', 's', 'í', 'i', 'k', 'a'], ['l', 'e', 't', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Answer to: Lakú n ball wasíika yá mad wasíika? 'Is Laku WRITING a letter or READING a letter?'"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex36a : Datum :=
  { id := "hartmannzimmermann2004_ex36a"
    source := ⟨"hartmann-zimmermann-2004", "(36a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "N fad-go núm littáfi-i, n fad-ug wam gáayi-m"
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("n", "I"), ("fad-ug", "buy-PERF"), ("wam gáayi-m", "s.th.else-NEG")]
    glossedWords := [⟨['N'], ['I'], [⟨['N'], ['I'], none⟩]⟩, ⟨['f', 'a', 'd', '-', 'g', 'o'], ['b', 'u', 'y', '-', 'P', 'E', 'R', 'F'], [⟨['f', 'a', 'd'], ['b', 'u', 'y'], none⟩, ⟨['g', 'o'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['n', 'ú', 'm'], ['o', 'n', 'l', 'y'], [⟨['n', 'ú', 'm'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['l', 'i', 't', 't', 'á', 'f', 'i', '-', 'i'], ['b', 'o', 'o', 'k', '-', 't', 'h', 'e'], [⟨['l', 'i', 't', 't', 'á', 'f', 'i'], ['b', 'o', 'o', 'k'], none⟩, ⟨['i'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['n'], ['I'], [⟨['n'], ['I'], none⟩]⟩, ⟨['f', 'a', 'd', '-', 'u', 'g'], ['b', 'u', 'y', '-', 'P', 'E', 'R', 'F'], [⟨['f', 'a', 'd'], ['b', 'u', 'y'], none⟩, ⟨['u', 'g'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['w', 'a', 'm', ' ', 'g', 'á', 'a', 'y', 'i', '-', 'm'], ['s', '.', 't', 'h', '.', 'e', 'l', 's', 'e', '-', 'N', 'E', 'G'], [⟨['w', 'a', 'm', ' ', 'g', 'á', 'a', 'y', 'i'], ['s', '.', 't', 'h', '.', 'e', 'l', 's', 'e'], none⟩, ⟨['m'], ['N', 'E', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "perfective"), ("association", "object")] }

def ex36b : Datum :=
  { id := "hartmannzimmermann2004_ex36b"
    source := ⟨"hartmann-zimmermann-2004", "(36b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "N fad-go núm littáfi-i, n yaa-g wamgáayi-m"
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("n", "I"), ("yaa-g", "do-PERF"), ("wamgáayi-m", "s.th.else-NEG")]
    glossedWords := [⟨['N'], ['I'], [⟨['N'], ['I'], none⟩]⟩, ⟨['f', 'a', 'd', '-', 'g', 'o'], ['b', 'u', 'y', '-', 'P', 'E', 'R', 'F'], [⟨['f', 'a', 'd'], ['b', 'u', 'y'], none⟩, ⟨['g', 'o'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['n', 'ú', 'm'], ['o', 'n', 'l', 'y'], [⟨['n', 'ú', 'm'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['l', 'i', 't', 't', 'á', 'f', 'i', '-', 'i'], ['b', 'o', 'o', 'k', '-', 't', 'h', 'e'], [⟨['l', 'i', 't', 't', 'á', 'f', 'i'], ['b', 'o', 'o', 'k'], none⟩, ⟨['i'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['n'], ['I'], [⟨['n'], ['I'], none⟩]⟩, ⟨['y', 'a', 'a', '-', 'g'], ['d', 'o', '-', 'P', 'E', 'R', 'F'], [⟨['y', 'a', 'a'], ['d', 'o'], none⟩, ⟨['g'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['w', 'a', 'm', 'g', 'á', 'a', 'y', 'i', '-', 'm'], ['s', '.', 't', 'h', '.', 'e', 'l', 's', 'e', '-', 'N', 'E', 'G'], [⟨['w', 'a', 'm', 'g', 'á', 'a', 'y', 'i'], ['s', '.', 't', 'h', '.', 'e', 'l', 's', 'e'], none⟩, ⟨['m'], ['N', 'E', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("association", "vp")] }

def ex36c : Datum :=
  { id := "hartmannzimmermann2004_ex36c"
    source := ⟨"hartmann-zimmermann-2004", "(36c)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "N fad-go núm littáfi-i, fon di n mad-go-m"
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("fon di", "but yet"), ("n", "I"), ("mad-go-m", "read-PERF-NEG")]
    glossedWords := [⟨['N'], ['I'], [⟨['N'], ['I'], none⟩]⟩, ⟨['f', 'a', 'd', '-', 'g', 'o'], ['b', 'u', 'y', '-', 'P', 'E', 'R', 'F'], [⟨['f', 'a', 'd'], ['b', 'u', 'y'], none⟩, ⟨['g', 'o'], ['P', 'E', 'R', 'F'], some '-'⟩]⟩, ⟨['n', 'ú', 'm'], ['o', 'n', 'l', 'y'], [⟨['n', 'ú', 'm'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['l', 'i', 't', 't', 'á', 'f', 'i', '-', 'i'], ['b', 'o', 'o', 'k', '-', 't', 'h', 'e'], [⟨['l', 'i', 't', 't', 'á', 'f', 'i'], ['b', 'o', 'o', 'k'], none⟩, ⟨['i'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['f', 'o', 'n', ' ', 'd', 'i'], ['b', 'u', 't', ' ', 'y', 'e', 't'], [⟨['f', 'o', 'n', ' ', 'd', 'i'], ['b', 'u', 't', ' ', 'y', 'e', 't'], none⟩]⟩, ⟨['n'], ['I'], [⟨['n'], ['I'], none⟩]⟩, ⟨['m', 'a', 'd', '-', 'g', 'o', '-', 'm'], ['r', 'e', 'a', 'd', '-', 'P', 'E', 'R', 'F', '-', 'N', 'E', 'G'], [⟨['m', 'a', 'd'], ['r', 'e', 'a', 'd'], none⟩, ⟨['g', 'o'], ['P', 'E', 'R', 'F'], some '-'⟩, ⟨['m'], ['N', 'E', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "perfective"), ("association", "verb")] }

def all : List Datum := [ex17b, ex24a, ex24b, ex25a, ex25b, ex25c, ex31, ex32a, ex32b, ex32c, ex36a, ex36b, ex36c]

end HartmannZimmermann2004.Examples
