module

public import Linglib.Data.Examples.Schema

/-!
# `SandeClemDabkowski2026` — typed example data

Auto-generated from `Linglib/Data/Examples/SandeClemDabkowski2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SandeClemDabkowski2026.Examples`.
-/

@[expose] public section

namespace SandeClemDabkowski2026.Examples

def ex11a : Datum :=
  { id := "sandeclemdabkowski2026_ex11a"
    source := ⟨"sande-clem-dabkowski-2026", "(11a)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e⁴ ji³ ɟaci²³.¹ joku-ni².³.⁴"
    glossedTokens := [("e⁴", "1SG.NOM"), ("ji³", "FUT"), ("ɟaci²³.¹", "Djatchi"), ("joku-ni².³.⁴", "PART-see")]
    glossedWords := [⟨[['e', '⁴']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['j', 'i', '³']], [['F', 'U', 'T']]⟩, ⟨[['ɟ', 'a', 'c', 'i', '²', '³', '¹']], [['D', 'j', 'a', 't', 'c', 'h', 'i']]⟩, ⟨[['j', 'o', 'k', 'u'], ['n', 'i', '²', '³', '⁴']], [['P', 'A', 'R', 'T'], ['s', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "S Aux O Part V"), ("verb", "ni"), ("particleATR", "plus")] }

def ex11b : Datum :=
  { id := "sandeclemdabkowski2026_ex11b"
    source := ⟨"sande-clem-dabkowski-2026", "(11b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e⁴ ni⁴ ɟaci²³.¹ jɔkʊ².³"
    glossedTokens := [("e⁴", "1SG.NOM"), ("ni⁴", "see.PFV"), ("ɟaci²³.¹", "Djatchi"), ("jɔkʊ².³", "PART")]
    glossedWords := [⟨[['e', '⁴']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'i', '⁴']], [['s', 'e', 'e', '.', 'P', 'F', 'V']]⟩, ⟨[['ɟ', 'a', 'c', 'i', '²', '³', '¹']], [['D', 'j', 'a', 't', 'c', 'h', 'i']]⟩, ⟨[['j', 'ɔ', 'k', 'ʊ', '²', '³']], [['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "S V O Part"), ("verb", "ni"), ("particleATR", "minus")] }

def ex11c : Datum :=
  { id := "sandeclemdabkowski2026_ex11c"
    source := ⟨"sande-clem-dabkowski-2026", "(11c)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e⁴ joku-ni².³.⁴ ɟaci²³.¹"
    glossedTokens := [("e⁴", "1SG.NOM"), ("joku-ni².³.⁴", "PART-see.PFV"), ("ɟaci²³.¹", "Djatchi")]
    glossedWords := [⟨[['e', '⁴']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['j', 'o', 'k', 'u'], ['n', 'i', '²', '³', '⁴']], [['P', 'A', 'R', 'T'], ['s', 'e', 'e', '.', 'P', 'F', 'V']]⟩, ⟨[['ɟ', 'a', 'c', 'i', '²', '³', '¹']], [['D', 'j', 'a', 't', 'c', 'h', 'i']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "S Part V O")] }

def ex12b : Datum :=
  { id := "sandeclemdabkowski2026_ex12b"
    source := ⟨"sande-clem-dabkowski-2026", "(12b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ɟaci²³.¹ ji³ ɔnɛ³.³ ɡbɔɡɔ².² jɔkʊ-ŋʷɔsa².³.³.¹"
    glossedTokens := [("ɟaci²³.¹", "Djatchi"), ("ji³", "FUT"), ("ɔnɛ³.³", "3SG.POSS"), ("ɡbɔɡɔ².²", "leg"), ("jɔkʊ-ŋʷɔsa².³.³.¹", "PART-scrape")]
    glossedWords := [⟨[['ɟ', 'a', 'c', 'i', '²', '³', '¹']], [['D', 'j', 'a', 't', 'c', 'h', 'i']]⟩, ⟨[['j', 'i', '³']], [['F', 'U', 'T']]⟩, ⟨[['ɔ', 'n', 'ɛ', '³', '³']], [['3', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['ɡ', 'b', 'ɔ', 'ɡ', 'ɔ', '²', '²']], [['l', 'e', 'g']]⟩, ⟨[['j', 'ɔ', 'k', 'ʊ'], ['ŋ', 'ʷ', 'ɔ', 's', 'a', '²', '³', '³', '¹']], [['P', 'A', 'R', 'T'], ['s', 'c', 'r', 'a', 'p', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "S Aux O Part V"), ("verb", "ngwOsa"), ("particleATR", "minus")] }

def ex13b : Datum :=
  { id := "sandeclemdabkowski2026_ex13b"
    source := ⟨"sande-clem-dabkowski-2026", "(13b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ɟaci²³.¹ ŋʷɔsa³.¹ ɔnɛ³.³ ɡbɔɡɔ².² jɔkʊ².³"
    glossedTokens := [("ɟaci²³.¹", "Djatchi"), ("ŋʷɔsa³.¹", "scrape.PFV"), ("ɔnɛ³.³", "3SG.POSS"), ("ɡbɔɡɔ².²", "leg"), ("jɔkʊ².³", "PART")]
    glossedWords := [⟨[['ɟ', 'a', 'c', 'i', '²', '³', '¹']], [['D', 'j', 'a', 't', 'c', 'h', 'i']]⟩, ⟨[['ŋ', 'ʷ', 'ɔ', 's', 'a', '³', '¹']], [['s', 'c', 'r', 'a', 'p', 'e', '.', 'P', 'F', 'V']]⟩, ⟨[['ɔ', 'n', 'ɛ', '³', '³']], [['3', 'S', 'G', '.', 'P', 'O', 'S', 'S']]⟩, ⟨[['ɡ', 'b', 'ɔ', 'ɡ', 'ɔ', '²', '²']], [['l', 'e', 'g']]⟩, ⟨[['j', 'ɔ', 'k', 'ʊ', '²', '³']], [['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "S V O Part"), ("verb", "ngwOsa"), ("particleATR", "minus")] }

def ex21a : Datum :=
  { id := "sandeclemdabkowski2026_ex21a"
    source := ⟨"sande-clem-dabkowski-2026", "(21a)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "jɔkʊ².³ ɔ³ ni=ɔ⁴.²"
    glossedTokens := [("jɔkʊ².³", "PART"), ("ɔ³", "3SG.NOM"), ("ni=ɔ⁴.²", "see.PFV=3SG.ACC")]
    glossedWords := [⟨[['j', 'ɔ', 'k', 'ʊ', '²', '³']], [['P', 'A', 'R', 'T']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'i'], ['ɔ', '⁴', '²']], [['s', 'e', 'e', '.', 'P', 'F', 'V'], ['3', 'S', 'G', '.', 'A', 'C', 'C']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part S V O"), ("verb", "ni"), ("particleATR", "minus")] }

def ex21b : Datum :=
  { id := "sandeclemdabkowski2026_ex21b"
    source := ⟨"sande-clem-dabkowski-2026", "(21b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku-ni².³.⁴ ɔ³ ni=ɔ⁴.² (jɔkʊ².³)"
    glossedTokens := [("joku-ni².³.⁴", "PART-see"), ("ɔ³", "3SG.NOM"), ("ni=ɔ⁴.²", "see.PFV=3SG.ACC"), ("(jɔkʊ².³)", "PART")]
    glossedWords := [⟨[['j', 'o', 'k', 'u'], ['n', 'i', '²', '³', '⁴']], [['P', 'A', 'R', 'T'], ['s', 'e', 'e']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'i'], ['ɔ', '⁴', '²']], [['s', 'e', 'e', '.', 'P', 'F', 'V'], ['3', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['j', 'ɔ', 'k', 'ʊ', '²', '³']], [['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part V S V O")] }

def ex21c : Datum :=
  { id := "sandeclemdabkowski2026_ex21c"
    source := ⟨"sande-clem-dabkowski-2026", "(21c)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ni⁴ ɔ³ ni=ɔ⁴.² jɔkʊ².³"
    glossedTokens := [("ni⁴", "see"), ("ɔ³", "3SG.NOM"), ("ni=ɔ⁴.²", "see.PFV=3SG.ACC"), ("jɔkʊ².³", "PART")]
    glossedWords := [⟨[['n', 'i', '⁴']], [['s', 'e', 'e']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'i'], ['ɔ', '⁴', '²']], [['s', 'e', 'e', '.', 'P', 'F', 'V'], ['3', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['j', 'ɔ', 'k', 'ʊ', '²', '³']], [['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "V S V O Part")] }

def ex21d : Datum :=
  { id := "sandeclemdabkowski2026_ex21d"
    source := ⟨"sande-clem-dabkowski-2026", "(21d)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ni⁴ ɔ³ =ɔ² jɔkʊ².³"
    glossedTokens := [("ni⁴", "see"), ("ɔ³", "3SG.NOM"), ("=ɔ²", "3SG.ACC"), ("jɔkʊ².³", "PART")]
    glossedWords := [⟨[['n', 'i', '⁴']], [['s', 'e', 'e']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[[], ['ɔ', '²']], [['3', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['j', 'ɔ', 'k', 'ʊ', '²', '³']], [['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "V S O Part")] }

def ex21e : Datum :=
  { id := "sandeclemdabkowski2026_ex21e"
    source := ⟨"sande-clem-dabkowski-2026", "(21e)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku².³ ɔ³ ni=ɔ⁴.² jɔkʊ².³"
    glossedTokens := [("joku².³", "PART"), ("ɔ³", "3SG.NOM"), ("ni=ɔ⁴.²", "see.PFV=3SG.ACC"), ("jɔkʊ².³", "PART")]
    glossedWords := [⟨[['j', 'o', 'k', 'u', '²', '³']], [['P', 'A', 'R', 'T']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['n', 'i'], ['ɔ', '⁴', '²']], [['s', 'e', 'e', '.', 'P', 'F', 'V'], ['3', 'S', 'G', '.', 'A', 'C', 'C']]⟩, ⟨[['j', 'ɔ', 'k', 'ʊ', '²', '³']], [['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part S V O Part")] }

def ex22 : Datum :=
  { id := "sandeclemdabkowski2026_ex22"
    source := ⟨"sande-clem-dabkowski-2026", "(22)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku².³ ɔ³ ji³ ɟaci²³.¹ ni⁴"
    glossedTokens := [("joku².³", "PART"), ("ɔ³", "3SG.NOM"), ("ji³", "FUT"), ("ɟaci²³.¹", "Djatchi"), ("ni⁴", "see")]
    glossedWords := [⟨[['j', 'o', 'k', 'u', '²', '³']], [['P', 'A', 'R', 'T']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['j', 'i', '³']], [['F', 'U', 'T']]⟩, ⟨[['ɟ', 'a', 'c', 'i', '²', '³', '¹']], [['D', 'j', 'a', 't', 'c', 'h', 'i']]⟩, ⟨[['n', 'i', '⁴']], [['s', 'e', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part S Aux O V"), ("verb", "ni"), ("particleATR", "plus")] }

def ex24b : Datum :=
  { id := "sandeclemdabkowski2026_ex24b"
    source := ⟨"sande-clem-dabkowski-2026", "(24b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku².³ ɔ³ ji³ ɟaci²³.¹ ni⁴"
    glossedTokens := [("joku².³", "PART"), ("ɔ³", "3SG.NOM"), ("ji³", "FUT"), ("ɟaci²³.¹", "Djatchi"), ("ni⁴", "see")]
    glossedWords := [⟨[['j', 'o', 'k', 'u', '²', '³']], [['P', 'A', 'R', 'T']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['j', 'i', '³']], [['F', 'U', 'T']]⟩, ⟨[['ɟ', 'a', 'c', 'i', '²', '³', '¹']], [['D', 'j', 'a', 't', 'c', 'h', 'i']]⟩, ⟨[['n', 'i', '⁴']], [['s', 'e', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("jɔkʊ².³ ɔ³ ji³ ɟaci²³.¹ ni⁴", .ungrammatical)]
    readings := []
    paperFeatures := [("pattern", "Part S Aux O V"), ("verb", "ni"), ("particleATR", "plus")] }

def ex41 : Datum :=
  { id := "sandeclemdabkowski2026_ex41"
    source := ⟨"sande-clem-dabkowski-2026", "(41)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku².³ ɔ³ ka³ ɟɔkʷɪ-a².³.² ni⁴"
    glossedTokens := [("joku².³", "PART"), ("ɔ³", "3SG.NOM"), ("ka³", "PROSP"), ("ɟɔkʷɪ-a².³.²", "bird-PL"), ("ni⁴", "see")]
    glossedWords := [⟨[['j', 'o', 'k', 'u', '²', '³']], [['P', 'A', 'R', 'T']]⟩, ⟨[['ɔ', '³']], [['3', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['k', 'a', '³']], [['P', 'R', 'O', 'S', 'P']]⟩, ⟨[['ɟ', 'ɔ', 'k', 'ʷ', 'ɪ'], ['a', '²', '³', '²']], [['b', 'i', 'r', 'd'], ['P', 'L']]⟩, ⟨[['n', 'i', '⁴']], [['s', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part S Aux O V"), ("verb", "ni"), ("particleATR", "plus"), ("interveningATR", "minus")] }

def ex49a : Datum :=
  { id := "sandeclemdabkowski2026_ex49a"
    source := ⟨"sande-clem-dabkowski-2026", "(49a)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "fas w-ale"
    glossedTokens := [("fas", "horse"), ("w-ale", "CL-DEM.DIST")]
    glossedWords := [⟨[['f', 'a', 's']], [['h', 'o', 'r', 's', 'e']]⟩, ⟨[['w'], ['a', 'l', 'e']], [['C', 'L'], ['D', 'E', 'M', '.', 'D', 'I', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "localDP"), ("headATR", "minus"), ("demATR", "minus")] }

def ex49b : Datum :=
  { id := "sandeclemdabkowski2026_ex49b"
    source := ⟨"sande-clem-dabkowski-2026", "(49b)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-ëlé"
    glossedTokens := [("béy", "goat"), ("w-ëlé", "CL-DEM.DIST")]
    glossedWords := [⟨[['b', 'é', 'y']], [['g', 'o', 'a', 't']]⟩, ⟨[['w'], ['ë', 'l', 'é']], [['C', 'L'], ['D', 'E', 'M', '.', 'D', 'I', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "localDP"), ("headATR", "plus"), ("demATR", "plus")] }

def ex50a : Datum :=
  { id := "sandeclemdabkowski2026_ex50a"
    source := ⟨"sande-clem-dabkowski-2026", "(50a)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "xaj b-u weex b-ale"
    glossedTokens := [("xaj", "dog"), ("b-u", "CL-REL"), ("weex", "be.white"), ("b-ale", "CL-DEM.DIST")]
    glossedWords := [⟨[['x', 'a', 'j']], [['d', 'o', 'g']]⟩, ⟨[['b'], ['u']], [['C', 'L'], ['R', 'E', 'L']]⟩, ⟨[['w', 'e', 'e', 'x']], [['b', 'e', '.', 'w', 'h', 'i', 't', 'e']]⟩, ⟨[['b'], ['a', 'l', 'e']], [['C', 'L'], ['D', 'E', 'M', '.', 'D', 'I', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "minus"), ("stativeATR", "minus"), ("demATR", "minus")] }

def ex50b : Datum :=
  { id := "sandeclemdabkowski2026_ex50b"
    source := ⟨"sande-clem-dabkowski-2026", "(50b)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-u réy w-ëlé"
    glossedTokens := [("béy", "goat"), ("w-u", "CL-REL"), ("réy", "be.big"), ("w-ëlé", "CL-DEM.DIST")]
    glossedWords := [⟨[['b', 'é', 'y']], [['g', 'o', 'a', 't']]⟩, ⟨[['w'], ['u']], [['C', 'L'], ['R', 'E', 'L']]⟩, ⟨[['r', 'é', 'y']], [['b', 'e', '.', 'b', 'i', 'g']]⟩, ⟨[['w'], ['ë', 'l', 'é']], [['C', 'L'], ['D', 'E', 'M', '.', 'D', 'I', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "plus"), ("stativeATR", "plus"), ("demATR", "plus")] }

def ex50c : Datum :=
  { id := "sandeclemdabkowski2026_ex50c"
    source := ⟨"sande-clem-dabkowski-2026", "(50c)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "xaj b-u réy b-ale"
    glossedTokens := [("xaj", "dog"), ("b-u", "CL-REL"), ("réy", "be.big"), ("b-ale", "CL-DEM.DIST")]
    glossedWords := [⟨[['x', 'a', 'j']], [['d', 'o', 'g']]⟩, ⟨[['b'], ['u']], [['C', 'L'], ['R', 'E', 'L']]⟩, ⟨[['r', 'é', 'y']], [['b', 'e', '.', 'b', 'i', 'g']]⟩, ⟨[['b'], ['a', 'l', 'e']], [['C', 'L'], ['D', 'E', 'M', '.', 'D', 'I', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "minus"), ("stativeATR", "plus"), ("demATR", "minus")] }

def ex50d : Datum :=
  { id := "sandeclemdabkowski2026_ex50d"
    source := ⟨"sande-clem-dabkowski-2026", "(50d)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-u weex w-ëlé"
    glossedTokens := [("béy", "goat"), ("w-u", "CL-REL"), ("weex", "be.white"), ("w-ëlé", "CL-DEM.DIST")]
    glossedWords := [⟨[['b', 'é', 'y']], [['g', 'o', 'a', 't']]⟩, ⟨[['w'], ['u']], [['C', 'L'], ['R', 'E', 'L']]⟩, ⟨[['w', 'e', 'e', 'x']], [['b', 'e', '.', 'w', 'h', 'i', 't', 'e']]⟩, ⟨[['w'], ['ë', 'l', 'é']], [['C', 'L'], ['D', 'E', 'M', '.', 'D', 'I', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "plus"), ("stativeATR", "minus"), ("demATR", "plus")] }

def all : List Datum := [ex11a, ex11b, ex11c, ex12b, ex13b, ex21a, ex21b, ex21c, ex21d, ex21e, ex22, ex24b, ex41, ex49a, ex49b, ex50a, ex50b, ex50c, ex50d]

end SandeClemDabkowski2026.Examples
