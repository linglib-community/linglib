module

public import Linglib.Data.Examples.Schema

/-!
# `Embick2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Embick2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Embick2010.Examples`.
-/

@[expose] public section

namespace Embick2010.Examples

def amavi : Datum :=
  { id := "embick2010_amavi"
    source := ⟨"embick-2010", "ch. 3, (3), (10a)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-v-ī"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", ""), ("h5", "agr"), ("h5exp", "-ī"), ("target", "5"), ("conditioner", "3"), ("claim", "attested")] }

def amavisti : Datum :=
  { id := "embick2010_amavisti"
    source := ⟨"embick-2010", "ch. 3, (3)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-v-istī"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", ""), ("h5", "agr"), ("h5exp", "-istī"), ("target", "5"), ("conditioner", "3"), ("claim", "attested")] }

def amaveram : Datum :=
  { id := "embick2010_amaveram"
    source := ⟨"embick-2010", "ch. 3, (3), (10b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-ve-ra-m"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", "-sā"), ("h5", "agr"), ("h5exp", "-m"), ("target", "5"), ("conditioner", "3"), ("claim", "blocked")] }

def amaverim : Datum :=
  { id := "embick2010_amaverim"
    source := ⟨"embick-2010", "ch. 3, (3)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-ve-ri-m"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", "-sī"), ("h5", "agr"), ("h5exp", "-m"), ("target", "5"), ("conditioner", "3"), ("claim", "blocked")] }

def amavero : Datum :=
  { id := "embick2010_amavero"
    source := ⟨"embick-2010", "ch. 3, (3)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-ve-r-ō"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", "-si"), ("h5", "agr"), ("h5exp", "-ō"), ("target", "5"), ("conditioner", "3"), ("claim", "blocked")] }

def capimus : Datum :=
  { id := "embick2010_capimus"
    source := ⟨"embick-2010", "ch. 3, (12), (17)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "cap-i-mus"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "CAP"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-i"), ("target", "2"), ("conditioner", "root"), ("claim", "attested")] }

def capessimus_root : Datum :=
  { id := "embick2010_capessimus_root"
    source := ⟨"embick-2010", "ch. 3, (16), (18)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "cap-ess-i-mus"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "CAP"), ("h1", "v"), ("h1exp", "-ess"), ("h2", "theme"), ("h2exp", "-i"), ("target", "2"), ("conditioner", "root"), ("claim", "blocked")] }

def capessimus_v : Datum :=
  { id := "embick2010_capessimus_v"
    source := ⟨"embick-2010", "ch. 3, (16), (18)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "cap-ess-i-mus"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "CAP"), ("h1", "v"), ("h1exp", "-ess"), ("h2", "theme"), ("h2exp", "-i"), ("target", "2"), ("conditioner", "1"), ("claim", "attested")] }

def marriage : Datum :=
  { id := "embick2010_marriage"
    source := ⟨"embick-2010", "ch. 2, (31), (46)–(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "marri-age"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "MARRY"), ("h1", "n"), ("h1exp", "-age"), ("target", "1"), ("conditioner", "root"), ("claim", "attested")] }

def marrying : Datum :=
  { id := "embick2010_marrying"
    source := ⟨"embick-2010", "ch. 2, (31), (48)–(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "marry-ing"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "MARRY"), ("h1", "v"), ("h1exp", ""), ("h2", "n"), ("h2exp", "-ing"), ("target", "2"), ("conditioner", "root"), ("claim", "blocked")] }

def bent : Datum :=
  { id := "embick2010_bent"
    source := ⟨"embick-2010", "ch. 2, (34), (54)–(56)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "ben-t"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "BEND"), ("h1", "v"), ("h1exp", ""), ("h2", "tense"), ("h2exp", "-t"), ("target", "2"), ("conditioner", "root"), ("claim", "attested")] }

def breakability : Datum :=
  { id := "embick2010_breakability"
    source := ⟨"embick-2010", "ch. 2, (36)–(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "break-abil-ity"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "BREAK"), ("h1", "a"), ("h1exp", "-able"), ("h2", "n"), ("h2exp", "-ity"), ("target", "2"), ("conditioner", "1"), ("claim", "attested")] }

def colorization_v : Datum :=
  { id := "embick2010_colorization_v"
    source := ⟨"embick-2010", "ch. 3, (49)–(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "color-iz-ation"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "COLOR"), ("h1", "v"), ("h1exp", "-ize"), ("h2", "n"), ("h2exp", "-ation"), ("target", "2"), ("conditioner", "1"), ("claim", "attested")] }

def colorization_root : Datum :=
  { id := "embick2010_colorization_root"
    source := ⟨"embick-2010", "ch. 3, (49)–(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "color-iz-ation"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "COLOR"), ("h1", "v"), ("h1exp", "-ize"), ("h2", "n"), ("h2exp", "-ation"), ("target", "2"), ("conditioner", "root"), ("claim", "blocked")] }

def bachaanaa : Datum :=
  { id := "embick2010_bachaanaa"
    source := ⟨"embick-2010", "ch. 3, (22b), (23), (27)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "bach-aa-naa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "BACH"), ("h1", "v"), ("h1exp", ""), ("h2", "voice"), ("h2exp", "-aa"), ("target", "2"), ("conditioner", "root"), ("claim", "attested")] }

def bachvaanaa : Datum :=
  { id := "embick2010_bachvaanaa"
    source := ⟨"embick-2010", "ch. 3, (25b), (26)–(27)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "bach-vaa-naa"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("root", "BACH"), ("h1", "v"), ("h1exp", ""), ("h2", "voicePassive"), ("h2exp", "-v"), ("h3", "v"), ("h3exp", ""), ("h4", "voice"), ("h4exp", "-aa"), ("target", "4"), ("conditioner", "root"), ("claim", "blocked")] }

def all : List Datum := [amavi, amavisti, amaveram, amaverim, amavero, capimus, capessimus_root, capessimus_v, marriage, marrying, bent, breakability, colorization_v, colorization_root, bachaanaa, bachvaanaa]

end Embick2010.Examples
