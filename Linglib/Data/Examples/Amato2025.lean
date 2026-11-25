module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Amato2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Amato2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Amato2025.Examples`.
-/

@[expose] public section

namespace Amato2025.Examples

def ex_4a : Datum :=
  { id := "amato2025_4a"
    source := ⟨"amato-2025", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa ha lavato le camicie."
    glossedTokens := [("Teresa", "Teresa"), ("ha", "have.PRS.3SG"), ("lavato", "wash.PRTC"), ("le", "the"), ("camicie.", "shirts")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['l', 'a', 'v', 'a', 't', 'o'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], [⟨['l', 'a', 'v', 'a', 't', 'o'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'm', 'i', 'c', 'i', 'e', '.'], ['s', 'h', 'i', 'r', 't', 's'], [⟨['c', 'a', 'm', 'i', 'c', 'i', 'e'], ['s', 'h', 'i', 'r', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "lavare"⟩]
    paperFeatures := [("clause", "transitive")] }

def ex_4b : Datum :=
  { id := "amato2025_4b"
    source := ⟨"amato-2025", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa ha risposto a sua madre."
    glossedTokens := [("Teresa", "Teresa"), ("ha", "have.PRS.3SG"), ("risposto", "answer.PRTC"), ("a", "at"), ("sua", "her"), ("madre.", "mother")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['r', 'i', 's', 'p', 'o', 's', 't', 'o'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C'], [⟨['r', 'i', 's', 'p', 'o', 's', 't', 'o'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C'], none⟩]⟩, ⟨['a'], ['a', 't'], [⟨['a'], ['a', 't'], none⟩]⟩, ⟨['s', 'u', 'a'], ['h', 'e', 'r'], [⟨['s', 'u', 'a'], ['h', 'e', 'r'], none⟩]⟩, ⟨['m', 'a', 'd', 'r', 'e', '.'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'a', 'd', 'r', 'e'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩, ⟨2, 1, "participle", some "rispondere"⟩]
    paperFeatures := [("clause", "unergative")] }

def ex_4c : Datum :=
  { id := "amato2025_4c"
    source := ⟨"amato-2025", "(4c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa è venut-a alla festa."
    glossedTokens := [("Teresa", "Teresa"), ("è", "be.PRS.3SG"), ("venut-a", "come.PRTC-SG.F"), ("alla", "to.the"), ("festa.", "party")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['v', 'e', 'n', 'u', 't', '-', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['v', 'e', 'n', 'u', 't'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩, ⟨['a', 'l', 'l', 'a'], ['t', 'o', '.', 't', 'h', 'e'], [⟨['a', 'l', 'l', 'a'], ['t', 'o', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['f', 'e', 's', 't', 'a', '.'], ['p', 'a', 'r', 't', 'y'], [⟨['f', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "venire"⟩]
    paperFeatures := [("clause", "unaccusative")] }

def ex_5a : Datum :=
  { id := "amato2025_5a"
    source := ⟨"amato-2025", "(5a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa si=è lavat-a."
    glossedTokens := [("Teresa", "Teresa"), ("si=è", "REFL.ACC.3SG=be.PRS.3SG"), ("lavat-a.", "wash.PRTC-SG.F")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C', '.', '3', 'S', 'G', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C', '.', '3', 'S', 'G'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['l', 'a', 'v', 'a', 't', '-', 'a', '.'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['l', 'a', 'v', 'a', 't'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "lavare"⟩]
    paperFeatures := [("clause", "directReflexive")] }

def ex_5b : Datum :=
  { id := "amato2025_5b"
    source := ⟨"amato-2025", "(5b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa si=è lavat-a il vestito."
    glossedTokens := [("Teresa", "Teresa"), ("si=è", "REFL.DAT.3SG=be.PRS.3SG"), ("lavat-a", "wash.PRTC-SG.F"), ("il", "the"), ("vestito.", "dress")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['l', 'a', 'v', 'a', 't', '-', 'a'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['l', 'a', 'v', 'a', 't'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'e', 's', 't', 'i', 't', 'o', '.'], ['d', 'r', 'e', 's', 's'], [⟨['v', 'e', 's', 't', 'i', 't', 'o'], ['d', 'r', 'e', 's', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "lavare"⟩]
    paperFeatures := [("clause", "indirectReflexive")] }

def ex_5c : Datum :=
  { id := "amato2025_5c"
    source := ⟨"amato-2025", "(5c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa si=è rispost-a."
    glossedTokens := [("Teresa", "Teresa"), ("si=è", "REFL.DAT.3SG=be.PRS.3SG"), ("rispost-a.", "answer.PRTC-SG.F")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['r', 'i', 's', 'p', 'o', 's', 't', '-', 'a', '.'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['r', 'i', 's', 'p', 'o', 's', 't'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "rispondere"⟩]
    paperFeatures := [("clause", "indirectReflexive")] }

def ex_5d : Datum :=
  { id := "amato2025_5d"
    source := ⟨"amato-2025", "(5d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri si=è mangiato il gelato."
    glossedTokens := [("Ieri", "yesterday"), ("si=è", "IMPERS=be.PRS.3SG"), ("mangiato", "eat.PRTC"), ("il", "the"), ("gelato.", "ice_cream")]
    glossedWords := [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['I', 'M', 'P', 'E', 'R', 'S', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['I', 'M', 'P', 'E', 'R', 'S'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['m', 'a', 'n', 'g', 'i', 'a', 't', 'o'], ['e', 'a', 't', '.', 'P', 'R', 'T', 'C'], [⟨['m', 'a', 'n', 'g', 'i', 'a', 't', 'o'], ['e', 'a', 't', '.', 'P', 'R', 'T', 'C'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'e', 'l', 'a', 't', 'o', '.'], ['i', 'c', 'e', '_', 'c', 'r', 'e', 'a', 'm'], [⟨['g', 'e', 'l', 'a', 't', 'o'], ['i', 'c', 'e', '_', 'c', 'r', 'e', 'a', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩, ⟨2, 1, "participle", some "mangiare"⟩]
    paperFeatures := [("clause", "impersonal")] }

def ex_29a_pl : Datum :=
  { id := "amato2025_29a_pl"
    source := ⟨"ussery-2009", "(4)"⟩
    reportedIn := some ⟨"amato-2025", "(29a)"⟩
    language := "icel1247"
    primaryText := "Það líka sumum stelpunum peningarnir."
    glossedTokens := [("Það", "expl"), ("líka", "like.3pl"), ("sumum", "some"), ("stelpunum", "girls.Dat"), ("peningarnir.", "money-the.Nom.pl")]
    glossedWords := [⟨['Þ', 'a', 'ð'], ['e', 'x', 'p', 'l'], [⟨['Þ', 'a', 'ð'], ['e', 'x', 'p', 'l'], none⟩]⟩, ⟨['l', 'í', 'k', 'a'], ['l', 'i', 'k', 'e', '.', '3', 'p', 'l'], [⟨['l', 'í', 'k', 'a'], ['l', 'i', 'k', 'e', '.', '3', 'p', 'l'], none⟩]⟩, ⟨['s', 'u', 'm', 'u', 'm'], ['s', 'o', 'm', 'e'], [⟨['s', 'u', 'm', 'u', 'm'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['s', 't', 'e', 'l', 'p', 'u', 'n', 'u', 'm'], ['g', 'i', 'r', 'l', 's', '.', 'D', 'a', 't'], [⟨['s', 't', 'e', 'l', 'p', 'u', 'n', 'u', 'm'], ['g', 'i', 'r', 'l', 's', '.', 'D', 'a', 't'], none⟩]⟩, ⟨['p', 'e', 'n', 'i', 'n', 'g', 'a', 'r', 'n', 'i', 'r', '.'], ['m', 'o', 'n', 'e', 'y', '-', 't', 'h', 'e', '.', 'N', 'o', 'm', '.', 'p', 'l'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "monoclausal"), ("agreement", "number")] }

def ex_29a_sg : Datum :=
  { id := "amato2025_29a_sg"
    source := ⟨"ussery-2009", "(4)"⟩
    reportedIn := some ⟨"amato-2025", "(29a)"⟩
    language := "icel1247"
    primaryText := "Það líkar sumum stelpunum peningarnir."
    glossedTokens := [("Það", "expl"), ("líkar", "like.3sg"), ("sumum", "some"), ("stelpunum", "girls.Dat"), ("peningarnir.", "money-the.Nom.pl")]
    glossedWords := [⟨['Þ', 'a', 'ð'], ['e', 'x', 'p', 'l'], [⟨['Þ', 'a', 'ð'], ['e', 'x', 'p', 'l'], none⟩]⟩, ⟨['l', 'í', 'k', 'a', 'r'], ['l', 'i', 'k', 'e', '.', '3', 's', 'g'], [⟨['l', 'í', 'k', 'a', 'r'], ['l', 'i', 'k', 'e', '.', '3', 's', 'g'], none⟩]⟩, ⟨['s', 'u', 'm', 'u', 'm'], ['s', 'o', 'm', 'e'], [⟨['s', 'u', 'm', 'u', 'm'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['s', 't', 'e', 'l', 'p', 'u', 'n', 'u', 'm'], ['g', 'i', 'r', 'l', 's', '.', 'D', 'a', 't'], [⟨['s', 't', 'e', 'l', 'p', 'u', 'n', 'u', 'm'], ['g', 'i', 'r', 'l', 's', '.', 'D', 'a', 't'], none⟩]⟩, ⟨['p', 'e', 'n', 'i', 'n', 'g', 'a', 'r', 'n', 'i', 'r', '.'], ['m', 'o', 'n', 'e', 'y', '-', 't', 'h', 'e', '.', 'N', 'o', 'm', '.', 'p', 'l'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "monoclausal"), ("agreement", "default")] }

def ex_29b_sg : Datum :=
  { id := "amato2025_29b_sg"
    source := ⟨"holmberg-hroarsdottir-2003", "(12a)"⟩
    reportedIn := some ⟨"amato-2025", "(29b)"⟩
    method := some .elicitation
    language := "icel1247"
    primaryText := "Það virðist einhverjum manni hestarnir vera seinir"
    glossedTokens := [("Það", "EXPL"), ("virðist", "seemSG"), ("einhverjum", "some"), ("manni", "manDAT"), ("hestarnir", "the_horsesNOM"), ("vera", "be"), ("seinir", "slowNOM")]
    glossedWords := [⟨['Þ', 'a', 'ð'], ['E', 'X', 'P', 'L'], [⟨['Þ', 'a', 'ð'], ['E', 'X', 'P', 'L'], none⟩]⟩, ⟨['v', 'i', 'r', 'ð', 'i', 's', 't'], ['s', 'e', 'e', 'm', 'S', 'G'], [⟨['v', 'i', 'r', 'ð', 'i', 's', 't'], ['s', 'e', 'e', 'm', 'S', 'G'], none⟩]⟩, ⟨['e', 'i', 'n', 'h', 'v', 'e', 'r', 'j', 'u', 'm'], ['s', 'o', 'm', 'e'], [⟨['e', 'i', 'n', 'h', 'v', 'e', 'r', 'j', 'u', 'm'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['m', 'a', 'n', 'n', 'i'], ['m', 'a', 'n', 'D', 'A', 'T'], [⟨['m', 'a', 'n', 'n', 'i'], ['m', 'a', 'n', 'D', 'A', 'T'], none⟩]⟩, ⟨['h', 'e', 's', 't', 'a', 'r', 'n', 'i', 'r'], ['t', 'h', 'e', '_', 'h', 'o', 'r', 's', 'e', 's', 'N', 'O', 'M'], [⟨['h', 'e', 's', 't', 'a', 'r', 'n', 'i', 'r'], ['t', 'h', 'e', '_', 'h', 'o', 'r', 's', 'e', 's', 'N', 'O', 'M'], none⟩]⟩, ⟨['v', 'e', 'r', 'a'], ['b', 'e'], [⟨['v', 'e', 'r', 'a'], ['b', 'e'], none⟩]⟩, ⟨['s', 'e', 'i', 'n', 'i', 'r'], ['s', 'l', 'o', 'w', 'N', 'O', 'M'], [⟨['s', 'e', 'i', 'n', 'i', 'r'], ['s', 'l', 'o', 'w', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "biclausal"), ("agreement", "default")] }

def ex_29b_pl : Datum :=
  { id := "amato2025_29b_pl"
    source := ⟨"holmberg-hroarsdottir-2003", "(12b)"⟩
    reportedIn := some ⟨"amato-2025", "(29b)"⟩
    method := some .elicitation
    language := "icel1247"
    primaryText := "Það virðast einhverjum manni hestarnir vera seinir"
    glossedTokens := [("Það", "EXPL"), ("virðast", "seemPL"), ("einhverjum", "some"), ("manni", "manDAT"), ("hestarnir", "the_horsesNOM"), ("vera", "be"), ("seinir", "slowNOM")]
    glossedWords := [⟨['Þ', 'a', 'ð'], ['E', 'X', 'P', 'L'], [⟨['Þ', 'a', 'ð'], ['E', 'X', 'P', 'L'], none⟩]⟩, ⟨['v', 'i', 'r', 'ð', 'a', 's', 't'], ['s', 'e', 'e', 'm', 'P', 'L'], [⟨['v', 'i', 'r', 'ð', 'a', 's', 't'], ['s', 'e', 'e', 'm', 'P', 'L'], none⟩]⟩, ⟨['e', 'i', 'n', 'h', 'v', 'e', 'r', 'j', 'u', 'm'], ['s', 'o', 'm', 'e'], [⟨['e', 'i', 'n', 'h', 'v', 'e', 'r', 'j', 'u', 'm'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['m', 'a', 'n', 'n', 'i'], ['m', 'a', 'n', 'D', 'A', 'T'], [⟨['m', 'a', 'n', 'n', 'i'], ['m', 'a', 'n', 'D', 'A', 'T'], none⟩]⟩, ⟨['h', 'e', 's', 't', 'a', 'r', 'n', 'i', 'r'], ['t', 'h', 'e', '_', 'h', 'o', 'r', 's', 'e', 's', 'N', 'O', 'M'], [⟨['h', 'e', 's', 't', 'a', 'r', 'n', 'i', 'r'], ['t', 'h', 'e', '_', 'h', 'o', 'r', 's', 'e', 's', 'N', 'O', 'M'], none⟩]⟩, ⟨['v', 'e', 'r', 'a'], ['b', 'e'], [⟨['v', 'e', 'r', 'a'], ['b', 'e'], none⟩]⟩, ⟨['s', 'e', 'i', 'n', 'i', 'r'], ['s', 'l', 'o', 'w', 'N', 'O', 'M'], [⟨['s', 'e', 'i', 'n', 'i', 'r'], ['s', 'l', 'o', 'w', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "biclausal"), ("agreement", "number")] }

def ex_35 : Datum :=
  { id := "amato2025_35"
    source := ⟨"rudin-1988", "(5a)"⟩
    reportedIn := some ⟨"amato-2025", "(35)"⟩
    language := "bulg1262"
    primaryText := "Koj kogo vižda?"
    glossedTokens := [("Koj", "who"), ("kogo", "whom"), ("vižda?", "sees")]
    glossedWords := [⟨['K', 'o', 'j'], ['w', 'h', 'o'], [⟨['K', 'o', 'j'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', 'o', 'g', 'o'], ['w', 'h', 'o', 'm'], [⟨['k', 'o', 'g', 'o'], ['w', 'h', 'o', 'm'], none⟩]⟩, ⟨['v', 'i', 'ž', 'd', 'a', '?'], ['s', 'e', 'e', 's'], [⟨['v', 'i', 'ž', 'd', 'a'], ['s', 'e', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨0, 1, "wh", some "koj"⟩, ⟨1, 1, "wh", some "kogo"⟩]
    paperFeatures := [] }

def ex_35_reverse : Datum :=
  { id := "amato2025_35_reverse"
    source := ⟨"rudin-1988", "(54b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Kogo koj vižda?"
    glossedTokens := [("Kogo", "whom"), ("koj", "who"), ("vižda?", "sees")]
    glossedWords := [⟨['K', 'o', 'g', 'o'], ['w', 'h', 'o', 'm'], [⟨['K', 'o', 'g', 'o'], ['w', 'h', 'o', 'm'], none⟩]⟩, ⟨['k', 'o', 'j'], ['w', 'h', 'o'], [⟨['k', 'o', 'j'], ['w', 'h', 'o'], none⟩]⟩, ⟨['v', 'i', 'ž', 'd', 'a', '?'], ['s', 'e', 'e', 's'], [⟨['v', 'i', 'ž', 'd', 'a'], ['s', 'e', 'e', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    spans := [⟨0, 1, "wh", some "kogo"⟩, ⟨1, 1, "wh", some "koj"⟩]
    paperFeatures := [] }

def ex_37 : Datum :=
  { id := "amato2025_37"
    source := ⟨"mahajan-1990", "(5)"⟩
    reportedIn := some ⟨"amato-2025", "(37)"⟩
    language := "hind1269"
    primaryText := "raam-ne roTii khaayii thii"
    glossedTokens := [("raam-ne", "Ram(m.)-erg."), ("roTii", "bread(f.)"), ("khaayii", "eat(perf.f.)"), ("thii", "be(pst.f.)")]
    glossedWords := [⟨['r', 'a', 'a', 'm', '-', 'n', 'e'], ['R', 'a', 'm', '(', 'm', '.', ')', '-', 'e', 'r', 'g', '.'], [⟨['r', 'a', 'a', 'm'], ['R', 'a', 'm', '(', 'm', '.', ')'], none⟩, ⟨['n', 'e'], ['e', 'r', 'g', '.'], some '-'⟩]⟩, ⟨['r', 'o', 'T', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '(', 'f', '.', ')'], [⟨['r', 'o', 'T', 'i', 'i'], ['b', 'r', 'e', 'a', 'd', '(', 'f', '.', ')'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', 'y', 'i', 'i'], ['e', 'a', 't', '(', 'p', 'e', 'r', 'f', '.', 'f', '.', ')'], [⟨['k', 'h', 'a', 'a', 'y', 'i', 'i'], ['e', 'a', 't', '(', 'p', 'e', 'r', 'f', '.', 'f', '.', ')'], none⟩]⟩, ⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 's', 't', '.', 'f', '.', ')'], [⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 's', 't', '.', 'f', '.', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("marking", "ergSubject"), ("controller", "object")] }

def ex_38a : Datum :=
  { id := "amato2025_38a"
    source := ⟨"mahajan-1990", "(6)"⟩
    reportedIn := some ⟨"amato-2025", "(38a)"⟩
    language := "hind1269"
    primaryText := "baccoN-ne siitaa-ko dekhaa thaa"
    glossedTokens := [("baccoN-ne", "children(m.)-erg."), ("siitaa-ko", "Sita(f.)-dat."), ("dekhaa", "see(perf.m.sg.)"), ("thaa", "be(pst.m.sg.)")]
    glossedWords := [⟨['b', 'a', 'c', 'c', 'o', 'N', '-', 'n', 'e'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '(', 'm', '.', ')', '-', 'e', 'r', 'g', '.'], [⟨['b', 'a', 'c', 'c', 'o', 'N'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '(', 'm', '.', ')'], none⟩, ⟨['n', 'e'], ['e', 'r', 'g', '.'], some '-'⟩]⟩, ⟨['s', 'i', 'i', 't', 'a', 'a', '-', 'k', 'o'], ['S', 'i', 't', 'a', '(', 'f', '.', ')', '-', 'd', 'a', 't', '.'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a', '(', 'f', '.', ')'], none⟩, ⟨['k', 'o'], ['d', 'a', 't', '.'], some '-'⟩]⟩, ⟨['d', 'e', 'k', 'h', 'a', 'a'], ['s', 'e', 'e', '(', 'p', 'e', 'r', 'f', '.', 'm', '.', 's', 'g', '.', ')'], [⟨['d', 'e', 'k', 'h', 'a', 'a'], ['s', 'e', 'e', '(', 'p', 'e', 'r', 'f', '.', 'm', '.', 's', 'g', '.', ')'], none⟩]⟩, ⟨['t', 'h', 'a', 'a'], ['b', 'e', '(', 'p', 's', 't', '.', 'm', '.', 's', 'g', '.', ')'], [⟨['t', 'h', 'a', 'a'], ['b', 'e', '(', 'p', 's', 't', '.', 'm', '.', 's', 'g', '.', ')'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("marking", "bothMarked"), ("controller", "default")] }

def ex_38b : Datum :=
  { id := "amato2025_38b"
    source := ⟨"mahajan-1990", "(4)"⟩
    reportedIn := some ⟨"amato-2025", "(38b)"⟩
    language := "hind1269"
    primaryText := "siitaa kelaa khaatii thii"
    glossedTokens := [("siitaa", "Sita(f.)"), ("kelaa", "banana(m.)"), ("khaatii", "eat(imp.f.)"), ("thii", "be(pst.f.)")]
    glossedWords := [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a', '(', 'f', '.', ')'], [⟨['s', 'i', 'i', 't', 'a', 'a'], ['S', 'i', 't', 'a', '(', 'f', '.', ')'], none⟩]⟩, ⟨['k', 'e', 'l', 'a', 'a'], ['b', 'a', 'n', 'a', 'n', 'a', '(', 'm', '.', ')'], [⟨['k', 'e', 'l', 'a', 'a'], ['b', 'a', 'n', 'a', 'n', 'a', '(', 'm', '.', ')'], none⟩]⟩, ⟨['k', 'h', 'a', 'a', 't', 'i', 'i'], ['e', 'a', 't', '(', 'i', 'm', 'p', '.', 'f', '.', ')'], [⟨['k', 'h', 'a', 'a', 't', 'i', 'i'], ['e', 'a', 't', '(', 'i', 'm', 'p', '.', 'f', '.', ')'], none⟩]⟩, ⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 's', 't', '.', 'f', '.', ')'], [⟨['t', 'h', 'i', 'i'], ['b', 'e', '(', 'p', 's', 't', '.', 'f', '.', ')'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("marking", "unmarkedSubject"), ("controller", "subject")] }

def all : List Datum := [ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_5c, ex_5d, ex_29a_pl, ex_29a_sg, ex_29b_sg, ex_29b_pl, ex_35, ex_35_reverse, ex_37, ex_38a, ex_38b]

/-- The clause types whose perfect auxiliary the paper compares (§3.1). -/
inductive Clause where
  /-- transitive: a transitive verb with canonical arguments -/
  | transitive
  /-- unergative: an unergative verb -/
  | unergative
  /-- unaccusative: an unaccusative verb -/
  | unaccusative
  /-- directReflexive: a reflexive clitic as the direct object -/
  | directReflexive
  /-- indirectReflexive: a reflexive clitic as the indirect object -/
  | indirectReflexive
  /-- impersonal: the impersonal pronoun si -/
  | impersonal
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option Clause :=
  e.parse? "clause" [("transitive", .transitive), ("unergative", .unergative), ("unaccusative", .unaccusative),
    ("directReflexive", .directReflexive), ("indirectReflexive", .indirectReflexive),
    ("impersonal", .impersonal)]

/-- The Icelandic DAT-NOM constructions the paper compares (§4.1.2). -/
inductive Construction where
  /-- monoclausal: the dative and the nominative are arguments of one clause -/
  | monoclausal
  /-- biclausal: the nominative is the subject of an embedded non-finite clause -/
  | biclausal
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `construction`. -/
def construction (e : Datum) : Option Construction :=
  e.parse? "construction" [("monoclausal", .monoclausal), ("biclausal", .biclausal)]

/-- The form of the finite verb. -/
inductive Agreement where
  /-- number: the verb agrees in number with the plural nominative -/
  | number
  /-- default: the verb is in the default third person singular -/
  | default
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `agreement`. -/
def agreement (e : Datum) : Option Agreement :=
  e.parse? "agreement" [("number", .number), ("default", .default)]

/-- The case marking of the arguments of the Hindi-Urdu clauses (§4.3.1). -/
inductive Marking where
  /-- ergSubject: the subject is ergative and the object unmarked -/
  | ergSubject
  /-- bothMarked: the subject is ergative and the object bears ko -/
  | bothMarked
  /-- unmarkedSubject: the subject is unmarked -/
  | unmarkedSubject
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `marking`. -/
def marking (e : Datum) : Option Marking :=
  e.parse? "marking" [("ergSubject", .ergSubject), ("bothMarked", .bothMarked),
    ("unmarkedSubject", .unmarkedSubject)]

/-- The argument whose features the form of the verb shows. -/
inductive Controller where
  /-- subject: the subject -/
  | subject
  /-- object: the object -/
  | object
  /-- default: neither: the verb is in its default form -/
  | default
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `controller`. -/
def controller (e : Datum) : Option Controller :=
  e.parse? "controller" [("subject", .subject), ("object", .object), ("default", .default)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- auxiliary: the word holding the perfect auxiliary -/
  | auxiliary
  /-- wh: a fronted wh-phrase -/
  | wh
  /-- participle: the past participle of the verb -/
  | participle
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("auxiliary", .auxiliary), ("wh", .wh), ("participle", .participle)]

/-- The perfect auxiliaries, the verbs of the Italian examples and the wh-words. -/
inductive Lexeme where
  /-- avere: avere 'have' -/
  | avere
  /-- essere: essere 'be' -/
  | essere
  /-- koj: Bulgarian koj 'who', nominative -/
  | koj
  /-- kogo: Bulgarian kogo 'whom', accusative -/
  | kogo
  /-- lavare: lavare 'wash' -/
  | lavare
  /-- rispondere: rispondere 'answer' -/
  | rispondere
  /-- venire: venire 'come' -/
  | venire
  /-- mangiare: mangiare 'eat' -/
  | mangiare
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("avere", .avere), ("essere", .essere), ("koj", .koj), ("kogo", .kogo), ("lavare", .lavare), ("rispondere", .rispondere), ("venire", .venire), ("mangiare", .mangiare)])

/-- The examples of the file. -/
inductive Example where
  | ex_4a
  | ex_4b
  | ex_4c
  | ex_5a
  | ex_5b
  | ex_5c
  | ex_5d
  | ex_29a_pl
  | ex_29a_sg
  | ex_29b_sg
  | ex_29b_pl
  | ex_35
  | ex_35_reverse
  | ex_37
  | ex_38a
  | ex_38b
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_4a, .ex_4b, .ex_4c, .ex_5a, .ex_5b, .ex_5c, .ex_5d, .ex_29a_pl, .ex_29a_sg, .ex_29b_sg,
    .ex_29b_pl, .ex_35, .ex_35_reverse, .ex_37, .ex_38a, .ex_38b]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_4a => _root_.Amato2025.Examples.ex_4a
  | .ex_4b => _root_.Amato2025.Examples.ex_4b
  | .ex_4c => _root_.Amato2025.Examples.ex_4c
  | .ex_5a => _root_.Amato2025.Examples.ex_5a
  | .ex_5b => _root_.Amato2025.Examples.ex_5b
  | .ex_5c => _root_.Amato2025.Examples.ex_5c
  | .ex_5d => _root_.Amato2025.Examples.ex_5d
  | .ex_29a_pl => _root_.Amato2025.Examples.ex_29a_pl
  | .ex_29a_sg => _root_.Amato2025.Examples.ex_29a_sg
  | .ex_29b_sg => _root_.Amato2025.Examples.ex_29b_sg
  | .ex_29b_pl => _root_.Amato2025.Examples.ex_29b_pl
  | .ex_35 => _root_.Amato2025.Examples.ex_35
  | .ex_35_reverse => _root_.Amato2025.Examples.ex_35_reverse
  | .ex_37 => _root_.Amato2025.Examples.ex_37
  | .ex_38a => _root_.Amato2025.Examples.ex_38a
  | .ex_38b => _root_.Amato2025.Examples.ex_38b

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Amato2025.Examples.all := rfl

/-- The value the example records under `clause`. -/
def Example.clause : Example → Option Clause
  | .ex_4a => some .transitive
  | .ex_4b => some .unergative
  | .ex_4c => some .unaccusative
  | .ex_5a => some .directReflexive
  | .ex_5b => some .indirectReflexive
  | .ex_5c => some .indirectReflexive
  | .ex_5d => some .impersonal
  | .ex_29a_pl => none
  | .ex_29a_sg => none
  | .ex_29b_sg => none
  | .ex_29b_pl => none
  | .ex_35 => none
  | .ex_35_reverse => none
  | .ex_37 => none
  | .ex_38a => none
  | .ex_38b => none

theorem Example.clause_datum :
    ∀ x : Example, _root_.Amato2025.Examples.clause x.datum = x.clause := by
  decide +kernel

/-- The value the example records under `construction`. -/
def Example.construction : Example → Option Construction
  | .ex_4a => none
  | .ex_4b => none
  | .ex_4c => none
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_5d => none
  | .ex_29a_pl => some .monoclausal
  | .ex_29a_sg => some .monoclausal
  | .ex_29b_sg => some .biclausal
  | .ex_29b_pl => some .biclausal
  | .ex_35 => none
  | .ex_35_reverse => none
  | .ex_37 => none
  | .ex_38a => none
  | .ex_38b => none

theorem Example.construction_datum :
    ∀ x : Example, _root_.Amato2025.Examples.construction x.datum = x.construction := by
  decide +kernel

/-- The value the example records under `agreement`. -/
def Example.agreement : Example → Option Agreement
  | .ex_4a => none
  | .ex_4b => none
  | .ex_4c => none
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_5d => none
  | .ex_29a_pl => some .number
  | .ex_29a_sg => some .default
  | .ex_29b_sg => some .default
  | .ex_29b_pl => some .number
  | .ex_35 => none
  | .ex_35_reverse => none
  | .ex_37 => none
  | .ex_38a => none
  | .ex_38b => none

theorem Example.agreement_datum :
    ∀ x : Example, _root_.Amato2025.Examples.agreement x.datum = x.agreement := by
  decide +kernel

/-- The value the example records under `marking`. -/
def Example.marking : Example → Option Marking
  | .ex_4a => none
  | .ex_4b => none
  | .ex_4c => none
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_5d => none
  | .ex_29a_pl => none
  | .ex_29a_sg => none
  | .ex_29b_sg => none
  | .ex_29b_pl => none
  | .ex_35 => none
  | .ex_35_reverse => none
  | .ex_37 => some .ergSubject
  | .ex_38a => some .bothMarked
  | .ex_38b => some .unmarkedSubject

theorem Example.marking_datum :
    ∀ x : Example, _root_.Amato2025.Examples.marking x.datum = x.marking := by
  decide +kernel

/-- The value the example records under `controller`. -/
def Example.controller : Example → Option Controller
  | .ex_4a => none
  | .ex_4b => none
  | .ex_4c => none
  | .ex_5a => none
  | .ex_5b => none
  | .ex_5c => none
  | .ex_5d => none
  | .ex_29a_pl => none
  | .ex_29a_sg => none
  | .ex_29b_sg => none
  | .ex_29b_pl => none
  | .ex_35 => none
  | .ex_35_reverse => none
  | .ex_37 => some .object
  | .ex_38a => some .default
  | .ex_38b => some .subject

theorem Example.controller_datum :
    ∀ x : Example, _root_.Amato2025.Examples.controller x.datum = x.controller := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_4a => [(.auxiliary, .avere), (.participle, .lavare)]
  | .ex_4b => [(.auxiliary, .avere), (.participle, .rispondere)]
  | .ex_4c => [(.auxiliary, .essere), (.participle, .venire)]
  | .ex_5a => [(.auxiliary, .essere), (.participle, .lavare)]
  | .ex_5b => [(.auxiliary, .essere), (.participle, .lavare)]
  | .ex_5c => [(.auxiliary, .essere), (.participle, .rispondere)]
  | .ex_5d => [(.auxiliary, .essere), (.participle, .mangiare)]
  | .ex_29a_pl => []
  | .ex_29a_sg => []
  | .ex_29b_sg => []
  | .ex_29b_pl => []
  | .ex_35 => [(.wh, .koj), (.wh, .kogo)]
  | .ex_35_reverse => [(.wh, .kogo), (.wh, .koj)]
  | .ex_37 => []
  | .ex_38a => []
  | .ex_38b => []

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.Amato2025.Examples.label? · = some l)).filterMap _root_.Amato2025.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end Amato2025.Examples
