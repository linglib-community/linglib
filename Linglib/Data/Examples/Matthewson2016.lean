module

public import Linglib.Data.Examples.Schema

/-!
# `Matthewson2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Matthewson2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Matthewson2016.Examples`.
-/

@[expose] public section

namespace Matthewson2016.Examples

def ex25 : Datum :=
  { id := "matthewson2016_ex25"
    source := ⟨"matthewson-2016", "(25)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "wá7=k'a ku=mám'teq láku7 áltsq7=a, t'u7 nílh=a cwílh=t'u7 ti=sk'éxem=a wa7 qan'ím-ens-an"
    glossedTokens := [("wá7=k'a", "be=INFER"), ("ku=mám'teq", "DET=walk"), ("láku7", "DEIC"), ("áltsq7=a", "outside=EXIS"), ("t'u7", "but"), ("nílh=a", "FOC=a"), ("cwílh=t'u7", "after.all=just"), ("ti=sk'éxem=a", "DET=wind=EXIS"), ("wa7", "IPFV"), ("qan'ím-ens-an", "hear-DIR-1SG.ERG")]
    glossedWords := [⟨['w', 'á', '7', '=', 'k', '\'', 'a'], ['b', 'e', '=', 'I', 'N', 'F', 'E', 'R'], [⟨['w', 'á', '7'], ['b', 'e'], none⟩, ⟨['k', '\'', 'a'], ['I', 'N', 'F', 'E', 'R'], some '='⟩]⟩, ⟨['k', 'u', '=', 'm', 'á', 'm', '\'', 't', 'e', 'q'], ['D', 'E', 'T', '=', 'w', 'a', 'l', 'k'], [⟨['k', 'u'], ['D', 'E', 'T'], none⟩, ⟨['m', 'á', 'm', '\'', 't', 'e', 'q'], ['w', 'a', 'l', 'k'], some '='⟩]⟩, ⟨['l', 'á', 'k', 'u', '7'], ['D', 'E', 'I', 'C'], [⟨['l', 'á', 'k', 'u', '7'], ['D', 'E', 'I', 'C'], none⟩]⟩, ⟨['á', 'l', 't', 's', 'q', '7', '=', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e', '=', 'E', 'X', 'I', 'S'], [⟨['á', 'l', 't', 's', 'q', '7'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩, ⟨['a'], ['E', 'X', 'I', 'S'], some '='⟩]⟩, ⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], [⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'í', 'l', 'h', '=', 'a'], ['F', 'O', 'C', '=', 'a'], [⟨['n', 'í', 'l', 'h'], ['F', 'O', 'C'], none⟩, ⟨['a'], ['a'], some '='⟩]⟩, ⟨['c', 'w', 'í', 'l', 'h', '=', 't', '\'', 'u', '7'], ['a', 'f', 't', 'e', 'r', '.', 'a', 'l', 'l', '=', 'j', 'u', 's', 't'], [⟨['c', 'w', 'í', 'l', 'h'], ['a', 'f', 't', 'e', 'r', '.', 'a', 'l', 'l'], none⟩, ⟨['t', '\'', 'u', '7'], ['j', 'u', 's', 't'], some '='⟩]⟩, ⟨['t', 'i', '=', 's', 'k', '\'', 'é', 'x', 'e', 'm', '=', 'a'], ['D', 'E', 'T', '=', 'w', 'i', 'n', 'd', '=', 'E', 'X', 'I', 'S'], [⟨['t', 'i'], ['D', 'E', 'T'], none⟩, ⟨['s', 'k', '\'', 'é', 'x', 'e', 'm'], ['w', 'i', 'n', 'd'], some '='⟩, ⟨['a'], ['E', 'X', 'I', 'S'], some '='⟩]⟩, ⟨['w', 'a', '7'], ['I', 'P', 'F', 'V'], [⟨['w', 'a', '7'], ['I', 'P', 'F', 'V'], none⟩]⟩, ⟨['q', 'a', 'n', '\'', 'í', 'm', '-', 'e', 'n', 's', '-', 'a', 'n'], ['h', 'e', 'a', 'r', '-', 'D', 'I', 'R', '-', '1', 'S', 'G', '.', 'E', 'R', 'G'], [⟨['q', 'a', 'n', '\'', 'í', 'm'], ['h', 'e', 'a', 'r'], none⟩, ⟨['e', 'n', 's'], ['D', 'I', 'R'], some '-'⟩, ⟨['a', 'n'], ['1', 'S', 'G', '.', 'E', 'R', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "k'a"), ("test", "deniability")] }

def ex26 : Datum :=
  { id := "matthewson2016_ex26"
    source := ⟨"matthewson-2016", "(26)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "wa7 lákw7a ku=mám'teq láku7 áltsq7=a, t'u7 nílh=a cwílh=t'u7 ti=sk'éxem=a wa7 qan'ím-ens-an"
    glossedTokens := [("wa7", "be"), ("lákw7a", "SENS.NON.VIS"), ("ku=mám'teq", "DET=walk"), ("láku7", "DEIC"), ("áltsq7=a", "outside=EXIS"), ("t'u7", "but"), ("nílh=a", "FOC=a"), ("cwílh=t'u7", "after.all=just"), ("ti=sk'éxem=a", "DET=wind=EXIS"), ("wa7", "IPFV"), ("qan'ím-ens-an", "hear-DIR-1SG.ERG")]
    glossedWords := [⟨['w', 'a', '7'], ['b', 'e'], [⟨['w', 'a', '7'], ['b', 'e'], none⟩]⟩, ⟨['l', 'á', 'k', 'w', '7', 'a'], ['S', 'E', 'N', 'S', '.', 'N', 'O', 'N', '.', 'V', 'I', 'S'], [⟨['l', 'á', 'k', 'w', '7', 'a'], ['S', 'E', 'N', 'S', '.', 'N', 'O', 'N', '.', 'V', 'I', 'S'], none⟩]⟩, ⟨['k', 'u', '=', 'm', 'á', 'm', '\'', 't', 'e', 'q'], ['D', 'E', 'T', '=', 'w', 'a', 'l', 'k'], [⟨['k', 'u'], ['D', 'E', 'T'], none⟩, ⟨['m', 'á', 'm', '\'', 't', 'e', 'q'], ['w', 'a', 'l', 'k'], some '='⟩]⟩, ⟨['l', 'á', 'k', 'u', '7'], ['D', 'E', 'I', 'C'], [⟨['l', 'á', 'k', 'u', '7'], ['D', 'E', 'I', 'C'], none⟩]⟩, ⟨['á', 'l', 't', 's', 'q', '7', '=', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e', '=', 'E', 'X', 'I', 'S'], [⟨['á', 'l', 't', 's', 'q', '7'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩, ⟨['a'], ['E', 'X', 'I', 'S'], some '='⟩]⟩, ⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], [⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'í', 'l', 'h', '=', 'a'], ['F', 'O', 'C', '=', 'a'], [⟨['n', 'í', 'l', 'h'], ['F', 'O', 'C'], none⟩, ⟨['a'], ['a'], some '='⟩]⟩, ⟨['c', 'w', 'í', 'l', 'h', '=', 't', '\'', 'u', '7'], ['a', 'f', 't', 'e', 'r', '.', 'a', 'l', 'l', '=', 'j', 'u', 's', 't'], [⟨['c', 'w', 'í', 'l', 'h'], ['a', 'f', 't', 'e', 'r', '.', 'a', 'l', 'l'], none⟩, ⟨['t', '\'', 'u', '7'], ['j', 'u', 's', 't'], some '='⟩]⟩, ⟨['t', 'i', '=', 's', 'k', '\'', 'é', 'x', 'e', 'm', '=', 'a'], ['D', 'E', 'T', '=', 'w', 'i', 'n', 'd', '=', 'E', 'X', 'I', 'S'], [⟨['t', 'i'], ['D', 'E', 'T'], none⟩, ⟨['s', 'k', '\'', 'é', 'x', 'e', 'm'], ['w', 'i', 'n', 'd'], some '='⟩, ⟨['a'], ['E', 'X', 'I', 'S'], some '='⟩]⟩, ⟨['w', 'a', '7'], ['I', 'P', 'F', 'V'], [⟨['w', 'a', '7'], ['I', 'P', 'F', 'V'], none⟩]⟩, ⟨['q', 'a', 'n', '\'', 'í', 'm', '-', 'e', 'n', 's', '-', 'a', 'n'], ['h', 'e', 'a', 'r', '-', 'D', 'I', 'R', '-', '1', 'S', 'G', '.', 'E', 'R', 'G'], [⟨['q', 'a', 'n', '\'', 'í', 'm'], ['h', 'e', 'a', 'r'], none⟩, ⟨['e', 'n', 's'], ['D', 'I', 'R'], some '-'⟩, ⟨['a', 'n'], ['1', 'S', 'G', '.', 'E', 'R', 'G'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "lákw7a"), ("test", "deniability")] }

def ex27 : Datum :=
  { id := "matthewson2016_ex27"
    source := ⟨"matthewson-2016", "(27)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "t'ec=k'a=t'u7 ku=páoy, t'u7 áoz=t'u7 kw=a=s áma"
    glossedTokens := [("t'ec=k'a=t'u7", "tasty=INFER=just"), ("ku=páoy", "DET=pie"), ("t'u7", "but"), ("áoz=t'u7", "NEG=just"), ("kw=a=s", "DET=IPFV=3POSS"), ("áma", "good")]
    glossedWords := [⟨['t', '\'', 'e', 'c', '=', 'k', '\'', 'a', '=', 't', '\'', 'u', '7'], ['t', 'a', 's', 't', 'y', '=', 'I', 'N', 'F', 'E', 'R', '=', 'j', 'u', 's', 't'], [⟨['t', '\'', 'e', 'c'], ['t', 'a', 's', 't', 'y'], none⟩, ⟨['k', '\'', 'a'], ['I', 'N', 'F', 'E', 'R'], some '='⟩, ⟨['t', '\'', 'u', '7'], ['j', 'u', 's', 't'], some '='⟩]⟩, ⟨['k', 'u', '=', 'p', 'á', 'o', 'y'], ['D', 'E', 'T', '=', 'p', 'i', 'e'], [⟨['k', 'u'], ['D', 'E', 'T'], none⟩, ⟨['p', 'á', 'o', 'y'], ['p', 'i', 'e'], some '='⟩]⟩, ⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], [⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], none⟩]⟩, ⟨['á', 'o', 'z', '=', 't', '\'', 'u', '7'], ['N', 'E', 'G', '=', 'j', 'u', 's', 't'], [⟨['á', 'o', 'z'], ['N', 'E', 'G'], none⟩, ⟨['t', '\'', 'u', '7'], ['j', 'u', 's', 't'], some '='⟩]⟩, ⟨['k', 'w', '=', 'a', '=', 's'], ['D', 'E', 'T', '=', 'I', 'P', 'F', 'V', '=', '3', 'P', 'O', 'S', 'S'], [⟨['k', 'w'], ['D', 'E', 'T'], none⟩, ⟨['a'], ['I', 'P', 'F', 'V'], some '='⟩, ⟨['s'], ['3', 'P', 'O', 'S', 'S'], some '='⟩]⟩, ⟨['á', 'm', 'a'], ['g', 'o', 'o', 'd'], [⟨['á', 'm', 'a'], ['g', 'o', 'o', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "k'a"), ("test", "deniability")] }

def ex28 : Datum :=
  { id := "matthewson2016_ex28"
    source := ⟨"matthewson-2016", "(28)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "t'éc=t'u7 lákw7a ku=páoy, t'u7 áoz=t'u7 kw=a=s áma"
    glossedTokens := [("t'éc=t'u7", "sweet=just"), ("lákw7a", "SENS.NON.VIS"), ("ku=páoy", "DET=pie"), ("t'u7", "but"), ("áoz=t'u7", "NEG=just"), ("kw=a=s", "DET=IPFV=3POSS"), ("áma", "good")]
    glossedWords := [⟨['t', '\'', 'é', 'c', '=', 't', '\'', 'u', '7'], ['s', 'w', 'e', 'e', 't', '=', 'j', 'u', 's', 't'], [⟨['t', '\'', 'é', 'c'], ['s', 'w', 'e', 'e', 't'], none⟩, ⟨['t', '\'', 'u', '7'], ['j', 'u', 's', 't'], some '='⟩]⟩, ⟨['l', 'á', 'k', 'w', '7', 'a'], ['S', 'E', 'N', 'S', '.', 'N', 'O', 'N', '.', 'V', 'I', 'S'], [⟨['l', 'á', 'k', 'w', '7', 'a'], ['S', 'E', 'N', 'S', '.', 'N', 'O', 'N', '.', 'V', 'I', 'S'], none⟩]⟩, ⟨['k', 'u', '=', 'p', 'á', 'o', 'y'], ['D', 'E', 'T', '=', 'p', 'i', 'e'], [⟨['k', 'u'], ['D', 'E', 'T'], none⟩, ⟨['p', 'á', 'o', 'y'], ['p', 'i', 'e'], some '='⟩]⟩, ⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], [⟨['t', '\'', 'u', '7'], ['b', 'u', 't'], none⟩]⟩, ⟨['á', 'o', 'z', '=', 't', '\'', 'u', '7'], ['N', 'E', 'G', '=', 'j', 'u', 's', 't'], [⟨['á', 'o', 'z'], ['N', 'E', 'G'], none⟩, ⟨['t', '\'', 'u', '7'], ['j', 'u', 's', 't'], some '='⟩]⟩, ⟨['k', 'w', '=', 'a', '=', 's'], ['D', 'E', 'T', '=', 'I', 'P', 'F', 'V', '=', '3', 'P', 'O', 'S', 'S'], [⟨['k', 'w'], ['D', 'E', 'T'], none⟩, ⟨['a'], ['I', 'P', 'F', 'V'], some '='⟩, ⟨['s'], ['3', 'P', 'O', 'S', 'S'], some '='⟩]⟩, ⟨['á', 'm', 'a'], ['g', 'o', 'o', 'd'], [⟨['á', 'm', 'a'], ['g', 'o', 'o', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "It smelled as if the pie was good, but there was too much salt so it was actually horrible."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "lákw7a"), ("test", "deniability")] }

def ex37 : Datum :=
  { id := "matthewson2016_ex37"
    source := ⟨"matthewson-2016", "(37)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=ima=hl dim ixw-t"
    glossedTokens := [("yugw=ima=hl", "IPFV=EPIS=CN"), ("dim", "PROSP"), ("ixw-t", "fish.with.line-3")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['d', 'i', 'm'], ['P', 'R', 'O', 'S', 'P'], [⟨['d', 'i', 'm'], ['P', 'R', 'O', 'S', 'P'], none⟩]⟩, ⟨['i', 'x', 'w', '-', 't'], ['f', 'i', 's', 'h', '.', 'w', 'i', 't', 'h', '.', 'l', 'i', 'n', 'e', '-', '3'], [⟨['i', 'x', 'w'], ['f', 'i', 's', 'h', '.', 'w', 'i', 't', 'h', '.', 'l', 'i', 'n', 'e'], none⟩, ⟨['t'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You're wondering where your friend is. You notice his rod and tackle box are not in their usual place."
    judgment := .acceptable
    contrasts := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "ima('a)"), ("reportedFrom", "Peterson 2010, p. 161")] }

def ex38 : Datum :=
  { id := "matthewson2016_ex38"
    source := ⟨"matthewson-2016", "(38)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl da'awhl ixw-t oo ligi nee=yimaa=dii ixw-t"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("da'awhl", "then"), ("ixw-t", "fish-3II"), ("oo", "or"), ("ligi", "INDEF"), ("nee=yimaa=dii", "NEG=EPIS=CNTR"), ("ixw-t", "fish-3II")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['d', 'a', '\'', 'a', 'w', 'h', 'l'], ['t', 'h', 'e', 'n'], [⟨['d', 'a', '\'', 'a', 'w', 'h', 'l'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['i', 'x', 'w', '-', 't'], ['f', 'i', 's', 'h', '-', '3', 'I', 'I'], [⟨['i', 'x', 'w'], ['f', 'i', 's', 'h'], none⟩, ⟨['t'], ['3', 'I', 'I'], some '-'⟩]⟩, ⟨['o', 'o'], ['o', 'r'], [⟨['o', 'o'], ['o', 'r'], none⟩]⟩, ⟨['l', 'i', 'g', 'i'], ['I', 'N', 'D', 'E', 'F'], [⟨['l', 'i', 'g', 'i'], ['I', 'N', 'D', 'E', 'F'], none⟩]⟩, ⟨['n', 'e', 'e', '=', 'y', 'i', 'm', 'a', 'a', '=', 'd', 'i', 'i'], ['N', 'E', 'G', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N', 'T', 'R'], [⟨['n', 'e', 'e'], ['N', 'E', 'G'], none⟩, ⟨['y', 'i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['d', 'i', 'i'], ['C', 'N', 'T', 'R'], some '='⟩]⟩, ⟨['i', 'x', 'w', '-', 't'], ['f', 'i', 's', 'h', '-', '3', 'I', 'I'], [⟨['i', 'x', 'w'], ['f', 'i', 's', 'h'], none⟩, ⟨['t'], ['3', 'I', 'I'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You thought your friend was fishing. But you see his rod and tackle box are still at his house. You really don't know if he's fishing or not."
    judgment := .acceptable
    contrasts := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "ima('a)"), ("reportedFrom", "Matthewson 2013a, p. 361")] }

def ex39 : Datum :=
  { id := "matthewson2016_ex39"
    source := ⟨"matthewson-2016", "(39)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'iléx̂ni hipt ke yox̂ hi-pá-ap-o'qa"
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IPFV.PL-PRES"), ("'iléx̂ni", "a.lot"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SBJ-S.PL-eat-MOD")]
    glossedWords := [⟨['h', 'i', '-', 'w', 'q', 'í', 'i', '-', 'c', 'i', 'x', '-', '∅'], ['3', 'S', 'U', 'B', 'J', '-', 't', 'h', 'r', 'o', 'w', '.', 'a', 'w', 'a', 'y', '-', 'I', 'P', 'F', 'V', '.', 'P', 'L', '-', 'P', 'R', 'E', 'S'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['w', 'q', 'í', 'i'], ['t', 'h', 'r', 'o', 'w', '.', 'a', 'w', 'a', 'y'], some '-'⟩, ⟨['c', 'i', 'x'], ['I', 'P', 'F', 'V', '.', 'P', 'L'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['\'', 'i', 'l', 'é', 'x', '̂', 'n', 'i'], ['a', '.', 'l', 'o', 't'], [⟨['\'', 'i', 'l', 'é', 'x', '̂', 'n', 'i'], ['a', '.', 'l', 'o', 't'], none⟩]⟩, ⟨['h', 'i', 'p', 't'], ['f', 'o', 'o', 'd'], [⟨['h', 'i', 'p', 't'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['k', 'e'], ['R', 'E', 'L'], [⟨['k', 'e'], ['R', 'E', 'L'], none⟩]⟩, ⟨['y', 'o', 'x', '̂'], ['D', 'E', 'M'], [⟨['y', 'o', 'x', '̂'], ['D', 'E', 'M'], none⟩]⟩, ⟨['h', 'i', '-', 'p', 'á', '-', 'a', 'p', '-', 'o', '\'', 'q', 'a'], ['3', 'S', 'B', 'J', '-', 'S', '.', 'P', 'L', '-', 'e', 'a', 't', '-', 'M', 'O', 'D'], [⟨['h', 'i'], ['3', 'S', 'B', 'J'], none⟩, ⟨['p', 'á'], ['S', '.', 'P', 'L'], some '-'⟩, ⟨['a', 'p'], ['e', 'a', 't'], some '-'⟩, ⟨['o', '\'', 'q', 'a'], ['M', 'O', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "I am watching people clean out a cooler and throw away various things."
    judgment := .acceptable
    contrasts := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "o'qa"), ("downwardEntailing", "false"), ("reportedFrom", "Deal 2011, p. 574")] }

def ex40 : Datum :=
  { id := "matthewson2016_ex40"
    source := ⟨"matthewson-2016", "(40)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'óykala hipt ke yox̂ hi-pá-ap-o'qa"
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IPFV.PL-PRES"), ("'óykala", "all"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SBJ-S.PL-eat-MOD")]
    glossedWords := [⟨['h', 'i', '-', 'w', 'q', 'í', 'i', '-', 'c', 'i', 'x', '-', '∅'], ['3', 'S', 'U', 'B', 'J', '-', 't', 'h', 'r', 'o', 'w', '.', 'a', 'w', 'a', 'y', '-', 'I', 'P', 'F', 'V', '.', 'P', 'L', '-', 'P', 'R', 'E', 'S'], [⟨['h', 'i'], ['3', 'S', 'U', 'B', 'J'], none⟩, ⟨['w', 'q', 'í', 'i'], ['t', 'h', 'r', 'o', 'w', '.', 'a', 'w', 'a', 'y'], some '-'⟩, ⟨['c', 'i', 'x'], ['I', 'P', 'F', 'V', '.', 'P', 'L'], some '-'⟩, ⟨['∅'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['\'', 'ó', 'y', 'k', 'a', 'l', 'a'], ['a', 'l', 'l'], [⟨['\'', 'ó', 'y', 'k', 'a', 'l', 'a'], ['a', 'l', 'l'], none⟩]⟩, ⟨['h', 'i', 'p', 't'], ['f', 'o', 'o', 'd'], [⟨['h', 'i', 'p', 't'], ['f', 'o', 'o', 'd'], none⟩]⟩, ⟨['k', 'e'], ['R', 'E', 'L'], [⟨['k', 'e'], ['R', 'E', 'L'], none⟩]⟩, ⟨['y', 'o', 'x', '̂'], ['D', 'E', 'M'], [⟨['y', 'o', 'x', '̂'], ['D', 'E', 'M'], none⟩]⟩, ⟨['h', 'i', '-', 'p', 'á', '-', 'a', 'p', '-', 'o', '\'', 'q', 'a'], ['3', 'S', 'B', 'J', '-', 'S', '.', 'P', 'L', '-', 'e', 'a', 't', '-', 'M', 'O', 'D'], [⟨['h', 'i'], ['3', 'S', 'B', 'J'], none⟩, ⟨['p', 'á'], ['S', '.', 'P', 'L'], some '-'⟩, ⟨['a', 'p'], ['e', 'a', 't'], some '-'⟩, ⟨['o', '\'', 'q', 'a'], ['M', 'O', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "As in (39)."
    judgment := .acceptable
    contrasts := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "o'qa"), ("downwardEntailing", "true"), ("reportedFrom", "Deal 2011, p. 574")] }

def ex42a : Datum :=
  { id := "matthewson2016_ex42a"
    source := ⟨"matthewson-2016", "(42a)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary mat ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("mat", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['m', 'a', 't'], ['M', 'O', 'D'], [⟨['m', 'a', 't'], ['M', 'O', 'D'], none⟩]⟩, ⟨['a', 'c', '-', 'q', 'í', 'c', '-', 'ə', 'l', 'x'], ['C', 'U', 'S', 'T', '-', 'r', 'u', 'n', '-', 'L', 'E', 'X'], [⟨['a', 'c'], ['C', 'U', 'S', 'T'], none⟩, ⟨['q', 'í', 'c'], ['r', 'u', 'n'], some '-'⟩, ⟨['ə', 'l', 'x'], ['L', 'E', 'X'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You know that Mary loves to go running and often goes on runs randomly. She could also be at the store or at school. I ask you, where is Mary?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "mat"), ("force", "possibility"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex42b : Datum :=
  { id := "matthewson2016_ex42b"
    source := ⟨"matthewson-2016", "(42b)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary cmay ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("cmay", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['c', 'm', 'a', 'y'], ['M', 'O', 'D'], [⟨['c', 'm', 'a', 'y'], ['M', 'O', 'D'], none⟩]⟩, ⟨['a', 'c', '-', 'q', 'í', 'c', '-', 'ə', 'l', 'x'], ['C', 'U', 'S', 'T', '-', 'r', 'u', 'n', '-', 'L', 'E', 'X'], [⟨['a', 'c'], ['C', 'U', 'S', 'T'], none⟩, ⟨['q', 'í', 'c'], ['r', 'u', 'n'], some '-'⟩, ⟨['ə', 'l', 'x'], ['L', 'E', 'X'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You know that Mary loves to go running and often goes on runs randomly. She could also be at the store or at school. I ask you, where is Mary?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "cmay"), ("force", "possibility"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex43a : Datum :=
  { id := "matthewson2016_ex43a"
    source := ⟨"matthewson-2016", "(43a)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary mat ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("mat", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['m', 'a', 't'], ['M', 'O', 'D'], [⟨['m', 'a', 't'], ['M', 'O', 'D'], none⟩]⟩, ⟨['a', 'c', '-', 'q', 'í', 'c', '-', 'ə', 'l', 'x'], ['C', 'U', 'S', 'T', '-', 'r', 'u', 'n', '-', 'L', 'E', 'X'], [⟨['a', 'c'], ['C', 'U', 'S', 'T'], none⟩, ⟨['q', 'í', 'c'], ['r', 'u', 'n'], some '-'⟩, ⟨['ə', 'l', 'x'], ['L', 'E', 'X'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Mary runs every day to train for a marathon. She usually runs at 6 pm on Tuesdays. Today is Tuesday and it's 6 pm. I ask you, where is Mary?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "mat"), ("force", "necessity"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex43b : Datum :=
  { id := "matthewson2016_ex43b"
    source := ⟨"matthewson-2016", "(43b)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary cmay ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("cmay", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    glossedWords := [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['c', 'm', 'a', 'y'], ['M', 'O', 'D'], [⟨['c', 'm', 'a', 'y'], ['M', 'O', 'D'], none⟩]⟩, ⟨['a', 'c', '-', 'q', 'í', 'c', '-', 'ə', 'l', 'x'], ['C', 'U', 'S', 'T', '-', 'r', 'u', 'n', '-', 'L', 'E', 'X'], [⟨['a', 'c'], ['C', 'U', 'S', 'T'], none⟩, ⟨['q', 'í', 'c'], ['r', 'u', 'n'], some '-'⟩, ⟨['ə', 'l', 'x'], ['L', 'E', 'X'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Mary runs every day to train for a marathon. She usually runs at 6 pm on Tuesdays. Today is Tuesday and it's 6 pm. I ask you, where is Mary?"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "cmay"), ("force", "necessity"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex57 : Datum :=
  { id := "matthewson2016_ex57"
    source := ⟨"matthewson-2016", "(57)"⟩
    reportedIn := none
    language := "siks1238"
    primaryText := "matonni ni-maat-ssksini-'p-wa ot-aanist-a'pssi-wa piiksiksinaa-wa aahkam-omitaa-wa"
    glossedTokens := [("matonni", "yesterday"), ("ni-maat-ssksini-'p-wa", "1-NEG-know.VTI-LOC:0-NONAFF"), ("ot-aanist-a'pssi-wa", "3-manner-be.VAI-3"), ("piiksiksinaa-wa", "snake-3"), ("aahkam-omitaa-wa", "EPIS-dog-3")]
    glossedWords := [⟨['m', 'a', 't', 'o', 'n', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['m', 'a', 't', 'o', 'n', 'n', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['n', 'i', '-', 'm', 'a', 'a', 't', '-', 's', 's', 'k', 's', 'i', 'n', 'i', '-', '\'', 'p', '-', 'w', 'a'], ['1', '-', 'N', 'E', 'G', '-', 'k', 'n', 'o', 'w', '.', 'V', 'T', 'I', '-', 'L', 'O', 'C', ':', '0', '-', 'N', 'O', 'N', 'A', 'F', 'F'], [⟨['n', 'i'], ['1'], none⟩, ⟨['m', 'a', 'a', 't'], ['N', 'E', 'G'], some '-'⟩, ⟨['s', 's', 'k', 's', 'i', 'n', 'i'], ['k', 'n', 'o', 'w', '.', 'V', 'T', 'I'], some '-'⟩, ⟨['\'', 'p'], ['L', 'O', 'C', ':', '0'], some '-'⟩, ⟨['w', 'a'], ['N', 'O', 'N', 'A', 'F', 'F'], some '-'⟩]⟩, ⟨['o', 't', '-', 'a', 'a', 'n', 'i', 's', 't', '-', 'a', '\'', 'p', 's', 's', 'i', '-', 'w', 'a'], ['3', '-', 'm', 'a', 'n', 'n', 'e', 'r', '-', 'b', 'e', '.', 'V', 'A', 'I', '-', '3'], [⟨['o', 't'], ['3'], none⟩, ⟨['a', 'a', 'n', 'i', 's', 't'], ['m', 'a', 'n', 'n', 'e', 'r'], some '-'⟩, ⟨['a', '\'', 'p', 's', 's', 'i'], ['b', 'e', '.', 'V', 'A', 'I'], some '-'⟩, ⟨['w', 'a'], ['3'], some '-'⟩]⟩, ⟨['p', 'i', 'i', 'k', 's', 'i', 'k', 's', 'i', 'n', 'a', 'a', '-', 'w', 'a'], ['s', 'n', 'a', 'k', 'e', '-', '3'], [⟨['p', 'i', 'i', 'k', 's', 'i', 'k', 's', 'i', 'n', 'a', 'a'], ['s', 'n', 'a', 'k', 'e'], none⟩, ⟨['w', 'a'], ['3'], some '-'⟩]⟩, ⟨['a', 'a', 'h', 'k', 'a', 'm', '-', 'o', 'm', 'i', 't', 'a', 'a', '-', 'w', 'a'], ['E', 'P', 'I', 'S', '-', 'd', 'o', 'g', '-', '3'], [⟨['a', 'a', 'h', 'k', 'a', 'm'], ['E', 'P', 'I', 'S'], none⟩, ⟨['o', 'm', 'i', 't', 'a', 'a'], ['d', 'o', 'g'], some '-'⟩, ⟨['w', 'a'], ['3'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Stacey bought a bone for Pat's pet, thinking it might be a dog. Later, she finds out the pet is a snake. When Pat asks her why she bought a bone, she says:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("flavor", "epistemic"), ("perspective", "past"), ("reportedFrom", "Louie 2012")] }

def ex58 : Datum :=
  { id := "matthewson2016_ex58"
    source := ⟨"matthewson-2016", "(58)"⟩
    reportedIn := none
    language := "kute1249"
    primaryText := "ⱡin hin sa·niⱡxuʔ-ni"
    glossedTokens := [("ⱡin", "EPIS"), ("hin", "2"), ("sa·niⱡxuʔ-ni", "sick-IND")]
    glossedWords := [⟨['ⱡ', 'i', 'n'], ['E', 'P', 'I', 'S'], [⟨['ⱡ', 'i', 'n'], ['E', 'P', 'I', 'S'], none⟩]⟩, ⟨['h', 'i', 'n'], ['2'], [⟨['h', 'i', 'n'], ['2'], none⟩]⟩, ⟨['s', 'a', '·', 'n', 'i', 'ⱡ', 'x', 'u', 'ʔ', '-', 'n', 'i'], ['s', 'i', 'c', 'k', '-', 'I', 'N', 'D'], [⟨['s', 'a', '·', 'n', 'i', 'ⱡ', 'x', 'u', 'ʔ'], ['s', 'i', 'c', 'k'], none⟩, ⟨['n', 'i'], ['I', 'N', 'D'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Your neighbour doesn't show up for work and you know there's been a flu going around. You send your son to bring her hot soup. She actually took the day off because her apartment flooded, so she asks why you sent her soup in the middle of the day."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("flavor", "epistemic"), ("perspective", "past"), ("reportedFrom", "Laturnus 2012")] }

def ex59 : Datum :=
  { id := "matthewson2016_ex59"
    source := ⟨"matthewson-2016", "(59)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "kwís=k'a=tu7"
    glossedTokens := [("kwís=k'a=tu7", "rain=EPIS=then")]
    glossedWords := [⟨['k', 'w', 'í', 's', '=', 'k', '\'', 'a', '=', 't', 'u', '7'], ['r', 'a', 'i', 'n', '=', 'E', 'P', 'I', 'S', '=', 't', 'h', 'e', 'n'], [⟨['k', 'w', 'í', 's'], ['r', 'a', 'i', 'n'], none⟩, ⟨['k', '\'', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['t', 'u', '7'], ['t', 'h', 'e', 'n'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "When you looked out of your window earlier today the ground was wet, so it looked like it might have rained. But you find out later that sprinklers had been watering the ground."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "k'a"), ("flavor", "epistemic"), ("perspective", "past")] }

def ex60 : Datum :=
  { id := "matthewson2016_ex60"
    source := ⟨"matthewson-2016", "(60)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis da'awhl"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain"), ("da'awhl", "then")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], [⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], none⟩]⟩, ⟨['d', 'a', '\'', 'a', 'w', 'h', 'l'], ['t', 'h', 'e', 'n'], [⟨['d', 'a', '\'', 'a', 'w', 'h', 'l'], ['t', 'h', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "When you looked out your window earlier today, the ground was wet, so it looked like it might have rained. But you found out later that the sprinklers had been watering the ground."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "past"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, p. 366")] }

def ex61 : Datum :=
  { id := "matthewson2016_ex61"
    source := ⟨"matthewson-2016", "(61)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis da'awhl"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain"), ("da'awhl", "then")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], [⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], none⟩]⟩, ⟨['d', 'a', '\'', 'a', 'w', 'h', 'l'], ['t', 'h', 'e', 'n'], [⟨['d', 'a', '\'', 'a', 'w', 'h', 'l'], ['t', 'h', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "When you looked out your window earlier today, water was falling, so it looked like it was raining. But you found out later it was the gutters leaking."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "present"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, p. 363")] }

def ex62 : Datum :=
  { id := "matthewson2016_ex62"
    source := ⟨"matthewson-2016", "(62)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl dim wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("dim", "PROSP"), ("wis", "rain")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['d', 'i', 'm'], ['P', 'R', 'O', 'S', 'P'], [⟨['d', 'i', 'm'], ['P', 'R', 'O', 'S', 'P'], none⟩]⟩, ⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], [⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "This morning you looked out your window and judging by the clouds, it looked like it might have been going to rain, so you took your raincoat. Later you're explaining to me why you did that."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true"), ("reportedFrom", "Matthewson 2013a, p. 366")] }

def ex63a : Datum :=
  { id := "matthewson2016_ex63a"
    source := ⟨"matthewson-2016", "(63a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], [⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You see puddles, and the flowers looking fresh and damp."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("orientation", "past"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, pp. 364–365")] }

def ex63b : Datum :=
  { id := "matthewson2016_ex63b"
    source := ⟨"matthewson-2016", "(63b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], [⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You hear pattering on the roof."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("orientation", "present"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, pp. 364–365")] }

def ex63c : Datum :=
  { id := "matthewson2016_ex63c"
    source := ⟨"matthewson-2016", "(63c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    glossedWords := [⟨['y', 'u', 'g', 'w', '=', 'i', 'm', 'a', 'a', '=', 'h', 'l'], ['I', 'P', 'F', 'V', '=', 'E', 'P', 'I', 'S', '=', 'C', 'N'], [⟨['y', 'u', 'g', 'w'], ['I', 'P', 'F', 'V'], none⟩, ⟨['i', 'm', 'a', 'a'], ['E', 'P', 'I', 'S'], some '='⟩, ⟨['h', 'l'], ['C', 'N'], some '='⟩]⟩, ⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], [⟨['w', 'i', 's'], ['r', 'a', 'i', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You hear thunder, so you think it might rain soon."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("orientation", "future"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, pp. 364–365")] }

def ex64 : Datum :=
  { id := "matthewson2016_ex64"
    source := ⟨"matthewson-2016", "(64)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "liga kua fano tei"
    glossedTokens := [("liga", "EPIS"), ("kua", "PRF"), ("fano", "go"), ("tei", "PRF")]
    glossedWords := [⟨['l', 'i', 'g', 'a'], ['E', 'P', 'I', 'S'], [⟨['l', 'i', 'g', 'a'], ['E', 'P', 'I', 'S'], none⟩]⟩, ⟨['k', 'u', 'a'], ['P', 'R', 'F'], [⟨['k', 'u', 'a'], ['P', 'R', 'F'], none⟩]⟩, ⟨['f', 'a', 'n', 'o'], ['g', 'o'], [⟨['f', 'a', 'n', 'o'], ['g', 'o'], none⟩]⟩, ⟨['t', 'e', 'i'], ['P', 'R', 'F'], [⟨['t', 'e', 'i'], ['P', 'R', 'F'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "liga"), ("force", "weak"), ("flavor", "epistemic"), ("reportedFrom", "Matthewson et al. 2012, p. 224")] }

def ex65 : Datum :=
  { id := "matthewson2016_ex65"
    source := ⟨"matthewson-2016", "(65)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "Hī ika a Tom he aho nei ... liga malolo a ia"
    glossedTokens := [("Hī", "catch.fish"), ("ika", "fish"), ("a", "ABS"), ("Tom", "Tom"), ("he", "on"), ("aho", "day"), ("nei", "this"), ("liga", "EPIS"), ("malolo", "strong"), ("a", "ABS"), ("ia", "3SG")]
    glossedWords := [⟨['H', 'ī'], ['c', 'a', 't', 'c', 'h', '.', 'f', 'i', 's', 'h'], [⟨['H', 'ī'], ['c', 'a', 't', 'c', 'h', '.', 'f', 'i', 's', 'h'], none⟩]⟩, ⟨['i', 'k', 'a'], ['f', 'i', 's', 'h'], [⟨['i', 'k', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['a'], ['A', 'B', 'S'], [⟨['a'], ['A', 'B', 'S'], none⟩]⟩, ⟨['T', 'o', 'm'], ['T', 'o', 'm'], [⟨['T', 'o', 'm'], ['T', 'o', 'm'], none⟩]⟩, ⟨['h', 'e'], ['o', 'n'], [⟨['h', 'e'], ['o', 'n'], none⟩]⟩, ⟨['a', 'h', 'o'], ['d', 'a', 'y'], [⟨['a', 'h', 'o'], ['d', 'a', 'y'], none⟩]⟩, ⟨['n', 'e', 'i'], ['t', 'h', 'i', 's'], [⟨['n', 'e', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['l', 'i', 'g', 'a'], ['E', 'P', 'I', 'S'], [⟨['l', 'i', 'g', 'a'], ['E', 'P', 'I', 'S'], none⟩]⟩, ⟨['m', 'a', 'l', 'o', 'l', 'o'], ['s', 't', 'r', 'o', 'n', 'g'], [⟨['m', 'a', 'l', 'o', 'l', 'o'], ['s', 't', 'r', 'o', 'n', 'g'], none⟩]⟩, ⟨['a'], ['A', 'B', 'S'], [⟨['a'], ['A', 'B', 'S'], none⟩]⟩, ⟨['i', 'a'], ['3', 'S', 'G'], [⟨['i', 'a'], ['3', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Tom wasn't fishing yesterday, and you were wondering about his health. But today you see him fishing."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "liga"), ("flavor", "epistemic"), ("reportedFrom", "Matthewson et al. 2012, p. 228")] }

def ex66 : Datum :=
  { id := "matthewson2016_ex66"
    source := ⟨"matthewson-2016", "(66)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "ne liga kua veli hifo e tama ke he pelapela"
    glossedTokens := [("ne", "PAST"), ("liga", "EPIS"), ("kua", "PRF"), ("veli", "fall"), ("hifo", "down"), ("e", "ABS"), ("tama", "child"), ("ke", "to"), ("he", ""), ("pelapela", "mud")]
    glossedWords := [⟨['n', 'e'], ['P', 'A', 'S', 'T'], [⟨['n', 'e'], ['P', 'A', 'S', 'T'], none⟩]⟩, ⟨['l', 'i', 'g', 'a'], ['E', 'P', 'I', 'S'], [⟨['l', 'i', 'g', 'a'], ['E', 'P', 'I', 'S'], none⟩]⟩, ⟨['k', 'u', 'a'], ['P', 'R', 'F'], [⟨['k', 'u', 'a'], ['P', 'R', 'F'], none⟩]⟩, ⟨['v', 'e', 'l', 'i'], ['f', 'a', 'l', 'l'], [⟨['v', 'e', 'l', 'i'], ['f', 'a', 'l', 'l'], none⟩]⟩, ⟨['h', 'i', 'f', 'o'], ['d', 'o', 'w', 'n'], [⟨['h', 'i', 'f', 'o'], ['d', 'o', 'w', 'n'], none⟩]⟩, ⟨['e'], ['A', 'B', 'S'], [⟨['e'], ['A', 'B', 'S'], none⟩]⟩, ⟨['t', 'a', 'm', 'a'], ['c', 'h', 'i', 'l', 'd'], [⟨['t', 'a', 'm', 'a'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['k', 'e'], ['t', 'o'], [⟨['k', 'e'], ['t', 'o'], none⟩]⟩, ⟨['h', 'e'], [], []⟩, ⟨['p', 'e', 'l', 'a', 'p', 'e', 'l', 'a'], ['m', 'u', 'd'], [⟨['p', 'e', 'l', 'a', 'p', 'e', 'l', 'a'], ['m', 'u', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "liga"), ("force", "strong"), ("flavor", "epistemic"), ("reportedFrom", "Seiter 1980, p. 13")] }

def ex67 : Datum :=
  { id := "matthewson2016_ex67"
    source := ⟨"matthewson-2016", "(67)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "kua maeke he tama ia ke taute pasikala afi"
    glossedTokens := [("kua", "PRF"), ("maeke", "CIRC.POSSIB"), ("he", "at"), ("tama", "child"), ("ia", "that"), ("ke", "SBJ"), ("taute", "fix"), ("pasikala", "bicycle"), ("afi", "fire")]
    glossedWords := [⟨['k', 'u', 'a'], ['P', 'R', 'F'], [⟨['k', 'u', 'a'], ['P', 'R', 'F'], none⟩]⟩, ⟨['m', 'a', 'e', 'k', 'e'], ['C', 'I', 'R', 'C', '.', 'P', 'O', 'S', 'S', 'I', 'B'], [⟨['m', 'a', 'e', 'k', 'e'], ['C', 'I', 'R', 'C', '.', 'P', 'O', 'S', 'S', 'I', 'B'], none⟩]⟩, ⟨['h', 'e'], ['a', 't'], [⟨['h', 'e'], ['a', 't'], none⟩]⟩, ⟨['t', 'a', 'm', 'a'], ['c', 'h', 'i', 'l', 'd'], [⟨['t', 'a', 'm', 'a'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['i', 'a'], ['t', 'h', 'a', 't'], [⟨['i', 'a'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'e'], ['S', 'B', 'J'], [⟨['k', 'e'], ['S', 'B', 'J'], none⟩]⟩, ⟨['t', 'a', 'u', 't', 'e'], ['f', 'i', 'x'], [⟨['t', 'a', 'u', 't', 'e'], ['f', 'i', 'x'], none⟩]⟩, ⟨['p', 'a', 's', 'i', 'k', 'a', 'l', 'a'], ['b', 'i', 'c', 'y', 'c', 'l', 'e'], [⟨['p', 'a', 's', 'i', 'k', 'a', 'l', 'a'], ['b', 'i', 'c', 'y', 'c', 'l', 'e'], none⟩]⟩, ⟨['a', 'f', 'i'], ['f', 'i', 'r', 'e'], [⟨['a', 'f', 'i'], ['f', 'i', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "maeke"), ("force", "weak"), ("flavor", "circumstantial"), ("reportedFrom", "Seiter 1980, p. 140")] }

def ex68 : Datum :=
  { id := "matthewson2016_ex68"
    source := ⟨"matthewson-2016", "(68)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "lata ke ō a tautolu he aho nei ki Queen Street"
    glossedTokens := [("lata", "CIRC.NECESS"), ("ke", "SBJ"), ("ō", "go.PL"), ("a", "ABS"), ("tautolu", "we.PL.INCL"), ("he", "on"), ("aho", "day"), ("nei", "this"), ("ki", "to"), ("Queen", "Queen"), ("Street", "Street")]
    glossedWords := [⟨['l', 'a', 't', 'a'], ['C', 'I', 'R', 'C', '.', 'N', 'E', 'C', 'E', 'S', 'S'], [⟨['l', 'a', 't', 'a'], ['C', 'I', 'R', 'C', '.', 'N', 'E', 'C', 'E', 'S', 'S'], none⟩]⟩, ⟨['k', 'e'], ['S', 'B', 'J'], [⟨['k', 'e'], ['S', 'B', 'J'], none⟩]⟩, ⟨['ō'], ['g', 'o', '.', 'P', 'L'], [⟨['ō'], ['g', 'o', '.', 'P', 'L'], none⟩]⟩, ⟨['a'], ['A', 'B', 'S'], [⟨['a'], ['A', 'B', 'S'], none⟩]⟩, ⟨['t', 'a', 'u', 't', 'o', 'l', 'u'], ['w', 'e', '.', 'P', 'L', '.', 'I', 'N', 'C', 'L'], [⟨['t', 'a', 'u', 't', 'o', 'l', 'u'], ['w', 'e', '.', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩]⟩, ⟨['h', 'e'], ['o', 'n'], [⟨['h', 'e'], ['o', 'n'], none⟩]⟩, ⟨['a', 'h', 'o'], ['d', 'a', 'y'], [⟨['a', 'h', 'o'], ['d', 'a', 'y'], none⟩]⟩, ⟨['n', 'e', 'i'], ['t', 'h', 'i', 's'], [⟨['n', 'e', 'i'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['k', 'i'], ['t', 'o'], [⟨['k', 'i'], ['t', 'o'], none⟩]⟩, ⟨['Q', 'u', 'e', 'e', 'n'], ['Q', 'u', 'e', 'e', 'n'], [⟨['Q', 'u', 'e', 'e', 'n'], ['Q', 'u', 'e', 'e', 'n'], none⟩]⟩, ⟨['S', 't', 'r', 'e', 'e', 't'], ['S', 't', 'r', 'e', 'e', 't'], [⟨['S', 't', 'r', 'e', 'e', 't'], ['S', 't', 'r', 'e', 'e', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "lata"), ("force", "strong"), ("flavor", "deontic"), ("reportedFrom", "Seiter 1980, p. 133")] }

def all : List Datum := [ex25, ex26, ex27, ex28, ex37, ex38, ex39, ex40, ex42a, ex42b, ex43a, ex43b, ex57, ex58, ex59, ex60, ex61, ex62, ex63a, ex63b, ex63c, ex64, ex65, ex66, ex67, ex68]

end Matthewson2016.Examples
