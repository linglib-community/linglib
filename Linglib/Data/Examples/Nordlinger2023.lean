module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Nordlinger2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Nordlinger2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Nordlinger2023.Examples`.
-/

@[expose] public section

namespace Nordlinger2023.Examples

def ex5a : Datum :=
  { id := "nordlinger2023_ex5a"
    source := ⟨"hurst-2012", "p. 226"⟩
    reportedIn := some ⟨"nordlinger-2023", "(5a)"⟩
    language := "swah1253"
    primaryText := "Juma a-li-m-tekeny-a Halima"
    glossedTokens := [("Juma", "Juma"), ("a-li-m-tekeny-a", "3SG.SBJ-PST-3SG.OBJ-tickle-FV"), ("Halima", "Halima")]
    glossedWords := [⟨['J', 'u', 'm', 'a'], ['J', 'u', 'm', 'a'], [⟨['J', 'u', 'm', 'a'], ['J', 'u', 'm', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 'm', '-', 't', 'e', 'k', 'e', 'n', 'y', '-', 'a'], ['3', 'S', 'G', '.', 'S', 'B', 'J', '-', 'P', 'S', 'T', '-', '3', 'S', 'G', '.', 'O', 'B', 'J', '-', 't', 'i', 'c', 'k', 'l', 'e', '-', 'F', 'V'], [⟨['a'], ['3', 'S', 'G', '.', 'S', 'B', 'J'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['m'], ['3', 'S', 'G', '.', 'O', 'B', 'J'], some '-'⟩, ⟨['t', 'e', 'k', 'e', 'n', 'y'], ['t', 'i', 'c', 'k', 'l', 'e'], some '-'⟩, ⟨['a'], ['F', 'V'], some '-'⟩]⟩, ⟨['H', 'a', 'l', 'i', 'm', 'a'], ['H', 'a', 'l', 'i', 'm', 'a'], [⟨['H', 'a', 'l', 'i', 'm', 'a'], ['H', 'a', 'l', 'i', 'm', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "base")] }

def ex9 : Datum :=
  { id := "nordlinger2023_ex9"
    source := ⟨"nordlinger-2023", "(9)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Oni vide-l-i drug drug-a"
    glossedTokens := [("Oni", "3PL.NOM"), ("vide-l-i", "see-PST-PL"), ("drug", "other"), ("drug-a", "other-ACC")]
    glossedWords := [⟨['O', 'n', 'i'], ['3', 'P', 'L', '.', 'N', 'O', 'M'], [⟨['O', 'n', 'i'], ['3', 'P', 'L', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['v', 'i', 'd', 'e', '-', 'l', '-', 'i'], ['s', 'e', 'e', '-', 'P', 'S', 'T', '-', 'P', 'L'], [⟨['v', 'i', 'd', 'e'], ['s', 'e', 'e'], none⟩, ⟨['l'], ['P', 'S', 'T'], some '-'⟩, ⟨['i'], ['P', 'L'], some '-'⟩]⟩, ⟨['d', 'r', 'u', 'g'], ['o', 't', 'h', 'e', 'r'], [⟨['d', 'r', 'u', 'g'], ['o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['d', 'r', 'u', 'g', '-', 'a'], ['o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['d', 'r', 'u', 'g'], ['o', 't', 'h', 'e', 'r'], none⟩, ⟨['a'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex11 : Datum :=
  { id := "nordlinger2023_ex11"
    source := ⟨"nordlinger-1998", "p. 142"⟩
    reportedIn := some ⟨"nordlinger-2023", "(11)"⟩
    language := "wamb1258"
    primaryText := "Alag-bulu wurlu-ngg-a nyurrunyurru"
    glossedTokens := [("Alag-bulu", "child-DU(NOM)"), ("wurlu-ngg-a", "3DU.SBJ-RR-NFUT"), ("nyurrunyurru", "chase")]
    glossedWords := [⟨['A', 'l', 'a', 'g', '-', 'b', 'u', 'l', 'u'], ['c', 'h', 'i', 'l', 'd', '-', 'D', 'U', '(', 'N', 'O', 'M', ')'], [⟨['A', 'l', 'a', 'g'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['b', 'u', 'l', 'u'], ['D', 'U', '(', 'N', 'O', 'M', ')'], some '-'⟩]⟩, ⟨['w', 'u', 'r', 'l', 'u', '-', 'n', 'g', 'g', '-', 'a'], ['3', 'D', 'U', '.', 'S', 'B', 'J', '-', 'R', 'R', '-', 'N', 'F', 'U', 'T'], [⟨['w', 'u', 'r', 'l', 'u'], ['3', 'D', 'U', '.', 'S', 'B', 'J'], none⟩, ⟨['n', 'g', 'g'], ['R', 'R'], some '-'⟩, ⟨['a'], ['N', 'F', 'U', 'T'], some '-'⟩]⟩, ⟨['n', 'y', 'u', 'r', 'r', 'u', 'n', 'y', 'u', 'r', 'r', 'u'], ['c', 'h', 'a', 's', 'e'], [⟨['n', 'y', 'u', 'r', 'r', 'u', 'n', 'y', 'u', 'r', 'r', 'u'], ['c', 'h', 'a', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex12 : Datum :=
  { id := "nordlinger2023_ex12"
    source := ⟨"hurst-2012", "p. 249"⟩
    reportedIn := some ⟨"nordlinger-2023", "(12)"⟩
    language := "swah1253"
    primaryText := "Juma na Halima wa-li-tekeny-an-a"
    glossedTokens := [("Juma", "Juma"), ("na", "and"), ("Halima", "Halima"), ("wa-li-tekeny-an-a", "3PL.SBJ-PST-tickle-RECP-FV")]
    glossedWords := [⟨['J', 'u', 'm', 'a'], ['J', 'u', 'm', 'a'], [⟨['J', 'u', 'm', 'a'], ['J', 'u', 'm', 'a'], none⟩]⟩, ⟨['n', 'a'], ['a', 'n', 'd'], [⟨['n', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['H', 'a', 'l', 'i', 'm', 'a'], ['H', 'a', 'l', 'i', 'm', 'a'], [⟨['H', 'a', 'l', 'i', 'm', 'a'], ['H', 'a', 'l', 'i', 'm', 'a'], none⟩]⟩, ⟨['w', 'a', '-', 'l', 'i', '-', 't', 'e', 'k', 'e', 'n', 'y', '-', 'a', 'n', '-', 'a'], ['3', 'P', 'L', '.', 'S', 'B', 'J', '-', 'P', 'S', 'T', '-', 't', 'i', 'c', 'k', 'l', 'e', '-', 'R', 'E', 'C', 'P', '-', 'F', 'V'], [⟨['w', 'a'], ['3', 'P', 'L', '.', 'S', 'B', 'J'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'e', 'k', 'e', 'n', 'y'], ['t', 'i', 'c', 'k', 'l', 'e'], some '-'⟩, ⟨['a', 'n'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['a'], ['F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex13 : Datum :=
  { id := "nordlinger2023_ex13"
    source := ⟨"konig-kokutani-2006", "p. 275"⟩
    reportedIn := some ⟨"nordlinger-2023", "(13)"⟩
    language := "mand1415"
    primaryText := "Tāmen dǎ-lái-dǎ-qù"
    glossedTokens := [("Tāmen", "3PL"), ("dǎ-lái-dǎ-qù", "beat-come-beat-go")]
    glossedWords := [⟨['T', 'ā', 'm', 'e', 'n'], ['3', 'P', 'L'], [⟨['T', 'ā', 'm', 'e', 'n'], ['3', 'P', 'L'], none⟩]⟩, ⟨['d', 'ǎ', '-', 'l', 'á', 'i', '-', 'd', 'ǎ', '-', 'q', 'ù'], ['b', 'e', 'a', 't', '-', 'c', 'o', 'm', 'e', '-', 'b', 'e', 'a', 't', '-', 'g', 'o'], [⟨['d', 'ǎ'], ['b', 'e', 'a', 't'], none⟩, ⟨['l', 'á', 'i'], ['c', 'o', 'm', 'e'], some '-'⟩, ⟨['d', 'ǎ'], ['b', 'e', 'a', 't'], some '-'⟩, ⟨['q', 'ù'], ['g', 'o'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex17a : Datum :=
  { id := "nordlinger2023_ex17a"
    source := ⟨"hurst-nordlinger-2021", "p. 105"⟩
    reportedIn := some ⟨"nordlinger-2023", "(17a)"⟩
    language := "icel1247"
    primaryText := "Stelpa-n og strákur-inn sáu hvort annað"
    glossedTokens := [("Stelpa-n", "girl.F.SG.NOM-DEF"), ("og", "and"), ("strákur-inn", "boy.M.SG.NOM-DEF"), ("sáu", "see.3PL.PST"), ("hvort", "each.N.SG.NOM"), ("annað", "other.N.SG.ACC")]
    glossedWords := [⟨['S', 't', 'e', 'l', 'p', 'a', '-', 'n'], ['g', 'i', 'r', 'l', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M', '-', 'D', 'E', 'F'], [⟨['S', 't', 'e', 'l', 'p', 'a'], ['g', 'i', 'r', 'l', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M'], none⟩, ⟨['n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['o', 'g'], ['a', 'n', 'd'], [⟨['o', 'g'], ['a', 'n', 'd'], none⟩]⟩, ⟨['s', 't', 'r', 'á', 'k', 'u', 'r', '-', 'i', 'n', 'n'], ['b', 'o', 'y', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M', '-', 'D', 'E', 'F'], [⟨['s', 't', 'r', 'á', 'k', 'u', 'r'], ['b', 'o', 'y', '.', 'M', '.', 'S', 'G', '.', 'N', 'O', 'M'], none⟩, ⟨['i', 'n', 'n'], ['D', 'E', 'F'], some '-'⟩]⟩, ⟨['s', 'á', 'u'], ['s', 'e', 'e', '.', '3', 'P', 'L', '.', 'P', 'S', 'T'], [⟨['s', 'á', 'u'], ['s', 'e', 'e', '.', '3', 'P', 'L', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['h', 'v', 'o', 'r', 't'], ['e', 'a', 'c', 'h', '.', 'N', '.', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['h', 'v', 'o', 'r', 't'], ['e', 'a', 'c', 'h', '.', 'N', '.', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['a', 'n', 'n', 'a', 'ð'], ['o', 't', 'h', 'e', 'r', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C'], [⟨['a', 'n', 'n', 'a', 'ð'], ['o', 't', 'h', 'e', 'r', '.', 'N', '.', 'S', 'G', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex18a : Datum :=
  { id := "nordlinger2023_ex18a"
    source := ⟨"nordlinger-2023", "(18a)"⟩
    reportedIn := none
    language := "warl1254"
    primaryText := "Ngarrka-jarra-rlu ka-pala-jana paka-rni"
    glossedTokens := [("Ngarrka-jarra-rlu", "man-DU-ERG"), ("ka-pala-jana", "IPFV-3DU.SBJ-3PL.OBJ"), ("paka-rni", "strike-NPST")]
    glossedWords := [⟨['N', 'g', 'a', 'r', 'r', 'k', 'a', '-', 'j', 'a', 'r', 'r', 'a', '-', 'r', 'l', 'u'], ['m', 'a', 'n', '-', 'D', 'U', '-', 'E', 'R', 'G'], [⟨['N', 'g', 'a', 'r', 'r', 'k', 'a'], ['m', 'a', 'n'], none⟩, ⟨['j', 'a', 'r', 'r', 'a'], ['D', 'U'], some '-'⟩, ⟨['r', 'l', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'a', '-', 'p', 'a', 'l', 'a', '-', 'j', 'a', 'n', 'a'], ['I', 'P', 'F', 'V', '-', '3', 'D', 'U', '.', 'S', 'B', 'J', '-', '3', 'P', 'L', '.', 'O', 'B', 'J'], [⟨['k', 'a'], ['I', 'P', 'F', 'V'], none⟩, ⟨['p', 'a', 'l', 'a'], ['3', 'D', 'U', '.', 'S', 'B', 'J'], some '-'⟩, ⟨['j', 'a', 'n', 'a'], ['3', 'P', 'L', '.', 'O', 'B', 'J'], some '-'⟩]⟩, ⟨['p', 'a', 'k', 'a', '-', 'r', 'n', 'i'], ['s', 't', 'r', 'i', 'k', 'e', '-', 'N', 'P', 'S', 'T'], [⟨['p', 'a', 'k', 'a'], ['s', 't', 'r', 'i', 'k', 'e'], none⟩, ⟨['r', 'n', 'i'], ['N', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "base")] }

def ex18b : Datum :=
  { id := "nordlinger2023_ex18b"
    source := ⟨"nordlinger-2023", "(18b)"⟩
    reportedIn := none
    language := "warl1254"
    primaryText := "Ngarrka-jarra-rlu ka-pala-nyanu paka-rni"
    glossedTokens := [("Ngarrka-jarra-rlu", "man-DU-ERG"), ("ka-pala-nyanu", "IPFV-3DU.SBJ-RR"), ("paka-rni", "strike-NPST")]
    glossedWords := [⟨['N', 'g', 'a', 'r', 'r', 'k', 'a', '-', 'j', 'a', 'r', 'r', 'a', '-', 'r', 'l', 'u'], ['m', 'a', 'n', '-', 'D', 'U', '-', 'E', 'R', 'G'], [⟨['N', 'g', 'a', 'r', 'r', 'k', 'a'], ['m', 'a', 'n'], none⟩, ⟨['j', 'a', 'r', 'r', 'a'], ['D', 'U'], some '-'⟩, ⟨['r', 'l', 'u'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['k', 'a', '-', 'p', 'a', 'l', 'a', '-', 'n', 'y', 'a', 'n', 'u'], ['I', 'P', 'F', 'V', '-', '3', 'D', 'U', '.', 'S', 'B', 'J', '-', 'R', 'R'], [⟨['k', 'a'], ['I', 'P', 'F', 'V'], none⟩, ⟨['p', 'a', 'l', 'a'], ['3', 'D', 'U', '.', 'S', 'B', 'J'], some '-'⟩, ⟨['n', 'y', 'a', 'n', 'u'], ['R', 'R'], some '-'⟩]⟩, ⟨['p', 'a', 'k', 'a', '-', 'r', 'n', 'i'], ['s', 't', 'r', 'i', 'k', 'e', '-', 'N', 'P', 'S', 'T'], [⟨['p', 'a', 'k', 'a'], ['s', 't', 'r', 'i', 'k', 'e'], none⟩, ⟨['r', 'n', 'i'], ['N', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex19 : Datum :=
  { id := "nordlinger2023_ex19"
    source := ⟨"siloni-2008", "p. 453"⟩
    reportedIn := some ⟨"nordlinger-2023", "(19)"⟩
    language := "hung1274"
    primaryText := "János és Mari csókol-óz-t-ak"
    glossedTokens := [("János", "János"), ("és", "and"), ("Mari", "Mari"), ("csókol-óz-t-ak", "kiss-RECP-PST-3PL")]
    glossedWords := [⟨['J', 'á', 'n', 'o', 's'], ['J', 'á', 'n', 'o', 's'], [⟨['J', 'á', 'n', 'o', 's'], ['J', 'á', 'n', 'o', 's'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'i'], ['M', 'a', 'r', 'i'], [⟨['M', 'a', 'r', 'i'], ['M', 'a', 'r', 'i'], none⟩]⟩, ⟨['c', 's', 'ó', 'k', 'o', 'l', '-', 'ó', 'z', '-', 't', '-', 'a', 'k'], ['k', 'i', 's', 's', '-', 'R', 'E', 'C', 'P', '-', 'P', 'S', 'T', '-', '3', 'P', 'L'], [⟨['c', 's', 'ó', 'k', 'o', 'l'], ['k', 'i', 's', 's'], none⟩, ⟨['ó', 'z'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['t'], ['P', 'S', 'T'], some '-'⟩, ⟨['a', 'k'], ['3', 'P', 'L'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex20 : Datum :=
  { id := "nordlinger2023_ex20"
    source := ⟨"dalrymple-et-al-1994", "p. 146"⟩
    reportedIn := some ⟨"nordlinger-2023", "(20)"⟩
    language := "nyan1308"
    primaryText := "Mbiǐdzi zi-ku-mény-an-a"
    glossedTokens := [("Mbiǐdzi", "10zebras"), ("zi-ku-mény-an-a", "10SBJ-PRS-hit-RECP-FV")]
    glossedWords := [⟨['M', 'b', 'i', 'ǐ', 'd', 'z', 'i'], ['1', '0', 'z', 'e', 'b', 'r', 'a', 's'], [⟨['M', 'b', 'i', 'ǐ', 'd', 'z', 'i'], ['1', '0', 'z', 'e', 'b', 'r', 'a', 's'], none⟩]⟩, ⟨['z', 'i', '-', 'k', 'u', '-', 'm', 'é', 'n', 'y', '-', 'a', 'n', '-', 'a'], ['1', '0', 'S', 'B', 'J', '-', 'P', 'R', 'S', '-', 'h', 'i', 't', '-', 'R', 'E', 'C', 'P', '-', 'F', 'V'], [⟨['z', 'i'], ['1', '0', 'S', 'B', 'J'], none⟩, ⟨['k', 'u'], ['P', 'R', 'S'], some '-'⟩, ⟨['m', 'é', 'n', 'y'], ['h', 'i', 't'], some '-'⟩, ⟨['a', 'n'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['a'], ['F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex21 : Datum :=
  { id := "nordlinger2023_ex21"
    source := ⟨"maslova-2008", "p. 230"⟩
    reportedIn := some ⟨"nordlinger-2023", "(21)"⟩
    language := "tong1318"
    primaryText := "Joni ba-la-yand-ana amukaintu wakwe"
    glossedTokens := [("Joni", "John"), ("ba-la-yand-ana", "3PL-PRS-love-RECP"), ("amukaintu", "wife"), ("wakwe", "his")]
    glossedWords := [⟨['J', 'o', 'n', 'i'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'n', 'i'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['b', 'a', '-', 'l', 'a', '-', 'y', 'a', 'n', 'd', '-', 'a', 'n', 'a'], ['3', 'P', 'L', '-', 'P', 'R', 'S', '-', 'l', 'o', 'v', 'e', '-', 'R', 'E', 'C', 'P'], [⟨['b', 'a'], ['3', 'P', 'L'], none⟩, ⟨['l', 'a'], ['P', 'R', 'S'], some '-'⟩, ⟨['y', 'a', 'n', 'd'], ['l', 'o', 'v', 'e'], some '-'⟩, ⟨['a', 'n', 'a'], ['R', 'E', 'C', 'P'], some '-'⟩]⟩, ⟨['a', 'm', 'u', 'k', 'a', 'i', 'n', 't', 'u'], ['w', 'i', 'f', 'e'], [⟨['a', 'm', 'u', 'k', 'a', 'i', 'n', 't', 'u'], ['w', 'i', 'f', 'e'], none⟩]⟩, ⟨['w', 'a', 'k', 'w', 'e'], ['h', 'i', 's'], [⟨['w', 'a', 'k', 'w', 'e'], ['h', 'i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex25 : Datum :=
  { id := "nordlinger2023_ex25"
    source := ⟨"evans-et-al-2007", "p. 570"⟩
    reportedIn := some ⟨"nordlinger-2023", "(25)"⟩
    language := "thay1249"
    primaryText := "Parr-an peln ii waarin-rr"
    glossedTokens := [("Parr-an", "kid-ERG"), ("peln", "3PL(ERG)"), ("ii", "there"), ("waarin-rr", "chase-RECP.NPST")]
    glossedWords := [⟨['P', 'a', 'r', 'r', '-', 'a', 'n'], ['k', 'i', 'd', '-', 'E', 'R', 'G'], [⟨['P', 'a', 'r', 'r'], ['k', 'i', 'd'], none⟩, ⟨['a', 'n'], ['E', 'R', 'G'], some '-'⟩]⟩, ⟨['p', 'e', 'l', 'n'], ['3', 'P', 'L', '(', 'E', 'R', 'G', ')'], [⟨['p', 'e', 'l', 'n'], ['3', 'P', 'L', '(', 'E', 'R', 'G', ')'], none⟩]⟩, ⟨['i', 'i'], ['t', 'h', 'e', 'r', 'e'], [⟨['i', 'i'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['w', 'a', 'a', 'r', 'i', 'n', '-', 'r', 'r'], ['c', 'h', 'a', 's', 'e', '-', 'R', 'E', 'C', 'P', '.', 'N', 'P', 'S', 'T'], [⟨['w', 'a', 'a', 'r', 'i', 'n'], ['c', 'h', 'a', 's', 'e'], none⟩, ⟨['r', 'r'], ['R', 'E', 'C', 'P', '.', 'N', 'P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex26a : Datum :=
  { id := "nordlinger2023_ex26a"
    source := ⟨"evans-et-al-2007", "p. 575"⟩
    reportedIn := some ⟨"nordlinger-2023", "(26a)"⟩
    language := "ngal1292"
    primaryText := "Ka-h-ngarrinj-yidjnja-n"
    glossedTokens := [("Ka-h-ngarrinj-yidjnja-n", "3/1-ASS-hand-touch/hold-PRS")]
    glossedWords := [⟨['K', 'a', '-', 'h', '-', 'n', 'g', 'a', 'r', 'r', 'i', 'n', 'j', '-', 'y', 'i', 'd', 'j', 'n', 'j', 'a', '-', 'n'], ['3', '/', '1', '-', 'A', 'S', 'S', '-', 'h', 'a', 'n', 'd', '-', 't', 'o', 'u', 'c', 'h', '/', 'h', 'o', 'l', 'd', '-', 'P', 'R', 'S'], [⟨['K', 'a'], ['3', '/', '1'], none⟩, ⟨['h'], ['A', 'S', 'S'], some '-'⟩, ⟨['n', 'g', 'a', 'r', 'r', 'i', 'n', 'j'], ['h', 'a', 'n', 'd'], some '-'⟩, ⟨['y', 'i', 'd', 'j', 'n', 'j', 'a'], ['t', 'o', 'u', 'c', 'h', '/', 'h', 'o', 'l', 'd'], some '-'⟩, ⟨['n'], ['P', 'R', 'S'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "base")] }

def ex26b : Datum :=
  { id := "nordlinger2023_ex26b"
    source := ⟨"evans-et-al-2007", "p. 576"⟩
    reportedIn := some ⟨"nordlinger-2023", "(26b)"⟩
    language := "ngal1292"
    primaryText := "Ke-h-langû-yidjnja-rr-inj"
    glossedTokens := [("Ke-h-langû-yidjnja-rr-inj", "3DU.DISH.SBJ-ASS-hand-hold-RR-PST:PFV")]
    glossedWords := [⟨['K', 'e', '-', 'h', '-', 'l', 'a', 'n', 'g', 'û', '-', 'y', 'i', 'd', 'j', 'n', 'j', 'a', '-', 'r', 'r', '-', 'i', 'n', 'j'], ['3', 'D', 'U', '.', 'D', 'I', 'S', 'H', '.', 'S', 'B', 'J', '-', 'A', 'S', 'S', '-', 'h', 'a', 'n', 'd', '-', 'h', 'o', 'l', 'd', '-', 'R', 'R', '-', 'P', 'S', 'T', ':', 'P', 'F', 'V'], [⟨['K', 'e'], ['3', 'D', 'U', '.', 'D', 'I', 'S', 'H', '.', 'S', 'B', 'J'], none⟩, ⟨['h'], ['A', 'S', 'S'], some '-'⟩, ⟨['l', 'a', 'n', 'g', 'û'], ['h', 'a', 'n', 'd'], some '-'⟩, ⟨['y', 'i', 'd', 'j', 'n', 'j', 'a'], ['h', 'o', 'l', 'd'], some '-'⟩, ⟨['r', 'r'], ['R', 'R'], some '-'⟩, ⟨['i', 'n', 'j'], ['P', 'S', 'T', ':', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex27a : Datum :=
  { id := "nordlinger2023_ex27a"
    source := ⟨"dimitriadis-2008", "p. 388"⟩
    reportedIn := some ⟨"nordlinger-2023", "(27a)"⟩
    language := "mode1248"
    primaryText := "O Giannis kje i Maria filithikan"
    glossedTokens := [("O", "the"), ("Giannis", "John"), ("kje", "and"), ("i", "the"), ("Maria", "Maria"), ("filithikan", "kissed-RECP.PL")]
    glossedWords := [⟨['O'], ['t', 'h', 'e'], [⟨['O'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i', 's'], ['J', 'o', 'h', 'n'], [⟨['G', 'i', 'a', 'n', 'n', 'i', 's'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['k', 'j', 'e'], ['a', 'n', 'd'], [⟨['k', 'j', 'e'], ['a', 'n', 'd'], none⟩]⟩, ⟨['i'], ['t', 'h', 'e'], [⟨['i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['f', 'i', 'l', 'i', 't', 'h', 'i', 'k', 'a', 'n'], ['k', 'i', 's', 's', 'e', 'd', '-', 'R', 'E', 'C', 'P', '.', 'P', 'L'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex28 : Datum :=
  { id := "nordlinger2023_ex28"
    source := ⟨"nordlinger-2023", "(28)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jean et Marie se sont embrassés"
    glossedTokens := [("Jean", "John"), ("et", "and"), ("Marie", "Mary"), ("se", "RR"), ("sont", "be.3PL.PRS"), ("embrassés", "kissed.3PL")]
    glossedWords := [⟨['J', 'e', 'a', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'e', 'a', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['e', 't'], ['a', 'n', 'd'], [⟨['e', 't'], ['a', 'n', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['s', 'e'], ['R', 'R'], [⟨['s', 'e'], ['R', 'R'], none⟩]⟩, ⟨['s', 'o', 'n', 't'], ['b', 'e', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['s', 'o', 'n', 't'], ['b', 'e', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['e', 'm', 'b', 'r', 'a', 's', 's', 'é', 's'], ['k', 'i', 's', 's', 'e', 'd', '.', '3', 'P', 'L'], [⟨['e', 'm', 'b', 'r', 'a', 's', 's', 'é', 's'], ['k', 'i', 's', 's', 'e', 'd', '.', '3', 'P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex29 : Datum :=
  { id := "nordlinger2023_ex29"
    source := ⟨"siloni-2008", "p. 453"⟩
    reportedIn := some ⟨"nordlinger-2023", "(29)"⟩
    language := "czec1258"
    primaryText := "Dan a Petr se políbili"
    glossedTokens := [("Dan", "Dan"), ("a", "and"), ("Petr", "Petr"), ("se", "RR"), ("políbili", "kissed")]
    glossedWords := [⟨['D', 'a', 'n'], ['D', 'a', 'n'], [⟨['D', 'a', 'n'], ['D', 'a', 'n'], none⟩]⟩, ⟨['a'], ['a', 'n', 'd'], [⟨['a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], [⟨['P', 'e', 't', 'r'], ['P', 'e', 't', 'r'], none⟩]⟩, ⟨['s', 'e'], ['R', 'R'], [⟨['s', 'e'], ['R', 'R'], none⟩]⟩, ⟨['p', 'o', 'l', 'í', 'b', 'i', 'l', 'i'], ['k', 'i', 's', 's', 'e', 'd'], [⟨['p', 'o', 'l', 'í', 'b', 'i', 'l', 'i'], ['k', 'i', 's', 's', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex35a : Datum :=
  { id := "nordlinger2023_ex35a"
    source := ⟨"siloni-2008", "p. 455"⟩
    reportedIn := some ⟨"nordlinger-2023", "(35a)"⟩
    language := "stan1290"
    primaryText := "Pierre et Jean se sont vaincus à la finale"
    glossedTokens := [("Pierre", "Pierre"), ("et", "and"), ("Jean", "Jean"), ("se", "RR"), ("sont", "be.3PL.PRS"), ("vaincus", "defeated.3PL"), ("à", "LOC"), ("la", "the.F"), ("finale", "final")]
    glossedWords := [⟨['P', 'i', 'e', 'r', 'r', 'e'], ['P', 'i', 'e', 'r', 'r', 'e'], [⟨['P', 'i', 'e', 'r', 'r', 'e'], ['P', 'i', 'e', 'r', 'r', 'e'], none⟩]⟩, ⟨['e', 't'], ['a', 'n', 'd'], [⟨['e', 't'], ['a', 'n', 'd'], none⟩]⟩, ⟨['J', 'e', 'a', 'n'], ['J', 'e', 'a', 'n'], [⟨['J', 'e', 'a', 'n'], ['J', 'e', 'a', 'n'], none⟩]⟩, ⟨['s', 'e'], ['R', 'R'], [⟨['s', 'e'], ['R', 'R'], none⟩]⟩, ⟨['s', 'o', 'n', 't'], ['b', 'e', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], [⟨['s', 'o', 'n', 't'], ['b', 'e', '.', '3', 'P', 'L', '.', 'P', 'R', 'S'], none⟩]⟩, ⟨['v', 'a', 'i', 'n', 'c', 'u', 's'], ['d', 'e', 'f', 'e', 'a', 't', 'e', 'd', '.', '3', 'P', 'L'], [⟨['v', 'a', 'i', 'n', 'c', 'u', 's'], ['d', 'e', 'f', 'e', 'a', 't', 'e', 'd', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['à'], ['L', 'O', 'C'], [⟨['à'], ['L', 'O', 'C'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e', '.', 'F'], [⟨['l', 'a'], ['t', 'h', 'e', '.', 'F'], none⟩]⟩, ⟨['f', 'i', 'n', 'a', 'l', 'e'], ['f', 'i', 'n', 'a', 'l'], [⟨['f', 'i', 'n', 'a', 'l', 'e'], ['f', 'i', 'n', 'a', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "reciprocal")] }

def ex36 : Datum :=
  { id := "nordlinger2023_ex36"
    source := ⟨"dimitriadis-2008", "p. 388"⟩
    reportedIn := some ⟨"nordlinger-2023", "(36)"⟩
    language := "mode1248"
    primaryText := "O Giannis filithike me ti Maria"
    glossedTokens := [("O", "the"), ("Giannis", "John"), ("filithike", "kissed-RECP.SG"), ("me", "with"), ("ti", "the"), ("Maria", "Maria")]
    glossedWords := [⟨['O'], ['t', 'h', 'e'], [⟨['O'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i', 's'], ['J', 'o', 'h', 'n'], [⟨['G', 'i', 'a', 'n', 'n', 'i', 's'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['f', 'i', 'l', 'i', 't', 'h', 'i', 'k', 'e'], ['k', 'i', 's', 's', 'e', 'd', '-', 'R', 'E', 'C', 'P', '.', 'S', 'G'], []⟩, ⟨['m', 'e'], ['w', 'i', 't', 'h'], [⟨['m', 'e'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['t', 'i'], ['t', 'h', 'e'], [⟨['t', 'i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "discontinuous")] }

def ex37 : Datum :=
  { id := "nordlinger2023_ex37"
    source := ⟨"hurst-2012", "p. 5"⟩
    reportedIn := some ⟨"nordlinger-2023", "(37)"⟩
    language := "swah1253"
    primaryText := "Juma a-li-tekeny-an-a na Halima"
    glossedTokens := [("Juma", "Juma"), ("a-li-tekeny-an-a", "3SG.SBJ-PST-tickle-RECP-FV"), ("na", "COM"), ("Halima", "Halima")]
    glossedWords := [⟨['J', 'u', 'm', 'a'], ['J', 'u', 'm', 'a'], [⟨['J', 'u', 'm', 'a'], ['J', 'u', 'm', 'a'], none⟩]⟩, ⟨['a', '-', 'l', 'i', '-', 't', 'e', 'k', 'e', 'n', 'y', '-', 'a', 'n', '-', 'a'], ['3', 'S', 'G', '.', 'S', 'B', 'J', '-', 'P', 'S', 'T', '-', 't', 'i', 'c', 'k', 'l', 'e', '-', 'R', 'E', 'C', 'P', '-', 'F', 'V'], [⟨['a'], ['3', 'S', 'G', '.', 'S', 'B', 'J'], none⟩, ⟨['l', 'i'], ['P', 'S', 'T'], some '-'⟩, ⟨['t', 'e', 'k', 'e', 'n', 'y'], ['t', 'i', 'c', 'k', 'l', 'e'], some '-'⟩, ⟨['a', 'n'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['a'], ['F', 'V'], some '-'⟩]⟩, ⟨['n', 'a'], ['C', 'O', 'M'], [⟨['n', 'a'], ['C', 'O', 'M'], none⟩]⟩, ⟨['H', 'a', 'l', 'i', 'm', 'a'], ['H', 'a', 'l', 'i', 'm', 'a'], [⟨['H', 'a', 'l', 'i', 'm', 'a'], ['H', 'a', 'l', 'i', 'm', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "discontinuous")] }

def ex38 : Datum :=
  { id := "nordlinger2023_ex38"
    source := ⟨"dimitriadis-2008", "p. 393"⟩
    reportedIn := some ⟨"nordlinger-2023", "(38)"⟩
    language := "hung1274"
    primaryText := "János csókol-óz-ott Kati-val"
    glossedTokens := [("János", "John"), ("csókol-óz-ott", "kiss-RECP-PST"), ("Kati-val", "Kate-WITH")]
    glossedWords := [⟨['J', 'á', 'n', 'o', 's'], ['J', 'o', 'h', 'n'], [⟨['J', 'á', 'n', 'o', 's'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['c', 's', 'ó', 'k', 'o', 'l', '-', 'ó', 'z', '-', 'o', 't', 't'], ['k', 'i', 's', 's', '-', 'R', 'E', 'C', 'P', '-', 'P', 'S', 'T'], [⟨['c', 's', 'ó', 'k', 'o', 'l'], ['k', 'i', 's', 's'], none⟩, ⟨['ó', 'z'], ['R', 'E', 'C', 'P'], some '-'⟩, ⟨['o', 't', 't'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['K', 'a', 't', 'i', '-', 'v', 'a', 'l'], ['K', 'a', 't', 'e', '-', 'W', 'I', 'T', 'H'], [⟨['K', 'a', 't', 'i'], ['K', 'a', 't', 'e'], none⟩, ⟨['v', 'a', 'l'], ['W', 'I', 'T', 'H'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "discontinuous")] }

def ex39 : Datum :=
  { id := "nordlinger2023_ex39"
    source := ⟨"siloni-2008", "p. 474"⟩
    reportedIn := some ⟨"nordlinger-2023", "(39)"⟩
    language := "stan1290"
    primaryText := "Jean s'-est embrassé avec Marie"
    glossedTokens := [("Jean", "Jean"), ("s'-est", "RR-be.3SG.PRS"), ("embrassé", "kissed"), ("avec", "with"), ("Marie", "Marie")]
    glossedWords := [⟨['J', 'e', 'a', 'n'], ['J', 'e', 'a', 'n'], [⟨['J', 'e', 'a', 'n'], ['J', 'e', 'a', 'n'], none⟩]⟩, ⟨['s', '\'', '-', 'e', 's', 't'], ['R', 'R', '-', 'b', 'e', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], [⟨['s', '\''], ['R', 'R'], none⟩, ⟨['e', 's', 't'], ['b', 'e', '.', '3', 'S', 'G', '.', 'P', 'R', 'S'], some '-'⟩]⟩, ⟨['e', 'm', 'b', 'r', 'a', 's', 's', 'é'], ['k', 'i', 's', 's', 'e', 'd'], [⟨['e', 'm', 'b', 'r', 'a', 's', 's', 'é'], ['k', 'i', 's', 's', 'e', 'd'], none⟩]⟩, ⟨['a', 'v', 'e', 'c'], ['w', 'i', 't', 'h'], [⟨['a', 'v', 'e', 'c'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("construction", "discontinuous")] }

def all : List Datum := [ex5a, ex9, ex11, ex12, ex13, ex17a, ex18a, ex18b, ex19, ex20, ex21, ex25, ex26a, ex26b, ex27a, ex28, ex29, ex35a, ex36, ex37, ex38, ex39]

/-- The construction a row illustrates. -/
inductive Construction where
  /-- base: the nonreciprocal clause a reciprocal one is compared with -/
  | base
  /-- reciprocal: a reciprocal construction with the reciprocants in one argument -/
  | reciprocal
  /-- discontinuous: a reciprocal construction with the reciprocants split across the subject and a comitative phrase -/
  | discontinuous
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `construction`. -/
def construction (e : Datum) : Option Construction :=
  e.parse? "construction" [("base", .base), ("reciprocal", .reciprocal), ("discontinuous", .discontinuous)]

end Nordlinger2023.Examples
