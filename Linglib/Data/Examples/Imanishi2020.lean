module

public import Linglib.Data.Examples.Schema

/-!
# `Imanishi2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Imanishi2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Imanishi2020.Examples`.
-/

@[expose] public section

namespace Imanishi2020.Examples

def s1a : Datum :=
  { id := "imanishi2020_s1a"
    source := ⟨"imanishi-2020", "(1a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [ki-k'ul-ïk ak'wal-a']."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("ki-k'ul-ïk", "A3PL-meet-NMLZ"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['y'], ['i', 'n'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '1', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['k', 'i'], ['k', '\'', 'u', 'l'], ['ï', 'k']], [['A', '3', 'P', 'L'], ['m', 'e', 'e', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("alignment", "S/A = set B on ajin, O = set A on the nominalized verb")] }

def s1b : Datum :=
  { id := "imanishi2020_s1b"
    source := ⟨"imanishi-2020", "(1b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [atin-ïk]."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("atin-ïk", "bathe-NMLZ")]
    glossedWords := [⟨[['y'], ['i', 'n'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '1', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['a', 't', 'i', 'n'], ['ï', 'k']], [['b', 'a', 't', 'h', 'e'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("alignment", "S = set B on ajin, no set A on the nominalized verb")] }

def s2a : Datum :=
  { id := "imanishi2020_s2a"
    source := ⟨"imanishi-2020", "(2a)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-jats'-oñ]."
    glossedTokens := [("Choñkol-ø", "PROG-B3SG"), ("i-jats'-oñ", "A3SG-hit-B1SG")]
    glossedWords := [⟨[['C', 'h', 'o', 'ñ', 'k', 'o', 'l'], ['ø']], [['P', 'R', 'O', 'G'], ['B', '3', 'S', 'G']]⟩, ⟨[['i'], ['j', 'a', 't', 's', '\''], ['o', 'ñ']], [['A', '3', 'S', 'G'], ['h', 'i', 't'], ['B', '1', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Coon 2013a:11"), ("alignment", "A = set A, O = set B inside the nominalized clause")] }

def s2b : Datum :=
  { id := "imanishi2020_s2b"
    source := ⟨"imanishi-2020", "(2b)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-majl-el]."
    glossedTokens := [("Choñkol-ø", "PROG-B3SG"), ("i-majl-el", "A3SG-go-NMLZ")]
    glossedWords := [⟨[['C', 'h', 'o', 'ñ', 'k', 'o', 'l'], ['ø']], [['P', 'R', 'O', 'G'], ['B', '3', 'S', 'G']]⟩, ⟨[['i'], ['m', 'a', 'j', 'l'], ['e', 'l']], [['A', '3', 'S', 'G'], ['g', 'o'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Coon 2013a:11"), ("alignment", "S = set A")] }

def s3a : Datum :=
  { id := "imanishi2020_s3a"
    source := ⟨"imanishi-2020", "(3a)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [hach w-il-on-i]."
    glossedTokens := [("lanan-ø", "PROG-B3SG"), ("hach", "B2SG"), ("w-il-on-i", "A1SG-see-DM-INTR")]
    glossedWords := [⟨[['l', 'a', 'n', 'a', 'n'], ['ø']], [['P', 'R', 'O', 'G'], ['B', '3', 'S', 'G']]⟩, ⟨[['h', 'a', 'c', 'h']], [['B', '2', 'S', 'G']]⟩, ⟨[['w'], ['i', 'l'], ['o', 'n'], ['i']], [['A', '1', 'S', 'G'], ['s', 'e', 'e'], ['D', 'M'], ['I', 'N', 'T', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Mateo Pedro 2009"), ("alignment", "A = set A, O = set B, the suffix -on supplying object Case")] }

def s3b : Datum :=
  { id := "imanishi2020_s3b"
    source := ⟨"imanishi-2020", "(3b)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [ha-way-i]."
    glossedTokens := [("lanan-ø", "PROG-B3SG"), ("ha-way-i", "A2SG-sleep-INTR")]
    glossedWords := [⟨[['l', 'a', 'n', 'a', 'n'], ['ø']], [['P', 'R', 'O', 'G'], ['B', '3', 'S', 'G']]⟩, ⟨[['h', 'a'], ['w', 'a', 'y'], ['i']], [['A', '2', 'S', 'G'], ['s', 'l', 'e', 'e', 'p'], ['I', 'N', 'T', 'R']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("source", "Mateo Pedro 2009"), ("alignment", "S = set A")] }

def s62 : Datum :=
  { id := "imanishi2020_s62"
    source := ⟨"imanishi-2020", "(62)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i katastrofi tis polis apo tus varvarus mesa se tris meres"
    glossedTokens := [("i", "the"), ("katastrofi", "destruction"), ("tis", "the"), ("polis", "city-GEN"), ("apo", "by"), ("tus", "the"), ("varvarus", "barbarians"), ("mesa", "within"), ("se", ""), ("tris", "three"), ("meres", "days")]
    glossedWords := [⟨[['i']], [['t', 'h', 'e']]⟩, ⟨[['k', 'a', 't', 'a', 's', 't', 'r', 'o', 'f', 'i']], [['d', 'e', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n']]⟩, ⟨[['t', 'i', 's']], [['t', 'h', 'e']]⟩, ⟨[['p', 'o', 'l', 'i', 's']], [['c', 'i', 't', 'y'], ['G', 'E', 'N']]⟩, ⟨[['a', 'p', 'o']], [['b', 'y']]⟩, ⟨[['t', 'u', 's']], [['t', 'h', 'e']]⟩, ⟨[['v', 'a', 'r', 'v', 'a', 'r', 'u', 's']], [['b', 'a', 'r', 'b', 'a', 'r', 'i', 'a', 'n', 's']]⟩, ⟨[['m', 'e', 's', 'a']], [['w', 'i', 't', 'h', 'i', 'n']]⟩, ⟨[['s', 'e']], [[]]⟩, ⟨[['t', 'r', 'i', 's']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['m', 'e', 'r', 'e', 's']], [['d', 'a', 'y', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("source", "Alexiadou 2001:76"), ("nominalization", "process nominal without an external argument")] }

def s64 : Datum :=
  { id := "imanishi2020_s64"
    source := ⟨"imanishi-2020", "(64)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-k'at-ïk ri tinamït [ri x-ø-b'än/x-ø-u-b'än ri a Juan] x-ø-xib'i-n."
    glossedTokens := [("ri", "DET"), ("ru-k'at-ïk", "A3SG-burn-NMLZ"), ("ri", "DET"), ("tinamït", "city"), ("ri", "DET"), ("x-ø-b'än/x-ø-u-b'än", "PFV-B3SG-do/PFV-B3SG-A3SG-do"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PFV-B3SG-scare-ANTIP")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['r', 'u'], ['k', '\'', 'a', 't'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['b', 'u', 'r', 'n'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['t', 'i', 'n', 'a', 'm', 'ï', 't']], [['c', 'i', 't', 'y']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['x'], ['ø'], ['b', '\'', 'ä', 'n', '/', 'x'], ['ø'], ['u'], ['b', '\'', 'ä', 'n']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['d', 'o', '/', 'P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['d', 'o']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['x'], ['ø'], ['x', 'i', 'b', '\'', 'i'], ['n']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['s', 'c', 'a', 'r', 'e'], ['A', 'N', 'T', 'I', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "the external argument appears in a relative clause")] }

def s65 : Datum :=
  { id := "imanishi2020_s65"
    source := ⟨"imanishi-2020", "(65)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-k'at-ïk ri tinamït r-oma ri a Juan x-ø-xib'i-n."
    glossedTokens := [("ri", "DET"), ("ru-k'at-ïk", "A3SG-burn-NMLZ"), ("ri", "DET"), ("tinamït", "city"), ("r-oma", "A3SG-because.of"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PFV-B3SG-scare-ANTIP")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['r', 'u'], ['k', '\'', 'a', 't'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['b', 'u', 'r', 'n'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['t', 'i', 'n', 'a', 'm', 'ï', 't']], [['c', 'i', 't', 'y']]⟩, ⟨[['r'], ['o', 'm', 'a']], [['A', '3', 'S', 'G'], ['b', 'e', 'c', 'a', 'u', 's', 'e', '.', 'o', 'f']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['x'], ['ø'], ['x', 'i', 'b', '\'', 'i'], ['n']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['s', 'c', 'a', 'r', 'e'], ['A', 'N', 'T', 'I', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "the by-phrase counterpart is degraded")] }

def s66 : Datum :=
  { id := "imanishi2020_s66"
    source := ⟨"imanishi-2020", "(66)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "nu-ki-k'ul-ïk/ki-nu-k'ul-ïk ak'wal-a'"
    glossedTokens := [("nu-ki-k'ul-ïk/ki-nu-k'ul-ïk", "A1SG-A3PL-meet-NMLZ/A3PL-A1SG-meet-NMLZ"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['n', 'u'], ['k', 'i'], ['k', '\'', 'u', 'l'], ['ï', 'k', '/', 'k', 'i'], ['n', 'u'], ['k', '\'', 'u', 'l'], ['ï', 'k']], [['A', '1', 'S', 'G'], ['A', '3', 'P', 'L'], ['m', 'e', 'e', 't'], ['N', 'M', 'L', 'Z', '/', 'A', '3', 'P', 'L'], ['A', '1', 'S', 'G'], ['m', 'e', 'e', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "two set A markers impossible in either order")] }

def s67 : Datum :=
  { id := "imanishi2020_s67"
    source := ⟨"imanishi-2020", "(67)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ru-k'at-ïk ri a Juan x-ø-xib'i-n."
    glossedTokens := [("ru-k'at-ïk", "A3SG-burn-NMLZ"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PFV-B3SG-scare-ANTIP")]
    glossedWords := [⟨[['r', 'u'], ['k', '\'', 'a', 't'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['b', 'u', 'r', 'n'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['x'], ['ø'], ['x', 'i', 'b', '\'', 'i'], ['n']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['s', 'c', 'a', 'r', 'e'], ['A', 'N', 'T', 'I', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "a sole argument is the internal argument")] }

def s68a : Datum :=
  { id := "imanishi2020_s68a"
    source := ⟨"imanishi-2020", "(68a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "nu-b'iyïn-ïk"
    glossedTokens := [("nu-b'iyïn-ïk", "A1SG-walk-NMLZ")]
    glossedWords := [⟨[['n', 'u'], ['b', '\'', 'i', 'y', 'ï', 'n'], ['ï', 'k']], [['A', '1', 'S', 'G'], ['w', 'a', 'l', 'k'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "unergative nominalization excludes its external argument")] }

def s68b : Datum :=
  { id := "imanishi2020_s68b"
    source := ⟨"imanishi-2020", "(68b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ru-tzopin-ïk ri xta Maria"
    glossedTokens := [("ru-tzopin-ïk", "A3SG-jump-NMLZ"), ("ri", "DET"), ("xta", "CL"), ("Maria", "Maria")]
    glossedWords := [⟨[['r', 'u'], ['t', 'z', 'o', 'p', 'i', 'n'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['j', 'u', 'm', 'p'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['x', 't', 'a']], [['C', 'L']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "unergative nominalization excludes its external argument")] }

def s69 : Datum :=
  { id := "imanishi2020_s69"
    source := ⟨"imanishi-2020", "(69)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-tzaq-ïk ri a Juan ütz."
    glossedTokens := [("ri", "DET"), ("ru-tzaq-ïk", "A3SG-fall-NMLZ"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("ütz", "good")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['r', 'u'], ['t', 'z', 'a', 'q'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['f', 'a', 'l', 'l'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['ü', 't', 'z']], [['g', 'o', 'o', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("nominalization", "unaccusative nominalized in subject position; the internal argument takes genitive")] }

def s70 : Datum :=
  { id := "imanishi2020_s70"
    source := ⟨"imanishi-2020", "(70)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Mach uts'aty [a-jats'-oñ]."
    glossedTokens := [("Mach", "NEG"), ("uts'aty", "good"), ("a-jats'-oñ", "A2SG-hit-B1SG")]
    glossedWords := [⟨[['M', 'a', 'c', 'h']], [['N', 'E', 'G']]⟩, ⟨[['u', 't', 's', '\'', 'a', 't', 'y']], [['g', 'o', 'o', 'd']]⟩, ⟨[['a'], ['j', 'a', 't', 's', '\''], ['o', 'ñ']], [['A', '2', 'S', 'G'], ['h', 'i', 't'], ['B', '1', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("source", "Coon 2013a:141"), ("nominalization", "external and internal argument both inside")] }

def s71 : Datum :=
  { id := "imanishi2020_s71"
    source := ⟨"imanishi-2020", "(71)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "[h-il-on ø] kawal watx'."
    glossedTokens := [("h-il-on", "A2SG-see-DM"), ("ø", "B3SG"), ("kawal", "very"), ("watx'", "good")]
    glossedWords := [⟨[['h'], ['i', 'l'], ['o', 'n']], [['A', '2', 'S', 'G'], ['s', 'e', 'e'], ['D', 'M']]⟩, ⟨[['ø']], [['B', '3', 'S', 'G']]⟩, ⟨[['k', 'a', 'w', 'a', 'l']], [['v', 'e', 'r', 'y']]⟩, ⟨[['w', 'a', 't', 'x', '\'']], [['g', 'o', 'o', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("source", "p.c. Pedro Mateo Pedro"), ("nominalization", "external argument inside the nominalized clause")] }

def s76a : Datum :=
  { id := "imanishi2020_s76a"
    source := ⟨"imanishi-2020", "(76a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-in-k'ul oxi' ak'wal-a'."
    glossedTokens := [("x-ø-in-k'ul", "PFV-B3SG-A1SG-meet"), ("oxi'", "three"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['x'], ['ø'], ['i', 'n'], ['k', '\'', 'u', 'l']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'S', 'G'], ['m', 'e', 'e', 't']]⟩, ⟨[['o', 'x', 'i', '\'']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "active root transitive")] }

def s76b : Datum :=
  { id := "imanishi2020_s76b"
    source := ⟨"imanishi-2020", "(76b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "oxi' ak'wal-a' x-e-k'ul r-oma ri Ana."
    glossedTokens := [("oxi'", "three"), ("ak'wal-a'", "child-PL"), ("x-e-k'ul", "PFV-B3PL-meet"), ("r-oma", "A3SG-because.of"), ("ri", "DET"), ("Ana", "Ana")]
    glossedWords := [⟨[['o', 'x', 'i', '\'']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩, ⟨[['x'], ['e'], ['k', '\'', 'u', 'l']], [['P', 'F', 'V'], ['B', '3', 'P', 'L'], ['m', 'e', 'e', 't']]⟩, ⟨[['r'], ['o', 'm', 'a']], [['A', '3', 'S', 'G'], ['b', 'e', 'c', 'a', 'u', 's', 'e', '.', 'o', 'f']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['A', 'n', 'a']], [['A', 'n', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive root transitive without overt passive morphology")] }

def s78a : Datum :=
  { id := "imanishi2020_s78a"
    source := ⟨"imanishi-2020", "(78a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-e-qa-tïk k'iy k'otz'i'j pa jardin."
    glossedTokens := [("röj", "we"), ("x-e-qa-tïk", "PFV-B3PL-A1PL-plant"), ("k'iy", "many"), ("k'otz'i'j", "flower"), ("pa", "PREP"), ("jardin", "garden")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['x'], ['e'], ['q', 'a'], ['t', 'ï', 'k']], [['P', 'F', 'V'], ['B', '3', 'P', 'L'], ['A', '1', 'P', 'L'], ['p', 'l', 'a', 'n', 't']]⟩, ⟨[['k', '\'', 'i', 'y']], [['m', 'a', 'n', 'y']]⟩, ⟨[['k', '\'', 'o', 't', 'z', '\'', 'i', '\'', 'j']], [['f', 'l', 'o', 'w', 'e', 'r']]⟩, ⟨[['p', 'a']], [['P', 'R', 'E', 'P']]⟩, ⟨[['j', 'a', 'r', 'd', 'i', 'n']], [['g', 'a', 'r', 'd', 'e', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "active, lax vowel")] }

def s78b : Datum :=
  { id := "imanishi2020_s78b"
    source := ⟨"imanishi-2020", "(78b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "k'iy k'otz'i'j x-e-tik pa jardin."
    glossedTokens := [("k'iy", "many"), ("k'otz'i'j", "flower"), ("x-e-tik", "PFV-B3PL-plant.PASS"), ("pa", "PREP"), ("jardin", "garden")]
    glossedWords := [⟨[['k', '\'', 'i', 'y']], [['m', 'a', 'n', 'y']]⟩, ⟨[['k', '\'', 'o', 't', 'z', '\'', 'i', '\'', 'j']], [['f', 'l', 'o', 'w', 'e', 'r']]⟩, ⟨[['x'], ['e'], ['t', 'i', 'k']], [['P', 'F', 'V'], ['B', '3', 'P', 'L'], ['p', 'l', 'a', 'n', 't', '.', 'P', 'A', 'S', 'S']]⟩, ⟨[['p', 'a']], [['P', 'R', 'E', 'P']]⟩, ⟨[['j', 'a', 'r', 'd', 'i', 'n']], [['g', 'a', 'r', 'd', 'e', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive, tensed vowel")] }

def s80a : Datum :=
  { id := "imanishi2020_s80a"
    source := ⟨"imanishi-2020", "(80a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-ø-qa-chäp ru-tik-ïk jun k'otz'i'j."
    glossedTokens := [("röj", "we"), ("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ru-tik-ïk", "A3SG-plant.PASS-NMLZ"), ("jun", "one"), ("k'otz'i'j", "flower")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'u'], ['t', 'i', 'k'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['p', 'l', 'a', 'n', 't', '.', 'P', 'A', 'S', 'S'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['j', 'u', 'n']], [['o', 'n', 'e']]⟩, ⟨[['k', '\'', 'o', 't', 'z', '\'', 'i', '\'', 'j']], [['f', 'l', 'o', 'w', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "tensed vowel: the nominalized verb is passivized")] }

def s80b : Datum :=
  { id := "imanishi2020_s80b"
    source := ⟨"imanishi-2020", "(80b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-oj-ajin che ru-tik-ïk jun k'otz'i'j."
    glossedTokens := [("y-oj-ajin", "IPFV-B1PL-PROG"), ("che", "PREP"), ("ru-tik-ïk", "A3SG-plant.PASS-NMLZ"), ("jun", "one"), ("k'otz'i'j", "flower")]
    glossedWords := [⟨[['y'], ['o', 'j'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '1', 'P', 'L'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['r', 'u'], ['t', 'i', 'k'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['p', 'l', 'a', 'n', 't', '.', 'P', 'A', 'S', 'S'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['j', 'u', 'n']], [['o', 'n', 'e']]⟩, ⟨[['k', '\'', 'o', 't', 'z', '\'', 'i', '\'', 'j']], [['f', 'l', 'o', 'w', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "tensed vowel: the nominalized verb is passivized")] }

def s82a : Datum :=
  { id := "imanishi2020_s82a"
    source := ⟨"imanishi-2020", "(82a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-e-qa-q'ete-j ri ak'wal-a'."
    glossedTokens := [("röj", "we"), ("x-e-qa-q'ete-j", "PFV-B3PL-A1PL-hug-TR"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['x'], ['e'], ['q', 'a'], ['q', '\'', 'e', 't', 'e'], ['j']], [['P', 'F', 'V'], ['B', '3', 'P', 'L'], ['A', '1', 'P', 'L'], ['h', 'u', 'g'], ['T', 'R']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "active derived transitive")] }

def s82b : Datum :=
  { id := "imanishi2020_s82b"
    source := ⟨"imanishi-2020", "(82b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ak'wal-a' x-e-q'ete-x."
    glossedTokens := [("ri", "DET"), ("ak'wal-a'", "child-PL"), ("x-e-q'ete-x", "PFV-B3PL-hug-PASS")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩, ⟨[['x'], ['e'], ['q', '\'', 'e', 't', 'e'], ['x']], [['P', 'F', 'V'], ['B', '3', 'P', 'L'], ['h', 'u', 'g'], ['P', 'A', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive suffix -x replaces -j")] }

def s83a : Datum :=
  { id := "imanishi2020_s83a"
    source := ⟨"imanishi-2020", "(83a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-ø-qa-chäp ki-q'ete-x-ïk ri ak'wal-a'."
    glossedTokens := [("röj", "we"), ("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ki-q'ete-x-ïk", "A3PL-hug-PASS-NMLZ"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['k', 'i'], ['q', '\'', 'e', 't', 'e'], ['x'], ['ï', 'k']], [['A', '3', 'P', 'L'], ['h', 'u', 'g'], ['P', 'A', 'S', 'S'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive morpheme under nominalization")] }

def s83b : Datum :=
  { id := "imanishi2020_s83b"
    source := ⟨"imanishi-2020", "(83b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj y-oj-ajin che ki-q'ete-x-ïk ri ak'wal-a'."
    glossedTokens := [("röj", "we"), ("y-oj-ajin", "IPFV-B1PL-PROG"), ("che", "PREP"), ("ki-q'ete-x-ïk", "A3PL-hug-PASS-NMLZ"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['y'], ['o', 'j'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '1', 'P', 'L'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['k', 'i'], ['q', '\'', 'e', 't', 'e'], ['x'], ['ï', 'k']], [['A', '3', 'P', 'L'], ['h', 'u', 'g'], ['P', 'A', 'S', 'S'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("voice", "passive morpheme under nominalization")] }

def s85 : Datum :=
  { id := "imanishi2020_s85"
    source := ⟨"imanishi-2020", "(85)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ixöq n-ø-ajin [che ki-k'ul-ïk ak'wal-a']."
    glossedTokens := [("ri", "DET"), ("ixöq", "woman"), ("n-ø-ajin", "IPFV-B3SG-PROG"), ("che", "PREP"), ("ki-k'ul-ïk", "A3PL-meet-NMLZ"), ("ak'wal-a'", "child-PL")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['i', 'x', 'ö', 'q']], [['w', 'o', 'm', 'a', 'n']]⟩, ⟨[['n'], ['ø'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '3', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['k', 'i'], ['k', '\'', 'u', 'l'], ['ï', 'k']], [['A', '3', 'P', 'L'], ['m', 'e', 'e', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l'], ['a', '\'']], [['c', 'h', 'i', 'l', 'd'], ['P', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("derivation", "object genitive from D, subject absolutive from the matrix Infl")] }

def s90 : Datum :=
  { id := "imanishi2020_s90"
    source := ⟨"imanishi-2020", "(90)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che jun b'ix."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("jun", "INDF"), ("b'ix", "song")]
    glossedWords := [⟨[['y'], ['i', 'n'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '1', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['j', 'u', 'n']], [['I', 'N', 'D', 'F']]⟩, ⟨[['b', '\'', 'i', 'x']], [['s', 'o', 'n', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("theta", "ajin assigns an agentive θ-role to its subject")] }

def s91 : Datum :=
  { id := "imanishi2020_s91"
    source := ⟨"imanishi-2020", "(91)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [atin-ïk]."
    glossedTokens := [("y-in-ajin", "IPFV-B1SG-PROG"), ("che", "PREP"), ("atin-ïk", "bathe-NMLZ")]
    glossedWords := [⟨[['y'], ['i', 'n'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '1', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['a', 't', 'i', 'n'], ['ï', 'k']], [['b', 'a', 't', 'h', 'e'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("derivation", "unergative base: no DP inside, no genitive")] }

def s92 : Datum :=
  { id := "imanishi2020_s92"
    source := ⟨"imanishi-2020", "(92)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri a Juan n-ø-ajin che (ru-)tzaq-ïk."
    glossedTokens := [("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("n-ø-ajin", "IPFV-B3SG-PROG"), ("che", "PREP"), ("(ru-)tzaq-ïk", "(A3SG-)fall-NMLZ")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['n'], ['ø'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '3', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['r', 'u'], ['t', 'z', 'a', 'q'], ['ï', 'k']], [['(', 'A', '3', 'S', 'G'], [')', 'f', 'a', 'l', 'l'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "unaccusative base resists nominalization under ajin")] }

def s93a : Datum :=
  { id := "imanishi2020_s93a"
    source := ⟨"imanishi-2020", "(93a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri a Juan n-ø-ajin n-ø-tzaq."
    glossedTokens := [("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("n-ø-ajin", "IPFV-B3SG-PROG"), ("n-ø-tzaq", "IPFV-B3SG-fall")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['n'], ['ø'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '3', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['n'], ['ø'], ['t', 'z', 'a', 'q']], [['I', 'P', 'F', 'V'], ['B', '3', 'S', 'G'], ['f', 'a', 'l', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "the unaccusative appears as a finite verb under ajin")] }

def s93b : Datum :=
  { id := "imanishi2020_s93b"
    source := ⟨"imanishi-2020", "(93b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri a Juan n-ø-tzaq."
    glossedTokens := [("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("n-ø-tzaq", "IPFV-B3SG-fall")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['n'], ['ø'], ['t', 'z', 'a', 'q']], [['I', 'P', 'F', 'V'], ['B', '3', 'S', 'G'], ['f', 'a', 'l', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "simple imperfective")] }

def s94 : Datum :=
  { id := "imanishi2020_s94"
    source := ⟨"imanishi-2020", "(94)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri wäy y-e-ajin che (ru/ki)-chaq'irse-x-ïk."
    glossedTokens := [("ri", "DET"), ("wäy", "tortilla"), ("y-e-ajin", "IPFV-B3PL-PROG"), ("che", "PREP"), ("(ru/ki)-chaq'irse-x-ïk", "A3SG/A3PL-dry-PASS-NMLZ")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩, ⟨[['y'], ['e'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '3', 'P', 'L'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['r', 'u', '/', 'k', 'i'], ['c', 'h', 'a', 'q', '\'', 'i', 'r', 's', 'e'], ['x'], ['ï', 'k']], [['A', '3', 'S', 'G', '/', 'A', '3', 'P', 'L'], ['d', 'r', 'y'], ['P', 'A', 'S', 'S'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "passive base resists nominalization under ajin")] }

def s95 : Datum :=
  { id := "imanishi2020_s95"
    source := ⟨"imanishi-2020", "(95)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri wäy y-e-chaq'irse-x."
    glossedTokens := [("ri", "DET"), ("wäy", "tortilla"), ("y-e-chaq'irse-x", "IPFV-B3PL-dry-PASS")]
    glossedWords := [⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩, ⟨[['y'], ['e'], ['c', 'h', 'a', 'q', '\'', 'i', 'r', 's', 'e'], ['x']], [['I', 'P', 'F', 'V'], ['B', '3', 'P', 'L'], ['d', 'r', 'y'], ['P', 'A', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("control", "simple imperfective passive")] }

def s96a : Datum :=
  { id := "imanishi2020_s96a"
    source := ⟨"imanishi-2020", "(96a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was engaged in falling."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("source", "Coon 2010a:104"), ("control", "engage in resists an unaccusative gerund")] }

def s96b : Datum :=
  { id := "imanishi2020_s96b"
    source := ⟨"imanishi-2020", "(96b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was engaged in being attacked."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("source", "Coon 2010a:104"), ("control", "engage in resists a passive gerund")] }

def s97 : Datum :=
  { id := "imanishi2020_s97"
    source := ⟨"imanishi-2020", "(97)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "n-ø-ajin jun nimaq'ij."
    glossedTokens := [("n-ø-ajin", "IPFV-B3SG-PROG"), ("jun", "INDF"), ("nimaq'ij", "celebration/festival")]
    glossedWords := [⟨[['n'], ['ø'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '3', 'S', 'G'], ['P', 'R', 'O', 'G']]⟩, ⟨[['j', 'u', 'n']], [['I', 'N', 'D', 'F']]⟩, ⟨[['n', 'i', 'm', 'a', 'q', '\'', 'i', 'j']], [['c', 'e', 'l', 'e', 'b', 'r', 'a', 't', 'i', 'o', 'n', '/', 'f', 'e', 's', 't', 'i', 'v', 'a', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("source", "Macario et al. 1998"), ("case", "no preposition when a single DP takes absolutive from Infl")] }

def s98a : Datum :=
  { id := "imanishi2020_s98a"
    source := ⟨"imanishi-2020", "(98a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj x-ø-qa-chäp [ki-k'ul-ïk rje']."
    glossedTokens := [("röj", "we"), ("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ki-k'ul-ïk", "A3PL-meet-NMLZ"), ("rje'", "they")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['k', 'i'], ['k', '\'', 'u', 'l'], ['ï', 'k']], [['A', '3', 'P', 'L'], ['m', 'e', 'e', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'j', 'e', '\'']], [['t', 'h', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("alignment", "subject inherent ergative from transitive v, object genitive: both set A")] }

def s98b : Datum :=
  { id := "imanishi2020_s98b"
    source := ⟨"imanishi-2020", "(98b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "rat x-ø-a-chäp [atin-ïk]."
    glossedTokens := [("rat", "you"), ("x-ø-a-chäp", "PFV-B3SG-A2SG-begin"), ("atin-ïk", "bathe-NMLZ")]
    glossedWords := [⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩, ⟨[['x'], ['ø'], ['a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['a', 't', 'i', 'n'], ['ï', 'k']], [['b', 'a', 't', 'h', 'e'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("alignment", "subject set A on chäp, no genitive inside")] }

def s100 : Datum :=
  { id := "imanishi2020_s100"
    source := ⟨"imanishi-2020", "(100)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "x-ø-u-chäp [q'et-e-n-ik] r-ichin ri ak'wal."
    glossedTokens := [("x-ø-u-chäp", "PFV-B3SG-A3SG-begin"), ("q'et-e-n-ik", "hug-BV-ANTIP-NMLZ"), ("r-ichin", "A3SG-RN"), ("ri", "DET"), ("ak'wal", "child")]
    glossedWords := [⟨[['x'], ['ø'], ['u'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['q', '\'', 'e', 't'], ['e'], ['n'], ['i', 'k']], [['h', 'u', 'g'], ['B', 'V'], ['A', 'N', 'T', 'I', 'P'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r'], ['i', 'c', 'h', 'i', 'n']], [['A', '3', 'S', 'G'], ['R', 'N']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a', 'k', '\'', 'w', 'a', 'l']], [['c', 'h', 'i', 'l', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("source", "García Matzar and Rodríguez Guaján 1997:457"), ("strategy", "antipassive: object oblique under the relational noun")] }

def s102 : Datum :=
  { id := "imanishi2020_s102"
    source := ⟨"imanishi-2020", "(102)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "röj y-oj-ajin che [choy-oj che']."
    glossedTokens := [("röj", "we"), ("y-oj-ajin", "IPFV-B1PL-PROG"), ("che", "PREP"), ("choy-oj", "cut-NMLZ"), ("che'", "tree")]
    glossedWords := [⟨[['r', 'ö', 'j']], [['w', 'e']]⟩, ⟨[['y'], ['o', 'j'], ['a', 'j', 'i', 'n']], [['I', 'P', 'F', 'V'], ['B', '1', 'P', 'L'], ['P', 'R', 'O', 'G']]⟩, ⟨[['c', 'h', 'e']], [['P', 'R', 'E', 'P']]⟩, ⟨[['c', 'h', 'o', 'y'], ['o', 'j']], [['c', 'u', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['c', 'h', 'e', '\'']], [['t', 'r', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("strategy", "incorporating -oj nominalization, no set A")] }

def s103 : Datum :=
  { id := "imanishi2020_s103"
    source := ⟨"imanishi-2020", "(103)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp (ri) [choy-oj che']."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("(ri)", "DET"), ("choy-oj", "cut-NMLZ"), ("che'", "tree")]
    glossedWords := [⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['c', 'h', 'o', 'y'], ['o', 'j']], [['c', 'u', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['c', 'h', 'e', '\'']], [['t', 'r', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("strategy", "incorporating -oj nominalization under chäp")] }

def s104 : Datum :=
  { id := "imanishi2020_s104"
    source := ⟨"imanishi-2020", "(104)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ru/ki-choy-oj che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ru/ki-choy-oj", "A3SG/A3PL-cut-NMLZ"), ("che'", "tree")]
    glossedWords := [⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'u', '/', 'k', 'i'], ['c', 'h', 'o', 'y'], ['o', 'j']], [['A', '3', 'S', 'G', '/', 'A', '3', 'P', 'L'], ['c', 'u', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['c', 'h', 'e', '\'']], [['t', 'r', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("strategy", "set A impossible on the -oj nominalization")] }

def s107 : Datum :=
  { id := "imanishi2020_s107"
    source := ⟨"imanishi-2020", "(107)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ri choy-oj ri che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ri", "DET"), ("choy-oj", "cut-NMLZ"), ("ri", "DET"), ("che'", "tree")]
    glossedWords := [⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['c', 'h', 'o', 'y'], ['o', 'j']], [['c', 'u', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['c', 'h', 'e', '\'']], [['t', 'r', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "a determiner-marked object cannot be incorporated")] }

def s109 : Datum :=
  { id := "imanishi2020_s109"
    source := ⟨"imanishi-2020", "(109)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ri choy-oj oxi' che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ri", "DET"), ("choy-oj", "cut-NMLZ"), ("oxi'", "three"), ("che'", "tree")]
    glossedWords := [⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['c', 'h', 'o', 'y'], ['o', 'j']], [['c', 'u', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['o', 'x', 'i', '\'']], [['t', 'h', 'r', 'e', 'e']]⟩, ⟨[['c', 'h', 'e', '\'']], [['t', 'r', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "a numeral-marked object cannot be incorporated")] }

def s112 : Datum :=
  { id := "imanishi2020_s112"
    source := ⟨"imanishi-2020", "(112)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "x-ø-qa-chäp ri choy-oj a-che'."
    glossedTokens := [("x-ø-qa-chäp", "PFV-B3SG-A1PL-begin"), ("ri", "DET"), ("choy-oj", "cut-NMLZ"), ("a-che'", "A2SG-tree")]
    glossedWords := [⟨[['x'], ['ø'], ['q', 'a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '1', 'P', 'L'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['c', 'h', 'o', 'y'], ['o', 'j']], [['c', 'u', 't'], ['N', 'M', 'L', 'Z']]⟩, ⟨[['a'], ['c', 'h', 'e', '\'']], [['A', '2', 'S', 'G'], ['t', 'r', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "a possessed object cannot be incorporated")] }

def s113 : Datum :=
  { id := "imanishi2020_s113"
    source := ⟨"imanishi-2020", "(113)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "achike x-ø-a-chäp (ri) choy-oj?"
    glossedTokens := [("achike", "what"), ("x-ø-a-chäp", "PFV-B3SG-A2SG-begin"), ("(ri)", "DET"), ("choy-oj", "cut-NMLZ")]
    glossedWords := [⟨[['a', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'a', 't']]⟩, ⟨[['x'], ['ø'], ['a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['c', 'h', 'o', 'y'], ['o', 'j']], [['c', 'u', 't'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "no wh-extraction of the incorporated object")] }

def s114 : Datum :=
  { id := "imanishi2020_s114"
    source := ⟨"imanishi-2020", "(114)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "achike x-ø-a-chäp ru-ch'ey-ïk?"
    glossedTokens := [("achike", "what"), ("x-ø-a-chäp", "PFV-B3SG-A2SG-begin"), ("ru-ch'ey-ïk", "A3SG-hit-NMLZ")]
    glossedWords := [⟨[['a', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'a', 't']]⟩, ⟨[['x'], ['ø'], ['a'], ['c', 'h', 'ä', 'p']], [['P', 'F', 'V'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['b', 'e', 'g', 'i', 'n']]⟩, ⟨[['r', 'u'], ['c', 'h', '\'', 'e', 'y'], ['ï', 'k']], [['A', '3', 'S', 'G'], ['h', 'i', 't'], ['N', 'M', 'L', 'Z']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.2"), ("incorporation", "wh-extraction from the -ïk nominalization")] }

def all : List Datum := [s1a, s1b, s2a, s2b, s3a, s3b, s62, s64, s65, s66, s67, s68a, s68b, s69, s70, s71, s76a, s76b, s78a, s78b, s80a, s80b, s82a, s82b, s83a, s83b, s85, s90, s91, s92, s93a, s93b, s94, s95, s96a, s96b, s97, s98a, s98b, s100, s102, s103, s104, s107, s109, s112, s113, s114]

end Imanishi2020.Examples
