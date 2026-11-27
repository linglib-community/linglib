module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Newman2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Newman2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Newman2024.Examples`.
-/

@[expose] public section

namespace Newman2024.Examples

def ex_50 : Datum :=
  { id := "newman2024_50"
    source := ⟨"coon-mateo-pedro-preminger-2014", "(12a)"⟩
    reportedIn := some ⟨"newman-2024", "(50)"⟩
    language := "qanj1241"
    primaryText := "Max-ach y-il-a'."
    glossedTokens := [("Max-ach", "PFV-B2SG"), ("y-il-a'", "A3SG-see-TV")]
    glossedWords := [⟨['M', 'a', 'x', '-', 'a', 'c', 'h'], ['P', 'F', 'V', '-', 'B', '2', 'S', 'G'], [⟨['M', 'a', 'x'], ['P', 'F', 'V'], none⟩, ⟨['a', 'c', 'h'], ['B', '2', 'S', 'G'], some '-'⟩]⟩, ⟨['y', '-', 'i', 'l', '-', 'a', '\''], ['A', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'T', 'V'], [⟨['y'], ['A', '3', 'S', 'G'], none⟩, ⟨['i', 'l'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', '\''], ['T', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("fronting", "none"), ("object", "dp")] }

def ex_51 : Datum :=
  { id := "newman2024_51"
    source := ⟨"coon-mateo-pedro-preminger-2014", "(21b)"⟩
    reportedIn := some ⟨"newman-2024", "(51)"⟩
    language := "qanj1241"
    primaryText := "Maktxel max y-il[-a'] naq winaq?"
    glossedTokens := [("Maktxel", "who"), ("max", "PFV"), ("y-il[-a']", "A3SG-see-TV"), ("naq", "CLF"), ("winaq", "man")]
    glossedWords := [⟨['M', 'a', 'k', 't', 'x', 'e', 'l'], ['w', 'h', 'o'], [⟨['M', 'a', 'k', 't', 'x', 'e', 'l'], ['w', 'h', 'o'], none⟩]⟩, ⟨['m', 'a', 'x'], ['P', 'F', 'V'], [⟨['m', 'a', 'x'], ['P', 'F', 'V'], none⟩]⟩, ⟨['y', '-', 'i', 'l', '[', '-', 'a', '\'', ']'], ['A', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'T', 'V'], [⟨['y'], ['A', '3', 'S', 'G'], none⟩, ⟨['i', 'l'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', '\''], ['T', 'V'], some '-'⟩]⟩, ⟨['n', 'a', 'q'], ['C', 'L', 'F'], [⟨['n', 'a', 'q'], ['C', 'L', 'F'], none⟩]⟩, ⟨['w', 'i', 'n', 'a', 'q'], ['m', 'a', 'n'], [⟨['w', 'i', 'n', 'a', 'q'], ['m', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("fronting", "object"), ("object", "dp")] }

def ex_52 : Datum :=
  { id := "newman2024_52"
    source := ⟨"coon-mateo-pedro-preminger-2014", "(1)"⟩
    reportedIn := some ⟨"newman-2024", "(52)"⟩
    language := "qanj1241"
    primaryText := "Maktxel max-ach il-on-i?"
    glossedTokens := [("Maktxel", "who"), ("max-ach", "PFV-B2SG"), ("il-on-i", "see-AF-ITV")]
    glossedWords := [⟨['M', 'a', 'k', 't', 'x', 'e', 'l'], ['w', 'h', 'o'], [⟨['M', 'a', 'k', 't', 'x', 'e', 'l'], ['w', 'h', 'o'], none⟩]⟩, ⟨['m', 'a', 'x', '-', 'a', 'c', 'h'], ['P', 'F', 'V', '-', 'B', '2', 'S', 'G'], [⟨['m', 'a', 'x'], ['P', 'F', 'V'], none⟩, ⟨['a', 'c', 'h'], ['B', '2', 'S', 'G'], some '-'⟩]⟩, ⟨['i', 'l', '-', 'o', 'n', '-', 'i'], ['s', 'e', 'e', '-', 'A', 'F', '-', 'I', 'T', 'V'], [⟨['i', 'l'], ['s', 'e', 'e'], none⟩, ⟨['o', 'n'], ['A', 'F'], some '-'⟩, ⟨['i'], ['I', 'T', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("fronting", "subject"), ("object", "dp")] }

def ex_53 : Datum :=
  { id := "newman2024_53"
    source := ⟨"coon-mateo-pedro-preminger-2014", "(21c)"⟩
    reportedIn := some ⟨"newman-2024", "(53)"⟩
    language := "qanj1241"
    primaryText := "Maktxel max y-il[-a'] ix ix?"
    glossedTokens := [("Maktxel", "who"), ("max", "PFV"), ("y-il[-a']", "A3SG-see-TV"), ("ix", "CLF"), ("ix", "woman")]
    glossedWords := [⟨['M', 'a', 'k', 't', 'x', 'e', 'l'], ['w', 'h', 'o'], [⟨['M', 'a', 'k', 't', 'x', 'e', 'l'], ['w', 'h', 'o'], none⟩]⟩, ⟨['m', 'a', 'x'], ['P', 'F', 'V'], [⟨['m', 'a', 'x'], ['P', 'F', 'V'], none⟩]⟩, ⟨['y', '-', 'i', 'l', '[', '-', 'a', '\'', ']'], ['A', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'T', 'V'], [⟨['y'], ['A', '3', 'S', 'G'], none⟩, ⟨['i', 'l'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', '\''], ['T', 'V'], some '-'⟩]⟩, ⟨['i', 'x'], ['C', 'L', 'F'], [⟨['i', 'x'], ['C', 'L', 'F'], none⟩]⟩, ⟨['i', 'x'], ['w', 'o', 'm', 'a', 'n'], [⟨['i', 'x'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("fronting", "subject"), ("object", "dp")] }

def ex_92 : Datum :=
  { id := "newman2024_92"
    source := ⟨"aissen-2011", "(25a)"⟩
    reportedIn := some ⟨"newman-2024", "(92)"⟩
    language := "kich1262"
    primaryText := "Jachiin x-u-loq' uuq?"
    glossedTokens := [("Jachiin", "WH"), ("x-u-loq'", "PFV-A3SG-buy"), ("uuq", "cloth")]
    glossedWords := [⟨['J', 'a', 'c', 'h', 'i', 'i', 'n'], ['W', 'H'], [⟨['J', 'a', 'c', 'h', 'i', 'i', 'n'], ['W', 'H'], none⟩]⟩, ⟨['x', '-', 'u', '-', 'l', 'o', 'q', '\''], ['P', 'F', 'V', '-', 'A', '3', 'S', 'G', '-', 'b', 'u', 'y'], [⟨['x'], ['P', 'F', 'V'], none⟩, ⟨['u'], ['A', '3', 'S', 'G'], some '-'⟩, ⟨['l', 'o', 'q', '\''], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['u', 'u', 'q'], ['c', 'l', 'o', 't', 'h'], [⟨['u', 'u', 'q'], ['c', 'l', 'o', 't', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("fronting", "subject"), ("object", "np")] }

def ex_92_det : Datum :=
  { id := "newman2024_92_det"
    source := ⟨"aissen-2011", "(25a)"⟩
    reportedIn := some ⟨"newman-2024", "(92)"⟩
    language := "kich1262"
    primaryText := "Jachiin x-u-loq' rii uuq?"
    glossedTokens := [("Jachiin", "WH"), ("x-u-loq'", "PFV-A3SG-buy"), ("rii", "DET"), ("uuq", "cloth")]
    glossedWords := [⟨['J', 'a', 'c', 'h', 'i', 'i', 'n'], ['W', 'H'], [⟨['J', 'a', 'c', 'h', 'i', 'i', 'n'], ['W', 'H'], none⟩]⟩, ⟨['x', '-', 'u', '-', 'l', 'o', 'q', '\''], ['P', 'F', 'V', '-', 'A', '3', 'S', 'G', '-', 'b', 'u', 'y'], [⟨['x'], ['P', 'F', 'V'], none⟩, ⟨['u'], ['A', '3', 'S', 'G'], some '-'⟩, ⟨['l', 'o', 'q', '\''], ['b', 'u', 'y'], some '-'⟩]⟩, ⟨['r', 'i', 'i'], ['D', 'E', 'T'], [⟨['r', 'i', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['u', 'u', 'q'], ['c', 'l', 'o', 't', 'h'], [⟨['u', 'u', 'q'], ['c', 'l', 'o', 't', 'h'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("fronting", "subject"), ("object", "dp")] }

def ex_107a : Datum :=
  { id := "newman2024_107a"
    source := ⟨"garcia-matzar-rodriguez-guajan-1997", "(468d,f)"⟩
    reportedIn := some ⟨"newman-2024", "(107a)"⟩
    language := "kaqc1270"
    primaryText := "Ja ri utiw-a', ja ri aq x-e-ki-tïj."
    glossedTokens := [("Ja", "FOC"), ("ri", "DET"), ("utiw-a',", "coyote-PL"), ("ja", "FOC"), ("ri", "DET"), ("aq", "pig"), ("x-e-ki-tïj.", "PFV-B3PL-A3PL-eat")]
    glossedWords := [⟨['J', 'a'], ['F', 'O', 'C'], [⟨['J', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['D', 'E', 'T'], [⟨['r', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['u', 't', 'i', 'w', '-', 'a', '\'', ','], ['c', 'o', 'y', 'o', 't', 'e', '-', 'P', 'L'], [⟨['u', 't', 'i', 'w'], ['c', 'o', 'y', 'o', 't', 'e'], none⟩, ⟨['a', '\''], ['P', 'L'], some '-'⟩]⟩, ⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['D', 'E', 'T'], [⟨['r', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['a', 'q'], ['p', 'i', 'g'], [⟨['a', 'q'], ['p', 'i', 'g'], none⟩]⟩, ⟨['x', '-', 'e', '-', 'k', 'i', '-', 't', 'ï', 'j', '.'], ['P', 'F', 'V', '-', 'B', '3', 'P', 'L', '-', 'A', '3', 'P', 'L', '-', 'e', 'a', 't'], [⟨['x'], ['P', 'F', 'V'], none⟩, ⟨['e'], ['B', '3', 'P', 'L'], some '-'⟩, ⟨['k', 'i'], ['A', '3', 'P', 'L'], some '-'⟩, ⟨['t', 'ï', 'j'], ['e', 'a', 't'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("fronting", "subjectObject"), ("object", "dp")] }

def ex_107b : Datum :=
  { id := "newman2024_107b"
    source := ⟨"garcia-matzar-rodriguez-guajan-1997", "(468d,f)"⟩
    reportedIn := some ⟨"newman-2024", "(107b)"⟩
    language := "kaqc1270"
    primaryText := "Ja ri aq, ja ri utiw-a' x-e-tij-o."
    glossedTokens := [("Ja", "FOC"), ("ri", "DET"), ("aq,", "pigs"), ("ja", "FOC"), ("ri", "DET"), ("utiw-a'", "coyote-PL"), ("x-e-tij-o.", "PFV-B3PL-eat-AF")]
    glossedWords := [⟨['J', 'a'], ['F', 'O', 'C'], [⟨['J', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['D', 'E', 'T'], [⟨['r', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['a', 'q', ','], ['p', 'i', 'g', 's'], [⟨['a', 'q'], ['p', 'i', 'g', 's'], none⟩]⟩, ⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i'], ['D', 'E', 'T'], [⟨['r', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['u', 't', 'i', 'w', '-', 'a', '\''], ['c', 'o', 'y', 'o', 't', 'e', '-', 'P', 'L'], [⟨['u', 't', 'i', 'w'], ['c', 'o', 'y', 'o', 't', 'e'], none⟩, ⟨['a', '\''], ['P', 'L'], some '-'⟩]⟩, ⟨['x', '-', 'e', '-', 't', 'i', 'j', '-', 'o', '.'], ['P', 'F', 'V', '-', 'B', '3', 'P', 'L', '-', 'e', 'a', 't', '-', 'A', 'F'], [⟨['x'], ['P', 'F', 'V'], none⟩, ⟨['e'], ['B', '3', 'P', 'L'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩, ⟨['o'], ['A', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Ja ri aq, ja ri utiw-a' x-e-tij-o kichin.", .acceptable)]
    readings := []
    paperFeatures := [("fronting", "objectSubject"), ("object", "dp")] }

def ex_108a : Datum :=
  { id := "newman2024_108a"
    source := ⟨"erlewine-2016", "(29b)"⟩
    reportedIn := some ⟨"newman-2024", "(108a)"⟩
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-u-tz'ët?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-u-tz'ët", "COM-BSG-A3SG-see")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', '\'', 'o'], ['∃'], [⟨['k', '\'', 'o'], ['∃'], none⟩]⟩, ⟨['x', '-', '∅', '-', 'u', '-', 't', 'z', '\'', 'ë', 't'], ['C', 'O', 'M', '-', 'B', 'S', 'G', '-', 'A', '3', 'S', 'G', '-', 's', 'e', 'e'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', 'S', 'G'], some '-'⟩, ⟨['u'], ['A', '3', 'S', 'G'], some '-'⟩, ⟨['t', 'z', '\'', 'ë', 't'], ['s', 'e', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject first", .acceptable), ("object first", .ungrammatical)]
    paperFeatures := [("fronting", "both"), ("object", "dp")] }

def ex_108b : Datum :=
  { id := "newman2024_108b"
    source := ⟨"erlewine-2016", "(29a)"⟩
    reportedIn := some ⟨"newman-2024", "(108b)"⟩
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-tz'ët-ö?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-tz'ët-ö", "COM-BSG-see-AF")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['k', '\'', 'o'], ['∃'], [⟨['k', '\'', 'o'], ['∃'], none⟩]⟩, ⟨['x', '-', '∅', '-', 't', 'z', '\'', 'ë', 't', '-', 'ö'], ['C', 'O', 'M', '-', 'B', 'S', 'G', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', 'S', 'G'], some '-'⟩, ⟨['t', 'z', '\'', 'ë', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject first", .ungrammatical), ("object first", .acceptable)]
    paperFeatures := [("fronting", "both"), ("object", "dp")] }

def ex_109a : Datum :=
  { id := "newman2024_109a"
    source := ⟨"erlewine-2016", "(33)"⟩
    reportedIn := some ⟨"newman-2024", "(109a)"⟩
    language := "kaqc1270"
    primaryText := "K'o k'o x-∅-u-tz'ët"
    glossedTokens := [("K'o", "∃"), ("k'o", "∃"), ("x-∅-u-tz'ët", "COM-B3SG-A3SG-see")]
    glossedWords := [⟨['K', '\'', 'o'], ['∃'], [⟨['K', '\'', 'o'], ['∃'], none⟩]⟩, ⟨['k', '\'', 'o'], ['∃'], [⟨['k', '\'', 'o'], ['∃'], none⟩]⟩, ⟨['x', '-', '∅', '-', 'u', '-', 't', 'z', '\'', 'ë', 't'], ['C', 'O', 'M', '-', 'B', '3', 'S', 'G', '-', 'A', '3', 'S', 'G', '-', 's', 'e', 'e'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['u'], ['A', '3', 'S', 'G'], some '-'⟩, ⟨['t', 'z', '\'', 'ë', 't'], ['s', 'e', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject first", .acceptable), ("object first", .ungrammatical)]
    paperFeatures := [("fronting", "both"), ("object", "dp")] }

def ex_109b : Datum :=
  { id := "newman2024_109b"
    source := ⟨"erlewine-2016", "(33)"⟩
    reportedIn := some ⟨"newman-2024", "(109b)"⟩
    language := "kaqc1270"
    primaryText := "K'o k'o x-∅-tz'et-ö"
    glossedTokens := [("K'o", "∃"), ("k'o", "∃"), ("x-∅-tz'et-ö", "COM-B3SG-see-AF")]
    glossedWords := [⟨['K', '\'', 'o'], ['∃'], [⟨['K', '\'', 'o'], ['∃'], none⟩]⟩, ⟨['k', '\'', 'o'], ['∃'], [⟨['k', '\'', 'o'], ['∃'], none⟩]⟩, ⟨['x', '-', '∅', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', 'B', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject first", .ungrammatical), ("object first", .acceptable)]
    paperFeatures := [("fronting", "both"), ("object", "dp")] }

def ex_110a : Datum :=
  { id := "newman2024_110a"
    source := ⟨"erlewine-2016", "(34)"⟩
    reportedIn := some ⟨"newman-2024", "(110a)"⟩
    language := "kaqc1270"
    primaryText := "ri achin ri ja ri xta Maria x-∅-u-tz'ët"
    glossedTokens := [("ri", "DET"), ("achin", "man"), ("ri", "REL"), ("ja", "FOC"), ("ri xta Maria", "Maria"), ("x-∅-u-tz'ët", "COM-B3SG-A3SG-see")]
    glossedWords := [⟨['r', 'i'], ['D', 'E', 'T'], [⟨['r', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i', ' ', 'x', 't', 'a', ' ', 'M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['r', 'i', ' ', 'x', 't', 'a', ' ', 'M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['x', '-', '∅', '-', 'u', '-', 't', 'z', '\'', 'ë', 't'], ['C', 'O', 'M', '-', 'B', '3', 'S', 'G', '-', 'A', '3', 'S', 'G', '-', 's', 'e', 'e'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['u'], ['A', '3', 'S', 'G'], some '-'⟩, ⟨['t', 'z', '\'', 'ë', 't'], ['s', 'e', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject first", .acceptable), ("object first", .ungrammatical)]
    paperFeatures := [("fronting", "both"), ("object", "dp")] }

def ex_110b : Datum :=
  { id := "newman2024_110b"
    source := ⟨"erlewine-2016", "(34)"⟩
    reportedIn := some ⟨"newman-2024", "(110b)"⟩
    language := "kaqc1270"
    primaryText := "ri achin ri ja ri xta Maria x-∅-tz'et-ö"
    glossedTokens := [("ri", "DET"), ("achin", "man"), ("ri", "REL"), ("ja", "FOC"), ("ri xta Maria", "Maria"), ("x-∅-tz'et-ö", "COM-B3SG-see-AF")]
    glossedWords := [⟨['r', 'i'], ['D', 'E', 'T'], [⟨['r', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], [⟨['a', 'c', 'h', 'i', 'n'], ['m', 'a', 'n'], none⟩]⟩, ⟨['r', 'i'], ['R', 'E', 'L'], [⟨['r', 'i'], ['R', 'E', 'L'], none⟩]⟩, ⟨['j', 'a'], ['F', 'O', 'C'], [⟨['j', 'a'], ['F', 'O', 'C'], none⟩]⟩, ⟨['r', 'i', ' ', 'x', 't', 'a', ' ', 'M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['r', 'i', ' ', 'x', 't', 'a', ' ', 'M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['x', '-', '∅', '-', 't', 'z', '\'', 'e', 't', '-', 'ö'], ['C', 'O', 'M', '-', 'B', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'A', 'F'], [⟨['x'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['t', 'z', '\'', 'e', 't'], ['s', 'e', 'e'], some '-'⟩, ⟨['ö'], ['A', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("subject first", .ungrammatical), ("object first", .acceptable)]
    paperFeatures := [("fronting", "both"), ("object", "dp")] }

def ex_149a : Datum :=
  { id := "newman2024_149a"
    source := ⟨"newman-2024", "(149a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo showed Lauri and Amy to each other's parents in the mirror."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "directFirst"), ("binder", "direct")] }

def ex_149b : Datum :=
  { id := "newman2024_149b"
    source := ⟨"newman-2024", "(149b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo showed pictures of each other to Lauri and Amy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "directFirst"), ("binder", "indirect")] }

def ex_149c : Datum :=
  { id := "newman2024_149c"
    source := ⟨"newman-2024", "(149c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo showed Lauri and Amy each other's parents in the mirror."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "indirectFirst"), ("binder", "indirect")] }

def ex_149d : Datum :=
  { id := "newman2024_149d"
    source := ⟨"newman-2024", "(149d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jo showed each other's parents Lauri and Amy in the mirror."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("order", "indirectFirst"), ("binder", "direct")] }

def ex_150a : Datum :=
  { id := "newman2024_150a"
    source := ⟨"miyagawa-tsujioka-2004", "(61b)"⟩
    reportedIn := some ⟨"newman-2024", "(150a)"⟩
    language := "nucl1643"
    primaryText := "John-ga Hanako-to Mary-o otagai-ni syookaisita."
    glossedTokens := [("John-ga", "John-NOM"), ("Hanako-to", "Hanako-and"), ("Mary-o", "Mary-ACC"), ("otagai-ni", "each.other-DAT"), ("syookaisita", "introduced")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'g', 'a'], ['J', 'o', 'h', 'n', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['H', 'a', 'n', 'a', 'k', 'o', '-', 't', 'o'], ['H', 'a', 'n', 'a', 'k', 'o', '-', 'a', 'n', 'd'], [⟨['H', 'a', 'n', 'a', 'k', 'o'], ['H', 'a', 'n', 'a', 'k', 'o'], none⟩, ⟨['t', 'o'], ['a', 'n', 'd'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'y', '-', 'o'], ['M', 'a', 'r', 'y', '-', 'A', 'C', 'C'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['o', 't', 'a', 'g', 'a', 'i', '-', 'n', 'i'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['o', 't', 'a', 'g', 'a', 'i'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], [⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alsoJudged := [.marginal]
    contrasts := []
    readings := []
    paperFeatures := [("order", "directFirst"), ("binder", "direct")] }

def ex_150b : Datum :=
  { id := "newman2024_150b"
    source := ⟨"newman-2024", "(150b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga otagai-no sensei-o Hanako-to Mary-ni syookaisita."
    glossedTokens := [("John-ga", "John-NOM"), ("otagai-no", "each.other-GEN"), ("sensei-o", "teacher-ACC"), ("Hanako-to", "Hanako-and"), ("Mary-ni", "Mary-DAT"), ("syookaisita", "introduced")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'g', 'a'], ['J', 'o', 'h', 'n', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['o', 't', 'a', 'g', 'a', 'i', '-', 'n', 'o'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['o', 't', 'a', 'g', 'a', 'i'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['s', 'e', 'n', 's', 'e', 'i', '-', 'o'], ['t', 'e', 'a', 'c', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['s', 'e', 'n', 's', 'e', 'i'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['H', 'a', 'n', 'a', 'k', 'o', '-', 't', 'o'], ['H', 'a', 'n', 'a', 'k', 'o', '-', 'a', 'n', 'd'], [⟨['H', 'a', 'n', 'a', 'k', 'o'], ['H', 'a', 'n', 'a', 'k', 'o'], none⟩, ⟨['t', 'o'], ['a', 'n', 'd'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'y', '-', 'n', 'i'], ['M', 'a', 'r', 'y', '-', 'D', 'A', 'T'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], [⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "directFirst"), ("binder", "indirect")] }

def ex_151a : Datum :=
  { id := "newman2024_151a"
    source := ⟨"miyagawa-tsujioka-2004", "(61a)"⟩
    reportedIn := some ⟨"newman-2024", "(151a)"⟩
    language := "nucl1643"
    primaryText := "John-ga Hanako-to Mary-ni otagai-o syookaisita."
    glossedTokens := [("John-ga", "John-NOM"), ("Hanako-to", "Hanako-and"), ("Mary-ni", "Mary-DAT"), ("otagai-o", "each.other-ACC"), ("syookaisita", "introduced")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'g', 'a'], ['J', 'o', 'h', 'n', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['H', 'a', 'n', 'a', 'k', 'o', '-', 't', 'o'], ['H', 'a', 'n', 'a', 'k', 'o', '-', 'a', 'n', 'd'], [⟨['H', 'a', 'n', 'a', 'k', 'o'], ['H', 'a', 'n', 'a', 'k', 'o'], none⟩, ⟨['t', 'o'], ['a', 'n', 'd'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'y', '-', 'n', 'i'], ['M', 'a', 'r', 'y', '-', 'D', 'A', 'T'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['o', 't', 'a', 'g', 'a', 'i', '-', 'o'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r', '-', 'A', 'C', 'C'], [⟨['o', 't', 'a', 'g', 'a', 'i'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], [⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "indirectFirst"), ("binder", "indirect")] }

def ex_151b : Datum :=
  { id := "newman2024_151b"
    source := ⟨"newman-2024", "(151b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga otagai-no sensei-ni Hanako-to Mary-o syookaisita."
    glossedTokens := [("John-ga", "John-NOM"), ("otagai-no", "each.other-GEN"), ("sensei-ni", "teacher-DAT"), ("Hanako-to", "Hanako-and"), ("Mary-o", "Mary-ACC"), ("syookaisita", "introduced")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'g', 'a'], ['J', 'o', 'h', 'n', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['o', 't', 'a', 'g', 'a', 'i', '-', 'n', 'o'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r', '-', 'G', 'E', 'N'], [⟨['o', 't', 'a', 'g', 'a', 'i'], ['e', 'a', 'c', 'h', '.', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['s', 'e', 'n', 's', 'e', 'i', '-', 'n', 'i'], ['t', 'e', 'a', 'c', 'h', 'e', 'r', '-', 'D', 'A', 'T'], [⟨['s', 'e', 'n', 's', 'e', 'i'], ['t', 'e', 'a', 'c', 'h', 'e', 'r'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['H', 'a', 'n', 'a', 'k', 'o', '-', 't', 'o'], ['H', 'a', 'n', 'a', 'k', 'o', '-', 'a', 'n', 'd'], [⟨['H', 'a', 'n', 'a', 'k', 'o'], ['H', 'a', 'n', 'a', 'k', 'o'], none⟩, ⟨['t', 'o'], ['a', 'n', 'd'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'y', '-', 'o'], ['M', 'a', 'r', 'y', '-', 'A', 'C', 'C'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], [⟨['s', 'y', 'o', 'o', 'k', 'a', 'i', 's', 'i', 't', 'a'], ['i', 'n', 't', 'r', 'o', 'd', 'u', 'c', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("order", "indirectFirst"), ("binder", "direct")] }

def ex_153a : Datum :=
  { id := "newman2024_153a"
    source := ⟨"newman-2024", "(153a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Gianis edhikse ton Maria s-ton eafton tis s-ton kathrefti."
    glossedTokens := [("O", "the"), ("Gianis", "Gianis.NOM"), ("edhikse", "showed"), ("ton", "the"), ("Maria", "Maria.ACC"), ("s-ton", "to-the"), ("eafton", "REFL.ACC"), ("tis", "GEN"), ("s-ton", "in-the"), ("kathrefti", "mirror.ACC")]
    glossedWords := [⟨['O'], ['t', 'h', 'e'], [⟨['O'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], [⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], [⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], none⟩]⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], [⟨['t', 'o', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'A', 'C', 'C'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['s', '-', 't', 'o', 'n'], ['t', 'o', '-', 't', 'h', 'e'], [⟨['s'], ['t', 'o'], none⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['e', 'a', 'f', 't', 'o', 'n'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C'], [⟨['e', 'a', 'f', 't', 'o', 'n'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['t', 'i', 's'], ['G', 'E', 'N'], [⟨['t', 'i', 's'], ['G', 'E', 'N'], none⟩]⟩, ⟨['s', '-', 't', 'o', 'n'], ['i', 'n', '-', 't', 'h', 'e'], [⟨['s'], ['i', 'n'], none⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], [⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "directFirst"), ("binder", "direct")] }

def ex_153b : Datum :=
  { id := "newman2024_153b"
    source := ⟨"newman-2024", "(153b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Gianis edhikse ton eafton tis s-tin Maria s-ton kathrefti."
    glossedTokens := [("O", "the"), ("Gianis", "Gianis.NOM"), ("edhikse", "showed"), ("ton", "the"), ("eafton", "REFL.ACC"), ("tis", "GEN"), ("s-tin", "to-the"), ("Maria", "Maria.ACC"), ("s-ton", "in-the"), ("kathrefti", "mirror.ACC")]
    glossedWords := [⟨['O'], ['t', 'h', 'e'], [⟨['O'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], [⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], [⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], none⟩]⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], [⟨['t', 'o', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 'a', 'f', 't', 'o', 'n'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C'], [⟨['e', 'a', 'f', 't', 'o', 'n'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['t', 'i', 's'], ['G', 'E', 'N'], [⟨['t', 'i', 's'], ['G', 'E', 'N'], none⟩]⟩, ⟨['s', '-', 't', 'i', 'n'], ['t', 'o', '-', 't', 'h', 'e'], [⟨['s'], ['t', 'o'], none⟩, ⟨['t', 'i', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'A', 'C', 'C'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['s', '-', 't', 'o', 'n'], ['i', 'n', '-', 't', 'h', 'e'], [⟨['s'], ['i', 'n'], none⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], [⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "directFirst"), ("binder", "indirect")] }

def ex_153c : Datum :=
  { id := "newman2024_153c"
    source := ⟨"newman-2024", "(153c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Gianis edhikse tis Marias ton eafton tis s-ton kathrefti."
    glossedTokens := [("O", "the"), ("Gianis", "Gianis.NOM"), ("edhikse", "showed"), ("tis", "the"), ("Marias", "Maria.GEN"), ("ton", "the"), ("eafton", "REFL.ACC"), ("tis", "GEN"), ("s-ton", "in-the"), ("kathrefti", "mirror.ACC")]
    glossedWords := [⟨['O'], ['t', 'h', 'e'], [⟨['O'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], [⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], [⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], none⟩]⟩, ⟨['t', 'i', 's'], ['t', 'h', 'e'], [⟨['t', 'i', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', 's'], ['M', 'a', 'r', 'i', 'a', '.', 'G', 'E', 'N'], [⟨['M', 'a', 'r', 'i', 'a', 's'], ['M', 'a', 'r', 'i', 'a', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], [⟨['t', 'o', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 'a', 'f', 't', 'o', 'n'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C'], [⟨['e', 'a', 'f', 't', 'o', 'n'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['t', 'i', 's'], ['G', 'E', 'N'], [⟨['t', 'i', 's'], ['G', 'E', 'N'], none⟩]⟩, ⟨['s', '-', 't', 'o', 'n'], ['i', 'n', '-', 't', 'h', 'e'], [⟨['s'], ['i', 'n'], none⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], [⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("order", "indirectFirst"), ("binder", "indirect")] }

def ex_153d : Datum :=
  { id := "newman2024_153d"
    source := ⟨"newman-2024", "(153d)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Gianis edhikse tu eaftu tis tin Maria s-ton kathrefti."
    glossedTokens := [("O", "the"), ("Gianis", "Gianis.NOM"), ("edhikse", "showed"), ("tu", "the"), ("eaftu", "REFL.GEN"), ("tis", "GEN"), ("tin", "the"), ("Maria", "Maria.ACC"), ("s-ton", "in-the"), ("kathrefti", "mirror.ACC")]
    glossedWords := [⟨['O'], ['t', 'h', 'e'], [⟨['O'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], [⟨['G', 'i', 'a', 'n', 'i', 's'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], [⟨['e', 'd', 'h', 'i', 'k', 's', 'e'], ['s', 'h', 'o', 'w', 'e', 'd'], none⟩]⟩, ⟨['t', 'u'], ['t', 'h', 'e'], [⟨['t', 'u'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 'a', 'f', 't', 'u'], ['R', 'E', 'F', 'L', '.', 'G', 'E', 'N'], [⟨['e', 'a', 'f', 't', 'u'], ['R', 'E', 'F', 'L', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['t', 'i', 's'], ['G', 'E', 'N'], [⟨['t', 'i', 's'], ['G', 'E', 'N'], none⟩]⟩, ⟨['t', 'i', 'n'], ['t', 'h', 'e'], [⟨['t', 'i', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'A', 'C', 'C'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['s', '-', 't', 'o', 'n'], ['i', 'n', '-', 't', 'h', 'e'], [⟨['s'], ['i', 'n'], none⟩, ⟨['t', 'o', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], [⟨['k', 'a', 't', 'h', 'r', 'e', 'f', 't', 'i'], ['m', 'i', 'r', 'r', 'o', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("order", "indirectFirst"), ("binder", "direct")] }

def ex_187a : Datum :=
  { id := "newman2024_187a"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(1)"⟩
    reportedIn := some ⟨"newman-2024", "(187a)"⟩
    language := "norw1258"
    primaryText := "Boka ble gitt Jon."
    glossedTokens := [("Boka", "the.book"), ("ble", "was"), ("gitt", "given"), ("Jon", "Jon")]
    glossedWords := [⟨['B', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], [⟨['B', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], none⟩]⟩, ⟨['b', 'l', 'e'], ['w', 'a', 's'], [⟨['b', 'l', 'e'], ['w', 'a', 's'], none⟩]⟩, ⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], [⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], none⟩]⟩, ⟨['J', 'o', 'n'], ['J', 'o', 'n'], [⟨['J', 'o', 'n'], ['J', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct")] }

def ex_187b : Datum :=
  { id := "newman2024_187b"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(1)"⟩
    reportedIn := some ⟨"newman-2024", "(187b)"⟩
    language := "norw1258"
    primaryText := "Jon ble gitt boka."
    glossedTokens := [("Jon", "Jon"), ("ble", "was"), ("gitt", "given"), ("boka", "the.book")]
    glossedWords := [⟨['J', 'o', 'n'], ['J', 'o', 'n'], [⟨['J', 'o', 'n'], ['J', 'o', 'n'], none⟩]⟩, ⟨['b', 'l', 'e'], ['w', 'a', 's'], [⟨['b', 'l', 'e'], ['w', 'a', 's'], none⟩]⟩, ⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], [⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], none⟩]⟩, ⟨['b', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], [⟨['b', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indirect")] }

def ex_200a : Datum :=
  { id := "newman2024_200a"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(5)"⟩
    reportedIn := some ⟨"newman-2024", "(200a)"⟩
    language := "norw1258"
    primaryText := "Hvem ble boka gitt?"
    glossedTokens := [("Hvem", "who"), ("ble", "was"), ("boka", "the.book"), ("gitt", "given")]
    glossedWords := [⟨['H', 'v', 'e', 'm'], ['w', 'h', 'o'], [⟨['H', 'v', 'e', 'm'], ['w', 'h', 'o'], none⟩]⟩, ⟨['b', 'l', 'e'], ['w', 'a', 's'], [⟨['b', 'l', 'e'], ['w', 'a', 's'], none⟩]⟩, ⟨['b', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], [⟨['b', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], none⟩]⟩, ⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], [⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct"), ("wh", "indirect")] }

def ex_200b : Datum :=
  { id := "newman2024_200b"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(5)"⟩
    reportedIn := some ⟨"newman-2024", "(200b)"⟩
    language := "norw1258"
    primaryText := "Hvem ble gitt boka?"
    glossedTokens := [("Hvem", "who"), ("ble", "was"), ("gitt", "given"), ("boka", "the.book")]
    glossedWords := [⟨['H', 'v', 'e', 'm'], ['w', 'h', 'o'], [⟨['H', 'v', 'e', 'm'], ['w', 'h', 'o'], none⟩]⟩, ⟨['b', 'l', 'e'], ['w', 'a', 's'], [⟨['b', 'l', 'e'], ['w', 'a', 's'], none⟩]⟩, ⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], [⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], none⟩]⟩, ⟨['b', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], [⟨['b', 'o', 'k', 'a'], ['t', 'h', 'e', '.', 'b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indirect"), ("wh", "indirect")] }

def ex_201a : Datum :=
  { id := "newman2024_201a"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(5)"⟩
    reportedIn := some ⟨"newman-2024", "(201a)"⟩
    language := "norw1258"
    primaryText := "Hvilken bok ble Jon gitt?"
    glossedTokens := [("Hvilken", "which"), ("bok", "book"), ("ble", "was"), ("Jon", "Jon"), ("gitt", "given")]
    glossedWords := [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'o', 'k'], ['b', 'o', 'o', 'k'], [⟨['b', 'o', 'k'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['b', 'l', 'e'], ['w', 'a', 's'], [⟨['b', 'l', 'e'], ['w', 'a', 's'], none⟩]⟩, ⟨['J', 'o', 'n'], ['J', 'o', 'n'], [⟨['J', 'o', 'n'], ['J', 'o', 'n'], none⟩]⟩, ⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], [⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indirect"), ("wh", "direct")] }

def ex_201b : Datum :=
  { id := "newman2024_201b"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(5)"⟩
    reportedIn := some ⟨"newman-2024", "(201b)"⟩
    language := "norw1258"
    primaryText := "Hvilken bok ble gitt Jon?"
    glossedTokens := [("Hvilken", "which"), ("bok", "book"), ("ble", "was"), ("gitt", "given"), ("Jon", "Jon")]
    glossedWords := [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], [⟨['H', 'v', 'i', 'l', 'k', 'e', 'n'], ['w', 'h', 'i', 'c', 'h'], none⟩]⟩, ⟨['b', 'o', 'k'], ['b', 'o', 'o', 'k'], [⟨['b', 'o', 'k'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['b', 'l', 'e'], ['w', 'a', 's'], [⟨['b', 'l', 'e'], ['w', 'a', 's'], none⟩]⟩, ⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], [⟨['g', 'i', 't', 't'], ['g', 'i', 'v', 'e', 'n'], none⟩]⟩, ⟨['J', 'o', 'n'], ['J', 'o', 'n'], [⟨['J', 'o', 'n'], ['J', 'o', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct"), ("wh", "direct")] }

def ex_202a : Datum :=
  { id := "newman2024_202a"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(14)"⟩
    reportedIn := some ⟨"newman-2024", "(202a)"⟩
    language := "zulu1248"
    primaryText := "I-nyama u-mama a-yi-phek-el-w-a-yo i-mnandi."
    glossedTokens := [("I-nyama", "9-meat"), ("u-mama", "1AUG-mother"), ("a-yi-phek-el-w-a-yo", "REL.1SM-9OM-cook-APPL-PASS-FV-RS"), ("i-mnandi", "9SM-tasty")]
    glossedWords := [⟨['I', '-', 'n', 'y', 'a', 'm', 'a'], ['9', '-', 'm', 'e', 'a', 't'], [⟨['I'], ['9'], none⟩, ⟨['n', 'y', 'a', 'm', 'a'], ['m', 'e', 'a', 't'], some '-'⟩]⟩, ⟨['u', '-', 'm', 'a', 'm', 'a'], ['1', 'A', 'U', 'G', '-', 'm', 'o', 't', 'h', 'e', 'r'], [⟨['u'], ['1', 'A', 'U', 'G'], none⟩, ⟨['m', 'a', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], some '-'⟩]⟩, ⟨['a', '-', 'y', 'i', '-', 'p', 'h', 'e', 'k', '-', 'e', 'l', '-', 'w', '-', 'a', '-', 'y', 'o'], ['R', 'E', 'L', '.', '1', 'S', 'M', '-', '9', 'O', 'M', '-', 'c', 'o', 'o', 'k', '-', 'A', 'P', 'P', 'L', '-', 'P', 'A', 'S', 'S', '-', 'F', 'V', '-', 'R', 'S'], [⟨['a'], ['R', 'E', 'L', '.', '1', 'S', 'M'], none⟩, ⟨['y', 'i'], ['9', 'O', 'M'], some '-'⟩, ⟨['p', 'h', 'e', 'k'], ['c', 'o', 'o', 'k'], some '-'⟩, ⟨['e', 'l'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['w'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a'], ['F', 'V'], some '-'⟩, ⟨['y', 'o'], ['R', 'S'], some '-'⟩]⟩, ⟨['i', '-', 'm', 'n', 'a', 'n', 'd', 'i'], ['9', 'S', 'M', '-', 't', 'a', 's', 't', 'y'], [⟨['i'], ['9', 'S', 'M'], none⟩, ⟨['m', 'n', 'a', 'n', 'd', 'i'], ['t', 'a', 's', 't', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indirect"), ("wh", "direct"), ("objectMarked", "direct")] }

def ex_202b : Datum :=
  { id := "newman2024_202b"
    source := ⟨"holmberg-sheehan-van-der-wal-2019", "(14)"⟩
    reportedIn := some ⟨"newman-2024", "(202b)"⟩
    language := "zulu1248"
    primaryText := "U-mama i-nyama e-m-phek-el-w-a-yo u-kathele."
    glossedTokens := [("U-mama", "1AUG-mother"), ("i-nyama", "9-meat"), ("e-m-phek-el-w-a-yo", "REL.9SM-1OM-cook-APPL-PASS-FV-RS"), ("u-kathele", "1SM-tired")]
    glossedWords := [⟨['U', '-', 'm', 'a', 'm', 'a'], ['1', 'A', 'U', 'G', '-', 'm', 'o', 't', 'h', 'e', 'r'], [⟨['U'], ['1', 'A', 'U', 'G'], none⟩, ⟨['m', 'a', 'm', 'a'], ['m', 'o', 't', 'h', 'e', 'r'], some '-'⟩]⟩, ⟨['i', '-', 'n', 'y', 'a', 'm', 'a'], ['9', '-', 'm', 'e', 'a', 't'], [⟨['i'], ['9'], none⟩, ⟨['n', 'y', 'a', 'm', 'a'], ['m', 'e', 'a', 't'], some '-'⟩]⟩, ⟨['e', '-', 'm', '-', 'p', 'h', 'e', 'k', '-', 'e', 'l', '-', 'w', '-', 'a', '-', 'y', 'o'], ['R', 'E', 'L', '.', '9', 'S', 'M', '-', '1', 'O', 'M', '-', 'c', 'o', 'o', 'k', '-', 'A', 'P', 'P', 'L', '-', 'P', 'A', 'S', 'S', '-', 'F', 'V', '-', 'R', 'S'], [⟨['e'], ['R', 'E', 'L', '.', '9', 'S', 'M'], none⟩, ⟨['m'], ['1', 'O', 'M'], some '-'⟩, ⟨['p', 'h', 'e', 'k'], ['c', 'o', 'o', 'k'], some '-'⟩, ⟨['e', 'l'], ['A', 'P', 'P', 'L'], some '-'⟩, ⟨['w'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a'], ['F', 'V'], some '-'⟩, ⟨['y', 'o'], ['R', 'S'], some '-'⟩]⟩, ⟨['u', '-', 'k', 'a', 't', 'h', 'e', 'l', 'e'], ['1', 'S', 'M', '-', 't', 'i', 'r', 'e', 'd'], [⟨['u'], ['1', 'S', 'M'], none⟩, ⟨['k', 'a', 't', 'h', 'e', 'l', 'e'], ['t', 'i', 'r', 'e', 'd'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct"), ("wh", "indirect"), ("objectMarked", "indirect")] }

def ex_204a : Datum :=
  { id := "newman2024_204a"
    source := ⟨"visser-1986", "(16)"⟩
    reportedIn := some ⟨"newman-2024", "(204a)"⟩
    language := "xhos1239"
    primaryText := "Umfundi u-ya-yi-nik-w-a incwadi."
    glossedTokens := [("Umfundi", "student"), ("u-ya-yi-nik-w-a", "AGR-PRES-OM-give-PASS-PRES"), ("incwadi", "book")]
    glossedWords := [⟨['U', 'm', 'f', 'u', 'n', 'd', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't'], [⟨['U', 'm', 'f', 'u', 'n', 'd', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't'], none⟩]⟩, ⟨['u', '-', 'y', 'a', '-', 'y', 'i', '-', 'n', 'i', 'k', '-', 'w', '-', 'a'], ['A', 'G', 'R', '-', 'P', 'R', 'E', 'S', '-', 'O', 'M', '-', 'g', 'i', 'v', 'e', '-', 'P', 'A', 'S', 'S', '-', 'P', 'R', 'E', 'S'], [⟨['u'], ['A', 'G', 'R'], none⟩, ⟨['y', 'a'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['y', 'i'], ['O', 'M'], some '-'⟩, ⟨['n', 'i', 'k'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['w'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['i', 'n', 'c', 'w', 'a', 'd', 'i'], ['b', 'o', 'o', 'k'], [⟨['i', 'n', 'c', 'w', 'a', 'd', 'i'], ['b', 'o', 'o', 'k'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indirect"), ("objectMarked", "direct")] }

def ex_204b : Datum :=
  { id := "newman2024_204b"
    source := ⟨"visser-1986", "(16)"⟩
    reportedIn := some ⟨"newman-2024", "(204b)"⟩
    language := "xhos1239"
    primaryText := "Incwadi i-ya-m-nik-w-a umfundi."
    glossedTokens := [("Incwadi", "book"), ("i-ya-m-nik-w-a", "AGR-PRES-OM-give-PASS-PRES"), ("umfundi", "student")]
    glossedWords := [⟨['I', 'n', 'c', 'w', 'a', 'd', 'i'], ['b', 'o', 'o', 'k'], [⟨['I', 'n', 'c', 'w', 'a', 'd', 'i'], ['b', 'o', 'o', 'k'], none⟩]⟩, ⟨['i', '-', 'y', 'a', '-', 'm', '-', 'n', 'i', 'k', '-', 'w', '-', 'a'], ['A', 'G', 'R', '-', 'P', 'R', 'E', 'S', '-', 'O', 'M', '-', 'g', 'i', 'v', 'e', '-', 'P', 'A', 'S', 'S', '-', 'P', 'R', 'E', 'S'], [⟨['i'], ['A', 'G', 'R'], none⟩, ⟨['y', 'a'], ['P', 'R', 'E', 'S'], some '-'⟩, ⟨['m'], ['O', 'M'], some '-'⟩, ⟨['n', 'i', 'k'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['w'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a'], ['P', 'R', 'E', 'S'], some '-'⟩]⟩, ⟨['u', 'm', 'f', 'u', 'n', 'd', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't'], [⟨['u', 'm', 'f', 'u', 'n', 'd', 'i'], ['s', 't', 'u', 'd', 'e', 'n', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct"), ("objectMarked", "indirect")] }

def ex_207a : Datum :=
  { id := "newman2024_207a"
    source := ⟨"anagnostopoulou-2003", "(33)"⟩
    reportedIn := some ⟨"newman-2024", "(207a)"⟩
    language := "mode1248"
    primaryText := "To vivlio tis charistike tis Maria-s."
    glossedTokens := [("To", "the"), ("vivlio", "book.NOM"), ("tis", "CL.GEN"), ("charistike", "award.NACT.3SG"), ("tis", "the"), ("Maria-s", "Maria-GEN")]
    glossedWords := [⟨['T', 'o'], ['t', 'h', 'e'], [⟨['T', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], [⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'i', 's'], ['C', 'L', '.', 'G', 'E', 'N'], [⟨['t', 'i', 's'], ['C', 'L', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['c', 'h', 'a', 'r', 'i', 's', 't', 'i', 'k', 'e'], ['a', 'w', 'a', 'r', 'd', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], [⟨['c', 'h', 'a', 'r', 'i', 's', 't', 'i', 'k', 'e'], ['a', 'w', 'a', 'r', 'd', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'i', 's'], ['t', 'h', 'e'], [⟨['t', 'i', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 's'], ['M', 'a', 'r', 'i', 'a', '-', 'G', 'E', 'N'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['s'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct")] }

def ex_207a_bare : Datum :=
  { id := "newman2024_207a_bare"
    source := ⟨"anagnostopoulou-2003", "(33)"⟩
    reportedIn := some ⟨"newman-2024", "(207a)"⟩
    language := "mode1248"
    primaryText := "To vivlio charistike tis Maria-s."
    glossedTokens := [("To", "the"), ("vivlio", "book.NOM"), ("charistike", "award.NACT.3SG"), ("tis", "the"), ("Maria-s", "Maria-GEN")]
    glossedWords := [⟨['T', 'o'], ['t', 'h', 'e'], [⟨['T', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], [⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['c', 'h', 'a', 'r', 'i', 's', 't', 'i', 'k', 'e'], ['a', 'w', 'a', 'r', 'd', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], [⟨['c', 'h', 'a', 'r', 'i', 's', 't', 'i', 'k', 'e'], ['a', 'w', 'a', 'r', 'd', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'i', 's'], ['t', 'h', 'e'], [⟨['t', 'i', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a', '-', 's'], ['M', 'a', 'r', 'i', 'a', '-', 'G', 'E', 'N'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩, ⟨['s'], ['G', 'E', 'N'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct")] }

def ex_207b : Datum :=
  { id := "newman2024_207b"
    source := ⟨"anagnostopoulou-2003", "(10a)"⟩
    reportedIn := some ⟨"newman-2024", "(207b)"⟩
    language := "mode1248"
    primaryText := "I Maria stalthike to grama."
    glossedTokens := [("I", "the"), ("Maria", "Maria.NOM"), ("stalthike", "sent.NACT.3SG"), ("to", "the"), ("grama", "letter.ACC")]
    glossedWords := [⟨['I'], ['t', 'h', 'e'], [⟨['I'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'N', 'O', 'M'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['s', 't', 'a', 'l', 't', 'h', 'i', 'k', 'e'], ['s', 'e', 'n', 't', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], [⟨['s', 't', 'a', 'l', 't', 'h', 'i', 'k', 'e'], ['s', 'e', 'n', 't', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'r', 'a', 'm', 'a'], ['l', 'e', 't', 't', 'e', 'r', '.', 'A', 'C', 'C'], [⟨['g', 'r', 'a', 'm', 'a'], ['l', 'e', 't', 't', 'e', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("subject", "indirect")] }

def ex_212a : Datum :=
  { id := "newman2024_212a"
    source := ⟨"anagnostopoulou-2003", "(308)"⟩
    reportedIn := some ⟨"newman-2024", "(212a)"⟩
    language := "mode1248"
    primaryText := "Tinos dhothike to vivlio?"
    glossedTokens := [("Tinos", "who.GEN"), ("dhothike", "gave.NACT.3SG"), ("to", "the"), ("vivlio", "book.NOM")]
    glossedWords := [⟨['T', 'i', 'n', 'o', 's'], ['w', 'h', 'o', '.', 'G', 'E', 'N'], [⟨['T', 'i', 'n', 'o', 's'], ['w', 'h', 'o', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['d', 'h', 'o', 't', 'h', 'i', 'k', 'e'], ['g', 'a', 'v', 'e', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], [⟨['d', 'h', 'o', 't', 'h', 'i', 'k', 'e'], ['g', 'a', 'v', 'e', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], [⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct"), ("wh", "indirect")] }

def ex_216a : Datum :=
  { id := "newman2024_216a"
    source := ⟨"newman-2024", "(216a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pianu tu estile i Maria to gramma."
    glossedTokens := [("Pianu", "who.GEN.M"), ("tu", "CL.GEN"), ("estile", "sent"), ("i", "the"), ("Maria", "Maria.NOM"), ("to", "the"), ("gramma", "letter.ACC")]
    glossedWords := [⟨['P', 'i', 'a', 'n', 'u'], ['w', 'h', 'o', '.', 'G', 'E', 'N', '.', 'M'], [⟨['P', 'i', 'a', 'n', 'u'], ['w', 'h', 'o', '.', 'G', 'E', 'N', '.', 'M'], none⟩]⟩, ⟨['t', 'u'], ['C', 'L', '.', 'G', 'E', 'N'], [⟨['t', 'u'], ['C', 'L', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['e', 's', 't', 'i', 'l', 'e'], ['s', 'e', 'n', 't'], [⟨['e', 's', 't', 'i', 'l', 'e'], ['s', 'e', 'n', 't'], none⟩]⟩, ⟨['i'], ['t', 'h', 'e'], [⟨['i'], ['t', 'h', 'e'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'N', 'O', 'M'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'r', 'a', 'm', 'm', 'a'], ['l', 'e', 't', 't', 'e', 'r', '.', 'A', 'C', 'C'], [⟨['g', 'r', 'a', 'm', 'm', 'a'], ['l', 'e', 't', 't', 'e', 'r', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "agent"), ("wh", "indirect")] }

def ex_216b : Datum :=
  { id := "newman2024_216b"
    source := ⟨"newman-2024", "(216b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Pianu tu dhothike to vivlio?"
    glossedTokens := [("Pianu", "who.GEN"), ("tu", "CL.GEN"), ("dhothike", "gave.NACT.3SG"), ("to", "the"), ("vivlio", "book.NOM")]
    glossedWords := [⟨['P', 'i', 'a', 'n', 'u'], ['w', 'h', 'o', '.', 'G', 'E', 'N'], [⟨['P', 'i', 'a', 'n', 'u'], ['w', 'h', 'o', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['t', 'u'], ['C', 'L', '.', 'G', 'E', 'N'], [⟨['t', 'u'], ['C', 'L', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['d', 'h', 'o', 't', 'h', 'i', 'k', 'e'], ['g', 'a', 'v', 'e', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], [⟨['d', 'h', 'o', 't', 'h', 'i', 'k', 'e'], ['g', 'a', 'v', 'e', '.', 'N', 'A', 'C', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], [⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'N', 'O', 'M'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "direct"), ("wh", "indirect")] }

def ex_219 : Datum :=
  { id := "newman2024_219"
    source := ⟨"anagnostopoulou-2003", "(18)"⟩
    reportedIn := some ⟨"newman-2024", "(219)"⟩
    language := "mode1248"
    primaryText := "Tu edhosa tu Giani to vivlio."
    glossedTokens := [("Tu", "CL.GEN"), ("edhosa", "gave.1SG"), ("tu", "the"), ("Giani", "Gianis.GEN"), ("to", "the"), ("vivlio", "book.ACC")]
    glossedWords := [⟨['T', 'u'], ['C', 'L', '.', 'G', 'E', 'N'], [⟨['T', 'u'], ['C', 'L', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['e', 'd', 'h', 'o', 's', 'a'], ['g', 'a', 'v', 'e', '.', '1', 'S', 'G'], [⟨['e', 'd', 'h', 'o', 's', 'a'], ['g', 'a', 'v', 'e', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['t', 'u'], ['t', 'h', 'e'], [⟨['t', 'u'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'i'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'G', 'E', 'N'], [⟨['G', 'i', 'a', 'n', 'i'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], [⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "agent")] }

def ex_219_bare : Datum :=
  { id := "newman2024_219_bare"
    source := ⟨"anagnostopoulou-2003", "(18)"⟩
    reportedIn := some ⟨"newman-2024", "(219)"⟩
    language := "mode1248"
    primaryText := "Edhosa tu Giani to vivlio."
    glossedTokens := [("Edhosa", "gave.1SG"), ("tu", "the"), ("Giani", "Gianis.GEN"), ("to", "the"), ("vivlio", "book.ACC")]
    glossedWords := [⟨['E', 'd', 'h', 'o', 's', 'a'], ['g', 'a', 'v', 'e', '.', '1', 'S', 'G'], [⟨['E', 'd', 'h', 'o', 's', 'a'], ['g', 'a', 'v', 'e', '.', '1', 'S', 'G'], none⟩]⟩, ⟨['t', 'u'], ['t', 'h', 'e'], [⟨['t', 'u'], ['t', 'h', 'e'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'i'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'G', 'E', 'N'], [⟨['G', 'i', 'a', 'n', 'i'], ['G', 'i', 'a', 'n', 'i', 's', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], [⟨['v', 'i', 'v', 'l', 'i', 'o'], ['b', 'o', 'o', 'k', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("subject", "agent")] }

def all : List Datum := [ex_50, ex_51, ex_52, ex_53, ex_92, ex_92_det, ex_107a, ex_107b, ex_108a, ex_108b, ex_109a, ex_109b, ex_110a, ex_110b, ex_149a, ex_149b, ex_149c, ex_149d, ex_150a, ex_150b, ex_151a, ex_151b, ex_153a, ex_153b, ex_153c, ex_153d, ex_187a, ex_187b, ex_200a, ex_200b, ex_201a, ex_201b, ex_202a, ex_202b, ex_204a, ex_204b, ex_207a, ex_207a_bare, ex_207b, ex_212a, ex_216a, ex_216b, ex_219, ex_219_bare]

/-- The arguments of a transitive clause in its left periphery, in order. -/
inductive Fronting where
  /-- none: neither argument is fronted -/
  | none
  /-- subject: the subject alone is fronted -/
  | subject
  /-- object: the object alone is fronted -/
  | object
  /-- subjectObject: both are fronted, the subject first -/
  | subjectObject
  /-- objectSubject: both are fronted, the object first -/
  | objectSubject
  /-- both: both are fronted, and the readings of the row say which is first -/
  | both
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `fronting`. -/
def fronting (e : Datum) : Option Fronting :=
  e.parse? "fronting" [("none", .none), ("subject", .subject), ("object", .object),
    ("subjectObject", .subjectObject), ("objectSubject", .objectSubject), ("both", .both)]

/-- The category of the object of a transitive clause. -/
inductive ObjectCategory where
  /-- dp: a noun phrase with a determiner, or a pronoun -/
  | dp
  /-- np: a noun phrase without a determiner -/
  | np
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `object`. -/
def object (e : Datum) : Option ObjectCategory :=
  e.parse? "object" [("dp", .dp), ("np", .np)]

/-- The order of the two objects of a ditransitive. -/
inductive Order where
  /-- directFirst: the direct object precedes the indirect object -/
  | directFirst
  /-- indirectFirst: the indirect object precedes the direct object -/
  | indirectFirst
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `order`. -/
def order (e : Datum) : Option Order :=
  e.parse? "order" [("directFirst", .directFirst), ("indirectFirst", .indirectFirst)]

/-- The object of a ditransitive that binds an anaphor in the other. -/
inductive Binder where
  /-- direct: the direct object binds into the indirect object -/
  | direct
  /-- indirect: the indirect object binds into the direct object -/
  | indirect
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `binder`. -/
def binder (e : Datum) : Option Binder :=
  e.parse? "binder" [("direct", .direct), ("indirect", .indirect)]

/-- The argument of a ditransitive that is the subject of the clause. -/
inductive Subject where
  /-- agent: the agent, in an active clause -/
  | agent
  /-- indirect: the indirect object, in a passive -/
  | indirect
  /-- direct: the direct object, in a passive -/
  | direct
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `subject`. -/
def subject (e : Datum) : Option Subject :=
  e.parse? "subject" [("agent", .agent), ("indirect", .indirect), ("direct", .direct)]

/-- The object of a ditransitive that is questioned or relativized. -/
inductive Moved where
  /-- indirect: the indirect object -/
  | indirect
  /-- direct: the direct object -/
  | direct
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `wh`. -/
def wh (e : Datum) : Option Moved :=
  e.parse? "wh" [("indirect", .indirect), ("direct", .direct)]

/-- The object of a ditransitive that the object marker on the verb cross-references. -/
inductive Marked where
  /-- indirect: the indirect object -/
  | indirect
  /-- direct: the direct object -/
  | direct
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `objectMarked`. -/
def objectMarked (e : Datum) : Option Marked :=
  e.parse? "objectMarked" [("indirect", .indirect), ("direct", .direct)]

/-- The readings of a clause with two fronted arguments. -/
inductive Reading where
  /-- subject first: the first fronted phrase is the subject -/
  | subjectFirst
  /-- object first: the first fronted phrase is the object -/
  | objectFirst
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .subjectFirst => "subject first"
  | .objectFirst => "object first"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

/-- The examples of the book that the study's predictions are fitted to. -/
inductive Example where
  | ex_50
  | ex_51
  | ex_52
  | ex_53
  | ex_92
  | ex_92_det
  | ex_107a
  | ex_107b
  | ex_108a
  | ex_108b
  | ex_109a
  | ex_109b
  | ex_110a
  | ex_110b
  | ex_149a
  | ex_149b
  | ex_149c
  | ex_149d
  | ex_150a
  | ex_150b
  | ex_151a
  | ex_151b
  | ex_153a
  | ex_153b
  | ex_153c
  | ex_153d
  | ex_187a
  | ex_187b
  | ex_200a
  | ex_200b
  | ex_201a
  | ex_201b
  | ex_202a
  | ex_202b
  | ex_204a
  | ex_204b
  | ex_207a
  | ex_207a_bare
  | ex_207b
  | ex_212a
  | ex_216a
  | ex_216b
  | ex_219
  | ex_219_bare
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_50, .ex_51, .ex_52, .ex_53, .ex_92, .ex_92_det, .ex_107a, .ex_107b, .ex_108a, .ex_108b,
    .ex_109a, .ex_109b, .ex_110a, .ex_110b, .ex_149a, .ex_149b, .ex_149c, .ex_149d, .ex_150a,
    .ex_150b, .ex_151a, .ex_151b, .ex_153a, .ex_153b, .ex_153c, .ex_153d, .ex_187a, .ex_187b,
    .ex_200a, .ex_200b, .ex_201a, .ex_201b, .ex_202a, .ex_202b, .ex_204a, .ex_204b, .ex_207a,
    .ex_207a_bare, .ex_207b, .ex_212a, .ex_216a, .ex_216b, .ex_219, .ex_219_bare]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_50 => _root_.Newman2024.Examples.ex_50
  | .ex_51 => _root_.Newman2024.Examples.ex_51
  | .ex_52 => _root_.Newman2024.Examples.ex_52
  | .ex_53 => _root_.Newman2024.Examples.ex_53
  | .ex_92 => _root_.Newman2024.Examples.ex_92
  | .ex_92_det => _root_.Newman2024.Examples.ex_92_det
  | .ex_107a => _root_.Newman2024.Examples.ex_107a
  | .ex_107b => _root_.Newman2024.Examples.ex_107b
  | .ex_108a => _root_.Newman2024.Examples.ex_108a
  | .ex_108b => _root_.Newman2024.Examples.ex_108b
  | .ex_109a => _root_.Newman2024.Examples.ex_109a
  | .ex_109b => _root_.Newman2024.Examples.ex_109b
  | .ex_110a => _root_.Newman2024.Examples.ex_110a
  | .ex_110b => _root_.Newman2024.Examples.ex_110b
  | .ex_149a => _root_.Newman2024.Examples.ex_149a
  | .ex_149b => _root_.Newman2024.Examples.ex_149b
  | .ex_149c => _root_.Newman2024.Examples.ex_149c
  | .ex_149d => _root_.Newman2024.Examples.ex_149d
  | .ex_150a => _root_.Newman2024.Examples.ex_150a
  | .ex_150b => _root_.Newman2024.Examples.ex_150b
  | .ex_151a => _root_.Newman2024.Examples.ex_151a
  | .ex_151b => _root_.Newman2024.Examples.ex_151b
  | .ex_153a => _root_.Newman2024.Examples.ex_153a
  | .ex_153b => _root_.Newman2024.Examples.ex_153b
  | .ex_153c => _root_.Newman2024.Examples.ex_153c
  | .ex_153d => _root_.Newman2024.Examples.ex_153d
  | .ex_187a => _root_.Newman2024.Examples.ex_187a
  | .ex_187b => _root_.Newman2024.Examples.ex_187b
  | .ex_200a => _root_.Newman2024.Examples.ex_200a
  | .ex_200b => _root_.Newman2024.Examples.ex_200b
  | .ex_201a => _root_.Newman2024.Examples.ex_201a
  | .ex_201b => _root_.Newman2024.Examples.ex_201b
  | .ex_202a => _root_.Newman2024.Examples.ex_202a
  | .ex_202b => _root_.Newman2024.Examples.ex_202b
  | .ex_204a => _root_.Newman2024.Examples.ex_204a
  | .ex_204b => _root_.Newman2024.Examples.ex_204b
  | .ex_207a => _root_.Newman2024.Examples.ex_207a
  | .ex_207a_bare => _root_.Newman2024.Examples.ex_207a_bare
  | .ex_207b => _root_.Newman2024.Examples.ex_207b
  | .ex_212a => _root_.Newman2024.Examples.ex_212a
  | .ex_216a => _root_.Newman2024.Examples.ex_216a
  | .ex_216b => _root_.Newman2024.Examples.ex_216b
  | .ex_219 => _root_.Newman2024.Examples.ex_219
  | .ex_219_bare => _root_.Newman2024.Examples.ex_219_bare

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Newman2024.Examples.all := rfl

/-- The value the example records under `fronting`. -/
def Example.fronting : Example → Option Fronting
  | .ex_50 => some .none
  | .ex_51 => some .object
  | .ex_52 => some .subject
  | .ex_53 => some .subject
  | .ex_92 => some .subject
  | .ex_92_det => some .subject
  | .ex_107a => some .subjectObject
  | .ex_107b => some .objectSubject
  | .ex_108a => some .both
  | .ex_108b => some .both
  | .ex_109a => some .both
  | .ex_109b => some .both
  | .ex_110a => some .both
  | .ex_110b => some .both
  | .ex_149a => none
  | .ex_149b => none
  | .ex_149c => none
  | .ex_149d => none
  | .ex_150a => none
  | .ex_150b => none
  | .ex_151a => none
  | .ex_151b => none
  | .ex_153a => none
  | .ex_153b => none
  | .ex_153c => none
  | .ex_153d => none
  | .ex_187a => none
  | .ex_187b => none
  | .ex_200a => none
  | .ex_200b => none
  | .ex_201a => none
  | .ex_201b => none
  | .ex_202a => none
  | .ex_202b => none
  | .ex_204a => none
  | .ex_204b => none
  | .ex_207a => none
  | .ex_207a_bare => none
  | .ex_207b => none
  | .ex_212a => none
  | .ex_216a => none
  | .ex_216b => none
  | .ex_219 => none
  | .ex_219_bare => none

theorem Example.fronting_datum :
    ∀ x : Example, _root_.Newman2024.Examples.fronting x.datum = x.fronting := by
  decide +kernel

/-- The value the example records under `object`. -/
def Example.object : Example → Option ObjectCategory
  | .ex_50 => some .dp
  | .ex_51 => some .dp
  | .ex_52 => some .dp
  | .ex_53 => some .dp
  | .ex_92 => some .np
  | .ex_92_det => some .dp
  | .ex_107a => some .dp
  | .ex_107b => some .dp
  | .ex_108a => some .dp
  | .ex_108b => some .dp
  | .ex_109a => some .dp
  | .ex_109b => some .dp
  | .ex_110a => some .dp
  | .ex_110b => some .dp
  | .ex_149a => none
  | .ex_149b => none
  | .ex_149c => none
  | .ex_149d => none
  | .ex_150a => none
  | .ex_150b => none
  | .ex_151a => none
  | .ex_151b => none
  | .ex_153a => none
  | .ex_153b => none
  | .ex_153c => none
  | .ex_153d => none
  | .ex_187a => none
  | .ex_187b => none
  | .ex_200a => none
  | .ex_200b => none
  | .ex_201a => none
  | .ex_201b => none
  | .ex_202a => none
  | .ex_202b => none
  | .ex_204a => none
  | .ex_204b => none
  | .ex_207a => none
  | .ex_207a_bare => none
  | .ex_207b => none
  | .ex_212a => none
  | .ex_216a => none
  | .ex_216b => none
  | .ex_219 => none
  | .ex_219_bare => none

theorem Example.object_datum :
    ∀ x : Example, _root_.Newman2024.Examples.object x.datum = x.object := by
  decide +kernel

/-- The value the example records under `order`. -/
def Example.order : Example → Option Order
  | .ex_50 => none
  | .ex_51 => none
  | .ex_52 => none
  | .ex_53 => none
  | .ex_92 => none
  | .ex_92_det => none
  | .ex_107a => none
  | .ex_107b => none
  | .ex_108a => none
  | .ex_108b => none
  | .ex_109a => none
  | .ex_109b => none
  | .ex_110a => none
  | .ex_110b => none
  | .ex_149a => some .directFirst
  | .ex_149b => some .directFirst
  | .ex_149c => some .indirectFirst
  | .ex_149d => some .indirectFirst
  | .ex_150a => some .directFirst
  | .ex_150b => some .directFirst
  | .ex_151a => some .indirectFirst
  | .ex_151b => some .indirectFirst
  | .ex_153a => some .directFirst
  | .ex_153b => some .directFirst
  | .ex_153c => some .indirectFirst
  | .ex_153d => some .indirectFirst
  | .ex_187a => none
  | .ex_187b => none
  | .ex_200a => none
  | .ex_200b => none
  | .ex_201a => none
  | .ex_201b => none
  | .ex_202a => none
  | .ex_202b => none
  | .ex_204a => none
  | .ex_204b => none
  | .ex_207a => none
  | .ex_207a_bare => none
  | .ex_207b => none
  | .ex_212a => none
  | .ex_216a => none
  | .ex_216b => none
  | .ex_219 => none
  | .ex_219_bare => none

theorem Example.order_datum :
    ∀ x : Example, _root_.Newman2024.Examples.order x.datum = x.order := by
  decide +kernel

/-- The value the example records under `binder`. -/
def Example.binder : Example → Option Binder
  | .ex_50 => none
  | .ex_51 => none
  | .ex_52 => none
  | .ex_53 => none
  | .ex_92 => none
  | .ex_92_det => none
  | .ex_107a => none
  | .ex_107b => none
  | .ex_108a => none
  | .ex_108b => none
  | .ex_109a => none
  | .ex_109b => none
  | .ex_110a => none
  | .ex_110b => none
  | .ex_149a => some .direct
  | .ex_149b => some .indirect
  | .ex_149c => some .indirect
  | .ex_149d => some .direct
  | .ex_150a => some .direct
  | .ex_150b => some .indirect
  | .ex_151a => some .indirect
  | .ex_151b => some .direct
  | .ex_153a => some .direct
  | .ex_153b => some .indirect
  | .ex_153c => some .indirect
  | .ex_153d => some .direct
  | .ex_187a => none
  | .ex_187b => none
  | .ex_200a => none
  | .ex_200b => none
  | .ex_201a => none
  | .ex_201b => none
  | .ex_202a => none
  | .ex_202b => none
  | .ex_204a => none
  | .ex_204b => none
  | .ex_207a => none
  | .ex_207a_bare => none
  | .ex_207b => none
  | .ex_212a => none
  | .ex_216a => none
  | .ex_216b => none
  | .ex_219 => none
  | .ex_219_bare => none

theorem Example.binder_datum :
    ∀ x : Example, _root_.Newman2024.Examples.binder x.datum = x.binder := by
  decide +kernel

/-- The value the example records under `subject`. -/
def Example.subject : Example → Option Subject
  | .ex_50 => none
  | .ex_51 => none
  | .ex_52 => none
  | .ex_53 => none
  | .ex_92 => none
  | .ex_92_det => none
  | .ex_107a => none
  | .ex_107b => none
  | .ex_108a => none
  | .ex_108b => none
  | .ex_109a => none
  | .ex_109b => none
  | .ex_110a => none
  | .ex_110b => none
  | .ex_149a => none
  | .ex_149b => none
  | .ex_149c => none
  | .ex_149d => none
  | .ex_150a => none
  | .ex_150b => none
  | .ex_151a => none
  | .ex_151b => none
  | .ex_153a => none
  | .ex_153b => none
  | .ex_153c => none
  | .ex_153d => none
  | .ex_187a => some .direct
  | .ex_187b => some .indirect
  | .ex_200a => some .direct
  | .ex_200b => some .indirect
  | .ex_201a => some .indirect
  | .ex_201b => some .direct
  | .ex_202a => some .indirect
  | .ex_202b => some .direct
  | .ex_204a => some .indirect
  | .ex_204b => some .direct
  | .ex_207a => some .direct
  | .ex_207a_bare => some .direct
  | .ex_207b => some .indirect
  | .ex_212a => some .direct
  | .ex_216a => some .agent
  | .ex_216b => some .direct
  | .ex_219 => some .agent
  | .ex_219_bare => some .agent

theorem Example.subject_datum :
    ∀ x : Example, _root_.Newman2024.Examples.subject x.datum = x.subject := by
  decide +kernel

/-- The value the example records under `wh`. -/
def Example.wh : Example → Option Moved
  | .ex_50 => none
  | .ex_51 => none
  | .ex_52 => none
  | .ex_53 => none
  | .ex_92 => none
  | .ex_92_det => none
  | .ex_107a => none
  | .ex_107b => none
  | .ex_108a => none
  | .ex_108b => none
  | .ex_109a => none
  | .ex_109b => none
  | .ex_110a => none
  | .ex_110b => none
  | .ex_149a => none
  | .ex_149b => none
  | .ex_149c => none
  | .ex_149d => none
  | .ex_150a => none
  | .ex_150b => none
  | .ex_151a => none
  | .ex_151b => none
  | .ex_153a => none
  | .ex_153b => none
  | .ex_153c => none
  | .ex_153d => none
  | .ex_187a => none
  | .ex_187b => none
  | .ex_200a => some .indirect
  | .ex_200b => some .indirect
  | .ex_201a => some .direct
  | .ex_201b => some .direct
  | .ex_202a => some .direct
  | .ex_202b => some .indirect
  | .ex_204a => none
  | .ex_204b => none
  | .ex_207a => none
  | .ex_207a_bare => none
  | .ex_207b => none
  | .ex_212a => some .indirect
  | .ex_216a => some .indirect
  | .ex_216b => some .indirect
  | .ex_219 => none
  | .ex_219_bare => none

theorem Example.wh_datum :
    ∀ x : Example, _root_.Newman2024.Examples.wh x.datum = x.wh := by
  decide +kernel

/-- The value the example records under `objectMarked`. -/
def Example.objectMarked : Example → Option Marked
  | .ex_50 => none
  | .ex_51 => none
  | .ex_52 => none
  | .ex_53 => none
  | .ex_92 => none
  | .ex_92_det => none
  | .ex_107a => none
  | .ex_107b => none
  | .ex_108a => none
  | .ex_108b => none
  | .ex_109a => none
  | .ex_109b => none
  | .ex_110a => none
  | .ex_110b => none
  | .ex_149a => none
  | .ex_149b => none
  | .ex_149c => none
  | .ex_149d => none
  | .ex_150a => none
  | .ex_150b => none
  | .ex_151a => none
  | .ex_151b => none
  | .ex_153a => none
  | .ex_153b => none
  | .ex_153c => none
  | .ex_153d => none
  | .ex_187a => none
  | .ex_187b => none
  | .ex_200a => none
  | .ex_200b => none
  | .ex_201a => none
  | .ex_201b => none
  | .ex_202a => some .direct
  | .ex_202b => some .indirect
  | .ex_204a => some .direct
  | .ex_204b => some .indirect
  | .ex_207a => none
  | .ex_207a_bare => none
  | .ex_207b => none
  | .ex_212a => none
  | .ex_216a => none
  | .ex_216b => none
  | .ex_219 => none
  | .ex_219_bare => none

theorem Example.objectMarked_datum :
    ∀ x : Example, _root_.Newman2024.Examples.objectMarked x.datum = x.objectMarked := by
  decide +kernel

/-- The readings the example judges, each with its judgment. -/
def Example.readings : Example → List (Reading × Judgment)
  | .ex_50 => []
  | .ex_51 => []
  | .ex_52 => []
  | .ex_53 => []
  | .ex_92 => []
  | .ex_92_det => []
  | .ex_107a => []
  | .ex_107b => []
  | .ex_108a => [(.subjectFirst, .acceptable), (.objectFirst, .ungrammatical)]
  | .ex_108b => [(.subjectFirst, .ungrammatical), (.objectFirst, .acceptable)]
  | .ex_109a => [(.subjectFirst, .acceptable), (.objectFirst, .ungrammatical)]
  | .ex_109b => [(.subjectFirst, .ungrammatical), (.objectFirst, .acceptable)]
  | .ex_110a => [(.subjectFirst, .acceptable), (.objectFirst, .ungrammatical)]
  | .ex_110b => [(.subjectFirst, .ungrammatical), (.objectFirst, .acceptable)]
  | .ex_149a => []
  | .ex_149b => []
  | .ex_149c => []
  | .ex_149d => []
  | .ex_150a => []
  | .ex_150b => []
  | .ex_151a => []
  | .ex_151b => []
  | .ex_153a => []
  | .ex_153b => []
  | .ex_153c => []
  | .ex_153d => []
  | .ex_187a => []
  | .ex_187b => []
  | .ex_200a => []
  | .ex_200b => []
  | .ex_201a => []
  | .ex_201b => []
  | .ex_202a => []
  | .ex_202b => []
  | .ex_204a => []
  | .ex_204b => []
  | .ex_207a => []
  | .ex_207a_bare => []
  | .ex_207b => []
  | .ex_212a => []
  | .ex_216a => []
  | .ex_216b => []
  | .ex_219 => []
  | .ex_219_bare => []

/-- The judgment the example records for the reading, if it records one. -/
def Example.reading (x : Example) (r : Reading) : Option Judgment :=
  (x.readings.lookup r)

theorem Example.reading_datum : ∀ (x : Example) (r : Reading),
    _root_.Newman2024.Examples.reading x.datum r = x.reading r := by
  decide +kernel

end Newman2024.Examples
