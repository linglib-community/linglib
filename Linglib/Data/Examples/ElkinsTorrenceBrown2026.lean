module

public import Linglib.Data.Examples.Schema

/-!
# `ElkinsTorrenceBrown2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ElkinsTorrenceBrown2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ElkinsTorrenceBrown2026.Examples`.
-/

@[expose] public section

namespace ElkinsTorrenceBrown2026.Examples

def ex_10b : Datum :=
  { id := "elkinstorrencebrown2026_10b"
    source := ⟨"elkins-torrence-brown-2026", "(10b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye kyim?"
    glossedTokens := [("alkye", "who"), ("∅-∅-kyim", "COMPL-B2/3S-die")]
    glossedWords := [⟨['a', 'l', 'k', 'y', 'e'], ['w', 'h', 'o'], [⟨['a', 'l', 'k', 'y', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'k', 'y', 'i', 'm'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'd', 'i', 'e'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['k', 'y', 'i', 'm'], ['d', 'i', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "absolutive"), ("reflex", "blocked")] }

def ex_11b : Datum :=
  { id := "elkinstorrencebrown2026_11b"
    source := ⟨"elkins-torrence-brown-2026", "(11b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Titi' tjaq' Li'y?"
    glossedTokens := [("titi'", "what"), ("∅-∅-t-jaq'", "COMPL-B2/3SG-A2/3SG-open"), ("Li'y", "María")]
    glossedWords := [⟨['t', 'i', 't', 'i', '\''], ['w', 'h', 'a', 't'], [⟨['t', 'i', 't', 'i', '\''], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 't', '-', 'j', 'a', 'q', '\''], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', 'G', '-', 'A', '2', '/', '3', 'S', 'G', '-', 'o', 'p', 'e', 'n'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['t'], ['A', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['j', 'a', 'q', '\''], ['o', 'p', 'e', 'n'], some '-'⟩]⟩, ⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], [⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "absolutive"), ("reflex", "blocked")] }

def ex_12b : Datum :=
  { id := "elkinstorrencebrown2026_12b"
    source := ⟨"elkins-torrence-brown-2026", "(12b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye jq'on te tjpel ja'?"
    glossedTokens := [("alkye", "who"), ("∅-∅-jq'o-n", "COMPL-B2/3S-open-ANTIP"), ("t-e", "A2/3S-RN:PAT"), ("tjpel", "door"), ("ja'", "house")]
    glossedWords := [⟨['a', 'l', 'k', 'y', 'e'], ['w', 'h', 'o'], [⟨['a', 'l', 'k', 'y', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'j', 'q', '\'', 'o', '-', 'n'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'o', 'p', 'e', 'n', '-', 'A', 'N', 'T', 'I', 'P'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['j', 'q', '\'', 'o'], ['o', 'p', 'e', 'n'], some '-'⟩, ⟨['n'], ['A', 'N', 'T', 'I', 'P'], some '-'⟩]⟩, ⟨['t', '-', 'e'], ['A', '2', '/', '3', 'S', '-', 'R', 'N', ':', 'P', 'A', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['e'], ['R', 'N', ':', 'P', 'A', 'T'], some '-'⟩]⟩, ⟨['t', 'j', 'p', 'e', 'l'], ['d', 'o', 'o', 'r'], [⟨['t', 'j', 'p', 'e', 'l'], ['d', 'o', 'o', 'r'], none⟩]⟩, ⟨['j', 'a', '\''], ['h', 'o', 'u', 's', 'e'], [⟨['j', 'a', '\''], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "ergative"), ("reflex", "blocked")] }

def ex_13a : Datum :=
  { id := "elkinstorrencebrown2026_13a"
    source := ⟨"elkins-torrence-brown-2026", "(13a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "El tsu'n Li'y spik'b'il tu'n xb'uy."
    glossedTokens := [("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n", "A2/3SG-clean-DS"), ("Li'y", "María"), ("spik'b'il", "window"), ("t-u'n", "A2/3SG-RN:INS"), ("xb'uy", "rag")]
    glossedWords := [⟨['∅', '-', '∅', '-', 'e', 'l'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', 'G', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['e', 'l'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['t', '-', 's', 'u', '-', '\'', 'n'], ['A', '2', '/', '3', 'S', 'G', '-', 'c', 'l', 'e', 'a', 'n', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['s', 'u'], ['c', 'l', 'e', 'a', 'n'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], [⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], none⟩]⟩, ⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], [⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], none⟩]⟩, ⟨['t', '-', 'u', '\'', 'n'], ['A', '2', '/', '3', 'S', 'G', '-', 'R', 'N', ':', 'I', 'N', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['u', '\'', 'n'], ['R', 'N', ':', 'I', 'N', 'S'], some '-'⟩]⟩, ⟨['x', 'b', '\'', 'u', 'y'], ['r', 'a', 'g'], [⟨['x', 'b', '\'', 'u', 'y'], ['r', 'a', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("El tsu'na' Li'y spik'b'il tu'n xb'uy.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.1"), ("mover", "none"), ("reflex", "blocked")] }

def ex_13b : Datum :=
  { id := "elkinstorrencebrown2026_13b"
    source := ⟨"elkins-torrence-brown-2026", "(13b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqu'n el tsu'n(a') Li'y spik'b'il?"
    glossedTokens := [("al-qu'n", "what-RN:INS"), ("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n(=a')", "A2/3SG-clean-DS=MVMT"), ("Li'y", "María"), ("spik'b'il", "window")]
    glossedWords := [⟨['a', 'l', '-', 'q', 'u', '\'', 'n'], ['w', 'h', 'a', 't', '-', 'R', 'N', ':', 'I', 'N', 'S'], [⟨['a', 'l'], ['w', 'h', 'a', 't'], none⟩, ⟨['q', 'u', '\'', 'n'], ['R', 'N', ':', 'I', 'N', 'S'], some '-'⟩]⟩, ⟨['∅', '-', '∅', '-', 'e', 'l'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', 'G', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['e', 'l'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['t', '-', 's', 'u', '-', '\'', 'n', '(', '=', 'a', '\'', ')'], ['A', '2', '/', '3', 'S', 'G', '-', 'c', 'l', 'e', 'a', 'n', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['s', 'u'], ['c', 'l', 'e', 'a', 'n'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], [⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], none⟩]⟩, ⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], [⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Alqu'n el tsu'na' Li'y spik'b'il?", .acceptable), ("Alqu'n el tsu'n Li'y spik'b'il?", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2.1"), ("mover", "instrument"), ("reflex", "licensed")] }

def ex_14b : Datum :=
  { id := "elkinstorrencebrown2026_14b"
    source := ⟨"elkins-torrence-brown-2026", "(14b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe tjaq'(a')ya tjpel ja'?"
    glossedTokens := [("al-qe", "who-RN:BEN"), ("∅-∅-t-jaq'(=a')=ya", "COMPL-B2/3SG-A2/3SG-open=MVMT=2P"), ("tjpel", "door"), ("ja'", "house")]
    glossedWords := [⟨['a', 'l', '-', 'q', 'e'], ['w', 'h', 'o', '-', 'R', 'N', ':', 'B', 'E', 'N'], [⟨['a', 'l'], ['w', 'h', 'o'], none⟩, ⟨['q', 'e'], ['R', 'N', ':', 'B', 'E', 'N'], some '-'⟩]⟩, ⟨['∅', '-', '∅', '-', 't', '-', 'j', 'a', 'q', '\'', '(', '=', 'a', '\'', ')', '=', 'y', 'a'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', 'G', '-', 'A', '2', '/', '3', 'S', 'G', '-', 'o', 'p', 'e', 'n', '=', 'M', 'V', 'M', 'T', '=', '2', 'P'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['t'], ['A', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['j', 'a', 'q', '\''], ['o', 'p', 'e', 'n'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩, ⟨['y', 'a'], ['2', 'P'], some '='⟩]⟩, ⟨['t', 'j', 'p', 'e', 'l'], ['d', 'o', 'o', 'r'], [⟨['t', 'j', 'p', 'e', 'l'], ['d', 'o', 'o', 'r'], none⟩]⟩, ⟨['j', 'a', '\''], ['h', 'o', 'u', 's', 'e'], [⟨['j', 'a', '\''], ['h', 'o', 'u', 's', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("mover", "benefactive"), ("reflex", "licensed")] }

def ex_15b : Datum :=
  { id := "elkinstorrencebrown2026_15b"
    source := ⟨"elkins-torrence-brown-2026", "(15b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe' xi' kq'o'n(a)ye' saqchb'il?"
    glossedTokens := [("al-qe", "who-RN:DAT"), ("∅-∅-xi'", "COMPL-B2/3SG-DIR"), ("k-q'o-'n(=a')=ye'", "A2/3P-give-DS=MVMT=2P"), ("saqchb'il", "toy")]
    glossedWords := [⟨['a', 'l', '-', 'q', 'e'], ['w', 'h', 'o', '-', 'R', 'N', ':', 'D', 'A', 'T'], [⟨['a', 'l'], ['w', 'h', 'o'], none⟩, ⟨['q', 'e'], ['R', 'N', ':', 'D', 'A', 'T'], some '-'⟩]⟩, ⟨['∅', '-', '∅', '-', 'x', 'i', '\''], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', 'G', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['x', 'i', '\''], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['k', '-', 'q', '\'', 'o', '-', '\'', 'n', '(', '=', 'a', '\'', ')', '=', 'y', 'e', '\''], ['A', '2', '/', '3', 'P', '-', 'g', 'i', 'v', 'e', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T', '=', '2', 'P'], [⟨['k'], ['A', '2', '/', '3', 'P'], none⟩, ⟨['q', '\'', 'o'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩, ⟨['y', 'e', '\''], ['2', 'P'], some '='⟩]⟩, ⟨['s', 'a', 'q', 'c', 'h', 'b', '\'', 'i', 'l'], ['t', 'o', 'y'], [⟨['s', 'a', 'q', 'c', 'h', 'b', '\'', 'i', 'l'], ['t', 'o', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("mover", "dative"), ("reflex", "licensed")] }

def ex_16b : Datum :=
  { id := "elkinstorrencebrown2026_16b"
    source := ⟨"elkins-torrence-brown-2026", "(16b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja e' chiyon(a') tx'yan ewi?"
    glossedTokens := [("ja", "where"), ("∅-e'", "COMPL-B2/3P"), ("chiyo-n(=a')", "bark-ANTIP=MVMT"), ("tx'yan", "dog")]
    glossedWords := [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['∅', '-', 'e', '\''], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'P'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['e', '\''], ['B', '2', '/', '3', 'P'], some '-'⟩]⟩, ⟨['c', 'h', 'i', 'y', 'o', '-', 'n', '(', '=', 'a', '\'', ')'], ['b', 'a', 'r', 'k', '-', 'A', 'N', 'T', 'I', 'P', '=', 'M', 'V', 'M', 'T'], [⟨['c', 'h', 'i', 'y', 'o'], ['b', 'a', 'r', 'k'], none⟩, ⟨['n'], ['A', 'N', 'T', 'I', 'P'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['t', 'x', '\'', 'y', 'a', 'n'], ['d', 'o', 'g'], [⟨['t', 'x', '\'', 'y', 'a', 'n'], ['d', 'o', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.3"), ("mover", "locative"), ("reflex", "licensed")] }

def ex_17b : Datum :=
  { id := "elkinstorrencebrown2026_17b"
    source := ⟨"elkins-torrence-brown-2026", "(17b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Tiqu'n el tsu'n(a') Li'y spik'b'il tu'n xb'uy?"
    glossedTokens := [("ti'-qu'n", "what-RN:REASON"), ("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n(=a')", "A2/3SG-clean-DS=MVMT"), ("Li'y", "María"), ("spik'b'il", "window"), ("t-u'n", "A2/3SG-RN:INS"), ("xb'uy", "rag")]
    glossedWords := [⟨['t', 'i', '\'', '-', 'q', 'u', '\'', 'n'], ['w', 'h', 'a', 't', '-', 'R', 'N', ':', 'R', 'E', 'A', 'S', 'O', 'N'], [⟨['t', 'i', '\''], ['w', 'h', 'a', 't'], none⟩, ⟨['q', 'u', '\'', 'n'], ['R', 'N', ':', 'R', 'E', 'A', 'S', 'O', 'N'], some '-'⟩]⟩, ⟨['∅', '-', '∅', '-', 'e', 'l'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', 'G', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['e', 'l'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['t', '-', 's', 'u', '-', '\'', 'n', '(', '=', 'a', '\'', ')'], ['A', '2', '/', '3', 'S', 'G', '-', 'c', 'l', 'e', 'a', 'n', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['s', 'u'], ['c', 'l', 'e', 'a', 'n'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], [⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], none⟩]⟩, ⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], [⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], none⟩]⟩, ⟨['t', '-', 'u', '\'', 'n'], ['A', '2', '/', '3', 'S', 'G', '-', 'R', 'N', ':', 'I', 'N', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['u', '\'', 'n'], ['R', 'N', ':', 'I', 'N', 'S'], some '-'⟩]⟩, ⟨['x', 'b', '\'', 'u', 'y'], ['r', 'a', 'g'], [⟨['x', 'b', '\'', 'u', 'y'], ['r', 'a', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("mover", "reason"), ("reflex", "licensed")] }

def ex_18b : Datum :=
  { id := "elkinstorrencebrown2026_18b"
    source := ⟨"elkins-torrence-brown-2026", "(18b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Tiqu'n tjoy(a') Xwan tx'yol toj k'ul?"
    glossedTokens := [("ti'-qu'n", "what-RN:PURP"), ("∅-∅-t-joy(=a')", "COMPL-B2/3S-A2/3S-look.for=MVMT"), ("Xwan", "Juan"), ("tx'yol", "mushroom"), ("t-oj", "A2/3S-RN:in"), ("k'ul", "forest")]
    glossedWords := [⟨['t', 'i', '\'', '-', 'q', 'u', '\'', 'n'], ['w', 'h', 'a', 't', '-', 'R', 'N', ':', 'P', 'U', 'R', 'P'], [⟨['t', 'i', '\''], ['w', 'h', 'a', 't'], none⟩, ⟨['q', 'u', '\'', 'n'], ['R', 'N', ':', 'P', 'U', 'R', 'P'], some '-'⟩]⟩, ⟨['∅', '-', '∅', '-', 't', '-', 'j', 'o', 'y', '(', '=', 'a', '\'', ')'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'A', '2', '/', '3', 'S', '-', 'l', 'o', 'o', 'k', '.', 'f', 'o', 'r', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['t'], ['A', '2', '/', '3', 'S'], some '-'⟩, ⟨['j', 'o', 'y'], ['l', 'o', 'o', 'k', '.', 'f', 'o', 'r'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['t', 'x', '\'', 'y', 'o', 'l'], ['m', 'u', 's', 'h', 'r', 'o', 'o', 'm'], [⟨['t', 'x', '\'', 'y', 'o', 'l'], ['m', 'u', 's', 'h', 'r', 'o', 'o', 'm'], none⟩]⟩, ⟨['t', '-', 'o', 'j'], ['A', '2', '/', '3', 'S', '-', 'R', 'N', ':', 'i', 'n'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['o', 'j'], ['R', 'N', ':', 'i', 'n'], some '-'⟩]⟩, ⟨['k', '\'', 'u', 'l'], ['f', 'o', 'r', 'e', 's', 't'], [⟨['k', '\'', 'u', 'l'], ['f', 'o', 'r', 'e', 's', 't'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("mover", "purpose"), ("reflex", "licensed")] }

def ex_19b : Datum :=
  { id := "elkinstorrencebrown2026_19b"
    source := ⟨"elkins-torrence-brown-2026", "(19b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Se'ntu'mel kub' tpa'n(a') Li'y lmet?"
    glossedTokens := [("se'n=tu'mel", "how=ENCL"), ("∅-∅-kub'", "COMPL-B2/3SG-DIR"), ("t-pa-'n(=a')", "A2/3SG-break-DS=MVMT"), ("Li'y", "María"), ("lmet", "bottle")]
    glossedWords := [⟨['s', 'e', '\'', 'n', '=', 't', 'u', '\'', 'm', 'e', 'l'], ['h', 'o', 'w', '=', 'E', 'N', 'C', 'L'], [⟨['s', 'e', '\'', 'n'], ['h', 'o', 'w'], none⟩, ⟨['t', 'u', '\'', 'm', 'e', 'l'], ['E', 'N', 'C', 'L'], some '='⟩]⟩, ⟨['∅', '-', '∅', '-', 'k', 'u', 'b', '\''], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', 'G', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], some '-'⟩, ⟨['k', 'u', 'b', '\''], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['t', '-', 'p', 'a', '-', '\'', 'n', '(', '=', 'a', '\'', ')'], ['A', '2', '/', '3', 'S', 'G', '-', 'b', 'r', 'e', 'a', 'k', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['p', 'a'], ['b', 'r', 'e', 'a', 'k'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], [⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], none⟩]⟩, ⟨['l', 'm', 'e', 't'], ['b', 'o', 't', 't', 'l', 'e'], [⟨['l', 'm', 'e', 't'], ['b', 'o', 't', 't', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.2.5"), ("mover", "manner"), ("reflex", "licensed")] }

def ex_20b : Datum :=
  { id := "elkinstorrencebrown2026_20b"
    source := ⟨"elkins-torrence-brown-2026", "(20b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jtoj kxe'l telq'a'n Xwan chmek'?"
    glossedTokens := [("jtoj", "when.NON.PST"), ("k-xe'-l", "B2/3S-DIR-POT"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey")]
    glossedWords := [⟨['j', 't', 'o', 'j'], ['w', 'h', 'e', 'n', '.', 'N', 'O', 'N', '.', 'P', 'S', 'T'], [⟨['j', 't', 'o', 'j'], ['w', 'h', 'e', 'n', '.', 'N', 'O', 'N', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['k', '-', 'x', 'e', '\'', '-', 'l'], ['B', '2', '/', '3', 'S', '-', 'D', 'I', 'R', '-', 'P', 'O', 'T'], [⟨['k'], ['B', '2', '/', '3', 'S'], none⟩, ⟨['x', 'e', '\''], ['D', 'I', 'R'], some '-'⟩, ⟨['l'], ['P', 'O', 'T'], some '-'⟩]⟩, ⟨['t', '-', 'e', 'l', 'q', '\'', 'a', '-', '\'', 'n'], ['A', '2', '/', '3', 'S', '-', 's', 't', 'e', 'a', 'l', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['e', 'l', 'q', '\'', 'a'], ['s', 't', 'e', 'a', 'l'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], [⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Jtoj kxe'l telq'a'na' Xwan chmek'?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.6"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_21b : Datum :=
  { id := "elkinstorrencebrown2026_21b"
    source := ⟨"elkins-torrence-brown-2026", "(21b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jtoje xi' telq'a'n Xwan chmek'?"
    glossedTokens := [("jtoje", "when.PST"), ("∅-∅-xi'", "COMPL-B2/3S-DIR"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey")]
    glossedWords := [⟨['j', 't', 'o', 'j', 'e'], ['w', 'h', 'e', 'n', '.', 'P', 'S', 'T'], [⟨['j', 't', 'o', 'j', 'e'], ['w', 'h', 'e', 'n', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'x', 'i', '\''], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['x', 'i', '\''], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['t', '-', 'e', 'l', 'q', '\'', 'a', '-', '\'', 'n'], ['A', '2', '/', '3', 'S', '-', 's', 't', 'e', 'a', 'l', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['e', 'l', 'q', '\'', 'a'], ['s', 't', 'e', 'a', 'l'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], [⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Jtoje xi' telq'a'na' Xwan chmek'?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.6"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_22 : Datum :=
  { id := "elkinstorrencebrown2026_22"
    source := ⟨"elkins-torrence-brown-2026", "(22)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja jaw(a') xhchin(a') Luch?"
    glossedTokens := [("ja", "where"), ("∅-∅-jaw(=a')", "COMPL-B2/3S-DIR=MVMT"), ("xhchi-n(=a')", "shout-ANTIP=MVMT"), ("Luch", "Pedro")]
    glossedWords := [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'j', 'a', 'w', '(', '=', 'a', '\'', ')'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['j', 'a', 'w'], ['D', 'I', 'R'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['x', 'h', 'c', 'h', 'i', '-', 'n', '(', '=', 'a', '\'', ')'], ['s', 'h', 'o', 'u', 't', '-', 'A', 'N', 'T', 'I', 'P', '=', 'M', 'V', 'M', 'T'], [⟨['x', 'h', 'c', 'h', 'i'], ['s', 'h', 'o', 'u', 't'], none⟩, ⟨['n'], ['A', 'N', 'T', 'I', 'P'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['L', 'u', 'c', 'h'], ['P', 'e', 'd', 'r', 'o'], [⟨['L', 'u', 'c', 'h'], ['P', 'e', 'd', 'r', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("mover", "locative"), ("directionals", "1"), ("hosts", "2")] }

def ex_24 : Datum :=
  { id := "elkinstorrencebrown2026_24"
    source := ⟨"elkins-torrence-brown-2026", "(24)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Se'ntu'mel in tma'n(a') Li'y kye tzaj wulin(a') Xwan weye'?"
    glossedTokens := [("se'n=tu'mel", "how=ENCL"), ("in", "INC"), ("∅-t-ma-'n(=a')", "B2/3S-A2/3S-say-DS=MVMT"), ("Li'y", "María"), ("kye", "COMP"), ("∅-∅-tzaj", "COM-B2/3S-DIR"), ("wuli-n(=a')", "insult-ANTIP=MVMT"), ("Xwan", "Juan"), ("w-e=ye'", "A1S-RN:DAT=1S")]
    glossedWords := [⟨['s', 'e', '\'', 'n', '=', 't', 'u', '\'', 'm', 'e', 'l'], ['h', 'o', 'w', '=', 'E', 'N', 'C', 'L'], [⟨['s', 'e', '\'', 'n'], ['h', 'o', 'w'], none⟩, ⟨['t', 'u', '\'', 'm', 'e', 'l'], ['E', 'N', 'C', 'L'], some '='⟩]⟩, ⟨['i', 'n'], ['I', 'N', 'C'], [⟨['i', 'n'], ['I', 'N', 'C'], none⟩]⟩, ⟨['∅', '-', 't', '-', 'm', 'a', '-', '\'', 'n', '(', '=', 'a', '\'', ')'], ['B', '2', '/', '3', 'S', '-', 'A', '2', '/', '3', 'S', '-', 's', 'a', 'y', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['B', '2', '/', '3', 'S'], none⟩, ⟨['t'], ['A', '2', '/', '3', 'S'], some '-'⟩, ⟨['m', 'a'], ['s', 'a', 'y'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], [⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], none⟩]⟩, ⟨['k', 'y', 'e'], ['C', 'O', 'M', 'P'], [⟨['k', 'y', 'e'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 't', 'z', 'a', 'j'], ['C', 'O', 'M', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['t', 'z', 'a', 'j'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['w', 'u', 'l', 'i', '-', 'n', '(', '=', 'a', '\'', ')'], ['i', 'n', 's', 'u', 'l', 't', '-', 'A', 'N', 'T', 'I', 'P', '=', 'M', 'V', 'M', 'T'], [⟨['w', 'u', 'l', 'i'], ['i', 'n', 's', 'u', 'l', 't'], none⟩, ⟨['n'], ['A', 'N', 'T', 'I', 'P'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['w', '-', 'e', '=', 'y', 'e', '\''], ['A', '1', 'S', '-', 'R', 'N', ':', 'D', 'A', 'T', '=', '1', 'S'], [⟨['w'], ['A', '1', 'S'], none⟩, ⟨['e'], ['R', 'N', ':', 'D', 'A', 'T'], some '-'⟩, ⟨['y', 'e', '\''], ['1', 'S'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "manner"), ("embeddedSize", "cP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_26 : Datum :=
  { id := "elkinstorrencebrown2026_26"
    source := ⟨"elkins-torrence-brown-2026", "(26)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Mixti' b'i'n wu'ne' se'n kub' tbincha'n(a') Li'y bisiklet."
    glossedTokens := [("mixti'", "NEG"), ("∅-b'i-'n(*=a')", "B2/3S-know-PASS=MVMT"), ("w-u'n=e'", "A1S-RN:AGT=1S"), ("se'n", "how"), ("∅-∅-kub'(=a')", "COM-B2/3S-DIR=MVMT"), ("t-b'incha-'n(=a')", "A2/3S-repair-DS=MVMT"), ("Li'y", "María"), ("bisiklet", "bicycle")]
    glossedWords := [⟨['m', 'i', 'x', 't', 'i', '\''], ['N', 'E', 'G'], [⟨['m', 'i', 'x', 't', 'i', '\''], ['N', 'E', 'G'], none⟩]⟩, ⟨['∅', '-', 'b', '\'', 'i', '-', '\'', 'n', '(', '*', '=', 'a', '\'', ')'], ['B', '2', '/', '3', 'S', '-', 'k', 'n', 'o', 'w', '-', 'P', 'A', 'S', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['B', '2', '/', '3', 'S'], none⟩, ⟨['b', '\'', 'i'], ['k', 'n', 'o', 'w'], some '-'⟩, ⟨['\'', 'n', '*'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['w', '-', 'u', '\'', 'n', '=', 'e', '\''], ['A', '1', 'S', '-', 'R', 'N', ':', 'A', 'G', 'T', '=', '1', 'S'], [⟨['w'], ['A', '1', 'S'], none⟩, ⟨['u', '\'', 'n'], ['R', 'N', ':', 'A', 'G', 'T'], some '-'⟩, ⟨['e', '\''], ['1', 'S'], some '='⟩]⟩, ⟨['s', 'e', '\'', 'n'], ['h', 'o', 'w'], [⟨['s', 'e', '\'', 'n'], ['h', 'o', 'w'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'k', 'u', 'b', '\'', '(', '=', 'a', '\'', ')'], ['C', 'O', 'M', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['k', 'u', 'b', '\''], ['D', 'I', 'R'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['t', '-', 'b', '\'', 'i', 'n', 'c', 'h', 'a', '-', '\'', 'n', '(', '=', 'a', '\'', ')'], ['A', '2', '/', '3', 'S', '-', 'r', 'e', 'p', 'a', 'i', 'r', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['b', '\'', 'i', 'n', 'c', 'h', 'a'], ['r', 'e', 'p', 'a', 'i', 'r'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], [⟨['L', 'i', '\'', 'y'], ['M', 'a', 'r', 'í', 'a'], none⟩]⟩, ⟨['b', 'i', 's', 'i', 'k', 'l', 'e', 't'], ['b', 'i', 'c', 'y', 'c', 'l', 'e'], [⟨['b', 'i', 's', 'i', 'k', 'l', 'e', 't'], ['b', 'i', 'c', 'y', 'c', 'l', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "manner"), ("embeddedSize", "cP"), ("landing", "embedded"), ("matrixReflex", "blocked"), ("embeddedReflex", "licensed")] }

def ex_28 : Datum :=
  { id := "elkinstorrencebrown2026_28"
    source := ⟨"elkins-torrence-brown-2026", "(28)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja xi'(ya') telq'a'n(a) Xwan chmek' aju tzaj klq'o'n qya?"
    glossedTokens := [("ja", "where"), ("∅-∅-xi'(=ya')", "COMPL-B2/3S-DIR=MVMT"), ("t-elq'a-'n(=a')", "A2/3S-steal-DS=MVMT"), ("Xwan", "Juan"), ("chmek'", "turkey"), ("aju", "REL"), ("∅-∅-tzaj", "COMPL-B2/3S-DIR"), ("k-lq'o-'n", "A2/3P-buy-DS"), ("qya", "woman")]
    glossedWords := [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'x', 'i', '\'', '(', '=', 'y', 'a', '\'', ')'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['x', 'i', '\''], ['D', 'I', 'R'], some '-'⟩, ⟨['y', 'a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['t', '-', 'e', 'l', 'q', '\'', 'a', '-', '\'', 'n', '(', '=', 'a', '\'', ')'], ['A', '2', '/', '3', 'S', '-', 's', 't', 'e', 'a', 'l', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['e', 'l', 'q', '\'', 'a'], ['s', 't', 'e', 'a', 'l'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], [⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], none⟩]⟩, ⟨['a', 'j', 'u'], ['R', 'E', 'L'], [⟨['a', 'j', 'u'], ['R', 'E', 'L'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 't', 'z', 'a', 'j'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['t', 'z', 'a', 'j'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['k', '-', 'l', 'q', '\'', 'o', '-', '\'', 'n'], ['A', '2', '/', '3', 'P', '-', 'b', 'u', 'y', '-', 'D', 'S'], [⟨['k'], ['A', '2', '/', '3', 'P'], none⟩, ⟨['l', 'q', '\'', 'o'], ['b', 'u', 'y'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['q', 'y', 'a'], ['w', 'o', 'm', 'a', 'n'], [⟨['q', 'y', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("matrix locative (where Juan stole it)", .acceptable), ("relative-clause locative (where the women bought it)", .unacceptable)]
    paperFeatures := [("section", "3.2"), ("mover", "locative")] }

def ex_29a : Datum :=
  { id := "elkinstorrencebrown2026_29a"
    source := ⟨"elkins-torrence-brown-2026", "(29a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja xi' telq'a'n Xwan chmek' aju tzaj(a') klq'o'n(a') qya?"
    glossedTokens := [("ja", "where"), ("∅-∅-xi'", "COMPL-B2/3S-DIR"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey"), ("aju", "REL"), ("∅-∅-tzaj(=a')", "COMPL-B2/3S-DIR=MVMT"), ("k-lq'o-'n(=a')", "A2/3P-buy-DS=MVMT"), ("qya", "woman")]
    glossedWords := [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'x', 'i', '\''], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['x', 'i', '\''], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['t', '-', 'e', 'l', 'q', '\'', 'a', '-', '\'', 'n'], ['A', '2', '/', '3', 'S', '-', 's', 't', 'e', 'a', 'l', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['e', 'l', 'q', '\'', 'a'], ['s', 't', 'e', 'a', 'l'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], [⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], none⟩]⟩, ⟨['a', 'j', 'u'], ['R', 'E', 'L'], [⟨['a', 'j', 'u'], ['R', 'E', 'L'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 't', 'z', 'a', 'j', '(', '=', 'a', '\'', ')'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['t', 'z', 'a', 'j'], ['D', 'I', 'R'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['k', '-', 'l', 'q', '\'', 'o', '-', '\'', 'n', '(', '=', 'a', '\'', ')'], ['A', '2', '/', '3', 'P', '-', 'b', 'u', 'y', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['k'], ['A', '2', '/', '3', 'P'], none⟩, ⟨['l', 'q', '\'', 'o'], ['b', 'u', 'y'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['q', 'y', 'a'], ['w', 'o', 'm', 'a', 'n'], [⟨['q', 'y', 'a'], ['w', 'o', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "locative")] }

def ex_31 : Datum :=
  { id := "elkinstorrencebrown2026_31"
    source := ⟨"elkins-torrence-brown-2026", "(31)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jatu'mel chu'xh(a) tu'n tk'a'yit(a') chmek'?"
    glossedTokens := [("ja=tu'mel", "where=ENCL"), ("∅-chu'x(=a')", "B2/3S-be.difficult=MVMT"), ("t-u'n", "A2/3S-RN:PURP"), ("t-k'a'y-it(=a')", "A1S-sell-PASS=MVMT"), ("chmek'", "turkey")]
    glossedWords := [⟨['j', 'a', '=', 't', 'u', '\'', 'm', 'e', 'l'], ['w', 'h', 'e', 'r', 'e', '=', 'E', 'N', 'C', 'L'], [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], none⟩, ⟨['t', 'u', '\'', 'm', 'e', 'l'], ['E', 'N', 'C', 'L'], some '='⟩]⟩, ⟨['∅', '-', 'c', 'h', 'u', '\'', 'x', '(', '=', 'a', '\'', ')'], ['B', '2', '/', '3', 'S', '-', 'b', 'e', '.', 'd', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['B', '2', '/', '3', 'S'], none⟩, ⟨['c', 'h', 'u', '\'', 'x'], ['b', 'e', '.', 'd', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['t', '-', 'u', '\'', 'n'], ['A', '2', '/', '3', 'S', '-', 'R', 'N', ':', 'P', 'U', 'R', 'P'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['u', '\'', 'n'], ['R', 'N', ':', 'P', 'U', 'R', 'P'], some '-'⟩]⟩, ⟨['t', '-', 'k', '\'', 'a', '\'', 'y', '-', 'i', 't', '(', '=', 'a', '\'', ')'], ['A', '1', 'S', '-', 's', 'e', 'l', 'l', '-', 'P', 'A', 'S', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['t'], ['A', '1', 'S'], none⟩, ⟨['k', '\'', 'a', '\'', 'y'], ['s', 'e', 'l', 'l'], some '-'⟩, ⟨['i', 't'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], [⟨['c', 'h', 'm', 'e', 'k', '\''], ['t', 'u', 'r', 'k', 'e', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("mover", "locative"), ("embeddedSize", "voiceP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_34 : Datum :=
  { id := "elkinstorrencebrown2026_34"
    source := ⟨"elkins-torrence-brown-2026", "(34)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe ok(a') kq'on(a')ye' Pabl jqol(*a') spik'b'il?"
    glossedTokens := [("al-qe", "who-RN:BEN"), ("∅-∅-ok(=a')", "COM-B2/3S-DIR=MVMT"), ("k-q'o-n(=a')=ye'", "A2/3P-make-DS=MVMT=2P"), ("Pabl", "Pablo"), ("jqo-l(*=a')", "open-INF=MVMT"), ("spik'b'il", "window")]
    glossedWords := [⟨['a', 'l', '-', 'q', 'e'], ['w', 'h', 'o', '-', 'R', 'N', ':', 'B', 'E', 'N'], [⟨['a', 'l'], ['w', 'h', 'o'], none⟩, ⟨['q', 'e'], ['R', 'N', ':', 'B', 'E', 'N'], some '-'⟩]⟩, ⟨['∅', '-', '∅', '-', 'o', 'k', '(', '=', 'a', '\'', ')'], ['C', 'O', 'M', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['o', 'k'], ['D', 'I', 'R'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['k', '-', 'q', '\'', 'o', '-', 'n', '(', '=', 'a', '\'', ')', '=', 'y', 'e', '\''], ['A', '2', '/', '3', 'P', '-', 'm', 'a', 'k', 'e', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T', '=', '2', 'P'], [⟨['k'], ['A', '2', '/', '3', 'P'], none⟩, ⟨['q', '\'', 'o'], ['m', 'a', 'k', 'e'], some '-'⟩, ⟨['n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩, ⟨['y', 'e', '\''], ['2', 'P'], some '='⟩]⟩, ⟨['P', 'a', 'b', 'l'], ['P', 'a', 'b', 'l', 'o'], [⟨['P', 'a', 'b', 'l'], ['P', 'a', 'b', 'l', 'o'], none⟩]⟩, ⟨['j', 'q', 'o', '-', 'l', '(', '*', '=', 'a', '\'', ')'], ['o', 'p', 'e', 'n', '-', 'I', 'N', 'F', '=', 'M', 'V', 'M', 'T'], [⟨['j', 'q', 'o'], ['o', 'p', 'e', 'n'], none⟩, ⟨['l', '*'], ['I', 'N', 'F'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], [⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.4"), ("mover", "benefactive"), ("embeddedSize", "bareVP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "blocked")] }

def ex_35c : Datum :=
  { id := "elkinstorrencebrown2026_35c"
    source := ⟨"elkins-torrence-brown-2026", "(35c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Iku' tzaj tlq'ona'"
    glossedTokens := [("iku'", "yes"), ("∅-∅-tzaj", "COM-B2/3S-DIR"), ("t-lq'o-'n=a'", "A2/3-buy-DS=MVMT")]
    glossedWords := [⟨['i', 'k', 'u', '\''], ['y', 'e', 's'], [⟨['i', 'k', 'u', '\''], ['y', 'e', 's'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 't', 'z', 'a', 'j'], ['C', 'O', 'M', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['t', 'z', 'a', 'j'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['t', '-', 'l', 'q', '\'', 'o', '-', '\'', 'n', '=', 'a', '\''], ['A', '2', '/', '3', '-', 'b', 'u', 'y', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['t'], ['A', '2', '/', '3'], none⟩, ⟨['l', 'q', '\'', 'o'], ['b', 'u', 'y'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answering: Did Juan buy the jocotes in the market?"
    judgment := .ungrammatical
    contrasts := [("Iku', atzu tzaj tlq'o'na'", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.5"), ("mover", "none"), ("reflex", "blocked")] }

def ex_37 : Datum :=
  { id := "elkinstorrencebrown2026_37"
    source := ⟨"elkins-torrence-brown-2026", "(37)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja'tumel e' k'a'yinjtz(a') muqin tu'n Xwan?"
    glossedTokens := [("ja=tu'mel", "where=ENCL"), ("e'", "COMPL"), ("∅-k'a'yi-njtz(=a')", "B2/3S-sell-PASS=MVMT"), ("muqin", "tortilla"), ("t-u'n", "A2/3S-RN:AGT"), ("Xwan", "Juan")]
    glossedWords := [⟨['j', 'a', '=', 't', 'u', '\'', 'm', 'e', 'l'], ['w', 'h', 'e', 'r', 'e', '=', 'E', 'N', 'C', 'L'], [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], none⟩, ⟨['t', 'u', '\'', 'm', 'e', 'l'], ['E', 'N', 'C', 'L'], some '='⟩]⟩, ⟨['e', '\''], ['C', 'O', 'M', 'P', 'L'], [⟨['e', '\''], ['C', 'O', 'M', 'P', 'L'], none⟩]⟩, ⟨['∅', '-', 'k', '\'', 'a', '\'', 'y', 'i', '-', 'n', 'j', 't', 'z', '(', '=', 'a', '\'', ')'], ['B', '2', '/', '3', 'S', '-', 's', 'e', 'l', 'l', '-', 'P', 'A', 'S', 'S', '=', 'M', 'V', 'M', 'T'], [⟨['∅'], ['B', '2', '/', '3', 'S'], none⟩, ⟨['k', '\'', 'a', '\'', 'y', 'i'], ['s', 'e', 'l', 'l'], some '-'⟩, ⟨['n', 'j', 't', 'z'], ['P', 'A', 'S', 'S'], some '-'⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['m', 'u', 'q', 'i', 'n'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], [⟨['m', 'u', 'q', 'i', 'n'], ['t', 'o', 'r', 't', 'i', 'l', 'l', 'a'], none⟩]⟩, ⟨['t', '-', 'u', '\'', 'n'], ['A', '2', '/', '3', 'S', '-', 'R', 'N', ':', 'A', 'G', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['u', '\'', 'n'], ['R', 'N', ':', 'A', 'G', 'T'], some '-'⟩]⟩, ⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['X', 'w', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.6"), ("mover", "locative"), ("reflex", "licensed"), ("voice", "passive")] }

def ex_38 : Datum :=
  { id := "elkinstorrencebrown2026_38"
    source := ⟨"elkins-torrence-brown-2026", "(38)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye tmaya qa el sun te spik'b'il tu'n xb'uy?"
    glossedTokens := [("alkye", "who"), ("∅-∅-t-ma=ya", "COM-B2/3S-A2/3S-say=2S"), ("qa", "COMP"), ("∅-∅-el", "COM-B2/3S-DIR"), ("su-n", "clean-ANTIP"), ("t-e", "A2/3S-RN:PAT"), ("spik'b'il", "window"), ("t-u'n", "A2/3S-RN:AGT"), ("xb'uy", "rag")]
    glossedWords := [⟨['a', 'l', 'k', 'y', 'e'], ['w', 'h', 'o'], [⟨['a', 'l', 'k', 'y', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 't', '-', 'm', 'a', '=', 'y', 'a'], ['C', 'O', 'M', '-', 'B', '2', '/', '3', 'S', '-', 'A', '2', '/', '3', 'S', '-', 's', 'a', 'y', '=', '2', 'S'], [⟨['∅'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['t'], ['A', '2', '/', '3', 'S'], some '-'⟩, ⟨['m', 'a'], ['s', 'a', 'y'], some '-'⟩, ⟨['y', 'a'], ['2', 'S'], some '='⟩]⟩, ⟨['q', 'a'], ['C', 'O', 'M', 'P'], [⟨['q', 'a'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'e', 'l'], ['C', 'O', 'M', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['e', 'l'], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['s', 'u', '-', 'n'], ['c', 'l', 'e', 'a', 'n', '-', 'A', 'N', 'T', 'I', 'P'], [⟨['s', 'u'], ['c', 'l', 'e', 'a', 'n'], none⟩, ⟨['n'], ['A', 'N', 'T', 'I', 'P'], some '-'⟩]⟩, ⟨['t', '-', 'e'], ['A', '2', '/', '3', 'S', '-', 'R', 'N', ':', 'P', 'A', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['e'], ['R', 'N', ':', 'P', 'A', 'T'], some '-'⟩]⟩, ⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], [⟨['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l'], ['w', 'i', 'n', 'd', 'o', 'w'], none⟩]⟩, ⟨['t', '-', 'u', '\'', 'n'], ['A', '2', '/', '3', 'S', '-', 'R', 'N', ':', 'A', 'G', 'T'], [⟨['t'], ['A', '2', '/', '3', 'S'], none⟩, ⟨['u', '\'', 'n'], ['R', 'N', ':', 'A', 'G', 'T'], some '-'⟩]⟩, ⟨['x', 'b', '\'', 'u', 'y'], ['r', 'a', 'g'], [⟨['x', 'b', '\'', 'u', 'y'], ['r', 'a', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.6"), ("mover", "ergative"), ("antipassive", "embedded only")] }

def ex_63 : Datum :=
  { id := "elkinstorrencebrown2026_63"
    source := ⟨"elkins-torrence-brown-2026", "(63)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja e' b'aj(a') el(a') laqj(a') kwetiy?"
    glossedTokens := [("ja", "where"), ("∅-e'", "COM-B2/3PL"), ("b'aj=a'", "DIR=MVMT"), ("el=a'", "DIR=MVMT"), ("laqj=a'", "explode=MVMT"), ("kwetiy", "fireworks")]
    glossedWords := [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], [⟨['j', 'a'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['∅', '-', 'e', '\''], ['C', 'O', 'M', '-', 'B', '2', '/', '3', 'P', 'L'], [⟨['∅'], ['C', 'O', 'M'], none⟩, ⟨['e', '\''], ['B', '2', '/', '3', 'P', 'L'], some '-'⟩]⟩, ⟨['b', '\'', 'a', 'j', '=', 'a', '\''], ['D', 'I', 'R', '=', 'M', 'V', 'M', 'T'], [⟨['b', '\'', 'a', 'j'], ['D', 'I', 'R'], none⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['e', 'l', '=', 'a', '\''], ['D', 'I', 'R', '=', 'M', 'V', 'M', 'T'], [⟨['e', 'l'], ['D', 'I', 'R'], none⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['l', 'a', 'q', 'j', '=', 'a', '\''], ['e', 'x', 'p', 'l', 'o', 'd', 'e', '=', 'M', 'V', 'M', 'T'], [⟨['l', 'a', 'q', 'j'], ['e', 'x', 'p', 'l', 'o', 'd', 'e'], none⟩, ⟨['a', '\''], ['M', 'V', 'M', 'T'], some '='⟩]⟩, ⟨['k', 'w', 'e', 't', 'i', 'y'], ['f', 'i', 'r', 'e', 'w', 'o', 'r', 'k', 's'], [⟨['k', 'w', 'e', 't', 'i', 'y'], ['f', 'i', 'r', 'e', 'w', 'o', 'r', 'k', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("mover", "locative"), ("directionals", "2"), ("hosts", "3")] }

def ex_65 : Datum :=
  { id := "elkinstorrencebrown2026_65"
    source := ⟨"elkins-torrence-brown-2026", "(65)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jni' hor kub' kjone' chib'j?"
    glossedTokens := [("jni'", "how.many"), ("hor", "hour"), ("∅-∅-kub'", "COMPL-B2/3S-DIR"), ("k-jon(*=a)=e'", "A2/3PL-cut-DS=MVMT=2PL"), ("chib'j", "meat")]
    glossedWords := [⟨['j', 'n', 'i', '\''], ['h', 'o', 'w', '.', 'm', 'a', 'n', 'y'], [⟨['j', 'n', 'i', '\''], ['h', 'o', 'w', '.', 'm', 'a', 'n', 'y'], none⟩]⟩, ⟨['h', 'o', 'r'], ['h', 'o', 'u', 'r'], [⟨['h', 'o', 'r'], ['h', 'o', 'u', 'r'], none⟩]⟩, ⟨['∅', '-', '∅', '-', 'k', 'u', 'b', '\''], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', '/', '3', 'S', '-', 'D', 'I', 'R'], [⟨['∅'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '2', '/', '3', 'S'], some '-'⟩, ⟨['k', 'u', 'b', '\''], ['D', 'I', 'R'], some '-'⟩]⟩, ⟨['k', '-', 'j', 'o', 'n', '(', '*', '=', 'a', ')', '=', 'e', '\''], ['A', '2', '/', '3', 'P', 'L', '-', 'c', 'u', 't', '-', 'D', 'S', '=', 'M', 'V', 'M', 'T', '=', '2', 'P', 'L'], []⟩, ⟨['c', 'h', 'i', 'b', '\'', 'j'], ['m', 'e', 'a', 't'], [⟨['c', 'h', 'i', 'b', '\'', 'j'], ['m', 'e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Jni' hor kub' kjonae' chib'j?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.3"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_51 : Datum :=
  { id := "elkinstorrencebrown2026_51"
    source := ⟨"mendes-ranero-2021", "(2)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(51)"⟩
    language := "kich1262"
    primaryText := "Jawi xatb'ee wi iwiir?"
    glossedTokens := [("Jawi", "where"), ("x-at-b'ee", "COMPL-B2SG-go"), ("*(wi)", "FP"), ("iwiir", "yesterday")]
    glossedWords := [⟨['J', 'a', 'w', 'i'], ['w', 'h', 'e', 'r', 'e'], [⟨['J', 'a', 'w', 'i'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['x', '-', 'a', 't', '-', 'b', '\'', 'e', 'e'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '2', 'S', 'G', '-', 'g', 'o'], [⟨['x'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['a', 't'], ['B', '2', 'S', 'G'], some '-'⟩, ⟨['b', '\'', 'e', 'e'], ['g', 'o'], some '-'⟩]⟩, ⟨['*', '(', 'w', 'i', ')'], ['F', 'P'], [⟨['*', 'w', 'i'], ['F', 'P'], none⟩]⟩, ⟨['i', 'w', 'i', 'i', 'r'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['i', 'w', 'i', 'i', 'r'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Jawi xatb'ee iwiir?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "locative"), ("reflex", "licensed")] }

def ex_52 : Datum :=
  { id := "elkinstorrencebrown2026_52"
    source := ⟨"mendes-ranero-2021", "(17)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(52)"⟩
    language := "kich1262"
    primaryText := "Jawi xkib'iij wi chi ke'e wi?"
    glossedTokens := [("Jawi", "where"), ("x-∅-ki-b'iij", "COMPL-B3SG-A3SG-say"), ("*(wi)", "FP"), ("chi", "COMP"), ("k-e-'e", "INC-B3PL-go"), ("*(wi)", "FP")]
    glossedWords := [⟨['J', 'a', 'w', 'i'], ['w', 'h', 'e', 'r', 'e'], [⟨['J', 'a', 'w', 'i'], ['w', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['x', '-', '∅', '-', 'k', 'i', '-', 'b', '\'', 'i', 'i', 'j'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '3', 'S', 'G', '-', 'A', '3', 'S', 'G', '-', 's', 'a', 'y'], [⟨['x'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['k', 'i'], ['A', '3', 'S', 'G'], some '-'⟩, ⟨['b', '\'', 'i', 'i', 'j'], ['s', 'a', 'y'], some '-'⟩]⟩, ⟨['*', '(', 'w', 'i', ')'], ['F', 'P'], [⟨['*', 'w', 'i'], ['F', 'P'], none⟩]⟩, ⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], [⟨['c', 'h', 'i'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['k', '-', 'e', '-', '\'', 'e'], ['I', 'N', 'C', '-', 'B', '3', 'P', 'L', '-', 'g', 'o'], [⟨['k'], ['I', 'N', 'C'], none⟩, ⟨['e'], ['B', '3', 'P', 'L'], some '-'⟩, ⟨['\'', 'e'], ['g', 'o'], some '-'⟩]⟩, ⟨['*', '(', 'w', 'i', ')'], ['F', 'P'], [⟨['*', 'w', 'i'], ['F', 'P'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "locative"), ("embeddedSize", "cP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_53 : Datum :=
  { id := "elkinstorrencebrown2026_53"
    source := ⟨"mendes-ranero-2021", "(19)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(53)"⟩
    language := "kich1262"
    primaryText := "Jas ruuk' karayiij katij wi le wa?"
    glossedTokens := [("Jas", "WH"), ("r-uuk'", "A3SG-RN"), ("k-∅-a-rayii-j", "INC-B3SG-A2SG-desire-ACT"), ("(*wi)", "FP"), ("k-∅-a-tij", "INC-B3SG-A2SG-eat"), ("*(wi)", "FP"), ("le", "DET"), ("wa", "food")]
    glossedWords := [⟨['J', 'a', 's'], ['W', 'H'], [⟨['J', 'a', 's'], ['W', 'H'], none⟩]⟩, ⟨['r', '-', 'u', 'u', 'k', '\''], ['A', '3', 'S', 'G', '-', 'R', 'N'], [⟨['r'], ['A', '3', 'S', 'G'], none⟩, ⟨['u', 'u', 'k', '\''], ['R', 'N'], some '-'⟩]⟩, ⟨['k', '-', '∅', '-', 'a', '-', 'r', 'a', 'y', 'i', 'i', '-', 'j'], ['I', 'N', 'C', '-', 'B', '3', 'S', 'G', '-', 'A', '2', 'S', 'G', '-', 'd', 'e', 's', 'i', 'r', 'e', '-', 'A', 'C', 'T'], [⟨['k'], ['I', 'N', 'C'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['a'], ['A', '2', 'S', 'G'], some '-'⟩, ⟨['r', 'a', 'y', 'i', 'i'], ['d', 'e', 's', 'i', 'r', 'e'], some '-'⟩, ⟨['j'], ['A', 'C', 'T'], some '-'⟩]⟩, ⟨['(', '*', 'w', 'i', ')'], ['F', 'P'], [⟨['*', 'w', 'i'], ['F', 'P'], none⟩]⟩, ⟨['k', '-', '∅', '-', 'a', '-', 't', 'i', 'j'], ['I', 'N', 'C', '-', 'B', '3', 'S', 'G', '-', 'A', '2', 'S', 'G', '-', 'e', 'a', 't'], [⟨['k'], ['I', 'N', 'C'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['a'], ['A', '2', 'S', 'G'], some '-'⟩, ⟨['t', 'i', 'j'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['*', '(', 'w', 'i', ')'], ['F', 'P'], [⟨['*', 'w', 'i'], ['F', 'P'], none⟩]⟩, ⟨['l', 'e'], ['D', 'E', 'T'], [⟨['l', 'e'], ['D', 'E', 'T'], none⟩]⟩, ⟨['w', 'a'], ['f', 'o', 'o', 'd'], [⟨['w', 'a'], ['f', 'o', 'o', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "instrument"), ("embeddedSize", "aspP"), ("landing", "matrix"), ("matrixReflex", "blocked"), ("embeddedReflex", "licensed")] }

def ex_64 : Datum :=
  { id := "elkinstorrencebrown2026_64"
    source := ⟨"mendes-ranero-2021", "(14a)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(64)"⟩
    language := "kaqc1270"
    primaryText := "Achike ruma xsamäj ri a Juan?"
    glossedTokens := [("Achike", "what"), ("ru-ma", "A3SG-RN"), ("x-∅-samäj", "COMPL-B3SG-work"), ("(*wi)", "FP"), ("ri", "DET"), ("a", "CLF"), ("Juan", "Juan")]
    glossedWords := [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'a', 't'], [⟨['A', 'c', 'h', 'i', 'k', 'e'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['r', 'u', '-', 'm', 'a'], ['A', '3', 'S', 'G', '-', 'R', 'N'], [⟨['r', 'u'], ['A', '3', 'S', 'G'], none⟩, ⟨['m', 'a'], ['R', 'N'], some '-'⟩]⟩, ⟨['x', '-', '∅', '-', 's', 'a', 'm', 'ä', 'j'], ['C', 'O', 'M', 'P', 'L', '-', 'B', '3', 'S', 'G', '-', 'w', 'o', 'r', 'k'], [⟨['x'], ['C', 'O', 'M', 'P', 'L'], none⟩, ⟨['∅'], ['B', '3', 'S', 'G'], some '-'⟩, ⟨['s', 'a', 'm', 'ä', 'j'], ['w', 'o', 'r', 'k'], some '-'⟩]⟩, ⟨['(', '*', 'w', 'i', ')'], ['F', 'P'], [⟨['*', 'w', 'i'], ['F', 'P'], none⟩]⟩, ⟨['r', 'i'], ['D', 'E', 'T'], [⟨['r', 'i'], ['D', 'E', 'T'], none⟩]⟩, ⟨['a'], ['C', 'L', 'F'], [⟨['a'], ['C', 'L', 'F'], none⟩]⟩, ⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Achike ruma xsamäj wi ri a Juan?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.3"), ("mover", "reason"), ("reflex", "blocked")] }

def all : List Datum := [ex_10b, ex_11b, ex_12b, ex_13a, ex_13b, ex_14b, ex_15b, ex_16b, ex_17b, ex_18b, ex_19b, ex_20b, ex_21b, ex_22, ex_24, ex_26, ex_28, ex_29a, ex_31, ex_34, ex_35c, ex_37, ex_38, ex_63, ex_65, ex_51, ex_52, ex_53, ex_64]

end ElkinsTorrenceBrown2026.Examples
