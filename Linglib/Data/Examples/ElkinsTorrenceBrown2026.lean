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
    glossedWords := [⟨[['a', 'l', 'k', 'y', 'e']], [['w', 'h', 'o']]⟩, ⟨[['∅'], ['∅'], ['k', 'y', 'i', 'm']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['d', 'i', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "absolutive"), ("reflex", "blocked")] }

def ex_11b : Datum :=
  { id := "elkinstorrencebrown2026_11b"
    source := ⟨"elkins-torrence-brown-2026", "(11b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Titi' tjaq' Li'y?"
    glossedTokens := [("titi'", "what"), ("∅-∅-t-jaq'", "COMPL-B2/3SG-A2/3SG-open"), ("Li'y", "María")]
    glossedWords := [⟨[['t', 'i', 't', 'i', '\'']], [['w', 'h', 'a', 't']]⟩, ⟨[['∅'], ['∅'], ['t'], ['j', 'a', 'q', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S', 'G'], ['A', '2', '/', '3', 'S', 'G'], ['o', 'p', 'e', 'n']]⟩, ⟨[['L', 'i', '\'', 'y']], [['M', 'a', 'r', 'í', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "absolutive"), ("reflex", "blocked")] }

def ex_12b : Datum :=
  { id := "elkinstorrencebrown2026_12b"
    source := ⟨"elkins-torrence-brown-2026", "(12b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye jq'on te tjpel ja'?"
    glossedTokens := [("alkye", "who"), ("∅-∅-jq'o-n", "COMPL-B2/3S-open-ANTIP"), ("t-e", "A2/3S-RN:PAT"), ("tjpel", "door"), ("ja'", "house")]
    glossedWords := [⟨[['a', 'l', 'k', 'y', 'e']], [['w', 'h', 'o']]⟩, ⟨[['∅'], ['∅'], ['j', 'q', '\'', 'o'], ['n']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['o', 'p', 'e', 'n'], ['A', 'N', 'T', 'I', 'P']]⟩, ⟨[['t'], ['e']], [['A', '2', '/', '3', 'S'], ['R', 'N', ':', 'P', 'A', 'T']]⟩, ⟨[['t', 'j', 'p', 'e', 'l']], [['d', 'o', 'o', 'r']]⟩, ⟨[['j', 'a', '\'']], [['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "ergative"), ("reflex", "blocked")] }

def ex_13a : Datum :=
  { id := "elkinstorrencebrown2026_13a"
    source := ⟨"elkins-torrence-brown-2026", "(13a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "El tsu'n Li'y spik'b'il tu'n xb'uy."
    glossedTokens := [("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n", "A2/3SG-clean-DS"), ("Li'y", "María"), ("spik'b'il", "window"), ("t-u'n", "A2/3SG-RN:INS"), ("xb'uy", "rag")]
    glossedWords := [⟨[['∅'], ['∅'], ['e', 'l']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S', 'G'], ['D', 'I', 'R']]⟩, ⟨[['t'], ['s', 'u'], ['\'', 'n']], [['A', '2', '/', '3', 'S', 'G'], ['c', 'l', 'e', 'a', 'n'], ['D', 'S']]⟩, ⟨[['L', 'i', '\'', 'y']], [['M', 'a', 'r', 'í', 'a']]⟩, ⟨[['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l']], [['w', 'i', 'n', 'd', 'o', 'w']]⟩, ⟨[['t'], ['u', '\'', 'n']], [['A', '2', '/', '3', 'S', 'G'], ['R', 'N', ':', 'I', 'N', 'S']]⟩, ⟨[['x', 'b', '\'', 'u', 'y']], [['r', 'a', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("El tsu'na' Li'y spik'b'il tu'n xb'uy.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.1"), ("mover", "none"), ("reflex", "blocked")] }

def ex_13b : Datum :=
  { id := "elkinstorrencebrown2026_13b"
    source := ⟨"elkins-torrence-brown-2026", "(13b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqu'n el tsu'n(a') Li'y spik'b'il?"
    glossedTokens := [("al-qu'n", "what-RN:INS"), ("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n(=a')", "A2/3SG-clean-DS=MVMT"), ("Li'y", "María"), ("spik'b'il", "window")]
    glossedWords := [⟨[['a', 'l'], ['q', 'u', '\'', 'n']], [['w', 'h', 'a', 't'], ['R', 'N', ':', 'I', 'N', 'S']]⟩, ⟨[['∅'], ['∅'], ['e', 'l']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S', 'G'], ['D', 'I', 'R']]⟩, ⟨[['t'], ['s', 'u'], ['\'', 'n'], ['a', '\'']], [['A', '2', '/', '3', 'S', 'G'], ['c', 'l', 'e', 'a', 'n'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['L', 'i', '\'', 'y']], [['M', 'a', 'r', 'í', 'a']]⟩, ⟨[['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l']], [['w', 'i', 'n', 'd', 'o', 'w']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Alqu'n el tsu'na' Li'y spik'b'il?", .acceptable), ("Alqu'n el tsu'n Li'y spik'b'il?", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2.1"), ("mover", "instrument"), ("reflex", "licensed")] }

def ex_14b : Datum :=
  { id := "elkinstorrencebrown2026_14b"
    source := ⟨"elkins-torrence-brown-2026", "(14b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe tjaq'(a')ya tjpel ja'?"
    glossedTokens := [("al-qe", "who-RN:BEN"), ("∅-∅-t-jaq'(=a')=ya", "COMPL-B2/3SG-A2/3SG-open=MVMT=2P"), ("tjpel", "door"), ("ja'", "house")]
    glossedWords := [⟨[['a', 'l'], ['q', 'e']], [['w', 'h', 'o'], ['R', 'N', ':', 'B', 'E', 'N']]⟩, ⟨[['∅'], ['∅'], ['t'], ['j', 'a', 'q', '\''], ['a', '\''], ['y', 'a']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S', 'G'], ['A', '2', '/', '3', 'S', 'G'], ['o', 'p', 'e', 'n'], ['M', 'V', 'M', 'T'], ['2', 'P']]⟩, ⟨[['t', 'j', 'p', 'e', 'l']], [['d', 'o', 'o', 'r']]⟩, ⟨[['j', 'a', '\'']], [['h', 'o', 'u', 's', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("mover", "benefactive"), ("reflex", "licensed")] }

def ex_15b : Datum :=
  { id := "elkinstorrencebrown2026_15b"
    source := ⟨"elkins-torrence-brown-2026", "(15b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe' xi' kq'o'n(a)ye' saqchb'il?"
    glossedTokens := [("al-qe", "who-RN:DAT"), ("∅-∅-xi'", "COMPL-B2/3SG-DIR"), ("k-q'o-'n(=a')=ye'", "A2/3P-give-DS=MVMT=2P"), ("saqchb'il", "toy")]
    glossedWords := [⟨[['a', 'l'], ['q', 'e']], [['w', 'h', 'o'], ['R', 'N', ':', 'D', 'A', 'T']]⟩, ⟨[['∅'], ['∅'], ['x', 'i', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S', 'G'], ['D', 'I', 'R']]⟩, ⟨[['k'], ['q', '\'', 'o'], ['\'', 'n'], ['a', '\''], ['y', 'e', '\'']], [['A', '2', '/', '3', 'P'], ['g', 'i', 'v', 'e'], ['D', 'S'], ['M', 'V', 'M', 'T'], ['2', 'P']]⟩, ⟨[['s', 'a', 'q', 'c', 'h', 'b', '\'', 'i', 'l']], [['t', 'o', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("mover", "dative"), ("reflex", "licensed")] }

def ex_16b : Datum :=
  { id := "elkinstorrencebrown2026_16b"
    source := ⟨"elkins-torrence-brown-2026", "(16b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja e' chiyon(a') tx'yan ewi?"
    glossedTokens := [("ja", "where"), ("∅-e'", "COMPL-B2/3P"), ("chiyo-n(=a')", "bark-ANTIP=MVMT"), ("tx'yan", "dog")]
    glossedWords := [⟨[['j', 'a']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['∅'], ['e', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'P']]⟩, ⟨[['c', 'h', 'i', 'y', 'o'], ['n'], ['a', '\'']], [['b', 'a', 'r', 'k'], ['A', 'N', 'T', 'I', 'P'], ['M', 'V', 'M', 'T']]⟩, ⟨[['t', 'x', '\'', 'y', 'a', 'n']], [['d', 'o', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.3"), ("mover", "locative"), ("reflex", "licensed")] }

def ex_17b : Datum :=
  { id := "elkinstorrencebrown2026_17b"
    source := ⟨"elkins-torrence-brown-2026", "(17b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Tiqu'n el tsu'n(a') Li'y spik'b'il tu'n xb'uy?"
    glossedTokens := [("ti'-qu'n", "what-RN:REASON"), ("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n(=a')", "A2/3SG-clean-DS=MVMT"), ("Li'y", "María"), ("spik'b'il", "window"), ("t-u'n", "A2/3SG-RN:INS"), ("xb'uy", "rag")]
    glossedWords := [⟨[['t', 'i', '\''], ['q', 'u', '\'', 'n']], [['w', 'h', 'a', 't'], ['R', 'N', ':', 'R', 'E', 'A', 'S', 'O', 'N']]⟩, ⟨[['∅'], ['∅'], ['e', 'l']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S', 'G'], ['D', 'I', 'R']]⟩, ⟨[['t'], ['s', 'u'], ['\'', 'n'], ['a', '\'']], [['A', '2', '/', '3', 'S', 'G'], ['c', 'l', 'e', 'a', 'n'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['L', 'i', '\'', 'y']], [['M', 'a', 'r', 'í', 'a']]⟩, ⟨[['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l']], [['w', 'i', 'n', 'd', 'o', 'w']]⟩, ⟨[['t'], ['u', '\'', 'n']], [['A', '2', '/', '3', 'S', 'G'], ['R', 'N', ':', 'I', 'N', 'S']]⟩, ⟨[['x', 'b', '\'', 'u', 'y']], [['r', 'a', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("mover", "reason"), ("reflex", "licensed")] }

def ex_18b : Datum :=
  { id := "elkinstorrencebrown2026_18b"
    source := ⟨"elkins-torrence-brown-2026", "(18b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Tiqu'n tjoy(a') Xwan tx'yol toj k'ul?"
    glossedTokens := [("ti'-qu'n", "what-RN:PURP"), ("∅-∅-t-joy(=a')", "COMPL-B2/3S-A2/3S-look.for=MVMT"), ("Xwan", "Juan"), ("tx'yol", "mushroom"), ("t-oj", "A2/3S-RN:in"), ("k'ul", "forest")]
    glossedWords := [⟨[['t', 'i', '\''], ['q', 'u', '\'', 'n']], [['w', 'h', 'a', 't'], ['R', 'N', ':', 'P', 'U', 'R', 'P']]⟩, ⟨[['∅'], ['∅'], ['t'], ['j', 'o', 'y'], ['a', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['A', '2', '/', '3', 'S'], ['l', 'o', 'o', 'k', '.', 'f', 'o', 'r'], ['M', 'V', 'M', 'T']]⟩, ⟨[['X', 'w', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['t', 'x', '\'', 'y', 'o', 'l']], [['m', 'u', 's', 'h', 'r', 'o', 'o', 'm']]⟩, ⟨[['t'], ['o', 'j']], [['A', '2', '/', '3', 'S'], ['R', 'N', ':', 'i', 'n']]⟩, ⟨[['k', '\'', 'u', 'l']], [['f', 'o', 'r', 'e', 's', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("mover", "purpose"), ("reflex", "licensed")] }

def ex_19b : Datum :=
  { id := "elkinstorrencebrown2026_19b"
    source := ⟨"elkins-torrence-brown-2026", "(19b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Se'ntu'mel kub' tpa'n(a') Li'y lmet?"
    glossedTokens := [("se'n=tu'mel", "how=ENCL"), ("∅-∅-kub'", "COMPL-B2/3SG-DIR"), ("t-pa-'n(=a')", "A2/3SG-break-DS=MVMT"), ("Li'y", "María"), ("lmet", "bottle")]
    glossedWords := [⟨[['s', 'e', '\'', 'n'], ['t', 'u', '\'', 'm', 'e', 'l']], [['h', 'o', 'w'], ['E', 'N', 'C', 'L']]⟩, ⟨[['∅'], ['∅'], ['k', 'u', 'b', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S', 'G'], ['D', 'I', 'R']]⟩, ⟨[['t'], ['p', 'a'], ['\'', 'n'], ['a', '\'']], [['A', '2', '/', '3', 'S', 'G'], ['b', 'r', 'e', 'a', 'k'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['L', 'i', '\'', 'y']], [['M', 'a', 'r', 'í', 'a']]⟩, ⟨[['l', 'm', 'e', 't']], [['b', 'o', 't', 't', 'l', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.5"), ("mover", "manner"), ("reflex", "licensed")] }

def ex_20b : Datum :=
  { id := "elkinstorrencebrown2026_20b"
    source := ⟨"elkins-torrence-brown-2026", "(20b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jtoj kxe'l telq'a'n Xwan chmek'?"
    glossedTokens := [("jtoj", "when.NON.PST"), ("k-xe'-l", "B2/3S-DIR-POT"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey")]
    glossedWords := [⟨[['j', 't', 'o', 'j']], [['w', 'h', 'e', 'n', '.', 'N', 'O', 'N', '.', 'P', 'S', 'T']]⟩, ⟨[['k'], ['x', 'e', '\''], ['l']], [['B', '2', '/', '3', 'S'], ['D', 'I', 'R'], ['P', 'O', 'T']]⟩, ⟨[['t'], ['e', 'l', 'q', '\'', 'a'], ['\'', 'n']], [['A', '2', '/', '3', 'S'], ['s', 't', 'e', 'a', 'l'], ['D', 'S']]⟩, ⟨[['X', 'w', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['c', 'h', 'm', 'e', 'k', '\'']], [['t', 'u', 'r', 'k', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jtoj kxe'l telq'a'na' Xwan chmek'?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.6"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_21b : Datum :=
  { id := "elkinstorrencebrown2026_21b"
    source := ⟨"elkins-torrence-brown-2026", "(21b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jtoje xi' telq'a'n Xwan chmek'?"
    glossedTokens := [("jtoje", "when.PST"), ("∅-∅-xi'", "COMPL-B2/3S-DIR"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey")]
    glossedWords := [⟨[['j', 't', 'o', 'j', 'e']], [['w', 'h', 'e', 'n', '.', 'P', 'S', 'T']]⟩, ⟨[['∅'], ['∅'], ['x', 'i', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R']]⟩, ⟨[['t'], ['e', 'l', 'q', '\'', 'a'], ['\'', 'n']], [['A', '2', '/', '3', 'S'], ['s', 't', 'e', 'a', 'l'], ['D', 'S']]⟩, ⟨[['X', 'w', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['c', 'h', 'm', 'e', 'k', '\'']], [['t', 'u', 'r', 'k', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jtoje xi' telq'a'na' Xwan chmek'?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.6"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_22 : Datum :=
  { id := "elkinstorrencebrown2026_22"
    source := ⟨"elkins-torrence-brown-2026", "(22)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja jaw(a') xhchin(a') Luch?"
    glossedTokens := [("ja", "where"), ("∅-∅-jaw(=a')", "COMPL-B2/3S-DIR=MVMT"), ("xhchi-n(=a')", "shout-ANTIP=MVMT"), ("Luch", "Pedro")]
    glossedWords := [⟨[['j', 'a']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['∅'], ['∅'], ['j', 'a', 'w'], ['a', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R'], ['M', 'V', 'M', 'T']]⟩, ⟨[['x', 'h', 'c', 'h', 'i'], ['n'], ['a', '\'']], [['s', 'h', 'o', 'u', 't'], ['A', 'N', 'T', 'I', 'P'], ['M', 'V', 'M', 'T']]⟩, ⟨[['L', 'u', 'c', 'h']], [['P', 'e', 'd', 'r', 'o']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("mover", "locative"), ("directionals", "1"), ("hosts", "2")] }

def ex_24 : Datum :=
  { id := "elkinstorrencebrown2026_24"
    source := ⟨"elkins-torrence-brown-2026", "(24)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Se'ntu'mel in tma'n(a') Li'y kye tzaj wulin(a') Xwan weye'?"
    glossedTokens := [("se'n=tu'mel", "how=ENCL"), ("in", "INC"), ("∅-t-ma-'n(=a')", "B2/3S-A2/3S-say-DS=MVMT"), ("Li'y", "María"), ("kye", "COMP"), ("∅-∅-tzaj", "COM-B2/3S-DIR"), ("wuli-n(=a')", "insult-ANTIP=MVMT"), ("Xwan", "Juan"), ("w-e=ye'", "A1S-RN:DAT=1S")]
    glossedWords := [⟨[['s', 'e', '\'', 'n'], ['t', 'u', '\'', 'm', 'e', 'l']], [['h', 'o', 'w'], ['E', 'N', 'C', 'L']]⟩, ⟨[['i', 'n']], [['I', 'N', 'C']]⟩, ⟨[['∅'], ['t'], ['m', 'a'], ['\'', 'n'], ['a', '\'']], [['B', '2', '/', '3', 'S'], ['A', '2', '/', '3', 'S'], ['s', 'a', 'y'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['L', 'i', '\'', 'y']], [['M', 'a', 'r', 'í', 'a']]⟩, ⟨[['k', 'y', 'e']], [['C', 'O', 'M', 'P']]⟩, ⟨[['∅'], ['∅'], ['t', 'z', 'a', 'j']], [['C', 'O', 'M'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R']]⟩, ⟨[['w', 'u', 'l', 'i'], ['n'], ['a', '\'']], [['i', 'n', 's', 'u', 'l', 't'], ['A', 'N', 'T', 'I', 'P'], ['M', 'V', 'M', 'T']]⟩, ⟨[['X', 'w', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['w'], ['e'], ['y', 'e', '\'']], [['A', '1', 'S'], ['R', 'N', ':', 'D', 'A', 'T'], ['1', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "manner"), ("embeddedSize", "cP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_26 : Datum :=
  { id := "elkinstorrencebrown2026_26"
    source := ⟨"elkins-torrence-brown-2026", "(26)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Mixti' b'i'n wu'ne' se'n kub' tbincha'n(a') Li'y bisiklet."
    glossedTokens := [("mixti'", "NEG"), ("∅-b'i-'n(*=a')", "B2/3S-know-PASS=MVMT"), ("w-u'n=e'", "A1S-RN:AGT=1S"), ("se'n", "how"), ("∅-∅-kub'(=a')", "COM-B2/3S-DIR=MVMT"), ("t-b'incha-'n(=a')", "A2/3S-repair-DS=MVMT"), ("Li'y", "María"), ("bisiklet", "bicycle")]
    glossedWords := [⟨[['m', 'i', 'x', 't', 'i', '\'']], [['N', 'E', 'G']]⟩, ⟨[['∅'], ['b', '\'', 'i'], ['\'', 'n', '*'], ['a', '\'']], [['B', '2', '/', '3', 'S'], ['k', 'n', 'o', 'w'], ['P', 'A', 'S', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['w'], ['u', '\'', 'n'], ['e', '\'']], [['A', '1', 'S'], ['R', 'N', ':', 'A', 'G', 'T'], ['1', 'S']]⟩, ⟨[['s', 'e', '\'', 'n']], [['h', 'o', 'w']]⟩, ⟨[['∅'], ['∅'], ['k', 'u', 'b', '\''], ['a', '\'']], [['C', 'O', 'M'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R'], ['M', 'V', 'M', 'T']]⟩, ⟨[['t'], ['b', '\'', 'i', 'n', 'c', 'h', 'a'], ['\'', 'n'], ['a', '\'']], [['A', '2', '/', '3', 'S'], ['r', 'e', 'p', 'a', 'i', 'r'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['L', 'i', '\'', 'y']], [['M', 'a', 'r', 'í', 'a']]⟩, ⟨[['b', 'i', 's', 'i', 'k', 'l', 'e', 't']], [['b', 'i', 'c', 'y', 'c', 'l', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "manner"), ("embeddedSize", "cP"), ("landing", "embedded"), ("matrixReflex", "blocked"), ("embeddedReflex", "licensed")] }

def ex_28 : Datum :=
  { id := "elkinstorrencebrown2026_28"
    source := ⟨"elkins-torrence-brown-2026", "(28)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja xi'(ya') telq'a'n(a) Xwan chmek' aju tzaj klq'o'n qya?"
    glossedTokens := [("ja", "where"), ("∅-∅-xi'(=ya')", "COMPL-B2/3S-DIR=MVMT"), ("t-elq'a-'n(=a')", "A2/3S-steal-DS=MVMT"), ("Xwan", "Juan"), ("chmek'", "turkey"), ("aju", "REL"), ("∅-∅-tzaj", "COMPL-B2/3S-DIR"), ("k-lq'o-'n", "A2/3P-buy-DS"), ("qya", "woman")]
    glossedWords := [⟨[['j', 'a']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['∅'], ['∅'], ['x', 'i', '\''], ['y', 'a', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R'], ['M', 'V', 'M', 'T']]⟩, ⟨[['t'], ['e', 'l', 'q', '\'', 'a'], ['\'', 'n'], ['a', '\'']], [['A', '2', '/', '3', 'S'], ['s', 't', 'e', 'a', 'l'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['X', 'w', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['c', 'h', 'm', 'e', 'k', '\'']], [['t', 'u', 'r', 'k', 'e', 'y']]⟩, ⟨[['a', 'j', 'u']], [['R', 'E', 'L']]⟩, ⟨[['∅'], ['∅'], ['t', 'z', 'a', 'j']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R']]⟩, ⟨[['k'], ['l', 'q', '\'', 'o'], ['\'', 'n']], [['A', '2', '/', '3', 'P'], ['b', 'u', 'y'], ['D', 'S']]⟩, ⟨[['q', 'y', 'a']], [['w', 'o', 'm', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix locative (where Juan stole it)", .acceptable), ("relative-clause locative (where the women bought it)", .unacceptable)]
    paperFeatures := [("section", "3.2"), ("mover", "locative")] }

def ex_29a : Datum :=
  { id := "elkinstorrencebrown2026_29a"
    source := ⟨"elkins-torrence-brown-2026", "(29a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja xi' telq'a'n Xwan chmek' aju tzaj(a') klq'o'n(a') qya?"
    glossedTokens := [("ja", "where"), ("∅-∅-xi'", "COMPL-B2/3S-DIR"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey"), ("aju", "REL"), ("∅-∅-tzaj(=a')", "COMPL-B2/3S-DIR=MVMT"), ("k-lq'o-'n(=a')", "A2/3P-buy-DS=MVMT"), ("qya", "woman")]
    glossedWords := [⟨[['j', 'a']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['∅'], ['∅'], ['x', 'i', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R']]⟩, ⟨[['t'], ['e', 'l', 'q', '\'', 'a'], ['\'', 'n']], [['A', '2', '/', '3', 'S'], ['s', 't', 'e', 'a', 'l'], ['D', 'S']]⟩, ⟨[['X', 'w', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['c', 'h', 'm', 'e', 'k', '\'']], [['t', 'u', 'r', 'k', 'e', 'y']]⟩, ⟨[['a', 'j', 'u']], [['R', 'E', 'L']]⟩, ⟨[['∅'], ['∅'], ['t', 'z', 'a', 'j'], ['a', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R'], ['M', 'V', 'M', 'T']]⟩, ⟨[['k'], ['l', 'q', '\'', 'o'], ['\'', 'n'], ['a', '\'']], [['A', '2', '/', '3', 'P'], ['b', 'u', 'y'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['q', 'y', 'a']], [['w', 'o', 'm', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "locative")] }

def ex_31 : Datum :=
  { id := "elkinstorrencebrown2026_31"
    source := ⟨"elkins-torrence-brown-2026", "(31)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jatu'mel chu'xh(a) tu'n tk'a'yit(a') chmek'?"
    glossedTokens := [("ja=tu'mel", "where=ENCL"), ("∅-chu'x(=a')", "B2/3S-be.difficult=MVMT"), ("t-u'n", "A2/3S-RN:PURP"), ("t-k'a'y-it(=a')", "A1S-sell-PASS=MVMT"), ("chmek'", "turkey")]
    glossedWords := [⟨[['j', 'a'], ['t', 'u', '\'', 'm', 'e', 'l']], [['w', 'h', 'e', 'r', 'e'], ['E', 'N', 'C', 'L']]⟩, ⟨[['∅'], ['c', 'h', 'u', '\'', 'x'], ['a', '\'']], [['B', '2', '/', '3', 'S'], ['b', 'e', '.', 'd', 'i', 'f', 'f', 'i', 'c', 'u', 'l', 't'], ['M', 'V', 'M', 'T']]⟩, ⟨[['t'], ['u', '\'', 'n']], [['A', '2', '/', '3', 'S'], ['R', 'N', ':', 'P', 'U', 'R', 'P']]⟩, ⟨[['t'], ['k', '\'', 'a', '\'', 'y'], ['i', 't'], ['a', '\'']], [['A', '1', 'S'], ['s', 'e', 'l', 'l'], ['P', 'A', 'S', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['c', 'h', 'm', 'e', 'k', '\'']], [['t', 'u', 'r', 'k', 'e', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("mover", "locative"), ("embeddedSize", "voiceP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_34 : Datum :=
  { id := "elkinstorrencebrown2026_34"
    source := ⟨"elkins-torrence-brown-2026", "(34)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe ok(a') kq'on(a')ye' Pabl jqol(*a') spik'b'il?"
    glossedTokens := [("al-qe", "who-RN:BEN"), ("∅-∅-ok(=a')", "COM-B2/3S-DIR=MVMT"), ("k-q'o-n(=a')=ye'", "A2/3P-make-DS=MVMT=2P"), ("Pabl", "Pablo"), ("jqo-l(*=a')", "open-INF=MVMT"), ("spik'b'il", "window")]
    glossedWords := [⟨[['a', 'l'], ['q', 'e']], [['w', 'h', 'o'], ['R', 'N', ':', 'B', 'E', 'N']]⟩, ⟨[['∅'], ['∅'], ['o', 'k'], ['a', '\'']], [['C', 'O', 'M'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R'], ['M', 'V', 'M', 'T']]⟩, ⟨[['k'], ['q', '\'', 'o'], ['n'], ['a', '\''], ['y', 'e', '\'']], [['A', '2', '/', '3', 'P'], ['m', 'a', 'k', 'e'], ['D', 'S'], ['M', 'V', 'M', 'T'], ['2', 'P']]⟩, ⟨[['P', 'a', 'b', 'l']], [['P', 'a', 'b', 'l', 'o']]⟩, ⟨[['j', 'q', 'o'], ['l', '*'], ['a', '\'']], [['o', 'p', 'e', 'n'], ['I', 'N', 'F'], ['M', 'V', 'M', 'T']]⟩, ⟨[['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l']], [['w', 'i', 'n', 'd', 'o', 'w']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("mover", "benefactive"), ("embeddedSize", "bareVP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "blocked")] }

def ex_35c : Datum :=
  { id := "elkinstorrencebrown2026_35c"
    source := ⟨"elkins-torrence-brown-2026", "(35c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Iku' tzaj tlq'ona'"
    glossedTokens := [("iku'", "yes"), ("∅-∅-tzaj", "COM-B2/3S-DIR"), ("t-lq'o-'n=a'", "A2/3-buy-DS=MVMT")]
    glossedWords := [⟨[['i', 'k', 'u', '\'']], [['y', 'e', 's']]⟩, ⟨[['∅'], ['∅'], ['t', 'z', 'a', 'j']], [['C', 'O', 'M'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R']]⟩, ⟨[['t'], ['l', 'q', '\'', 'o'], ['\'', 'n'], ['a', '\'']], [['A', '2', '/', '3'], ['b', 'u', 'y'], ['D', 'S'], ['M', 'V', 'M', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Answering: Did Juan buy the jocotes in the market?"
    judgment := .ungrammatical
    alternatives := [("Iku', atzu tzaj tlq'o'na'", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.5"), ("mover", "none"), ("reflex", "blocked")] }

def ex_37 : Datum :=
  { id := "elkinstorrencebrown2026_37"
    source := ⟨"elkins-torrence-brown-2026", "(37)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja'tumel e' k'a'yinjtz(a') muqin tu'n Xwan?"
    glossedTokens := [("ja=tu'mel", "where=ENCL"), ("e'", "COMPL"), ("∅-k'a'yi-njtz(=a')", "B2/3S-sell-PASS=MVMT"), ("muqin", "tortilla"), ("t-u'n", "A2/3S-RN:AGT"), ("Xwan", "Juan")]
    glossedWords := [⟨[['j', 'a'], ['t', 'u', '\'', 'm', 'e', 'l']], [['w', 'h', 'e', 'r', 'e'], ['E', 'N', 'C', 'L']]⟩, ⟨[['e', '\'']], [['C', 'O', 'M', 'P', 'L']]⟩, ⟨[['∅'], ['k', '\'', 'a', '\'', 'y', 'i'], ['n', 'j', 't', 'z'], ['a', '\'']], [['B', '2', '/', '3', 'S'], ['s', 'e', 'l', 'l'], ['P', 'A', 'S', 'S'], ['M', 'V', 'M', 'T']]⟩, ⟨[['m', 'u', 'q', 'i', 'n']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩, ⟨[['t'], ['u', '\'', 'n']], [['A', '2', '/', '3', 'S'], ['R', 'N', ':', 'A', 'G', 'T']]⟩, ⟨[['X', 'w', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.6"), ("mover", "locative"), ("reflex", "licensed"), ("voice", "passive")] }

def ex_38 : Datum :=
  { id := "elkinstorrencebrown2026_38"
    source := ⟨"elkins-torrence-brown-2026", "(38)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye tmaya qa el sun te spik'b'il tu'n xb'uy?"
    glossedTokens := [("alkye", "who"), ("∅-∅-t-ma=ya", "COM-B2/3S-A2/3S-say=2S"), ("qa", "COMP"), ("∅-∅-el", "COM-B2/3S-DIR"), ("su-n", "clean-ANTIP"), ("t-e", "A2/3S-RN:PAT"), ("spik'b'il", "window"), ("t-u'n", "A2/3S-RN:AGT"), ("xb'uy", "rag")]
    glossedWords := [⟨[['a', 'l', 'k', 'y', 'e']], [['w', 'h', 'o']]⟩, ⟨[['∅'], ['∅'], ['t'], ['m', 'a'], ['y', 'a']], [['C', 'O', 'M'], ['B', '2', '/', '3', 'S'], ['A', '2', '/', '3', 'S'], ['s', 'a', 'y'], ['2', 'S']]⟩, ⟨[['q', 'a']], [['C', 'O', 'M', 'P']]⟩, ⟨[['∅'], ['∅'], ['e', 'l']], [['C', 'O', 'M'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R']]⟩, ⟨[['s', 'u'], ['n']], [['c', 'l', 'e', 'a', 'n'], ['A', 'N', 'T', 'I', 'P']]⟩, ⟨[['t'], ['e']], [['A', '2', '/', '3', 'S'], ['R', 'N', ':', 'P', 'A', 'T']]⟩, ⟨[['s', 'p', 'i', 'k', '\'', 'b', '\'', 'i', 'l']], [['w', 'i', 'n', 'd', 'o', 'w']]⟩, ⟨[['t'], ['u', '\'', 'n']], [['A', '2', '/', '3', 'S'], ['R', 'N', ':', 'A', 'G', 'T']]⟩, ⟨[['x', 'b', '\'', 'u', 'y']], [['r', 'a', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.6"), ("mover", "ergative"), ("antipassive", "embedded only")] }

def ex_63 : Datum :=
  { id := "elkinstorrencebrown2026_63"
    source := ⟨"elkins-torrence-brown-2026", "(63)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja e' b'aj(a') el(a') laqj(a') kwetiy?"
    glossedTokens := [("ja", "where"), ("∅-e'", "COM-B2/3PL"), ("b'aj=a'", "DIR=MVMT"), ("el=a'", "DIR=MVMT"), ("laqj=a'", "explode=MVMT"), ("kwetiy", "fireworks")]
    glossedWords := [⟨[['j', 'a']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['∅'], ['e', '\'']], [['C', 'O', 'M'], ['B', '2', '/', '3', 'P', 'L']]⟩, ⟨[['b', '\'', 'a', 'j'], ['a', '\'']], [['D', 'I', 'R'], ['M', 'V', 'M', 'T']]⟩, ⟨[['e', 'l'], ['a', '\'']], [['D', 'I', 'R'], ['M', 'V', 'M', 'T']]⟩, ⟨[['l', 'a', 'q', 'j'], ['a', '\'']], [['e', 'x', 'p', 'l', 'o', 'd', 'e'], ['M', 'V', 'M', 'T']]⟩, ⟨[['k', 'w', 'e', 't', 'i', 'y']], [['f', 'i', 'r', 'e', 'w', 'o', 'r', 'k', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("mover", "locative"), ("directionals", "2"), ("hosts", "3")] }

def ex_65 : Datum :=
  { id := "elkinstorrencebrown2026_65"
    source := ⟨"elkins-torrence-brown-2026", "(65)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jni' hor kub' kjone' chib'j?"
    glossedTokens := [("jni'", "how.many"), ("hor", "hour"), ("∅-∅-kub'", "COMPL-B2/3S-DIR"), ("k-jon(*=a)=e'", "A2/3PL-cut-DS=MVMT=2PL"), ("chib'j", "meat")]
    glossedWords := [⟨[['j', 'n', 'i', '\'']], [['h', 'o', 'w', '.', 'm', 'a', 'n', 'y']]⟩, ⟨[['h', 'o', 'r']], [['h', 'o', 'u', 'r']]⟩, ⟨[['∅'], ['∅'], ['k', 'u', 'b', '\'']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', '/', '3', 'S'], ['D', 'I', 'R']]⟩, ⟨[['k'], ['j', 'o', 'n', '*'], ['a'], ['e', '\'']], [['A', '2', '/', '3', 'P', 'L'], ['c', 'u', 't'], ['D', 'S'], ['M', 'V', 'M', 'T'], ['2', 'P', 'L']]⟩, ⟨[['c', 'h', 'i', 'b', '\'', 'j']], [['m', 'e', 'a', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jni' hor kub' kjonae' chib'j?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.3"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_51 : Datum :=
  { id := "elkinstorrencebrown2026_51"
    source := ⟨"mendes-ranero-2021", "(2)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(51)"⟩
    language := "kich1262"
    primaryText := "Jawi xatb'ee wi iwiir?"
    glossedTokens := [("Jawi", "where"), ("x-at-b'ee", "COMPL-B2SG-go"), ("*(wi)", "FP"), ("iwiir", "yesterday")]
    glossedWords := [⟨[['J', 'a', 'w', 'i']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['x'], ['a', 't'], ['b', '\'', 'e', 'e']], [['C', 'O', 'M', 'P', 'L'], ['B', '2', 'S', 'G'], ['g', 'o']]⟩, ⟨[['*', 'w', 'i']], [['F', 'P']]⟩, ⟨[['i', 'w', 'i', 'i', 'r']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jawi xatb'ee iwiir?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "locative"), ("reflex", "licensed")] }

def ex_52 : Datum :=
  { id := "elkinstorrencebrown2026_52"
    source := ⟨"mendes-ranero-2021", "(17)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(52)"⟩
    language := "kich1262"
    primaryText := "Jawi xkib'iij wi chi ke'e wi?"
    glossedTokens := [("Jawi", "where"), ("x-∅-ki-b'iij", "COMPL-B3SG-A3SG-say"), ("*(wi)", "FP"), ("chi", "COMP"), ("k-e-'e", "INC-B3PL-go"), ("*(wi)", "FP")]
    glossedWords := [⟨[['J', 'a', 'w', 'i']], [['w', 'h', 'e', 'r', 'e']]⟩, ⟨[['x'], ['∅'], ['k', 'i'], ['b', '\'', 'i', 'i', 'j']], [['C', 'O', 'M', 'P', 'L'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['s', 'a', 'y']]⟩, ⟨[['*', 'w', 'i']], [['F', 'P']]⟩, ⟨[['c', 'h', 'i']], [['C', 'O', 'M', 'P']]⟩, ⟨[['k'], ['e'], ['\'', 'e']], [['I', 'N', 'C'], ['B', '3', 'P', 'L'], ['g', 'o']]⟩, ⟨[['*', 'w', 'i']], [['F', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "locative"), ("embeddedSize", "cP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_53 : Datum :=
  { id := "elkinstorrencebrown2026_53"
    source := ⟨"mendes-ranero-2021", "(19)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(53)"⟩
    language := "kich1262"
    primaryText := "Jas ruuk' karayiij katij wi le wa?"
    glossedTokens := [("Jas", "WH"), ("r-uuk'", "A3SG-RN"), ("k-∅-a-rayii-j", "INC-B3SG-A2SG-desire-ACT"), ("(*wi)", "FP"), ("k-∅-a-tij", "INC-B3SG-A2SG-eat"), ("*(wi)", "FP"), ("le", "DET"), ("wa", "food")]
    glossedWords := [⟨[['J', 'a', 's']], [['W', 'H']]⟩, ⟨[['r'], ['u', 'u', 'k', '\'']], [['A', '3', 'S', 'G'], ['R', 'N']]⟩, ⟨[['k'], ['∅'], ['a'], ['r', 'a', 'y', 'i', 'i'], ['j']], [['I', 'N', 'C'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['d', 'e', 's', 'i', 'r', 'e'], ['A', 'C', 'T']]⟩, ⟨[['*', 'w', 'i']], [['F', 'P']]⟩, ⟨[['k'], ['∅'], ['a'], ['t', 'i', 'j']], [['I', 'N', 'C'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['e', 'a', 't']]⟩, ⟨[['*', 'w', 'i']], [['F', 'P']]⟩, ⟨[['l', 'e']], [['D', 'E', 'T']]⟩, ⟨[['w', 'a']], [['f', 'o', 'o', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "instrument"), ("embeddedSize", "aspP"), ("landing", "matrix"), ("matrixReflex", "blocked"), ("embeddedReflex", "licensed")] }

def ex_64 : Datum :=
  { id := "elkinstorrencebrown2026_64"
    source := ⟨"mendes-ranero-2021", "(14a)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(64)"⟩
    language := "kaqc1270"
    primaryText := "Achike ruma xsamäj ri a Juan?"
    glossedTokens := [("Achike", "what"), ("ru-ma", "A3SG-RN"), ("x-∅-samäj", "COMPL-B3SG-work"), ("(*wi)", "FP"), ("ri", "DET"), ("a", "CLF"), ("Juan", "Juan")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'a', 't']]⟩, ⟨[['r', 'u'], ['m', 'a']], [['A', '3', 'S', 'G'], ['R', 'N']]⟩, ⟨[['x'], ['∅'], ['s', 'a', 'm', 'ä', 'j']], [['C', 'O', 'M', 'P', 'L'], ['B', '3', 'S', 'G'], ['w', 'o', 'r', 'k']]⟩, ⟨[['*', 'w', 'i']], [['F', 'P']]⟩, ⟨[['r', 'i']], [['D', 'E', 'T']]⟩, ⟨[['a']], [['C', 'L', 'F']]⟩, ⟨[['J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Achike ruma xsamäj wi ri a Juan?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.3"), ("mover", "reason"), ("reflex", "blocked")] }

def all : List Datum := [ex_10b, ex_11b, ex_12b, ex_13a, ex_13b, ex_14b, ex_15b, ex_16b, ex_17b, ex_18b, ex_19b, ex_20b, ex_21b, ex_22, ex_24, ex_26, ex_28, ex_29a, ex_31, ex_34, ex_35c, ex_37, ex_38, ex_63, ex_65, ex_51, ex_52, ex_53, ex_64]

end ElkinsTorrenceBrown2026.Examples
