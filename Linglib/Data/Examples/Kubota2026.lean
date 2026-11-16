module

public import Linglib.Data.Examples.Schema

/-!
# `Kubota2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Kubota2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kubota2026.Examples`.
-/

@[expose] public section

namespace Kubota2026.Examples

def ex10_nanka_noncancelable : Datum :=
  { id := "kubota2026_ex10_nanka_noncancelable"
    source := ⟨"kubota-2026", "(10)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa jitsu-ni mooshi-bun-nai mono-da-ga, watashi-wa satō-iri-no ryokucha nanka kesshite nomanai."
    glossedTokens := [("Satō-iri-no", "sugar-put.in-GEN"), ("ryokucha-wa", "green.tea-TOP"), ("jitsu-ni", "real-ADV"), ("mooshi-bun-nai", "complaint-NEG"), ("mono-da-ga", "thing-COP-but"), ("watashi-wa", "I-TOP"), ("satō-iri-no", "sugar-put.in-GEN"), ("ryokucha", "green.tea"), ("nanka", "NANKA"), ("kesshite", "never"), ("nomanai", "drink-NEG")]
    glossedWords := [⟨['S', 'a', 't', 'ō', '-', 'i', 'r', 'i', '-', 'n', 'o'], ['s', 'u', 'g', 'a', 'r', '-', 'p', 'u', 't', '.', 'i', 'n', '-', 'G', 'E', 'N'], [⟨['S', 'a', 't', 'ō'], ['s', 'u', 'g', 'a', 'r'], none⟩, ⟨['i', 'r', 'i'], ['p', 'u', 't', '.', 'i', 'n'], some '-'⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['r', 'y', 'o', 'k', 'u', 'c', 'h', 'a', '-', 'w', 'a'], ['g', 'r', 'e', 'e', 'n', '.', 't', 'e', 'a', '-', 'T', 'O', 'P'], [⟨['r', 'y', 'o', 'k', 'u', 'c', 'h', 'a'], ['g', 'r', 'e', 'e', 'n', '.', 't', 'e', 'a'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['j', 'i', 't', 's', 'u', '-', 'n', 'i'], ['r', 'e', 'a', 'l', '-', 'A', 'D', 'V'], [⟨['j', 'i', 't', 's', 'u'], ['r', 'e', 'a', 'l'], none⟩, ⟨['n', 'i'], ['A', 'D', 'V'], some '-'⟩]⟩, ⟨['m', 'o', 'o', 's', 'h', 'i', '-', 'b', 'u', 'n', '-', 'n', 'a', 'i'], ['c', 'o', 'm', 'p', 'l', 'a', 'i', 'n', 't', '-', 'N', 'E', 'G'], []⟩, ⟨['m', 'o', 'n', 'o', '-', 'd', 'a', '-', 'g', 'a'], ['t', 'h', 'i', 'n', 'g', '-', 'C', 'O', 'P', '-', 'b', 'u', 't'], [⟨['m', 'o', 'n', 'o'], ['t', 'h', 'i', 'n', 'g'], none⟩, ⟨['d', 'a'], ['C', 'O', 'P'], some '-'⟩, ⟨['g', 'a'], ['b', 'u', 't'], some '-'⟩]⟩, ⟨['w', 'a', 't', 'a', 's', 'h', 'i', '-', 'w', 'a'], ['I', '-', 'T', 'O', 'P'], [⟨['w', 'a', 't', 'a', 's', 'h', 'i'], ['I'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['s', 'a', 't', 'ō', '-', 'i', 'r', 'i', '-', 'n', 'o'], ['s', 'u', 'g', 'a', 'r', '-', 'p', 'u', 't', '.', 'i', 'n', '-', 'G', 'E', 'N'], [⟨['s', 'a', 't', 'ō'], ['s', 'u', 'g', 'a', 'r'], none⟩, ⟨['i', 'r', 'i'], ['p', 'u', 't', '.', 'i', 'n'], some '-'⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['r', 'y', 'o', 'k', 'u', 'c', 'h', 'a'], ['g', 'r', 'e', 'e', 'n', '.', 't', 'e', 'a'], [⟨['r', 'y', 'o', 'k', 'u', 'c', 'h', 'a'], ['g', 'r', 'e', 'e', 'n', '.', 't', 'e', 'a'], none⟩]⟩, ⟨['n', 'a', 'n', 'k', 'a'], ['N', 'A', 'N', 'K', 'A'], [⟨['n', 'a', 'n', 'k', 'a'], ['N', 'A', 'N', 'K', 'A'], none⟩]⟩, ⟨['k', 'e', 's', 's', 'h', 'i', 't', 'e'], ['n', 'e', 'v', 'e', 'r'], [⟨['k', 'e', 's', 's', 'h', 'i', 't', 'e'], ['n', 'e', 'v', 'e', 'r'], none⟩]⟩, ⟨['n', 'o', 'm', 'a', 'n', 'a', 'i'], ['d', 'r', 'i', 'n', 'k', '-', 'N', 'E', 'G'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "noncancelability"), ("contextStance", "positive")] }

def ex11_mushiro_unexpected : Datum :=
  { id := "kubota2026_ex11_mushiro_unexpected"
    source := ⟨"kubota-2026", "(11)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru."
    glossedTokens := [("Igai-na", "unexpected-ADN"), ("koto-ni", "thing-DAT"), ("sunao-ni", "honest-ADV"), ("misu-o", "mistake-ACC"), ("mitome-ta", "admit-PAST"), ("hō-ga", "way-NOM"), ("mushiro", "rather"), ("yoi", "good"), ("kekka-ni", "result-DAT"), ("tsunagaru", "lead.to")]
    glossedWords := [⟨['I', 'g', 'a', 'i', '-', 'n', 'a'], ['u', 'n', 'e', 'x', 'p', 'e', 'c', 't', 'e', 'd', '-', 'A', 'D', 'N'], [⟨['I', 'g', 'a', 'i'], ['u', 'n', 'e', 'x', 'p', 'e', 'c', 't', 'e', 'd'], none⟩, ⟨['n', 'a'], ['A', 'D', 'N'], some '-'⟩]⟩, ⟨['k', 'o', 't', 'o', '-', 'n', 'i'], ['t', 'h', 'i', 'n', 'g', '-', 'D', 'A', 'T'], [⟨['k', 'o', 't', 'o'], ['t', 'h', 'i', 'n', 'g'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['s', 'u', 'n', 'a', 'o', '-', 'n', 'i'], ['h', 'o', 'n', 'e', 's', 't', '-', 'A', 'D', 'V'], [⟨['s', 'u', 'n', 'a', 'o'], ['h', 'o', 'n', 'e', 's', 't'], none⟩, ⟨['n', 'i'], ['A', 'D', 'V'], some '-'⟩]⟩, ⟨['m', 'i', 's', 'u', '-', 'o'], ['m', 'i', 's', 't', 'a', 'k', 'e', '-', 'A', 'C', 'C'], [⟨['m', 'i', 's', 'u'], ['m', 'i', 's', 't', 'a', 'k', 'e'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'i', 't', 'o', 'm', 'e', '-', 't', 'a'], ['a', 'd', 'm', 'i', 't', '-', 'P', 'A', 'S', 'T'], [⟨['m', 'i', 't', 'o', 'm', 'e'], ['a', 'd', 'm', 'i', 't'], none⟩, ⟨['t', 'a'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['h', 'ō', '-', 'g', 'a'], ['w', 'a', 'y', '-', 'N', 'O', 'M'], [⟨['h', 'ō'], ['w', 'a', 'y'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'u', 's', 'h', 'i', 'r', 'o'], ['r', 'a', 't', 'h', 'e', 'r'], [⟨['m', 'u', 's', 'h', 'i', 'r', 'o'], ['r', 'a', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['y', 'o', 'i'], ['g', 'o', 'o', 'd'], [⟨['y', 'o', 'i'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['k', 'e', 'k', 'k', 'a', '-', 'n', 'i'], ['r', 'e', 's', 'u', 'l', 't', '-', 'D', 'A', 'T'], [⟨['k', 'e', 'k', 'k', 'a'], ['r', 'e', 's', 'u', 'l', 't'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['t', 's', 'u', 'n', 'a', 'g', 'a', 'r', 'u'], ['l', 'e', 'a', 'd', '.', 't', 'o'], [⟨['t', 's', 'u', 'n', 'a', 'g', 'a', 'r', 'u'], ['l', 'e', 'a', 'd', '.', 't', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "mushiro"), ("phenomenon", "noncancelability"), ("contextExpectation", "unexpected")] }

def ex12_yahari_expected : Datum :=
  { id := "kubota2026_ex12_yahari_expected"
    source := ⟨"kubota-2026", "(12)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru."
    glossedTokens := [("Igai-na", "unexpected"), ("koto-wa", "thing-TOP"), ("nani-mo", "nothing"), ("na-ku", "exist-NEG"), ("sunao-ni", "honestly"), ("misu-o", "mistake-ACC"), ("mitome-ta", "admit-PAST"), ("hō-ga", "way-NOM"), ("yahari", "after.all"), ("yoi", "good"), ("kekka-ni", "result-DAT"), ("tsunagaru", "lead")]
    glossedWords := [⟨['I', 'g', 'a', 'i', '-', 'n', 'a'], ['u', 'n', 'e', 'x', 'p', 'e', 'c', 't', 'e', 'd'], []⟩, ⟨['k', 'o', 't', 'o', '-', 'w', 'a'], ['t', 'h', 'i', 'n', 'g', '-', 'T', 'O', 'P'], [⟨['k', 'o', 't', 'o'], ['t', 'h', 'i', 'n', 'g'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['n', 'a', 'n', 'i', '-', 'm', 'o'], ['n', 'o', 't', 'h', 'i', 'n', 'g'], []⟩, ⟨['n', 'a', '-', 'k', 'u'], ['e', 'x', 'i', 's', 't', '-', 'N', 'E', 'G'], [⟨['n', 'a'], ['e', 'x', 'i', 's', 't'], none⟩, ⟨['k', 'u'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['s', 'u', 'n', 'a', 'o', '-', 'n', 'i'], ['h', 'o', 'n', 'e', 's', 't', 'l', 'y'], []⟩, ⟨['m', 'i', 's', 'u', '-', 'o'], ['m', 'i', 's', 't', 'a', 'k', 'e', '-', 'A', 'C', 'C'], [⟨['m', 'i', 's', 'u'], ['m', 'i', 's', 't', 'a', 'k', 'e'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['m', 'i', 't', 'o', 'm', 'e', '-', 't', 'a'], ['a', 'd', 'm', 'i', 't', '-', 'P', 'A', 'S', 'T'], [⟨['m', 'i', 't', 'o', 'm', 'e'], ['a', 'd', 'm', 'i', 't'], none⟩, ⟨['t', 'a'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['h', 'ō', '-', 'g', 'a'], ['w', 'a', 'y', '-', 'N', 'O', 'M'], [⟨['h', 'ō'], ['w', 'a', 'y'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['y', 'a', 'h', 'a', 'r', 'i'], ['a', 'f', 't', 'e', 'r', '.', 'a', 'l', 'l'], [⟨['y', 'a', 'h', 'a', 'r', 'i'], ['a', 'f', 't', 'e', 'r', '.', 'a', 'l', 'l'], none⟩]⟩, ⟨['y', 'o', 'i'], ['g', 'o', 'o', 'd'], [⟨['y', 'o', 'i'], ['g', 'o', 'o', 'd'], none⟩]⟩, ⟨['k', 'e', 'k', 'k', 'a', '-', 'n', 'i'], ['r', 'e', 's', 'u', 'l', 't', '-', 'D', 'A', 'T'], [⟨['k', 'e', 'k', 'k', 'a'], ['r', 'e', 's', 'u', 'l', 't'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['t', 's', 'u', 'n', 'a', 'g', 'a', 'r', 'u'], ['l', 'e', 'a', 'd'], [⟨['t', 's', 'u', 'n', 'a', 'g', 'a', 'r', 'u'], ['l', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "yahari"), ("phenomenon", "noncancelability"), ("contextExpectation", "expected")] }

def ex37_nanka_counterstance : Datum :=
  { id := "kubota2026_ex37_nanka_counterstance"
    source := ⟨"kubota-2026", "(37)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Satō-iri-no ryokucha-tte, oishii yo ne. B: Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "evaluativeAssertion")] }

def ex38_nanka_no_counterstance : Datum :=
  { id := "kubota2026_ex38_nanka_no_counterstance"
    source := ⟨"kubota-2026", "(38)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? B: Satō-iri-no ryokucha-nanka oishiku-nai-yo."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := [("A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? B: Satō-iri-no ryokucha-wa oishiku-nai-yo.", .acceptable)]
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")] }

def ex39_dose_q1 : Datum :=
  { id := "kubota2026_ex39_dose_q1"
    source := ⟨"kubota-2026", "(39), response to Q1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Q1: Satō-iri-no ryokucha-wa oishii-ka-na? A: Satō-iri-no ryokucha-wa dōse mazui yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "polarQuestion")] }

def ex39_dose_q2 : Datum :=
  { id := "kubota2026_ex39_dose_q2"
    source := ⟨"kubota-2026", "(39), response to Q2"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Q2: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? A: Satō-iri-no ryokucha-wa dōse mazui yo."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")] }

def ex40_nanka_denial : Datum :=
  { id := "kubota2026_ex40_nanka_denial"
    source := ⟨"kubota-2026", "(40)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Satō-iri-no ryokucha nanka watashi-wa noma-nai. B: Iya, sonna hazu-wa nai yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "denial"), ("denialTarget", "prejacent")] }

def ex41_dose_denial : Datum :=
  { id := "kubota2026_ex41_dose_denial"
    source := ⟨"kubota-2026", "(41)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Watashi-ni-wa dōse kinmedaru-wa tor-e-nai. B: Iya, sonna hazu-wa nai yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "denial"), ("denialTarget", "prejacent")] }

def ex42_perspective_shift : Datum :=
  { id := "kubota2026_ex42_perspective_shift"
    source := ⟨"kubota-2026", "(42)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sensei-wa boku-ga (dōse) SALT-ni(-nanka) tōra-nai-to omot-te-ta rashii."
    glossedTokens := [("Sensei-wa", "advisor-TOP"), ("boku-ga", "I-NOM"), ("(dōse)", "DŌSE"), ("SALT-ni(-nanka)", "SALT-DAT-NANKA"), ("tōra-nai-to", "pass-NEG-C"), ("omot-te-ta", "think-PST"), ("rashii", "seem")]
    glossedWords := [⟨['S', 'e', 'n', 's', 'e', 'i', '-', 'w', 'a'], ['a', 'd', 'v', 'i', 's', 'o', 'r', '-', 'T', 'O', 'P'], [⟨['S', 'e', 'n', 's', 'e', 'i'], ['a', 'd', 'v', 'i', 's', 'o', 'r'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['b', 'o', 'k', 'u', '-', 'g', 'a'], ['I', '-', 'N', 'O', 'M'], [⟨['b', 'o', 'k', 'u'], ['I'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['(', 'd', 'ō', 's', 'e', ')'], ['D', 'Ō', 'S', 'E'], [⟨['d', 'ō', 's', 'e'], ['D', 'Ō', 'S', 'E'], none⟩]⟩, ⟨['S', 'A', 'L', 'T', '-', 'n', 'i', '(', '-', 'n', 'a', 'n', 'k', 'a', ')'], ['S', 'A', 'L', 'T', '-', 'D', 'A', 'T', '-', 'N', 'A', 'N', 'K', 'A'], [⟨['S', 'A', 'L', 'T'], ['S', 'A', 'L', 'T'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩, ⟨['n', 'a', 'n', 'k', 'a'], ['N', 'A', 'N', 'K', 'A'], some '-'⟩]⟩, ⟨['t', 'ō', 'r', 'a', '-', 'n', 'a', 'i', '-', 't', 'o'], ['p', 'a', 's', 's', '-', 'N', 'E', 'G', '-', 'C'], [⟨['t', 'ō', 'r', 'a'], ['p', 'a', 's', 's'], none⟩, ⟨['n', 'a', 'i'], ['N', 'E', 'G'], some '-'⟩, ⟨['t', 'o'], ['C'], some '-'⟩]⟩, ⟨['o', 'm', 'o', 't', '-', 't', 'e', '-', 't', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], []⟩, ⟨['r', 'a', 's', 'h', 'i', 'i'], ['s', 'e', 'e', 'm'], [⟨['r', 'a', 's', 'h', 'i', 'i'], ['s', 'e', 'e', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker was confident their paper would be accepted; the advisor held a pessimistic view."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse+nanka"), ("phenomenon", "perspectiveShift"), ("perspectiveHolder", "attitudeHolder")] }

def ex45a_nanka_epistemic : Datum :=
  { id := "kubota2026_ex45a_nanka_epistemic"
    source := ⟨"kubota-2026", "(45a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Konna tokoro ni nihonjin-nanka inai hazu da."
    glossedTokens := [("Konna", "such"), ("tokoro", "place"), ("ni", "LOC"), ("nihonjin-nanka", "Japanese-NANKA"), ("inai", "exist-NEG"), ("hazu", "supposed"), ("da", "COP")]
    glossedWords := [⟨['K', 'o', 'n', 'n', 'a'], ['s', 'u', 'c', 'h'], [⟨['K', 'o', 'n', 'n', 'a'], ['s', 'u', 'c', 'h'], none⟩]⟩, ⟨['t', 'o', 'k', 'o', 'r', 'o'], ['p', 'l', 'a', 'c', 'e'], [⟨['t', 'o', 'k', 'o', 'r', 'o'], ['p', 'l', 'a', 'c', 'e'], none⟩]⟩, ⟨['n', 'i'], ['L', 'O', 'C'], [⟨['n', 'i'], ['L', 'O', 'C'], none⟩]⟩, ⟨['n', 'i', 'h', 'o', 'n', 'j', 'i', 'n', '-', 'n', 'a', 'n', 'k', 'a'], ['J', 'a', 'p', 'a', 'n', 'e', 's', 'e', '-', 'N', 'A', 'N', 'K', 'A'], [⟨['n', 'i', 'h', 'o', 'n', 'j', 'i', 'n'], ['J', 'a', 'p', 'a', 'n', 'e', 's', 'e'], none⟩, ⟨['n', 'a', 'n', 'k', 'a'], ['N', 'A', 'N', 'K', 'A'], some '-'⟩]⟩, ⟨['i', 'n', 'a', 'i'], ['e', 'x', 'i', 's', 't', '-', 'N', 'E', 'G'], []⟩, ⟨['h', 'a', 'z', 'u'], ['s', 'u', 'p', 'p', 'o', 's', 'e', 'd'], [⟨['h', 'a', 'z', 'u'], ['s', 'u', 'p', 'p', 'o', 's', 'e', 'd'], none⟩]⟩, ⟨['d', 'a'], ['C', 'O', 'P'], [⟨['d', 'a'], ['C', 'O', 'P'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic"), ("evaluation", "neutral")] }

def ex45b_nanka_ability : Datum :=
  { id := "kubota2026_ex45b_nanka_ability"
    source := ⟨"kubota-2026", "(45b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi ni-wa kin medaru-nanka torenai."
    glossedTokens := [("Watashi", "I"), ("ni-wa", "DAT-TOP"), ("kin medaru-nanka", "gold.medal-NANKA"), ("torenai", "get-POT-NEG")]
    glossedWords := [⟨['W', 'a', 't', 'a', 's', 'h', 'i'], ['I'], [⟨['W', 'a', 't', 'a', 's', 'h', 'i'], ['I'], none⟩]⟩, ⟨['n', 'i', '-', 'w', 'a'], ['D', 'A', 'T', '-', 'T', 'O', 'P'], [⟨['n', 'i'], ['D', 'A', 'T'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['k', 'i', 'n', ' ', 'm', 'e', 'd', 'a', 'r', 'u', '-', 'n', 'a', 'n', 'k', 'a'], ['g', 'o', 'l', 'd', '.', 'm', 'e', 'd', 'a', 'l', '-', 'N', 'A', 'N', 'K', 'A'], [⟨['k', 'i', 'n', ' ', 'm', 'e', 'd', 'a', 'r', 'u'], ['g', 'o', 'l', 'd', '.', 'm', 'e', 'd', 'a', 'l'], none⟩, ⟨['n', 'a', 'n', 'k', 'a'], ['N', 'A', 'N', 'K', 'A'], some '-'⟩]⟩, ⟨['t', 'o', 'r', 'e', 'n', 'a', 'i'], ['g', 'e', 't', '-', 'P', 'O', 'T', '-', 'N', 'E', 'G'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial"), ("evaluation", "neutral")] }

def ex45c_nanka_deontic : Datum :=
  { id := "kubota2026_ex45c_nanka_deontic"
    source := ⟨"kubota-2026", "(45c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tookyoo-ni-nanka ika-nai hō-ga yokat-ta."
    glossedTokens := [("Tookyoo-ni-nanka", "Tokyo-DAT-NANKA"), ("ika-nai", "go-NEG"), ("hō-ga", "way-NOM"), ("yokat-ta", "good-PST")]
    glossedWords := [⟨['T', 'o', 'o', 'k', 'y', 'o', 'o', '-', 'n', 'i', '-', 'n', 'a', 'n', 'k', 'a'], ['T', 'o', 'k', 'y', 'o', '-', 'D', 'A', 'T', '-', 'N', 'A', 'N', 'K', 'A'], [⟨['T', 'o', 'o', 'k', 'y', 'o', 'o'], ['T', 'o', 'k', 'y', 'o'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩, ⟨['n', 'a', 'n', 'k', 'a'], ['N', 'A', 'N', 'K', 'A'], some '-'⟩]⟩, ⟨['i', 'k', 'a', '-', 'n', 'a', 'i'], ['g', 'o', '-', 'N', 'E', 'G'], [⟨['i', 'k', 'a'], ['g', 'o'], none⟩, ⟨['n', 'a', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['h', 'ō', '-', 'g', 'a'], ['w', 'a', 'y', '-', 'N', 'O', 'M'], [⟨['h', 'ō'], ['w', 'a', 'y'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['y', 'o', 'k', 'a', 't', '-', 't', 'a'], ['g', 'o', 'o', 'd', '-', 'P', 'S', 'T'], [⟨['y', 'o', 'k', 'a', 't'], ['g', 'o', 'o', 'd'], none⟩, ⟨['t', 'a'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hō-ga yokat-ta"), ("modalFlavor", "deontic"), ("evaluation", "pejorative")] }

def ex45d_nanka_bouletic : Datum :=
  { id := "kubota2026_ex45d_nanka_bouletic"
    source := ⟨"kubota-2026", "(45d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Aisu kuriimu-nanka iranai."
    glossedTokens := [("Aisu kuriimu-nanka", "Ice.cream-NANKA"), ("iranai", "need-NEG")]
    glossedWords := [⟨['A', 'i', 's', 'u', ' ', 'k', 'u', 'r', 'i', 'i', 'm', 'u', '-', 'n', 'a', 'n', 'k', 'a'], ['I', 'c', 'e', '.', 'c', 'r', 'e', 'a', 'm', '-', 'N', 'A', 'N', 'K', 'A'], [⟨['A', 'i', 's', 'u', ' ', 'k', 'u', 'r', 'i', 'i', 'm', 'u'], ['I', 'c', 'e', '.', 'c', 'r', 'e', 'a', 'm'], none⟩, ⟨['n', 'a', 'n', 'k', 'a'], ['N', 'A', 'N', 'K', 'A'], some '-'⟩]⟩, ⟨['i', 'r', 'a', 'n', 'a', 'i'], ['n', 'e', 'e', 'd', '-', 'N', 'E', 'G'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "iranai"), ("modalFlavor", "bouletic"), ("evaluation", "pejorative")] }

def ex46a_semete_epistemic : Datum :=
  { id := "kubota2026_ex46a_semete_epistemic"
    source := ⟨"kubota-2026", "(46a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono-yoona tokoro-ni-wa semete Nihonjin-wa iru hazu-da."
    glossedTokens := [("Kono-yoona", "this-like"), ("tokoro-ni-wa", "place-LOC-TOP"), ("semete", "at.least"), ("Nihonjin-wa", "Japanese.top"), ("iru", "exist"), ("hazu-da", "should-COP")]
    glossedWords := [⟨['K', 'o', 'n', 'o', '-', 'y', 'o', 'o', 'n', 'a'], ['t', 'h', 'i', 's', '-', 'l', 'i', 'k', 'e'], [⟨['K', 'o', 'n', 'o'], ['t', 'h', 'i', 's'], none⟩, ⟨['y', 'o', 'o', 'n', 'a'], ['l', 'i', 'k', 'e'], some '-'⟩]⟩, ⟨['t', 'o', 'k', 'o', 'r', 'o', '-', 'n', 'i', '-', 'w', 'a'], ['p', 'l', 'a', 'c', 'e', '-', 'L', 'O', 'C', '-', 'T', 'O', 'P'], [⟨['t', 'o', 'k', 'o', 'r', 'o'], ['p', 'l', 'a', 'c', 'e'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['s', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], [⟨['s', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], none⟩]⟩, ⟨['N', 'i', 'h', 'o', 'n', 'j', 'i', 'n', '-', 'w', 'a'], ['J', 'a', 'p', 'a', 'n', 'e', 's', 'e', '.', 't', 'o', 'p'], []⟩, ⟨['i', 'r', 'u'], ['e', 'x', 'i', 's', 't'], [⟨['i', 'r', 'u'], ['e', 'x', 'i', 's', 't'], none⟩]⟩, ⟨['h', 'a', 'z', 'u', '-', 'd', 'a'], ['s', 'h', 'o', 'u', 'l', 'd', '-', 'C', 'O', 'P'], [⟨['h', 'a', 'z', 'u'], ['s', 'h', 'o', 'u', 'l', 'd'], none⟩, ⟨['d', 'a'], ['C', 'O', 'P'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic")] }

def ex46b_semete_ability : Datum :=
  { id := "kubota2026_ex46b_semete_ability"
    source := ⟨"kubota-2026", "(46b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi-ni-wa semete dō-medaru-wa toreru."
    glossedTokens := [("Watashi-ni-wa", "I-DAT-TOP"), ("semete", "at.least"), ("dō-medaru-wa", "bronze-medal-TOP"), ("toreru", "obtain.can")]
    glossedWords := [⟨['W', 'a', 't', 'a', 's', 'h', 'i', '-', 'n', 'i', '-', 'w', 'a'], ['I', '-', 'D', 'A', 'T', '-', 'T', 'O', 'P'], [⟨['W', 'a', 't', 'a', 's', 'h', 'i'], ['I'], none⟩, ⟨['n', 'i'], ['D', 'A', 'T'], some '-'⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['s', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], [⟨['s', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], none⟩]⟩, ⟨['d', 'ō', '-', 'm', 'e', 'd', 'a', 'r', 'u', '-', 'w', 'a'], ['b', 'r', 'o', 'n', 'z', 'e', '-', 'm', 'e', 'd', 'a', 'l', '-', 'T', 'O', 'P'], [⟨['d', 'ō'], ['b', 'r', 'o', 'n', 'z', 'e'], none⟩, ⟨['m', 'e', 'd', 'a', 'r', 'u'], ['m', 'e', 'd', 'a', 'l'], some '-'⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['t', 'o', 'r', 'e', 'r', 'u'], ['o', 'b', 't', 'a', 'i', 'n', '.', 'c', 'a', 'n'], [⟨['t', 'o', 'r', 'e', 'r', 'u'], ['o', 'b', 't', 'a', 'i', 'n', '.', 'c', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial")] }

def ex46c_semete_desiderative : Datum :=
  { id := "kubota2026_ex46c_semete_desiderative"
    source := ⟨"kubota-2026", "(46c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete yobō-sesshu-wa uke-tai."
    glossedTokens := [("Semete", "at.least"), ("yobō-sesshu-wa", "vaccination-TOP"), ("uke-tai", "receive-want")]
    glossedWords := [⟨['S', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], [⟨['S', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], none⟩]⟩, ⟨['y', 'o', 'b', 'ō', '-', 's', 'e', 's', 's', 'h', 'u', '-', 'w', 'a'], ['v', 'a', 'c', 'c', 'i', 'n', 'a', 't', 'i', 'o', 'n', '-', 'T', 'O', 'P'], []⟩, ⟨['u', 'k', 'e', '-', 't', 'a', 'i'], ['r', 'e', 'c', 'e', 'i', 'v', 'e', '-', 'w', 'a', 'n', 't'], [⟨['u', 'k', 'e'], ['r', 'e', 'c', 'e', 'i', 'v', 'e'], none⟩, ⟨['t', 'a', 'i'], ['w', 'a', 'n', 't'], some '-'⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-tai"), ("modalFlavor", "bouletic")] }

def ex46d_semete_deontic : Datum :=
  { id := "kubota2026_ex46d_semete_deontic"
    source := ⟨"kubota-2026", "(46d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete ryohi-wa harau-beki-da."
    glossedTokens := [("Semete", "at.least"), ("ryohi-wa", "travel.expenses-top"), ("harau-beki-da", "pay-should-COP")]
    glossedWords := [⟨['S', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], [⟨['S', 'e', 'm', 'e', 't', 'e'], ['a', 't', '.', 'l', 'e', 'a', 's', 't'], none⟩]⟩, ⟨['r', 'y', 'o', 'h', 'i', '-', 'w', 'a'], ['t', 'r', 'a', 'v', 'e', 'l', '.', 'e', 'x', 'p', 'e', 'n', 's', 'e', 's', '-', 't', 'o', 'p'], [⟨['r', 'y', 'o', 'h', 'i'], ['t', 'r', 'a', 'v', 'e', 'l', '.', 'e', 'x', 'p', 'e', 'n', 's', 'e', 's'], none⟩, ⟨['w', 'a'], ['t', 'o', 'p'], some '-'⟩]⟩, ⟨['h', 'a', 'r', 'a', 'u', '-', 'b', 'e', 'k', 'i', '-', 'd', 'a'], ['p', 'a', 'y', '-', 's', 'h', 'o', 'u', 'l', 'd', '-', 'C', 'O', 'P'], [⟨['h', 'a', 'r', 'a', 'u'], ['p', 'a', 'y'], none⟩, ⟨['b', 'e', 'k', 'i'], ['s', 'h', 'o', 'u', 'l', 'd'], some '-'⟩, ⟨['d', 'a'], ['C', 'O', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-beki"), ("modalFlavor", "deontic")] }

def all : List Datum := [ex10_nanka_noncancelable, ex11_mushiro_unexpected, ex12_yahari_expected, ex37_nanka_counterstance, ex38_nanka_no_counterstance, ex39_dose_q1, ex39_dose_q2, ex40_nanka_denial, ex41_dose_denial, ex42_perspective_shift, ex45a_nanka_epistemic, ex45b_nanka_ability, ex45c_nanka_deontic, ex45d_nanka_bouletic, ex46a_semete_epistemic, ex46b_semete_ability, ex46c_semete_desiderative, ex46d_semete_deontic]

end Kubota2026.Examples
