module

public import Linglib.Data.Examples.Schema

/-!
# `Beslin2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Beslin2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Beslin2026.Examples`.
-/

@[expose] public section

namespace Beslin2026.Examples

def ex1 : Datum :=
  { id := "beslin2026_ex1"
    source := ⟨"beslin-2026", "(1)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ri ak'al na nojel ta q'ij k-ø-tz'ib'-an-ik, xaq xow we je'lik taq tzij <k-ø-u-tz'ib'-aj>."
    glossedTokens := [("Ri", "DET"), ("ak'al", "child"), ("na", "NEG"), ("nojel", "every"), ("ta", "IRR"), ("q'ij", "day"), ("k-ø-tz'ib'-an-ik,", "NPST-ABS3SG-write-AP-IV"), ("xaq", "PRT"), ("xow", "just"), ("we", "DET"), ("je'lik", "pretty"), ("taq", "PL"), ("tzij", "word"), ("k-ø-u-tz'ib'-aj", "NPST-ERG3SG-ABS3SG-write-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex1_ap : Datum :=
  { id := "beslin2026_ex1_ap"
    source := ⟨"beslin-2026", "(1)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ri ak'al na nojel ta q'ij k-ø-tz'ib'-an-ik, xaq xow we je'lik taq tzij <k-ø-tz'ib'-an-ik>."
    glossedTokens := [("Ri", "DET"), ("ak'al", "child"), ("na", "NEG"), ("nojel", "every"), ("ta", "IRR"), ("q'ij", "day"), ("k-ø-tz'ib'-an-ik,", "NPST-ABS3SG-write-AP-IV"), ("xaq", "PRT"), ("xow", "just"), ("we", "DET"), ("je'lik", "pretty"), ("taq", "PL"), ("tzij", "word"), ("k-ø-tz'ib'-an-ik", "NPST-ABS3SG-write-AP-IV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "antipassive"), ("remnant", "object")] }

def ex2 : Datum :=
  { id := "beslin2026_ex2"
    source := ⟨"beslin-2026", "(2)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ri ak'al k-ø-tz'ib'-an ronojel q'ij, are ri je'lik taq tzij no <k-ø-u-tz'ib'-aj>."
    glossedTokens := [("Ri", "DET"), ("ak'al", "child"), ("k-ø-tz'ib'-an", "NPST-ABS3SG-write-AP"), ("ronojel", "every"), ("q'ij,", "day"), ("are", "EMPH"), ("ri", "DET"), ("je'lik", "pretty"), ("taq", "PL"), ("tzij", "word"), ("no", "NO"), ("k-ø-u-tz'ib'-aj", "NPST-ERG3SG-ABS3SG-write-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex2_ap : Datum :=
  { id := "beslin2026_ex2_ap"
    source := ⟨"beslin-2026", "(2)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ri ak'al k-ø-tz'ib'-an ronojel q'ij, are ri je'lik taq tzij no <k-ø-tz'ib'-an-ik>."
    glossedTokens := [("Ri", "DET"), ("ak'al", "child"), ("k-ø-tz'ib'-an", "NPST-ABS3SG-write-AP"), ("ronojel", "every"), ("q'ij,", "day"), ("are", "EMPH"), ("ri", "DET"), ("je'lik", "pretty"), ("taq", "PL"), ("tzij", "word"), ("no", "NO"), ("k-ø-tz'ib'-an-ik", "NPST-ABS3SG-write-AP-IV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "antipassive"), ("remnant", "object")] }

def ex3 : Datum :=
  { id := "beslin2026_ex3"
    source := ⟨"beslin-2026", "(3)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ri ak'al k-ø-tz'ib'-an ronojel q'ij, pero na wetam ta jas uwach <k-ø-u-tz'ib'-aj>."
    glossedTokens := [("Ri", "DET"), ("ak'al", "child"), ("k-ø-tz'ib'-an", "NPST-ABS3SG-write-AP"), ("ronojel", "every"), ("q'ij,", "day"), ("pero", "but"), ("na", "NEG"), ("wetam", "know"), ("ta", "IRR"), ("jas", "what"), ("uwach", "kind"), ("k-ø-u-tz'ib'-aj", "NPST-ERG3SG-ABS3SG-write-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex3_ap : Datum :=
  { id := "beslin2026_ex3_ap"
    source := ⟨"beslin-2026", "(3)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ri ak'al k-ø-tz'ib'-an ronojel q'ij, pero na wetam ta jas uwach <k-ø-tz'ib'-an-ik>."
    glossedTokens := [("Ri", "DET"), ("ak'al", "child"), ("k-ø-tz'ib'-an", "NPST-ABS3SG-write-AP"), ("ronojel", "every"), ("q'ij,", "day"), ("pero", "but"), ("na", "NEG"), ("wetam", "know"), ("ta", "IRR"), ("jas", "what"), ("uwach", "kind"), ("k-ø-tz'ib'-an-ik", "NPST-ABS3SG-write-AP-IV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "antipassive"), ("remnant", "object")] }

def ex11 : Datum :=
  { id := "beslin2026_ex11"
    source := ⟨"beslin-2026", "(11)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ma-jun x-ø-u-b'aq ri ch'ajo'n, xaq xow Ixkeem <x-ø-b'aq-ow>."
    glossedTokens := [("Ma-jun", "no-one"), ("x-ø-u-b'aq", "PST-ABS3SG-ERG3SG-scrub"), ("ri", "DET"), ("ch'ajo'n,", "clothes"), ("xaq", "PRT"), ("xow", "just"), ("Ixkeem", "Ixkeem"), ("x-ø-b'aq-ow", "PST-ABS3SG-scrub-AF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "transitive"), ("target", "agentFocus"), ("remnant", "subject")] }

def ex35 : Datum :=
  { id := "beslin2026_ex35"
    source := ⟨"beslin-2026", "(35)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Na k-ø-kem-on taj, xow we pas <k-ø-u-kem-o>."
    glossedTokens := [("Na", "NEG"), ("k-ø-kem-on", "NPST-ABS3SG-weave-AP"), ("taj,", "IRR"), ("xow", "just"), ("we", "DET"), ("pas", "sash"), ("k-ø-u-kem-o", "NPST-ABS3SG-ERG3SG-weave-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex36 : Datum :=
  { id := "beslin2026_ex36"
    source := ⟨"beslin-2026", "(36)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Na x-ø-loq'om-an ta pa k'ayb'al, xow ri k'aj <x-ø-u-loq'-o>."
    glossedTokens := [("Na", "NEG"), ("x-ø-loq'om-an", "PST-ABS3SG-buy-AP"), ("ta", "IRR"), ("pa", "on"), ("k'ayb'al,", "market"), ("xow", "just"), ("ri", "DET"), ("k'aj", "flour"), ("x-ø-u-loq'-o", "PST-ABS3SG-ERG3SG-buy-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex37 : Datum :=
  { id := "beslin2026_ex37"
    source := ⟨"beslin-2026", "(37)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "K-ø-su'-un le ixoq pa ri ja, xow ri uchi' ja no."
    glossedTokens := [("K-ø-su'-un", "NPST-ABS3SG-clean-AP"), ("le", "DET"), ("ixoq", "woman"), ("pa", "on"), ("ri", "DET"), ("ja,", "house"), ("xow", "just"), ("ri", "DET"), ("uchi'", "door"), ("ja", "house"), ("no", "no")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex55 : Datum :=
  { id := "beslin2026_ex55"
    source := ⟨"beslin-2026", "(55)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Ri nan Juana k-ø-k'ay-in pa k'ayib'al. Ch-a-ch'ak-a' jas uwach ri jastaq <k-ø-u-k'ay-ij>!"
    glossedTokens := [("Ri", "DET"), ("nan", "CLF"), ("Juana", "Juana"), ("k-ø-k'ay-in", "NPST-ABS3SG-sell-AP"), ("pa", "on"), ("k'ayib'al.", "market"), ("Ch-a-ch'ak-a'", "IMP-ABS2SG-guess-IMP"), ("jas", "what"), ("uwach", "kind"), ("ri", "DET"), ("jastaq", "thing"), ("k-ø-u-k'ay-ij", "NPST-ABS3SG-ERG3SG-sell-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex51 : Datum :=
  { id := "beslin2026_ex51"
    source := ⟨"beslin-2026", "(51)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "Xa xe ri ma Juan x-ø-loq'-o kotz'i'j. Kan qitzij? Ta-b'ij pe chwe achike kotz'i'j <x-ø-u-löq'>!"
    glossedTokens := [("Xa", "EMPH"), ("xe", "only"), ("ri", "DET"), ("ma", "CLF"), ("Juan", "Juan"), ("x-ø-loq'-o", "PST-ABS3SG-buy-AF"), ("kotz'i'j.", "flower"), ("Kan", "PRT"), ("qitzij?", "truth"), ("Ta-b'ij", "IMP-say"), ("pe", "PRT"), ("chwe", "to.me"), ("achike", "what"), ("kotz'i'j", "flower"), ("x-ø-u-löq'", "PST-ABS3SG-ERG3SG-buy.ACT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "agentFocus"), ("target", "transitive"), ("remnant", "object")] }

def ex52 : Datum :=
  { id := "beslin2026_ex52"
    source := ⟨"beslin-2026", "(52)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "Ri aq x-ø-kam-is-äx ruma jun ixöq. Kan qitzij? Achike ixöq <x-ø-kam-sa-n ri aq>?"
    glossedTokens := [("Ri", "DET"), ("aq", "pig"), ("x-ø-kam-is-äx", "PST-ABS3SG-die-CAUS-PASS"), ("ruma", "RN"), ("jun", "a"), ("ixöq.", "woman"), ("Kan", "PRT"), ("qitzij?", "truth"), ("Achike", "which"), ("ixöq", "woman"), ("x-ø-kam-sa-n", "PST-ABS3SG-die-CAUS-AF"), ("ri", "DET"), ("aq", "pig")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "passive"), ("target", "agentFocus"), ("remnant", "subject")] }

def ex53 : Datum :=
  { id := "beslin2026_ex53"
    source := ⟨"beslin-2026", "(53)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "Xta Juana n-ø-k'ay-in pa k'ayib'äl wkami. Ta-wla achike <n-ø-ø-k'ay-ij>!"
    glossedTokens := [("Xta", "CLF"), ("Juana", "Juana"), ("n-ø-k'ay-in", "NPST-ABS3SG-sell-AP"), ("pa", "on"), ("k'ayib'äl", "market"), ("wkami.", "now"), ("Ta-wla", "IMP-guess"), ("achike", "what"), ("n-ø-ø-k'ay-ij", "NPST-ABS3SG-ERG3SG-buy-ACT.TV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "antipassive"), ("target", "transitive"), ("remnant", "object")] }

def ex46 : Datum :=
  { id := "beslin2026_ex46"
    source := ⟨"merchant-2001", "p. 19"⟩
    reportedIn := some ⟨"beslin-2026", "(46)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "Sally ate, but I don't know what <Sally ate what>."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "intransitive"), ("target", "transitive"), ("remnant", "object")] }

def ex47a : Datum :=
  { id := "beslin2026_ex47a"
    source := ⟨"beslin-2026", "(47a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "We're donating our car to some organization, but it's unclear to which organization <we're donating our car to which organization>."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "transitiveTo"), ("target", "transitiveTail"), ("remnant", "oblique")] }

def ex47b : Datum :=
  { id := "beslin2026_ex47b"
    source := ⟨"beslin-2026", "(47b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "We're donating our car to some organization, but it's unclear which organization <we're donating our car to which organization>."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "transitiveTo"), ("target", "transitiveTo"), ("remnant", "oblique")] }

def ex48a : Datum :=
  { id := "beslin2026_ex48a"
    source := ⟨"beslin-2026", "(48a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "We're donating our car, but it's unclear to which organization <we're donating our car to which organization>."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "transitive"), ("target", "transitiveTail"), ("remnant", "oblique")] }

def ex48b : Datum :=
  { id := "beslin2026_ex48b"
    source := ⟨"beslin-2026", "(48b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "We're donating our car, but it's unclear which organization <we're donating our car to which organization>."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "transitive"), ("target", "transitiveTo"), ("remnant", "oblique")] }

def ex69a : Datum :=
  { id := "beslin2026_ex69a"
    source := ⟨"merchant-2013", "(5a)"⟩
    reportedIn := some ⟨"beslin-2026", "(69a)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "Joe was murdered, but we don't know who."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "passive"), ("target", "active"), ("remnant", "subject")] }

def ex69b : Datum :=
  { id := "beslin2026_ex69b"
    source := ⟨"merchant-2013", "(5b)"⟩
    reportedIn := some ⟨"beslin-2026", "(69b)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "Someone murdered Joe, but we don't know who by."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "active"), ("target", "passive"), ("remnant", "oblique")] }

def ex70b : Datum :=
  { id := "beslin2026_ex70b"
    source := ⟨"johnson-2004", "p. 7"⟩
    reportedIn := some ⟨"beslin-2026", "(70b)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "This can freeze. Please do."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "vp"), ("antecedent", "inchoative"), ("target", "causative"), ("remnant", "none")] }

def ex71 : Datum :=
  { id := "beslin2026_ex71"
    source := ⟨"kehler-2002", "p. 53"⟩
    reportedIn := some ⟨"beslin-2026", "(71)"⟩
    method := some .elicitation
    language := "stan1293"
    primaryText := "This problem was to have been looked into, but obviously nobody did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "vp"), ("antecedent", "passive"), ("target", "active"), ("remnant", "none")] }

def ex75a : Datum :=
  { id := "beslin2026_ex75a"
    source := ⟨"beslin-2026", "(75a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "ital1282"
    primaryText := "Pettina sé stessa e non so chi altro <pettina>."
    glossedTokens := [("Pettina", "combs"), ("sé", "herself"), ("stessa", "herself"), ("e", "and"), ("non", "NEG"), ("so", "know"), ("chi", "who"), ("altro", "else"), ("pettina", "combs")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "active"), ("target", "active"), ("remnant", "object")] }

def ex75b : Datum :=
  { id := "beslin2026_ex75b"
    source := ⟨"beslin-2026", "(75b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "ital1282"
    primaryText := "Si pettina e non so chi altro <pettina>."
    glossedTokens := [("Si", "REFL.CL.3"), ("pettina", "combs"), ("e", "and"), ("non", "NEG"), ("so", "know"), ("chi", "who"), ("altro", "else"), ("pettina", "combs")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "reflexive"), ("target", "active"), ("remnant", "object")] }

def ex76a : Datum :=
  { id := "beslin2026_ex76a"
    source := ⟨"beslin-2026", "(76a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "sout1528"
    primaryText := "Marija češlja seb-e, ali ne znam koga još <Marija češlja>."
    glossedTokens := [("Marija", "Mary"), ("češlja", "combs"), ("seb-e,", "self.3-ACC"), ("ali", "but"), ("ne", "NEG"), ("znam", "know"), ("koga", "who"), ("još", "else"), ("Marija", "Mary"), ("češlja", "combs")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "active"), ("target", "active"), ("remnant", "object")] }

def ex76b : Datum :=
  { id := "beslin2026_ex76b"
    source := ⟨"beslin-2026", "(76b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "sout1528"
    primaryText := "Marija se češlja, ali ne znam koga još <Marija češlja>."
    glossedTokens := [("Marija", "Mary"), ("se", "REFL.CL.3"), ("češlja,", "combs"), ("ali", "but"), ("ne", "NEG"), ("znam", "know"), ("koga", "who"), ("još", "else"), ("Marija", "Mary"), ("češlja", "combs")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ellipsis"), ("ellipsis", "tp"), ("antecedent", "reflexive"), ("target", "active"), ("remnant", "object")] }

def ex58b : Datum :=
  { id := "beslin2026_ex58b"
    source := ⟨"beslin-2026", "(58b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "kam-sa-j"
    glossedTokens := [("kam-sa-j", "die-CAUS-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "intransitive"), ("order", "caus")] }

def ex59b : Datum :=
  { id := "beslin2026_ex59b"
    source := ⟨"beslin-2026", "(59b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "atin-isa-j"
    glossedTokens := [("atin-isa-j", "wash-CAUS-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "intransitive"), ("order", "caus")] }

def ex60b : Datum :=
  { id := "beslin2026_ex60b"
    source := ⟨"beslin-2026", "(60b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "b'in-isa-j"
    glossedTokens := [("b'in-isa-j", "walk-CAUS-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "intransitive"), ("order", "caus")] }

def ex61b : Datum :=
  { id := "beslin2026_ex61b"
    source := ⟨"beslin-2026", "(61b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "kix-sa-j"
    glossedTokens := [("kix-sa-j", "shame-CAUS-TV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "intransitive"), ("order", "caus")] }

def ex62a : Datum :=
  { id := "beslin2026_ex62a"
    source := ⟨"beslin-2026", "(62a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "loq'-sa-j"
    glossedTokens := [("loq'-sa-j", "buy-CAUS-TV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "transitive"), ("order", "caus")] }

def ex62b : Datum :=
  { id := "beslin2026_ex62b"
    source := ⟨"beslin-2026", "(62b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "tz'ib'-ax-sa-j"
    glossedTokens := [("tz'ib'-ax-sa-j", "write-PASS-CAUS-TV")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "passive"), ("order", "caus")] }

def ex63a : Datum :=
  { id := "beslin2026_ex63a"
    source := ⟨"beslin-2026", "(63a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "X-e-qa-k'ay-in-sa-j pa k'ayb'al ronojel q'ij."
    glossedTokens := [("X-e-qa-k'ay-in-sa-j", "PST-ABS3PL-ERG1PL-sell-AP-CAUS-TV"), ("pa", "in"), ("k'ayb'al", "market"), ("ronojel", "every"), ("q'ij", "day")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "antipassive"), ("order", "caus")] }

def ex63b : Datum :=
  { id := "beslin2026_ex63b"
    source := ⟨"beslin-2026", "(63b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "X-e-qa-tz'ib'-an-sa-j pa qa-tzij."
    glossedTokens := [("X-e-qa-tz'ib'-an-sa-j", "PST-ABS3PL-ERG1PL-write-AP-CAUS-TV"), ("pa", "in"), ("qa-tzij", "A1PL-language")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "antipassive"), ("order", "caus")] }

def ex64 : Datum :=
  { id := "beslin2026_ex64"
    source := ⟨"beslin-2026", "(64)"⟩
    reportedIn := none
    method := some .elicitation
    language := "kich1262"
    primaryText := "Le' nan k-e'-atin-is-an, le' ati't k-e-war-tis-an."
    glossedTokens := [("Le'", "DET"), ("nan", "mother"), ("k-e'-atin-is-an,", "NPST-ABS3PL-wash-CAUS-AP"), ("le'", "DET"), ("ati't", "grandma"), ("k-e-war-tis-an", "NPST-ABS3PL-sleep-CAUS-AP")]
    context := "Talking about duties of family members in child-rearing..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "antipassive"), ("order", "causThenBase")] }

def ex65 : Datum :=
  { id := "beslin2026_ex65"
    source := ⟨"burukina-polinsky-2025", "fn. 14"⟩
    reportedIn := some ⟨"beslin-2026", "(65)"⟩
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "La yawa' x-ø-u-chul-un-isa-j ri kik'."
    glossedTokens := [("La", "DET"), ("yawa'", "patient"), ("x-ø-u-chul-un-isa-j", "PST-ABS3SG-ERG3SG-urinate-AP-CAUS-TV"), ("ri", "DET"), ("kik'", "blood")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "antipassive"), ("order", "caus")] }

def ex66 : Datum :=
  { id := "beslin2026_ex66"
    source := ⟨"garcia-matzar-rodriguez-guajan-1997", "p. 437"⟩
    reportedIn := some ⟨"beslin-2026", "(66)"⟩
    method := some .elicitation
    language := "kaqc1270"
    primaryText := "X-e-saqar-isa-n chi Iximche' ri ajq'ij-a'."
    glossedTokens := [("X-e-saqar-isa-n", "PST-B3PL-white-CAUS-AP"), ("chi", "in"), ("Iximche'", "Iximche'"), ("ri", "DET"), ("ajq'ij-a'", "priest-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "causative"), ("base", "antipassive"), ("order", "causThenBase")] }

def all : List Datum := [ex1, ex1_ap, ex2, ex2_ap, ex3, ex3_ap, ex11, ex35, ex36, ex37, ex55, ex51, ex52, ex53, ex46, ex47a, ex47b, ex48a, ex48b, ex69a, ex69b, ex70b, ex71, ex75a, ex75b, ex76a, ex76b, ex58b, ex59b, ex60b, ex61b, ex62a, ex62b, ex63a, ex63b, ex64, ex65, ex66]

end Beslin2026.Examples
