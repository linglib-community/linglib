module

public import Linglib.Data.Examples.Schema

/-!
# `ClemDeal2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ClemDeal2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ClemDeal2026.Examples`.
-/

@[expose] public section

namespace ClemDeal2026.Examples

def ex_4a : Datum :=
  { id := "clemdeal2026_4a"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka yunka-w."
    glossedTokens := [("Ka", "1"), ("yunka-w", "swim-1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("objectSyntax", "absent")] }

def ex_4a_ri : Datum :=
  { id := "clemdeal2026_4a_ri"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka-ri yunka-w."
    glossedTokens := [("Ka-ri", "1-ERG"), ("yunka-w", "swim-1")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("objectSyntax", "absent"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_4b : Datum :=
  { id := "clemdeal2026_4b"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Wi'nawe chiwe-r-in tanan-ke."
    glossedTokens := [("Wi'nawe", "my.son"), ("chiwe-r-in", "get.lost-IND-3"), ("tanan-ke", "forest-LOC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("objectSyntax", "absent")] }

def ex_4b_ri : Datum :=
  { id := "clemdeal2026_4b_ri"
    source := ⟨"bourdeau-2015", "p. 19"⟩
    reportedIn := some ⟨"clem-deal-2026", "(4b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Wi'nawe-ri chiwe-r-in tanan-ke."
    glossedTokens := [("Wi'nawe-ri", "my.son-ERG"), ("chiwe-r-in", "get.lost-IND-3"), ("tanan-ke", "forest-LOC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("objectSyntax", "absent"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_6a : Datum :=
  { id := "clemdeal2026_6a"
    source := ⟨"bourdeau-2015", "p. 24"⟩
    reportedIn := some ⟨"clem-deal-2026", "(6a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "I'wara ka-ri-nke pera-ra-w-nke."
    glossedTokens := [("I'wara", "yesterday"), ("ka-ri-nke", "1-ERG-2.O"), ("pera-ra-w-nke", "call-IND-1-2.O")]
    context := ""
    judgment := .acceptable
    alternatives := [("I'wara ka-ri-nke pera-ra-nke.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("object", "2"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject"), ("oagrOnS", "yes")] }

def ex_6b : Datum :=
  { id := "clemdeal2026_6b"
    source := ⟨"bourdeau-2015", "p. 24"⟩
    reportedIn := some ⟨"clem-deal-2026", "(6b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya-ri-nkema au-ra-i-nkema kampita."
    glossedTokens := [("Kiya-ri-nkema", "1PL.EXCL-ERG-2PL.O"), ("au-ra-i-nkema", "hit-IND-1PL.EXCL-2PL.O"), ("kampita", "2PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "2"), ("objectNumber", "aug"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject"), ("oagrOnS", "yes")] }

def ex_6b_nke : Datum :=
  { id := "clemdeal2026_6b_nke"
    source := ⟨"bourdeau-2015", "p. 24"⟩
    reportedIn := some ⟨"clem-deal-2026", "(6b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya-ri-nke au-ra-i-nkema kampita."
    glossedTokens := [("Kiya-ri-nke", "1PL.EXCL-ERG-2PL.O"), ("au-ra-i-nkema", "hit-IND-1PL.EXCL-2PL.O"), ("kampita", "2PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "2"), ("objectNumber", "aug"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject"), ("oagrOnS", "yes")] }

def ex_7a : Datum :=
  { id := "clemdeal2026_7a"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "I'wara kema nu'wi-r-an-ku."
    glossedTokens := [("I'wara", "yesterday"), ("kema", "2"), ("nu'wi-r-an-ku", "tell.off-IND-2-1.O")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "1"), ("objectNumber", "min"), ("objectSyntax", "dropped")] }

def ex_7a_ri : Datum :=
  { id := "clemdeal2026_7a_ri"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "I'wara kema-ri nu'wi-r-an-ku."
    glossedTokens := [("I'wara", "yesterday"), ("kema-ri", "2-ERG"), ("nu'wi-r-an-ku", "tell.off-IND-2-1.O")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "1"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_7b : Datum :=
  { id := "clemdeal2026_7b"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ya'wan-rusa kete-r-in-kui."
    glossedTokens := [("Ya'wan-rusa", "snake-PL"), ("kete-r-in-kui", "bite-IND-3-1PL.EXCL.O")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ya'wan-usa kete-r-in-kui.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "aug"), ("object", "1excl"), ("objectNumber", "aug"), ("objectSyntax", "dropped")] }

def ex_7b_ri : Datum :=
  { id := "clemdeal2026_7b_ri"
    source := ⟨"bourdeau-2015", "p. 27"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ya'wan-rusa-ri kete-r-in-kui."
    glossedTokens := [("Ya'wan-rusa-ri", "snake-PL-ERG"), ("kete-r-in-kui", "bite-IND-3-1PL.EXCL.O")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "aug"), ("object", "1excl"), ("objectNumber", "aug"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_7c : Datum :=
  { id := "clemdeal2026_7c"
    source := ⟨"bourdeau-2015", "p. 28"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru nate-r-in-ke."
    glossedTokens := [("Pitru", "Peter"), ("nate-r-in-ke", "trust-IND-3-2.O")]
    context := ""
    judgment := .acceptable
    alternatives := [("Pitru nate-r-in-nke.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "2"), ("objectNumber", "min"), ("objectSyntax", "dropped")] }

def ex_7c_ri : Datum :=
  { id := "clemdeal2026_7c_ri"
    source := ⟨"bourdeau-2015", "p. 28"⟩
    reportedIn := some ⟨"clem-deal-2026", "(7c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru-ri nate-r-in-ke."
    glossedTokens := [("Pitru-ri", "Peter-ERG"), ("nate-r-in-ke", "trust-IND-3-2.O")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "2"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_8a : Datum :=
  { id := "clemdeal2026_8a"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya na'wan-ra-i Pitru."
    glossedTokens := [("Kiya", "1PL.EXCL"), ("na'wan-ra-i", "miss-IND-1PL.EXCL"), ("Pitru", "Peter")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kiya na'wan-a-i Pitru.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_8a_ri : Datum :=
  { id := "clemdeal2026_8a_ri"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kiya-ri na'wan-ra-i Pitru."
    glossedTokens := [("Kiya-ri", "1PL.EXCL-ERG"), ("na'wan-ra-i", "miss-IND-1PL.EXCL"), ("Pitru", "Peter")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kiya-ri na'wan-a-i Pitru.", .acceptable)]
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "aug"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_8b : Datum :=
  { id := "clemdeal2026_8b"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kema paki-r-an mi'ne."
    glossedTokens := [("Kema", "2"), ("paki-r-an", "break-IND-2"), ("mi'ne", "mocahua")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_8b_ri : Datum :=
  { id := "clemdeal2026_8b_ri"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kema-ri paki-r-an mi'ne."
    glossedTokens := [("Kema-ri", "2-ERG"), ("paki-r-an", "break-IND-2"), ("mi'ne", "mocahua")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_8c : Datum :=
  { id := "clemdeal2026_8c"
    source := ⟨"bourdeau-2015", "p. 33"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru iwa-r-in pepekunu."
    glossedTokens := [("Pitru", "Peter"), ("iwa-r-in", "steal-IND-3"), ("pepekunu", "necklace")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_8c_ri : Datum :=
  { id := "clemdeal2026_8c_ri"
    source := ⟨"bourdeau-2015", "p. 33"⟩
    reportedIn := some ⟨"clem-deal-2026", "(8c)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru-ri iwa-r-in pepekunu."
    glossedTokens := [("Pitru-ri", "Peter-ERG"), ("iwa-r-in", "steal-IND-3"), ("pepekunu", "necklace")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_9a : Datum :=
  { id := "clemdeal2026_9a"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pituru Kusi awe-r-in."
    glossedTokens := [("Pituru", "Pedro"), ("Kusi", "Jose"), ("awe-r-in", "hit-IND-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_9a_ri : Datum :=
  { id := "clemdeal2026_9a_ri"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pituru-ri Kusi awe-r-in."
    glossedTokens := [("Pituru-ri", "Pedro-ERG"), ("Kusi", "Jose"), ("awe-r-in", "hit-IND-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_9b : Datum :=
  { id := "clemdeal2026_9b"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kusi Pituru awe-r-in."
    glossedTokens := [("Kusi", "Jose"), ("Pituru", "Pedro"), ("awe-r-in", "hit-IND-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "fronted")] }

def ex_9b_ri : Datum :=
  { id := "clemdeal2026_9b_ri"
    source := ⟨"barraza-de-garcia-2005", "p. 159"⟩
    reportedIn := some ⟨"clem-deal-2026", "(9b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Kusi Pituru-ri awe-r-in."
    glossedTokens := [("Kusi", "Jose"), ("Pituru-ri", "Pedro-ERG"), ("awe-r-in", "hit-IND-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "fronted"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_11 : Datum :=
  { id := "clemdeal2026_11"
    source := ⟨"clem-deal-2026", "(11)"⟩
    reportedIn := none
    method := some .elicitation
    language := "chay1248"
    primaryText := "I'wara kema-ku nu'wi-r-an-ku."
    glossedTokens := [("I'wara", "yesterday"), ("kema-ku", "2-1.O"), ("nu'wi-r-an-ku", "tell.off-IND-2-1.O")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "min"), ("object", "1"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("oagrOnS", "yes")] }

def ex_21a : Datum :=
  { id := "clemdeal2026_21a"
    source := ⟨"barraza-de-garcia-2005", "p. 161"⟩
    reportedIn := some ⟨"clem-deal-2026", "(21a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Sanapi i-te-r-in."
    glossedTokens := [("Sanapi", "woman"), ("i-te-r-in", "say-VAL-IND-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "dropped")] }

def ex_21a_ri : Datum :=
  { id := "clemdeal2026_21a_ri"
    source := ⟨"barraza-de-garcia-2005", "p. 161"⟩
    reportedIn := some ⟨"clem-deal-2026", "(21a)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Sanapi-ri i-te-r-in."
    glossedTokens := [("Sanapi-ri", "woman-ERG"), ("i-te-r-in", "say-VAL-IND-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "dropped"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_21b : Datum :=
  { id := "clemdeal2026_21b"
    source := ⟨"barraza-de-garcia-2005", "p. 162"⟩
    reportedIn := some ⟨"clem-deal-2026", "(21b)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Sanapi i-te-r-in."
    glossedTokens := [("Sanapi", "woman"), ("i-te-r-in", "say-VAL-IND-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_27 : Datum :=
  { id := "clemdeal2026_27"
    source := ⟨"bourdeau-2015", "p. 32"⟩
    reportedIn := some ⟨"clem-deal-2026", "(27)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru na'wan-in sa'-in."
    glossedTokens := [("Pitru", "Peter"), ("na'wan-in", "miss-3"), ("sa'-in", "spouse-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu")] }

def ex_27_ri : Datum :=
  { id := "clemdeal2026_27_ri"
    source := ⟨"bourdeau-2015", "p. 32"⟩
    reportedIn := some ⟨"clem-deal-2026", "(27)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Pitru-ri na'wan-in sa'-in."
    glossedTokens := [("Pitru-ri", "Peter-ERG"), ("na'wan-in", "miss-3"), ("sa'-in", "spouse-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "min"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_28 : Datum :=
  { id := "clemdeal2026_28"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(28)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka mapa-te-ra-we kara kayu atari kayu."
    glossedTokens := [("Ka", "1"), ("mapa-te-ra-we", "receive-VAL-IND-1"), ("kara", "three"), ("kayu", "egg"), ("atari", "hen"), ("kayu", "egg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "aug"), ("objectSyntax", "inSitu")] }

def ex_28_ri : Datum :=
  { id := "clemdeal2026_28_ri"
    source := ⟨"bourdeau-2015", "p. 31"⟩
    reportedIn := some ⟨"clem-deal-2026", "(28)"⟩
    method := some .description
    language := "chay1248"
    primaryText := "Ka-ri mapa-te-ra-we kara kayu atari kayu."
    glossedTokens := [("Ka-ri", "1-ERG"), ("mapa-te-ra-we", "receive-VAL-IND-1"), ("kara", "three"), ("kayu", "egg"), ("atari", "hen"), ("kayu", "egg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "min"), ("object", "3"), ("objectNumber", "aug"), ("objectSyntax", "inSitu"), ("case", "-ri"), ("caseOn", "subject")] }

def ex_42a : Datum :=
  { id := "clemdeal2026_42a"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42a)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha salamat türgennik sie-te."
    glossedTokens := [("Masha", "Masha"), ("salamat", "porridge"), ("türgennik", "quickly"), ("sie-te", "eat-PST.3SG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "fronted")] }

def ex_42a_y : Datum :=
  { id := "clemdeal2026_42a_y"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42a)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha salamat-y türgennik sie-te."
    glossedTokens := [("Masha", "Masha"), ("salamat-y", "porridge-ACC"), ("türgennik", "quickly"), ("sie-te", "eat-PST.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "fronted"), ("case", "-y"), ("caseOn", "object")] }

def ex_42b : Datum :=
  { id := "clemdeal2026_42b"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42b)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha türgennik salamat sie-te."
    glossedTokens := [("Masha", "Masha"), ("türgennik", "quickly"), ("salamat", "porridge"), ("sie-te", "eat-PST.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "belowAdverb")] }

def ex_42b_y : Datum :=
  { id := "clemdeal2026_42b_y"
    source := ⟨"baker-vinokurova-2010", "p. 602"⟩
    reportedIn := some ⟨"clem-deal-2026", "(42b)"⟩
    method := some .description
    language := "yaku1245"
    primaryText := "Masha türgennik salamat-y sie-te."
    glossedTokens := [("Masha", "Masha"), ("türgennik", "quickly"), ("salamat-y", "porridge-ACC"), ("sie-te", "eat-PST.3SG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "belowAdverb"), ("case", "-y"), ("caseOn", "object")] }

def ex_45a : Datum :=
  { id := "clemdeal2026_45a"
    source := ⟨"valenzuela-2011", "p. 100"⟩
    reportedIn := some ⟨"clem-deal-2026", "(45a)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kwa tek-susu-llen."
    glossedTokens := [("Kwa", "1SG"), ("tek-susu-llen", "CAUS-grow.up-1SG>2SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "sg"), ("object", "2"), ("objectNumber", "sg"), ("objectSyntax", "dropped")] }

def ex_45b : Datum :=
  { id := "clemdeal2026_45b"
    source := ⟨"valenzuela-2011", "p. 100"⟩
    reportedIn := some ⟨"clem-deal-2026", "(45b)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Ma'ki'na kenmama' lumer-lama'u'ku?"
    glossedTokens := [("Ma'ki'na", "why"), ("kenmama'", "2PL"), ("lumer-lama'u'ku", "laugh.at-NFUT.2PL>1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2"), ("subjectNumber", "pl"), ("object", "1"), ("objectNumber", "sg"), ("objectSyntax", "dropped")] }

def ex_46a : Datum :=
  { id := "clemdeal2026_46a"
    source := ⟨"valenzuela-2011", "p. 100"⟩
    reportedIn := some ⟨"clem-deal-2026", "(46a)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kuda=ler aperku-tu-dek-llidek pu'yek."
    glossedTokens := [("Kuda=ler", "1PL.EXCL=ERG"), ("aperku-tu-dek-llidek", "not.share-VAL-3PL.O-1PL.EXCL>3PL"), ("pu'yek", "fishing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1excl"), ("subjectNumber", "pl"), ("object", "3"), ("objectNumber", "pl"), ("objectSyntax", "dropped"), ("case", "=ler"), ("caseOn", "subject")] }

def ex_46b : Datum :=
  { id := "clemdeal2026_46b"
    source := ⟨"valenzuela-2011", "p. 105"⟩
    reportedIn := some ⟨"clem-deal-2026", "(46b)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kishu ka'-lli nana isha."
    glossedTokens := [("Kishu", "Jesús"), ("ka'-lli", "eat-NFUT.3SG"), ("nana", "that"), ("isha", "paujil")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "inSitu")] }

def ex_46b_ler : Datum :=
  { id := "clemdeal2026_46b_ler"
    source := ⟨"valenzuela-2011", "p. 105"⟩
    reportedIn := some ⟨"clem-deal-2026", "(46b)"⟩
    method := some .description
    language := "jebe1250"
    primaryText := "Kishu=ler ka'-lli nana isha."
    glossedTokens := [("Kishu=ler", "Jesús=ERG"), ("ka'-lli", "eat-NFUT.3SG"), ("nana", "that"), ("isha", "paujil")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "inSitu"), ("case", "=ler"), ("caseOn", "subject")] }

def ex_49a : Datum :=
  { id := "clemdeal2026_49a"
    source := ⟨"maslova-2003", "p. 93"⟩
    reportedIn := some ⟨"clem-deal-2026", "(49a)"⟩
    method := some .description
    language := "sout2750"
    primaryText := "Tet kimnī met-kele kudede-m."
    glossedTokens := [("Tet", "your"), ("kimnī", "whip"), ("met-kele", "me-ACC"), ("kudede-m", "kill-TR.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3"), ("subjectNumber", "sg"), ("object", "1"), ("objectNumber", "sg"), ("objectSyntax", "inSitu"), ("case", "-gele"), ("caseOn", "object")] }

def ex_49b : Datum :=
  { id := "clemdeal2026_49b"
    source := ⟨"maslova-2003", "p. 95"⟩
    reportedIn := some ⟨"clem-deal-2026", "(49b)"⟩
    method := some .description
    language := "sout2750"
    primaryText := "Met tet-ul kudede-t."
    glossedTokens := [("Met", "I"), ("tet-ul", "you-ACC"), ("kudede-t", "kill-FUT(TR.1SG)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "sg"), ("object", "2"), ("objectNumber", "sg"), ("objectSyntax", "inSitu"), ("case", "-ul"), ("caseOn", "object")] }

def ex_49c : Datum :=
  { id := "clemdeal2026_49c"
    source := ⟨"maslova-2003", "p. 89"⟩
    reportedIn := some ⟨"clem-deal-2026", "(49c)"⟩
    method := some .description
    language := "sout2750"
    primaryText := "Met mēmē iŋī."
    glossedTokens := [("Met", "I"), ("mēmē", "bear"), ("iŋī", "be.afraid(TR.1SG)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1"), ("subjectNumber", "sg"), ("object", "3"), ("objectNumber", "sg"), ("objectSyntax", "inSitu")] }

def all : List Datum := [ex_4a, ex_4a_ri, ex_4b, ex_4b_ri, ex_6a, ex_6b, ex_6b_nke, ex_7a, ex_7a_ri, ex_7b, ex_7b_ri, ex_7c, ex_7c_ri, ex_8a, ex_8a_ri, ex_8b, ex_8b_ri, ex_8c, ex_8c_ri, ex_9a, ex_9a_ri, ex_9b, ex_9b_ri, ex_11, ex_21a, ex_21a_ri, ex_21b, ex_27, ex_27_ri, ex_28, ex_28_ri, ex_42a, ex_42a_y, ex_42b, ex_42b_y, ex_45a, ex_45b, ex_46a, ex_46b, ex_46b_ler, ex_49a, ex_49b, ex_49c]

end ClemDeal2026.Examples
