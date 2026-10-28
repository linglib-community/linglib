module

public import Linglib.Data.Examples.Schema

/-!
# `Giannakidou2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Giannakidou2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Giannakidou2002.Examples`.
-/

@[expose] public section

namespace Giannakidou2002.Examples

def ex1 : Datum :=
  { id := "giannakidou2002_ex1"
    source := ⟨"giannakidou-2002", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess slept until midnight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "stative"), ("licenser", "none"), ("test", "plain")] }

def ex2 : Datum :=
  { id := "giannakidou2002_ex2"
    source := ⟨"giannakidou-2002", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess was writing a letter until midnight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "progressive"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex3 : Datum :=
  { id := "giannakidou2002_ex3"
    source := ⟨"giannakidou-2002", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess arrived until midnight."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex4 : Datum :=
  { id := "giannakidou2002_ex4"
    source := ⟨"giannakidou-2002", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess ate a sandwich until noon."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex8a : Datum :=
  { id := "giannakidou2002_ex8a"
    source := ⟨"giannakidou-2002", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't arrive until midnight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "plain")] }

def ex8b : Datum :=
  { id := "giannakidou2002_ex8b"
    source := ⟨"giannakidou-2002", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't sleep until midnight."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "plain")] }

def ex22 : Datum :=
  { id := "giannakidou2002_ex22"
    source := ⟨"giannakidou-2002", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nancy remained a spinster until she died."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "stative"), ("licenser", "none"), ("test", "plain")] }

def ex61a : Datum :=
  { id := "giannakidou2002_ex61a"
    source := ⟨"giannakidou-2002", "(61a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't sleep until midnight. At midnight she got up, got dressed and went out for a walk."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "noEventContinuation")] }

def ex61b : Datum :=
  { id := "giannakidou2002_ex61b"
    source := ⟨"giannakidou-2002", "(61b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Until midnight, the princess didn't sleep."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("connective", "until"), ("aspect", "simplePast"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "preposed")] }

def ex32 : Datum :=
  { id := "giannakidou2002_ex32"
    source := ⟨"giannakidou-2002", "(32)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa egrafe ena grama mexri ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("egrafe", "wrote.imperf.3sg"), ("ena", "a"), ("grama", "letter"), ("mexri", "until"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex33 : Datum :=
  { id := "giannakidou2002_ex33"
    source := ⟨"giannakidou-2002", "(33)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa kimotane mexri ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("kimotane", "slept.imperf.3sg"), ("mexri", "until"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "none"), ("test", "plain")] }

def ex34 : Datum :=
  { id := "giannakidou2002_ex34"
    source := ⟨"giannakidou-2002", "(34)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa eftase mexri ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("eftase", "arrived.perf.3sg"), ("mexri", "until"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex35 : Datum :=
  { id := "giannakidou2002_ex35"
    source := ⟨"giannakidou-2002", "(35)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen eftase mexri ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("eftase", "arrived.perf.3sg"), ("mexri", "until"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "plain")] }

def ex36 : Datum :=
  { id := "giannakidou2002_ex36"
    source := ⟨"giannakidou-2002", "(36)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen eftase para monon ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("eftase", "arrived.perf.3sg"), ("para", "but"), ("monon", "only"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "plain")] }

def ex36pos : Datum :=
  { id := "giannakidou2002_ex36pos"
    source := ⟨"giannakidou-2002", "(36)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa eftase para monon ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("eftase", "arrived.perf.3sg"), ("para", "but"), ("monon", "only"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex37 : Datum :=
  { id := "giannakidou2002_ex37"
    source := ⟨"giannakidou-2002", "(37)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen (apo)kimithike para monon ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("(apo)kimithike", "fell.asleep.perf.3sg"), ("para", "but"), ("monon", "only"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "plain")] }

def ex38 : Datum :=
  { id := "giannakidou2002_ex38"
    source := ⟨"giannakidou-2002", "(38)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen eftase para monon ta mesanixta. Dhen eftase kan ekino to vradi."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("eftase", "arrived.perf.3sg"), ("para", "but"), ("monon", "only"), ("ta", "the"), ("mesanixta", "midnight"), ("Dhen", "not"), ("eftase", "arrived"), ("kan", "even"), ("ekino", "that"), ("to vradi", "night")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "noEventContinuation")] }

def ex40 : Datum :=
  { id := "giannakidou2002_ex40"
    source := ⟨"giannakidou-2002", "(40)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Kitouse to tavani xoris na milisi para monon otan efije o jatros."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "paraMonon"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "without"), ("test", "plain")] }

def ex41pm : Datum :=
  { id := "giannakidou2002_ex41pm"
    source := ⟨"giannakidou-2002", "(41)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Amfivalo an ixe erthi para monon ta mesanixta."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("connective", "paraMonon"), ("aspect", "perfect"), ("eventuality", "eventive"), ("licenser", "doubt"), ("test", "plain")] }

def ex41mx : Datum :=
  { id := "giannakidou2002_ex41mx"
    source := ⟨"giannakidou-2002", "(41)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Amfivalo an ixe erthi mexri ta mesanixta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "mexri"), ("aspect", "perfect"), ("eventuality", "eventive"), ("licenser", "doubt"), ("test", "plain")] }

def ex42pm : Datum :=
  { id := "giannakidou2002_ex42pm"
    source := ⟨"giannakidou-2002", "(42)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Jati na pantreftis para monon otan prepi anagastika na to kanis?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("connective", "paraMonon"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "question"), ("test", "plain")] }

def ex42mx : Datum :=
  { id := "giannakidou2002_ex42mx"
    source := ⟨"giannakidou-2002", "(42)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Jati na pantreftis mexri otan prepi anagastika na to kanis?"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("connective", "mexri"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "question"), ("test", "plain")] }

def ex48 : Datum :=
  { id := "giannakidou2002_ex48"
    source := ⟨"giannakidou-2002", "(48)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen kimotane mexri ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("kimotane", "slept.imperf.3sg"), ("mexri", "until"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The princess was in a state of not-sleeping until midnight.", .acceptable), ("It is not true that the princess slept until midnight. (She woke up earlier than that.)", .acceptable)]
    paperFeatures := [("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "plain")] }

def ex49 : Datum :=
  { id := "giannakidou2002_ex49"
    source := ⟨"giannakidou-2002", "(49)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen kimithike mexri ta mesanixta."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("kimithike", "slept.perf.3sg"), ("mexri", "until"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "plain")] }

def ex51 : Datum :=
  { id := "giannakidou2002_ex51"
    source := ⟨"giannakidou-2002", "(51)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen kimotane mexri ta mesanixta. Ke tote, apofasise na sikothi, na ndithi ke na vgi ekso."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("kimotane", "slept.imperf.3sg"), ("mexri", "until"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "noEventContinuation")] }

def ex53 : Datum :=
  { id := "giannakidou2002_ex53"
    source := ⟨"giannakidou-2002", "(53)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Mexri ta mesanixta i prigipisa dhen kimotane."
    glossedTokens := [("Mexri", "Until"), ("ta", "the"), ("mesanixta", "midnight"), ("i", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("kimotane", "slept.imperf.3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "preposed")] }

def ex57 : Datum :=
  { id := "giannakidou2002_ex57"
    source := ⟨"giannakidou-2002", "(57)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen kimithike para monon ta mesanixta. Ke tote, apofasise na sikothi, na ndithi ke na vgi ekso."
    glossedTokens := [("I", "the"), ("prigipisa", "princess"), ("dhen", "not"), ("kimithike", "slept.perf.3sg"), ("para", "but"), ("monon", "only"), ("ta", "the"), ("mesanixta", "midnight")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("eventuality", "stative"), ("licenser", "negation"), ("test", "noEventContinuation")] }

def ex72 : Datum :=
  { id := "giannakidou2002_ex72"
    source := ⟨"giannakidou-2002", "(72)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen eftase prin apo ta mesanixta. Eftase argotera i den eftase kan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "prin"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "noEventContinuation")] }

def ex77 : Datum :=
  { id := "giannakidou2002_ex77"
    source := ⟨"giannakidou-2002", "(77a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen pandreftike prin pethani."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "prin"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "plain")] }

def ex43 : Datum :=
  { id := "giannakidou2002_ex43"
    source := ⟨"giannakidou-2002", "(43)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Prinsessan svaf (þangað) til klukkan fimm"
    glossedTokens := [("Prinsessan", "princess-the"), ("svaf", "slept"), ("(þangað) til", "mexri"), ("klukkan fimm", "five o'clock")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "simplePast"), ("eventuality", "stative"), ("licenser", "none"), ("test", "plain")] }

def ex44 : Datum :=
  { id := "giannakidou2002_ex44"
    source := ⟨"giannakidou-2002", "(44)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Prinsessan var að skrifa bréf (þangað) til klukkan fimm."
    glossedTokens := [("Prinsessan", "princess-the"), ("var", "was"), ("að", "to"), ("skrifa", "write"), ("bréf", "letters"), ("(þangað) til", "mexri"), ("klukkan fimm", "five o'clock")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "progressive"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex45 : Datum :=
  { id := "giannakidou2002_ex45"
    source := ⟨"giannakidou-2002", "(45)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Prinsessan kom (þangað) til klukkan fimm"
    glossedTokens := [("Prinsessan", "princess-the"), ("kom", "arrived"), ("(þangað) til", "until"), ("klukkan fimm", "five o'clock")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex46 : Datum :=
  { id := "giannakidou2002_ex46"
    source := ⟨"giannakidou-2002", "(46)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Prinsessan kom ekki fyrr en klukkan fimm."
    glossedTokens := [("Prinsessan", "princess-the"), ("kom", "arrived"), ("ekki", "not"), ("fyrr en", "para monon"), ("klukkan fimm", "five o'clock")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "plain")] }

def ex46pos : Datum :=
  { id := "giannakidou2002_ex46pos"
    source := ⟨"giannakidou-2002", "(46)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Prinsessan kom fyrr en klukkan fimm."
    glossedTokens := [("Prinsessan", "princess-the"), ("kom", "arrived"), ("fyrr en", "para monon"), ("klukkan fimm", "five o'clock")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex47a : Datum :=
  { id := "giannakidou2002_ex47a"
    source := ⟨"giannakidou-2002", "(47a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Marie kwam tot 9 uur niet aan."
    glossedTokens := [("Marie", "Marie"), ("kwam", "came"), ("tot", "until"), ("9", "9"), ("uur", "hour"), ("niet", "not"), ("aan", "on")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "negation"), ("test", "plain")] }

def ex47a2 : Datum :=
  { id := "giannakidou2002_ex47a2"
    source := ⟨"giannakidou-2002", "(47a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Marie kwam tot 9 uur aan."
    glossedTokens := [("Marie", "Marie"), ("kwam", "came"), ("tot", "until"), ("9", "9"), ("uur", "hour"), ("aan", "on")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex47b : Datum :=
  { id := "giannakidou2002_ex47b"
    source := ⟨"giannakidou-2002", "(47b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Marie kwam pas om 9 uur aan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "pas"), ("aspect", "simplePast"), ("eventuality", "eventive"), ("licenser", "none"), ("test", "plain")] }

def ex67a : Datum :=
  { id := "giannakidou2002_ex67a"
    source := ⟨"giannakidou-2002", "(67a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "(Ja) Posi ora kimotane i Ariadne?"
    glossedTokens := [("Ja", "For"), ("Posi", "how"), ("ora", "time"), ("kimotane", "slept.imperf.3sg"), ("i", "the"), ("Ariadne", "Ariadne")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "howLong"), ("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "none")] }

def ex67b : Datum :=
  { id := "giannakidou2002_ex67b"
    source := ⟨"giannakidou-2002", "(67b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "(Ja) Posi ora dhen petakse ti bala i Ariadne?"
    glossedTokens := [("Ja", "For"), ("Posi", "how"), ("ora", "time"), ("dhen", "not"), ("petakse", "threw.perf.3sg"), ("ti", "the"), ("bala", "ball"), ("i Ariadne", "Ariadne")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "howLong"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation")] }

def ex67c : Datum :=
  { id := "giannakidou2002_ex67c"
    source := ⟨"giannakidou-2002", "(67c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "(Ja) Posi ora dhen petuse ti bala i Ariadne?"
    glossedTokens := [("Ja", "For"), ("Posi", "how"), ("ora", "time"), ("dhen", "not"), ("petuse", "threw.imperf.3sg"), ("ti", "the"), ("bala", "ball"), ("i Ariadne", "Ariadne")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "howLong"), ("aspect", "imperfective"), ("eventuality", "eventive"), ("licenser", "negation")] }

def ex68a : Datum :=
  { id := "giannakidou2002_ex68a"
    source := ⟨"giannakidou-2002", "(68a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Eplina ta pjata oso kimotane i Ariadne."
    glossedTokens := [("Eplina", "washed.perf.1sg"), ("ta", "the"), ("pjata", "dishes"), ("oso", "while"), ("kimotane", "slept.imperf.3sg"), ("i", "the"), ("Ariadne", "A.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "while"), ("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "none")] }

def ex68b : Datum :=
  { id := "giannakidou2002_ex68b"
    source := ⟨"giannakidou-2002", "(68b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Eplina ta pjata oso dhen petakse ti bala i Ariadne."
    glossedTokens := [("Eplina", "Washed"), ("ta", "the"), ("pjata", "dishes"), ("oso", "while"), ("dhen", "not"), ("petakse", "threw.perf.3sg"), ("ti", "the"), ("bala", "ball"), ("i Ariadne", "A.")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "while"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation")] }

def ex68c : Datum :=
  { id := "giannakidou2002_ex68c"
    source := ⟨"giannakidou-2002", "(68c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Eplina ta pjata oso dhen petuse ti bala i Ariadne."
    glossedTokens := [("Eplina", "Washed"), ("ta", "the"), ("pjata", "dishes"), ("oso", "while"), ("dhen", "not"), ("petuse", "threw.imperf.3sg"), ("ti", "the"), ("bala", "ball"), ("i Ariadne", "A.")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "while"), ("aspect", "imperfective"), ("eventuality", "eventive"), ("licenser", "negation")] }

def ex69 : Datum :=
  { id := "giannakidou2002_ex69"
    source := ⟨"giannakidou-2002", "(69)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Ariadni itan distixismeni ja pola xronia."
    glossedTokens := [("I", "the"), ("Ariadni", "A."), ("itan", "was"), ("distixismeni", "unhappy"), ("ja", "for"), ("pola", "many"), ("xronia", "years")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "forAdverbial"), ("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "none")] }

def ex70b : Datum :=
  { id := "giannakidou2002_ex70b"
    source := ⟨"giannakidou-2002", "(70b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Ariadni dhen ksipnise ja 10 lepta."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "forAdverbial"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation")] }

def ex70c : Datum :=
  { id := "giannakidou2002_ex70c"
    source := ⟨"giannakidou-2002", "(70c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Ariadni dhen ksipnuse ja 10 lepta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "forAdverbial"), ("aspect", "imperfective"), ("eventuality", "eventive"), ("licenser", "negation")] }

def ex71a : Datum :=
  { id := "giannakidou2002_ex71a"
    source := ⟨"giannakidou-2002", "(71a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Gnorize tin apandisi!"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "imperative"), ("aspect", "imperfective"), ("eventuality", "stative"), ("licenser", "none")] }

def ex71b : Datum :=
  { id := "giannakidou2002_ex71b"
    source := ⟨"giannakidou-2002", "(71b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Diavase to grama!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "imperative"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "none")] }

def ex71c : Datum :=
  { id := "giannakidou2002_ex71c"
    source := ⟨"giannakidou-2002", "(71c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Mi diavasis to grama!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "imperative"), ("aspect", "perfective"), ("eventuality", "eventive"), ("licenser", "negation")] }

def all : List Datum := [ex1, ex2, ex3, ex4, ex8a, ex8b, ex22, ex61a, ex61b, ex32, ex33, ex34, ex35, ex36, ex36pos, ex37, ex38, ex40, ex41pm, ex41mx, ex42pm, ex42mx, ex48, ex49, ex51, ex53, ex57, ex72, ex77, ex43, ex44, ex45, ex46, ex46pos, ex47a, ex47a2, ex47b, ex67a, ex67b, ex67c, ex68a, ex68b, ex68c, ex69, ex70b, ex70c, ex71a, ex71b, ex71c]

end Giannakidou2002.Examples
