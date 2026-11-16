module

public import Linglib.Data.Examples.Schema

/-!
# `BeaversUdayana2022` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaversUdayana2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaversUdayana2022.Examples`.
-/

@[expose] public section

namespace BeaversUdayana2022.Examples

def bu2022_2a : Datum :=
  { id := "bu2022_2a"
    source := ⟨"beavers-udayana-2022", "(2a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali ber-dandan."
    glossedTokens := [("Ali", "Ali"), ("ber-dandan", "MV-dress")]
    glossedWords := [⟨[['A', 'l', 'i']], [['A', 'l', 'i']]⟩, ⟨[['b', 'e', 'r'], ['d', 'a', 'n', 'd', 'a', 'n']], [['M', 'V'], ['d', 'r', 'e', 's', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "inherent reflexive"), ("root class", "naturally reflexive")] }

def bu2022_2b : Datum :=
  { id := "bu2022_2b"
    source := ⟨"beavers-udayana-2022", "(2b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual dengan mudah."
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("dengan", "with"), ("mudah", "easy")]
    glossedWords := [⟨[['M', 'o', 'b', 'i', 'l']], [['c', 'a', 'r']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l']], [['M', 'V'], ['s', 'e', 'l', 'l']]⟩, ⟨[['d', 'e', 'n', 'g', 'a', 'n']], [['w', 'i', 't', 'h']]⟩, ⟨[['m', 'u', 'd', 'a', 'h']], [['e', 'a', 's', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("reading", "generic")] }

def bu2022_7 : Datum :=
  { id := "bu2022_7"
    source := ⟨"beavers-udayana-2022", "(7)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual kemarin."
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("kemarin", "yesterday")]
    glossedWords := [⟨[['M', 'o', 'b', 'i', 'l']], [['c', 'a', 'r']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l']], [['M', 'V'], ['s', 'e', 'l', 'l']]⟩, ⟨[['k', 'e', 'm', 'a', 'r', 'i', 'n']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "passive middle"), ("reading", "episodic")] }

def bu2022_9a : Datum :=
  { id := "bu2022_9a"
    source := ⟨"beavers-udayana-2022", "(9a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual tapi tidak ada orang yang men-jual=nya."
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("orang", "man"), ("yang", "REL"), ("men-jual=nya", "AV-sell=3SG")]
    glossedWords := [⟨[['M', 'o', 'b', 'i', 'l']], [['c', 'a', 'r']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l']], [['M', 'V'], ['s', 'e', 'l', 'l']]⟩, ⟨[['t', 'a', 'p', 'i']], [['b', 'u', 't']]⟩, ⟨[['t', 'i', 'd', 'a', 'k']], [['N', 'E', 'G']]⟩, ⟨[['a', 'd', 'a']], [['e', 'x', 'i', 's', 't']]⟩, ⟨[['o', 'r', 'a', 'n', 'g']], [['m', 'a', 'n']]⟩, ⟨[['y', 'a', 'n', 'g']], [['R', 'E', 'L']]⟩, ⟨[['m', 'e', 'n'], ['j', 'u', 'a', 'l'], ['n', 'y', 'a']], [['A', 'V'], ['s', 'e', 'l', 'l'], ['3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "agent denial")] }

def bu2022_10c : Datum :=
  { id := "bu2022_10c"
    source := ⟨"beavers-udayana-2022", "(10c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual dengan sendiri=nya."
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("dengan", "with"), ("sendiri=nya", "alone=DEF")]
    glossedWords := [⟨[['M', 'o', 'b', 'i', 'l']], [['c', 'a', 'r']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l']], [['M', 'V'], ['s', 'e', 'l', 'l']]⟩, ⟨[['d', 'e', 'n', 'g', 'a', 'n']], [['w', 'i', 't', 'h']]⟩, ⟨[['s', 'e', 'n', 'd', 'i', 'r', 'i'], ['n', 'y', 'a']], [['a', 'l', 'o', 'n', 'e'], ['D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "dengan sendiri=nya")] }

def bu2022_11 : Datum :=
  { id := "bu2022_11"
    source := ⟨"beavers-udayana-2022", "(11)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu di-jual oleh Tono."
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("di-jual", "PASS-sell"), ("oleh", "by"), ("Tono", "Tono")]
    glossedWords := [⟨[['M', 'o', 'b', 'i', 'l']], [['c', 'a', 'r']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['d', 'i'], ['j', 'u', 'a', 'l']], [['P', 'A', 'S', 'S'], ['s', 'e', 'l', 'l']]⟩, ⟨[['o', 'l', 'e', 'h']], [['b', 'y']]⟩, ⟨[['T', 'o', 'n', 'o']], [['T', 'o', 'n', 'o']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "di- passive"), ("diagnostic", "oleh phrase")] }

def bu2022_13 : Datum :=
  { id := "bu2022_13"
    source := ⟨"beavers-udayana-2022", "(13)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-jual untuk meng-(k)umpul-kan dana."
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-jual", "MV-sell"), ("untuk", "for"), ("meng-(k)umpul-kan", "AV-collect-CAUS"), ("dana", "fund")]
    glossedWords := [⟨[['O', 'r', 'a', 'n', 'g']], [['m', 'a', 'n']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l']], [['M', 'V'], ['s', 'e', 'l', 'l']]⟩, ⟨[['u', 'n', 't', 'u', 'k']], [['f', 'o', 'r']]⟩, ⟨[['m', 'e', 'n', 'g'], ['k', 'u', 'm', 'p', 'u', 'l'], ['k', 'a', 'n']], [['A', 'V'], ['c', 'o', 'l', 'l', 'e', 'c', 't'], ['C', 'A', 'U', 'S']]⟩, ⟨[['d', 'a', 'n', 'a']], [['f', 'u', 'n', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A charity bachelor auction."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "rationale clause")] }

def bu2022_17b : Datum :=
  { id := "bu2022_17b"
    source := ⟨"beavers-udayana-2022", "(17b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-dandan dengan sendiri=nya."
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-dandan", "MV-dress"), ("dengan", "with"), ("sendiri=nya", "alone=DEF")]
    glossedWords := [⟨[['O', 'r', 'a', 'n', 'g']], [['m', 'a', 'n']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['d', 'a', 'n', 'd', 'a', 'n']], [['M', 'V'], ['d', 'r', 'e', 's', 's']]⟩, ⟨[['d', 'e', 'n', 'g', 'a', 'n']], [['w', 'i', 't', 'h']]⟩, ⟨[['s', 'e', 'n', 'd', 'i', 'r', 'i'], ['n', 'y', 'a']], [['a', 'l', 'o', 'n', 'e'], ['D', 'E', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "inherent reflexive"), ("diagnostic", "dengan sendiri=nya")] }

def bu2022_18a : Datum :=
  { id := "bu2022_18a"
    source := ⟨"beavers-udayana-2022", "(24b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-cuci=mata."
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-cuci=mata", "MV-wash=eye")]
    glossedWords := [⟨[['O', 'r', 'a', 'n', 'g']], [['m', 'a', 'n']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['c', 'u', 'c', 'i'], ['m', 'a', 't', 'a']], [['M', 'V'], ['w', 'a', 's', 'h'], ['e', 'y', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("compositional: washed his eyes", .acceptable), ("idiomatic: watched the girls go by (24b)", .acceptable)]
    paperFeatures := [("middle type", "incorporation"), ("object", "incorporated NP")] }

def bu2022_19b : Datum :=
  { id := "bu2022_19b"
    source := ⟨"beavers-udayana-2022", "(19b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Gadis itu ber-cuci dengan cepat kaki."
    glossedTokens := [("Gadis", "girl"), ("itu", "that"), ("ber-cuci", "MV-wash"), ("dengan", "with"), ("cepat", "quick"), ("kaki", "leg")]
    glossedWords := [⟨[['G', 'a', 'd', 'i', 's']], [['g', 'i', 'r', 'l']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['c', 'u', 'c', 'i']], [['M', 'V'], ['w', 'a', 's', 'h']]⟩, ⟨[['d', 'e', 'n', 'g', 'a', 'n']], [['w', 'i', 't', 'h']]⟩, ⟨[['c', 'e', 'p', 'a', 't']], [['q', 'u', 'i', 'c', 'k']]⟩, ⟨[['k', 'a', 'k', 'i']], [['l', 'e', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporation"), ("diagnostic", "non-separability")] }

def bu2022_22 : Datum :=
  { id := "bu2022_22"
    source := ⟨"beavers-udayana-2022", "(22)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia ber-jual=mobil. Mobil itu mahal."
    glossedTokens := [("Dia", "3SG"), ("ber-jual=mobil", "MV-sell=car"), ("Mobil", "car"), ("itu", "that"), ("mahal", "expensive")]
    glossedWords := [⟨[['D', 'i', 'a']], [['3', 'S', 'G']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l'], ['m', 'o', 'b', 'i', 'l']], [['M', 'V'], ['s', 'e', 'l', 'l'], ['c', 'a', 'r']]⟩, ⟨[['M', 'o', 'b', 'i', 'l']], [['c', 'a', 'r']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['m', 'a', 'h', 'a', 'l']], [['e', 'x', 'p', 'e', 'n', 's', 'i', 'v', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporation"), ("diagnostic", "discourse opacity")] }

def bu2022_26b : Datum :=
  { id := "bu2022_26b"
    source := ⟨"beavers-udayana-2022", "(26b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-jual=diri."
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-jual=diri", "MV-sell=REFL")]
    glossedWords := [⟨[['O', 'r', 'a', 'n', 'g']], [['m', 'a', 'n']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l'], ['d', 'i', 'r', 'i']], [['M', 'V'], ['s', 'e', 'l', 'l'], ['R', 'E', 'F', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "E.g. sold into servitude."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporated reflexive"), ("object", "diri")] }

def bu2022_28 : Datum :=
  { id := "bu2022_28"
    source := ⟨"beavers-udayana-2022", "(28)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-jual=baju=diri."
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-jual=baju=diri", "MV-sell=dress=REFL")]
    glossedWords := [⟨[['O', 'r', 'a', 'n', 'g']], [['m', 'a', 'n']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['j', 'u', 'a', 'l'], ['b', 'a', 'j', 'u'], ['d', 'i', 'r', 'i']], [['M', 'V'], ['s', 'e', 'l', 'l'], ['d', 'r', 'e', 's', 's'], ['R', 'E', 'F', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporation"), ("diagnostic", "complementary distribution")] }

def bu2022_44a : Datum :=
  { id := "bu2022_44a"
    source := ⟨"beavers-udayana-2022", "(44a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Tono dan Ali ber-dandan."
    glossedTokens := [("Tono", "Tono"), ("dan", "and"), ("Ali", "Ali"), ("ber-dandan", "MV-dress")]
    glossedWords := [⟨[['T', 'o', 'n', 'o']], [['T', 'o', 'n', 'o']]⟩, ⟨[['d', 'a', 'n']], [['a', 'n', 'd']]⟩, ⟨[['A', 'l', 'i']], [['A', 'l', 'i']]⟩, ⟨[['b', 'e', 'r'], ['d', 'a', 'n', 'd', 'a', 'n']], [['M', 'V'], ['d', 'r', 'e', 's', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Tono dressed himself and Ali was dressed by his mother."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "mixed readings"), ("analysis", "open variable vs existential")] }

def bu2022_59 : Datum :=
  { id := "bu2022_59"
    source := ⟨"beavers-udayana-2022", "(59)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Tono ber-topi."
    glossedTokens := [("Tono", "Tono"), ("ber-topi", "MV-hat")]
    glossedWords := [⟨[['T', 'o', 'n', 'o']], [['T', 'o', 'n', 'o']]⟩, ⟨[['b', 'e', 'r'], ['t', 'o', 'p', 'i']], [['M', 'V'], ['h', 'a', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "conflation"), ("root class", "relational noun")] }

def bu2022_62 : Datum :=
  { id := "bu2022_62"
    source := ⟨"beavers-udayana-2022", "(62)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia ber-tangan tapi tidak ada yang men-(t)angan-kan=nya."
    glossedTokens := [("Dia", "3SG"), ("ber-tangan", "MV-hand"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("yang", "REL"), ("men-(t)angan-kan=nya", "AV-hand-CAUS=3SG")]
    glossedWords := [⟨[['D', 'i', 'a']], [['3', 'S', 'G']]⟩, ⟨[['b', 'e', 'r'], ['t', 'a', 'n', 'g', 'a', 'n']], [['M', 'V'], ['h', 'a', 'n', 'd']]⟩, ⟨[['t', 'a', 'p', 'i']], [['b', 'u', 't']]⟩, ⟨[['t', 'i', 'd', 'a', 'k']], [['N', 'E', 'G']]⟩, ⟨[['a', 'd', 'a']], [['e', 'x', 'i', 's', 't']]⟩, ⟨[['y', 'a', 'n', 'g']], [['R', 'E', 'L']]⟩, ⟨[['m', 'e', 'n'], ['t', 'a', 'n', 'g', 'a', 'n'], ['k', 'a', 'n'], ['n', 'y', 'a']], [['A', 'V'], ['h', 'a', 'n', 'd'], ['C', 'A', 'U', 'S'], ['3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "conflation"), ("diagnostic", "change denial")] }

def bu2022_67a : Datum :=
  { id := "bu2022_67a"
    source := ⟨"beavers-udayana-2022", "(67a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Pasukan itu ter-pecah dua tapi tidak ada yang mem-(p)ecah=nya."
    glossedTokens := [("Pasukan", "troop"), ("itu", "that"), ("ter-pecah", "MV-break"), ("dua", "two"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("yang", "REL"), ("mem-(p)ecah=nya", "AV-break=3SG")]
    glossedWords := [⟨[['P', 'a', 's', 'u', 'k', 'a', 'n']], [['t', 'r', 'o', 'o', 'p']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['t', 'e', 'r'], ['p', 'e', 'c', 'a', 'h']], [['M', 'V'], ['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['d', 'u', 'a']], [['t', 'w', 'o']]⟩, ⟨[['t', 'a', 'p', 'i']], [['b', 'u', 't']]⟩, ⟨[['t', 'i', 'd', 'a', 'k']], [['N', 'E', 'G']]⟩, ⟨[['a', 'd', 'a']], [['e', 'x', 'i', 's', 't']]⟩, ⟨[['y', 'a', 'n', 'g']], [['R', 'E', 'L']]⟩, ⟨[['m', 'e', 'm'], ['p', 'e', 'c', 'a', 'h'], ['n', 'y', 'a']], [['A', 'V'], ['b', 'r', 'e', 'a', 'k'], ['3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "anticausative"), ("diagnostic", "causer denial")] }

def bu2022_74 : Datum :=
  { id := "bu2022_74"
    source := ⟨"beavers-udayana-2022", "(74)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Pasukan itu ber-pecah dua tapi tidak ada yang mem-(p)ecah=nya."
    glossedTokens := [("Pasukan", "troop"), ("itu", "that"), ("ber-pecah", "MV-break"), ("dua", "two"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("yang", "REL"), ("mem-(p)ecah=nya", "AV-break=3SG")]
    glossedWords := [⟨[['P', 'a', 's', 'u', 'k', 'a', 'n']], [['t', 'r', 'o', 'o', 'p']]⟩, ⟨[['i', 't', 'u']], [['t', 'h', 'a', 't']]⟩, ⟨[['b', 'e', 'r'], ['p', 'e', 'c', 'a', 'h']], [['M', 'V'], ['b', 'r', 'e', 'a', 'k']]⟩, ⟨[['d', 'u', 'a']], [['t', 'w', 'o']]⟩, ⟨[['t', 'a', 'p', 'i']], [['b', 'u', 't']]⟩, ⟨[['t', 'i', 'd', 'a', 'k']], [['N', 'E', 'G']]⟩, ⟨[['a', 'd', 'a']], [['e', 'x', 'i', 's', 't']]⟩, ⟨[['y', 'a', 'n', 'g']], [['R', 'E', 'L']]⟩, ⟨[['m', 'e', 'm'], ['p', 'e', 'c', 'a', 'h'], ['n', 'y', 'a']], [['A', 'V'], ['b', 'r', 'e', 'a', 'k'], ['3', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "causer denial")] }

def all : List Datum := [bu2022_2a, bu2022_2b, bu2022_7, bu2022_9a, bu2022_10c, bu2022_11, bu2022_13, bu2022_17b, bu2022_18a, bu2022_19b, bu2022_22, bu2022_26b, bu2022_28, bu2022_44a, bu2022_59, bu2022_62, bu2022_67a, bu2022_74]

end BeaversUdayana2022.Examples
