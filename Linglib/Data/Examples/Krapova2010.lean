module

public import Linglib.Data.Examples.Schema

/-!
# `Krapova2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Krapova2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krapova2010.Examples`.
-/

@[expose] public section

namespace Krapova2010.Examples

def ex_56a : Datum :=
  { id := "krapova2010_56a"
    source := ⟨"krapova-2010", "(56a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Naistina săžaljavam, deto ne otdelix poveče vnimanie na postrojkata."
    glossedTokens := [("Naistina", "really"), ("săžaljavam,", "regret-1sg"), ("deto", "that"), ("ne", "not"), ("otdelix", "devoted-1sg"), ("poveče", "more"), ("vnimanie", "attention"), ("na", "to"), ("postrojkata", "construction-the")]
    glossedWords := [⟨['N', 'a', 'i', 's', 't', 'i', 'n', 'a'], ['r', 'e', 'a', 'l', 'l', 'y'], [⟨['N', 'a', 'i', 's', 't', 'i', 'n', 'a'], ['r', 'e', 'a', 'l', 'l', 'y'], none⟩]⟩, ⟨['s', 'ă', 'ž', 'a', 'l', 'j', 'a', 'v', 'a', 'm', ','], ['r', 'e', 'g', 'r', 'e', 't', '-', '1', 's', 'g'], []⟩, ⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['n', 'e'], ['n', 'o', 't'], [⟨['n', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['o', 't', 'd', 'e', 'l', 'i', 'x'], ['d', 'e', 'v', 'o', 't', 'e', 'd', '-', '1', 's', 'g'], []⟩, ⟨['p', 'o', 'v', 'e', 'č', 'e'], ['m', 'o', 'r', 'e'], [⟨['p', 'o', 'v', 'e', 'č', 'e'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['v', 'n', 'i', 'm', 'a', 'n', 'i', 'e'], ['a', 't', 't', 'e', 'n', 't', 'i', 'o', 'n'], [⟨['v', 'n', 'i', 'm', 'a', 'n', 'i', 'e'], ['a', 't', 't', 'e', 'n', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['n', 'a'], ['t', 'o'], [⟨['n', 'a'], ['t', 'o'], none⟩]⟩, ⟨['p', 'o', 's', 't', 'r', 'o', 'j', 'k', 'a', 't', 'a'], ['c', 'o', 'n', 's', 't', 'r', 'u', 'c', 't', 'i', 'o', 'n', '-', 't', 'h', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Naistina săžaljavam, če ne otdelix poveče vnimanie na postrojkata.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_56b : Datum :=
  { id := "krapova2010_56b"
    source := ⟨"krapova-2010", "(56b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Samo me e jad, deto grivnata izčezna sled zatămnenieto."
    glossedTokens := [("Samo", "only"), ("me", "me-ClAcc"), ("e", "is"), ("jad,", "anger"), ("deto", "that"), ("grivnata", "bracelet-the"), ("izčezna", "disappeared-3sg"), ("sled", "after"), ("zatămnenieto", "eclipse-the")]
    glossedWords := [⟨['S', 'a', 'm', 'o'], ['o', 'n', 'l', 'y'], [⟨['S', 'a', 'm', 'o'], ['o', 'n', 'l', 'y'], none⟩]⟩, ⟨['m', 'e'], ['m', 'e', '-', 'C', 'l', 'A', 'c', 'c'], []⟩, ⟨['e'], ['i', 's'], [⟨['e'], ['i', 's'], none⟩]⟩, ⟨['j', 'a', 'd', ','], ['a', 'n', 'g', 'e', 'r'], [⟨['j', 'a', 'd'], ['a', 'n', 'g', 'e', 'r'], none⟩]⟩, ⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'r', 'i', 'v', 'n', 'a', 't', 'a'], ['b', 'r', 'a', 'c', 'e', 'l', 'e', 't', '-', 't', 'h', 'e'], []⟩, ⟨['i', 'z', 'č', 'e', 'z', 'n', 'a'], ['d', 'i', 's', 'a', 'p', 'p', 'e', 'a', 'r', 'e', 'd', '-', '3', 's', 'g'], []⟩, ⟨['s', 'l', 'e', 'd'], ['a', 'f', 't', 'e', 'r'], [⟨['s', 'l', 'e', 'd'], ['a', 'f', 't', 'e', 'r'], none⟩]⟩, ⟨['z', 'a', 't', 'ă', 'm', 'n', 'e', 'n', 'i', 'e', 't', 'o'], ['e', 'c', 'l', 'i', 'p', 's', 'e', '-', 't', 'h', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Samo me e jad, če grivnata izčezna sled zatămnenieto.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "jad me e"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_57a : Datum :=
  { id := "krapova2010_57a"
    source := ⟨"krapova-2010", "(57a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Nikak ne săžaljavam, deto sreštata im se e provalila."
    glossedTokens := [("Nikak", "not-at-all"), ("ne", "not"), ("săžaljavam,", "regret-1sg"), ("deto", "that"), ("sreštata", "meeting-the"), ("im", "their"), ("se", "refl"), ("e", "is"), ("provalila", "failed-prt")]
    glossedWords := [⟨['N', 'i', 'k', 'a', 'k'], ['n', 'o', 't', '-', 'a', 't', '-', 'a', 'l', 'l'], []⟩, ⟨['n', 'e'], ['n', 'o', 't'], [⟨['n', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['s', 'ă', 'ž', 'a', 'l', 'j', 'a', 'v', 'a', 'm', ','], ['r', 'e', 'g', 'r', 'e', 't', '-', '1', 's', 'g'], []⟩, ⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'r', 'e', 'š', 't', 'a', 't', 'a'], ['m', 'e', 'e', 't', 'i', 'n', 'g', '-', 't', 'h', 'e'], []⟩, ⟨['i', 'm'], ['t', 'h', 'e', 'i', 'r'], [⟨['i', 'm'], ['t', 'h', 'e', 'i', 'r'], none⟩]⟩, ⟨['s', 'e'], ['r', 'e', 'f', 'l'], [⟨['s', 'e'], ['r', 'e', 'f', 'l'], none⟩]⟩, ⟨['e'], ['i', 's'], [⟨['e'], ['i', 's'], none⟩]⟩, ⟨['p', 'r', 'o', 'v', 'a', 'l', 'i', 'l', 'a'], ['f', 'a', 'i', 'l', 'e', 'd', '-', 'p', 'r', 't'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Nikak ne săžaljavam, če sreštata im se e provalila.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "1")] }

def ex_57b : Datum :=
  { id := "krapova2010_57b"
    source := ⟨"krapova-2010", "(57b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Vinoven li săm deto gostite pristignaxa kăsno?"
    glossedTokens := [("Vinoven", "guilty"), ("li", "Q"), ("săm", "am"), ("deto", "that"), ("gostite", "the guests"), ("pristignaxa", "arrived-3pl"), ("kăsno", "late")]
    glossedWords := [⟨['V', 'i', 'n', 'o', 'v', 'e', 'n'], ['g', 'u', 'i', 'l', 't', 'y'], [⟨['V', 'i', 'n', 'o', 'v', 'e', 'n'], ['g', 'u', 'i', 'l', 't', 'y'], none⟩]⟩, ⟨['l', 'i'], ['Q'], [⟨['l', 'i'], ['Q'], none⟩]⟩, ⟨['s', 'ă', 'm'], ['a', 'm'], [⟨['s', 'ă', 'm'], ['a', 'm'], none⟩]⟩, ⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['g', 'o', 's', 't', 'i', 't', 'e'], ['t', 'h', 'e', ' ', 'g', 'u', 'e', 's', 't', 's'], [⟨['g', 'o', 's', 't', 'i', 't', 'e'], ['t', 'h', 'e', ' ', 'g', 'u', 'e', 's', 't', 's'], none⟩]⟩, ⟨['p', 'r', 'i', 's', 't', 'i', 'g', 'n', 'a', 'x', 'a'], ['a', 'r', 'r', 'i', 'v', 'e', 'd', '-', '3', 'p', 'l'], []⟩, ⟨['k', 'ă', 's', 'n', 'o'], ['l', 'a', 't', 'e'], [⟨['k', 'ă', 's', 'n', 'o'], ['l', 'a', 't', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Vinoven li săm če gostite pristignaxa kăsno?", .acceptable)]
    readings := []
    paperFeatures := [("verb", "vinoven săm"), ("complementizer", "deto"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "yes"), ("person", "1")] }

def ex_57c : Datum :=
  { id := "krapova2010_57c"
    source := ⟨"krapova-2010", "(57c)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Săžaljavam, deto ne moža da ostaneš poveče."
    glossedTokens := [("Săžaljavam,", "regret-1sg"), ("deto", "that"), ("ne", "not"), ("moža", "could-2sg"), ("da", "Mod"), ("ostaneš", "stay-2sg"), ("poveče", "more")]
    glossedWords := [⟨['S', 'ă', 'ž', 'a', 'l', 'j', 'a', 'v', 'a', 'm', ','], ['r', 'e', 'g', 'r', 'e', 't', '-', '1', 's', 'g'], []⟩, ⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['n', 'e'], ['n', 'o', 't'], [⟨['n', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['m', 'o', 'ž', 'a'], ['c', 'o', 'u', 'l', 'd', '-', '2', 's', 'g'], []⟩, ⟨['d', 'a'], ['M', 'o', 'd'], [⟨['d', 'a'], ['M', 'o', 'd'], none⟩]⟩, ⟨['o', 's', 't', 'a', 'n', 'e', 'š'], ['s', 't', 'a', 'y', '-', '2', 's', 'g'], []⟩, ⟨['p', 'o', 'v', 'e', 'č', 'e'], ['m', 'o', 'r', 'e'], [⟨['p', 'o', 'v', 'e', 'č', 'e'], ['m', 'o', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Săžaljavam, če ne moža da ostaneš poveče.", .acceptable), ("Săžaljavam, deto ne moža da ostaneš poveče, no vsăšnost ti ostana poveče.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "contradiction"), ("person", "1")] }

def ex_58a : Datum :=
  { id := "krapova2010_58a"
    source := ⟨"krapova-2010", "(58a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Văzmutix se deto ne sa mogli da provedat sreštata."
    glossedTokens := [("Văzmutix", "resent-1sg"), ("se", "refl"), ("deto", "that"), ("ne", "not"), ("sa", "are-3pl"), ("mogli", "able-pl"), ("da", "Mod"), ("provedat", "organize-3pl"), ("sreštata", "meeting-the")]
    glossedWords := [⟨['V', 'ă', 'z', 'm', 'u', 't', 'i', 'x'], ['r', 'e', 's', 'e', 'n', 't', '-', '1', 's', 'g'], []⟩, ⟨['s', 'e'], ['r', 'e', 'f', 'l'], [⟨['s', 'e'], ['r', 'e', 'f', 'l'], none⟩]⟩, ⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['n', 'e'], ['n', 'o', 't'], [⟨['n', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['s', 'a'], ['a', 'r', 'e', '-', '3', 'p', 'l'], []⟩, ⟨['m', 'o', 'g', 'l', 'i'], ['a', 'b', 'l', 'e', '-', 'p', 'l'], []⟩, ⟨['d', 'a'], ['M', 'o', 'd'], [⟨['d', 'a'], ['M', 'o', 'd'], none⟩]⟩, ⟨['p', 'r', 'o', 'v', 'e', 'd', 'a', 't'], ['o', 'r', 'g', 'a', 'n', 'i', 'z', 'e', '-', '3', 'p', 'l'], []⟩, ⟨['s', 'r', 'e', 'š', 't', 'a', 't', 'a'], ['m', 'e', 'e', 't', 'i', 'n', 'g', '-', 't', 'h', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := [("Văzmutix se če ne sa mogli da provedat sreštata.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "văzmuštavam se"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_58b : Datum :=
  { id := "krapova2010_58b"
    source := ⟨"krapova-2010", "(58b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Otkrix deto sreštata im se e provalila."
    glossedTokens := [("Otkrix", "found-out-1sg"), ("deto", "that"), ("sreštata", "meeting-the"), ("im", "their"), ("se", "refl"), ("e", "is"), ("provalila", "failed-prt")]
    glossedWords := [⟨['O', 't', 'k', 'r', 'i', 'x'], ['f', 'o', 'u', 'n', 'd', '-', 'o', 'u', 't', '-', '1', 's', 'g'], []⟩, ⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], [⟨['d', 'e', 't', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'r', 'e', 'š', 't', 'a', 't', 'a'], ['m', 'e', 'e', 't', 'i', 'n', 'g', '-', 't', 'h', 'e'], []⟩, ⟨['i', 'm'], ['t', 'h', 'e', 'i', 'r'], [⟨['i', 'm'], ['t', 'h', 'e', 'i', 'r'], none⟩]⟩, ⟨['s', 'e'], ['r', 'e', 'f', 'l'], [⟨['s', 'e'], ['r', 'e', 'f', 'l'], none⟩]⟩, ⟨['e'], ['i', 's'], [⟨['e'], ['i', 's'], none⟩]⟩, ⟨['p', 'r', 'o', 'v', 'a', 'l', 'i', 'l', 'a'], ['f', 'a', 'i', 'l', 'e', 'd', '-', 'p', 'r', 't'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := [("Otkrix če sreštata im se e provalila.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "otkrivam"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_59a : Datum :=
  { id := "krapova2010_59a"
    source := ⟨"krapova-2010", "(59a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Săžaljavam za provala na sreštata."
    glossedTokens := [("Săžaljavam", "regret-1sg"), ("za", "for"), ("provala", "failure-the"), ("na", "of"), ("sreštata", "meeting-the")]
    glossedWords := [⟨['S', 'ă', 'ž', 'a', 'l', 'j', 'a', 'v', 'a', 'm'], ['r', 'e', 'g', 'r', 'e', 't', '-', '1', 's', 'g'], []⟩, ⟨['z', 'a'], ['f', 'o', 'r'], [⟨['z', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['p', 'r', 'o', 'v', 'a', 'l', 'a'], ['f', 'a', 'i', 'l', 'u', 'r', 'e', '-', 't', 'h', 'e'], []⟩, ⟨['n', 'a'], ['o', 'f'], [⟨['n', 'a'], ['o', 'f'], none⟩]⟩, ⟨['s', 'r', 'e', 'š', 't', 'a', 't', 'a'], ['m', 'e', 'e', 't', 'i', 'n', 'g', '-', 't', 'h', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Săžaljavam na provala na sreštata.", .ungrammatical), ("Săžaljavam provala na sreštata.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("diagnostic", "zaPhrase")] }

def ex_59b : Datum :=
  { id := "krapova2010_59b"
    source := ⟨"krapova-2010", "(59b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Vinoven li săm za zakăsnenieto na gostite?"
    glossedTokens := [("Vinoven", "guilty"), ("li", "Q"), ("săm", "am"), ("za", "for"), ("zakăsnenieto", "delay-the"), ("na", "of"), ("gostite", "visitors-the")]
    glossedWords := [⟨['V', 'i', 'n', 'o', 'v', 'e', 'n'], ['g', 'u', 'i', 'l', 't', 'y'], [⟨['V', 'i', 'n', 'o', 'v', 'e', 'n'], ['g', 'u', 'i', 'l', 't', 'y'], none⟩]⟩, ⟨['l', 'i'], ['Q'], [⟨['l', 'i'], ['Q'], none⟩]⟩, ⟨['s', 'ă', 'm'], ['a', 'm'], [⟨['s', 'ă', 'm'], ['a', 'm'], none⟩]⟩, ⟨['z', 'a'], ['f', 'o', 'r'], [⟨['z', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['z', 'a', 'k', 'ă', 's', 'n', 'e', 'n', 'i', 'e', 't', 'o'], ['d', 'e', 'l', 'a', 'y', '-', 't', 'h', 'e'], []⟩, ⟨['n', 'a'], ['o', 'f'], [⟨['n', 'a'], ['o', 'f'], none⟩]⟩, ⟨['g', 'o', 's', 't', 'i', 't', 'e'], ['v', 'i', 's', 'i', 't', 'o', 'r', 's', '-', 't', 'h', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Vinoven li săm na zakăsnenieto na gostite?", .ungrammatical), ("Vinoven li săm zakăsnenieto na gostite?", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "vinoven săm"), ("diagnostic", "zaPhrase")] }

def fn46i : Datum :=
  { id := "krapova2010_fn46i"
    source := ⟨"krapova-2010", "fn. 46 (i)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Văzmutix se če ne sa mogli da provedat sreštata."
    glossedTokens := [("Văzmutix", "resent-1sg"), ("se", "refl"), ("če", "that"), ("ne", "not"), ("sa", "are-3pl"), ("mogli", "able-pl"), ("da", "Mod"), ("provedat", "organize-3pl"), ("sreštata", "meeting-the")]
    glossedWords := [⟨['V', 'ă', 'z', 'm', 'u', 't', 'i', 'x'], ['r', 'e', 's', 'e', 'n', 't', '-', '1', 's', 'g'], []⟩, ⟨['s', 'e'], ['r', 'e', 'f', 'l'], [⟨['s', 'e'], ['r', 'e', 'f', 'l'], none⟩]⟩, ⟨['č', 'e'], ['t', 'h', 'a', 't'], [⟨['č', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['n', 'e'], ['n', 'o', 't'], [⟨['n', 'e'], ['n', 'o', 't'], none⟩]⟩, ⟨['s', 'a'], ['a', 'r', 'e', '-', '3', 'p', 'l'], []⟩, ⟨['m', 'o', 'g', 'l', 'i'], ['a', 'b', 'l', 'e', '-', 'p', 'l'], []⟩, ⟨['d', 'a'], ['M', 'o', 'd'], [⟨['d', 'a'], ['M', 'o', 'd'], none⟩]⟩, ⟨['p', 'r', 'o', 'v', 'e', 'd', 'a', 't'], ['o', 'r', 'g', 'a', 'n', 'i', 'z', 'e', '-', '3', 'p', 'l'], []⟩, ⟨['s', 'r', 'e', 'š', 't', 'a', 't', 'a'], ['m', 'e', 'e', 't', 'i', 'n', 'g', '-', 't', 'h', 'e'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Văzmutix se če ne sa mogli da provedat sreštata, no vsăšnost te provedoxa sreštata.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "văzmuštavam se"), ("complementizer", "če"), ("diagnostic", "contradiction"), ("person", "1")] }

def all : List Datum := [ex_56a, ex_56b, ex_57a, ex_57b, ex_57c, ex_58a, ex_58b, ex_59a, ex_59b, fn46i]

end Krapova2010.Examples
