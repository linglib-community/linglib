module

public import Linglib.Data.Examples.Schema

/-!
# `BeaversEtAl2021` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaversEtAl2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaversEtAl2021.Examples`.
-/

@[expose] public section

namespace BeaversEtAl2021.Examples

def beavers_etal2021_1c : Datum :=
  { id := "beavers_etal2021_1c"
    source := ⟨"beavers-etal-2021", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The vase cracked."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root class", "result"), ("form", "monomorphemic verb")] }

def beavers_etal2021_7a : Datum :=
  { id := "beavers_etal2021_7a"
    source := ⟨"beavers-etal-2021", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Look at the bright picture on your left."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root class", "property concept"), ("form", "basic stative")] }

def beavers_etal2021_10a : Datum :=
  { id := "beavers_etal2021_10a"
    source := ⟨"beavers-etal-2021", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The bright photo has never brightened."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "property concept")] }

def beavers_etal2021_11c : Datum :=
  { id := "beavers_etal2021_11c"
    source := ⟨"beavers-etal-2021", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The shattered vase has never shattered."
    glossedTokens := []
    context := "An artist makes ceramic pieces that, properly assembled, would form a vase."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")] }

def beavers_etal2021_13 : Datum :=
  { id := "beavers_etal2021_13"
    source := ⟨"beavers-etal-2021", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The window is broken but it never broke. It was manufactured that way."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result"), ("judgedBy", "some speakers")] }

def beavers_etal2021_15a : Datum :=
  { id := "beavers_etal2021_15a"
    source := ⟨"beavers-etal-2021", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sharpened the knife again."
    glossedTokens := []
    context := "John buys a knife forged already sharp, uses it until it becomes blunt, and sharpens it with a whetting stone."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive: could be just one sharpening", .acceptable)]
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "property concept")] }

def beavers_etal2021_16a : Datum :=
  { id := "beavers_etal2021_16a"
    source := ⟨"beavers-etal-2021", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris thawed the meat again."
    glossedTokens := []
    context := "Chris kills a rabbit, butchers it, freezes the fresh meat for a week, then puts it out to thaw."
    judgment := .unacceptable
    alternatives := []
    readings := [("repetitive: necessarily two defrostings", .acceptable)]
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")] }

def beavers_etal2021_25a : Datum :=
  { id := "beavers_etal2021_25a"
    source := ⟨"beavers-etal-2021", "(25a)"⟩
    reportedIn := none
    language := "cash1251"
    primaryText := "madin papanka ëdkitëkënia."
    glossedTokens := [("madi=n", "sand=POSS"), ("papa=n=ka=a", "father=A/S=VAL=3A/S"), ("ëd-ki-tëkën-i-a", "dry-INTR-again-IPFV-NPROX")]
    glossedWords := [⟨[['m', 'a', 'd', 'i'], ['n']], [['s', 'a', 'n', 'd'], ['P', 'O', 'S', 'S']]⟩, ⟨[['p', 'a', 'p', 'a'], ['n'], ['k', 'a'], ['a']], [['f', 'a', 't', 'h', 'e', 'r'], ['A', '/', 'S'], ['V', 'A', 'L'], ['3', 'A', '/', 'S']]⟩, ⟨[['ë', 'd'], ['k', 'i'], ['t', 'ë', 'k', 'ë', 'n'], ['i'], ['a']], [['d', 'r', 'y'], ['I', 'N', 'T', 'R'], ['a', 'g', 'a', 'i', 'n'], ['I', 'P', 'F', 'V'], ['N', 'P', 'R', 'O', 'X']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The desert starts off dry. Then it is made nondry. Then it turns dry again."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "property concept")] }

def beavers_etal2021_26 : Datum :=
  { id := "beavers_etal2021_26"
    source := ⟨"beavers-etal-2021", "(26)"⟩
    reportedIn := none
    language := "cash1251"
    primaryText := "maxákana rë(të)tëkëa."
    glossedTokens := [("maxat=ka=na", "stone=VAL=1A/S"), ("rëtë-tëkën-a", "kill-again-PFV")]
    glossedWords := [⟨[['m', 'a', 'x', 'a', 't'], ['k', 'a'], ['n', 'a']], [['s', 't', 'o', 'n', 'e'], ['V', 'A', 'L'], ['1', 'A', '/', 'S']]⟩, ⟨[['r', 'ë', 't', 'ë'], ['t', 'ë', 'k', 'ë', 'n'], ['a']], [['k', 'i', 'l', 'l'], ['a', 'g', 'a', 'i', 'n'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The stone was always dead. Then it was brought to life. Then I kill it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")] }

def beavers_etal2021_28a : Datum :=
  { id := "beavers_etal2021_28a"
    source := ⟨"beavers-etal-2021", "(28a)"⟩
    reportedIn := none
    language := "kiny1244"
    primaryText := "Icy-uma gi-hor-a gi-tyay-e."
    glossedTokens := [("Icy-uma", "7-knife"), ("gi-hor-a", "7S-always-FV"), ("gi-tyay-e", "7S-sharp-PFV")]
    glossedWords := [⟨[['I', 'c', 'y'], ['u', 'm', 'a']], [['7'], ['k', 'n', 'i', 'f', 'e']]⟩, ⟨[['g', 'i'], ['h', 'o', 'r'], ['a']], [['7', 'S'], ['a', 'l', 'w', 'a', 'y', 's'], ['F', 'V']]⟩, ⟨[['g', 'i'], ['t', 'y', 'a', 'y'], ['e']], [['7', 'S'], ['s', 'h', 'a', 'r', 'p'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Habimana buys a knife that is manufactured very sharp."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "property concept")] }

def beavers_etal2021_28b : Datum :=
  { id := "beavers_etal2021_28b"
    source := ⟨"beavers-etal-2021", "(28b)"⟩
    reportedIn := none
    language := "kiny1244"
    primaryText := "Umu-keri u-hor-a u-tek-ets-e."
    glossedTokens := [("Umu-keri", "3-fruit"), ("u-hor-a", "3S-always-FV"), ("u-tek-ets-e", "3S-cook-STV-PFV")]
    glossedWords := [⟨[['U', 'm', 'u'], ['k', 'e', 'r', 'i']], [['3'], ['f', 'r', 'u', 'i', 't']]⟩, ⟨[['u'], ['h', 'o', 'r'], ['a']], [['3', 'S'], ['a', 'l', 'w', 'a', 'y', 's'], ['F', 'V']]⟩, ⟨[['u'], ['t', 'e', 'k'], ['e', 't', 's'], ['e']], [['3', 'S'], ['c', 'o', 'o', 'k'], ['S', 'T', 'V'], ['P', 'F', 'V']]⟩]
    lgrConformance := some .morphemeAligned
    context := "A hypothetical fruit that is always soft and ripe since it first grows and can be eaten any time."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")] }

def beavers_etal2021_29b : Datum :=
  { id := "beavers_etal2021_29b"
    source := ⟨"beavers-etal-2021", "(29b)"⟩
    reportedIn := none
    language := "kiny1244"
    primaryText := "Karemera y-ongey-e ku-men-a iki-rahure."
    glossedTokens := [("Karemera", "Karemera"), ("y-ongey-e", "1S-again-PFV"), ("ku-men-a", "INF-break-FV"), ("iki-rahure", "7-glass")]
    glossedWords := [⟨[['K', 'a', 'r', 'e', 'm', 'e', 'r', 'a']], [['K', 'a', 'r', 'e', 'm', 'e', 'r', 'a']]⟩, ⟨[['y'], ['o', 'n', 'g', 'e', 'y'], ['e']], [['1', 'S'], ['a', 'g', 'a', 'i', 'n'], ['P', 'F', 'V']]⟩, ⟨[['k', 'u'], ['m', 'e', 'n'], ['a']], [['I', 'N', 'F'], ['b', 'r', 'e', 'a', 'k'], ['F', 'V']]⟩, ⟨[['i', 'k', 'i'], ['r', 'a', 'h', 'u', 'r', 'e']], [['7'], ['g', 'l', 'a', 's', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Small pieces of glass, manufactured in that size, are assembled into a single pane, which Karemera then breaks."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")] }

def beavers_etal2021_31 : Datum :=
  { id := "beavers_etal2021_31"
    source := ⟨"beavers-etal-2021", "(31)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ha-gesher 'arox 'aval 'afpaʕam lo hu'arax."
    glossedTokens := [("ha-gesher", "the-bridge"), ("'arox", "long"), ("'aval", "but"), ("'afpaʕam", "never"), ("lo", "NEG"), ("hu'arax", "lengthened.PASS")]
    glossedWords := [⟨[['h', 'a'], ['g', 'e', 's', 'h', 'e', 'r']], [['t', 'h', 'e'], ['b', 'r', 'i', 'd', 'g', 'e']]⟩, ⟨[['\'', 'a', 'r', 'o', 'x']], [['l', 'o', 'n', 'g']]⟩, ⟨[['\'', 'a', 'v', 'a', 'l']], [['b', 'u', 't']]⟩, ⟨[['\'', 'a', 'f', 'p', 'a', 'ʕ', 'a', 'm']], [['n', 'e', 'v', 'e', 'r']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['h', 'u', '\'', 'a', 'r', 'a', 'x']], [['l', 'e', 'n', 'g', 't', 'h', 'e', 'n', 'e', 'd', '.', 'P', 'A', 'S', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "property concept")] }

def beavers_etal2021_32 : Datum :=
  { id := "beavers_etal2021_32"
    source := ⟨"beavers-etal-2021", "(32)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ha-zxuxit menupecet, 'aval hi 'afpaʕam lo hitnapca."
    glossedTokens := [("ha-zxuxit", "the-glass"), ("menupecet", "shattered"), ("'aval", "but"), ("hi", "it"), ("'afpaʕam", "never"), ("lo", "NEG"), ("hitnapca", "shattered.REFL")]
    glossedWords := [⟨[['h', 'a'], ['z', 'x', 'u', 'x', 'i', 't']], [['t', 'h', 'e'], ['g', 'l', 'a', 's', 's']]⟩, ⟨[['m', 'e', 'n', 'u', 'p', 'e', 'c', 'e', 't']], [['s', 'h', 'a', 't', 't', 'e', 'r', 'e', 'd']]⟩, ⟨[['\'', 'a', 'v', 'a', 'l']], [['b', 'u', 't']]⟩, ⟨[['h', 'i']], [['i', 't']]⟩, ⟨[['\'', 'a', 'f', 'p', 'a', 'ʕ', 'a', 'm']], [['n', 'e', 'v', 'e', 'r']]⟩, ⟨[['l', 'o']], [['N', 'E', 'G']]⟩, ⟨[['h', 'i', 't', 'n', 'a', 'p', 'c', 'a']], [['s', 'h', 'a', 't', 't', 'e', 'r', 'e', 'd', '.', 'R', 'E', 'F', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")] }

def beavers_etal2021_33b : Datum :=
  { id := "beavers_etal2021_33b"
    source := ⟨"beavers-etal-2021", "(33b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Kim nipca šuv/mexadaš 'et ha-zxuxit."
    glossedTokens := [("Kim", "Kim"), ("nipca", "shattered"), ("šuv/mexadaš", "again/anew"), ("'et", "ACC"), ("ha-zxuxit", "the-glass")]
    glossedWords := [⟨[['K', 'i', 'm']], [['K', 'i', 'm']]⟩, ⟨[['n', 'i', 'p', 'c', 'a']], [['s', 'h', 'a', 't', 't', 'e', 'r', 'e', 'd']]⟩, ⟨[['š', 'u', 'v', '/', 'm', 'e', 'x', 'a', 'd', 'a', 'š']], [['a', 'g', 'a', 'i', 'n', '/', 'a', 'n', 'e', 'w']]⟩, ⟨[['\'', 'e', 't']], [['A', 'C', 'C']]⟩, ⟨[['h', 'a'], ['z', 'x', 'u', 'x', 'i', 't']], [['t', 'h', 'e'], ['g', 'l', 'a', 's', 's']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Small pieces of glass, manufactured in that size, are assembled into a single pane, which Kim then shatters."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")] }

def beavers_etal2021_35b : Datum :=
  { id := "beavers_etal2021_35b"
    source := ⟨"beavers-etal-2021", "(35b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "kāc phoɖ-leli āhe pəɳ ti kədhi phuʈ-leli nāhi."
    glossedTokens := [("kāc", "glass.NOM.F.SG"), ("phoɖ-leli", "shatter.TR-PART.F.SG"), ("āhe", "be.PRS.3SG"), ("pəɳ", "but"), ("ti", "DEM.F.SG"), ("kədhi", "ever"), ("phuʈ-leli", "shatter.INTR-PART.F.SG"), ("nāhi", "NEG")]
    glossedWords := [⟨[['k', 'ā', 'c']], [['g', 'l', 'a', 's', 's', '.', 'N', 'O', 'M', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['p', 'h', 'o', 'ɖ'], ['l', 'e', 'l', 'i']], [['s', 'h', 'a', 't', 't', 'e', 'r', '.', 'T', 'R'], ['P', 'A', 'R', 'T', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['ā', 'h', 'e']], [['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'ə', 'ɳ']], [['b', 'u', 't']]⟩, ⟨[['t', 'i']], [['D', 'E', 'M', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['k', 'ə', 'd', 'h', 'i']], [['e', 'v', 'e', 'r']]⟩, ⟨[['p', 'h', 'u', 'ʈ'], ['l', 'e', 'l', 'i']], [['s', 'h', 'a', 't', 't', 'e', 'r', '.', 'I', 'N', 'T', 'R'], ['P', 'A', 'R', 'T', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['n', 'ā', 'h', 'i']], [['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "change denial"), ("root class", "result")] }

def beavers_etal2021_36b : Datum :=
  { id := "beavers_etal2021_36b"
    source := ⟨"beavers-etal-2021", "(36b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "Kim-ne parat kach phoɖ-li."
    glossedTokens := [("Kim-ne", "Kim-ERG"), ("parat", "again"), ("kach", "glass.F.SG.NOM"), ("phoɖ-li", "break-PFV.F.SG")]
    glossedWords := [⟨[['K', 'i', 'm'], ['n', 'e']], [['K', 'i', 'm'], ['E', 'R', 'G']]⟩, ⟨[['p', 'a', 'r', 'a', 't']], [['a', 'g', 'a', 'i', 'n']]⟩, ⟨[['k', 'a', 'c', 'h']], [['g', 'l', 'a', 's', 's', '.', 'F', '.', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['p', 'h', 'o', 'ɖ'], ['l', 'i']], [['b', 'r', 'e', 'a', 'k'], ['P', 'F', 'V', '.', 'F', '.', 'S', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Small pieces of glass, manufactured in that size, are assembled into a single pane, which Kim then shatters."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "restitutive again"), ("root class", "result")] }

def beavers_etal2021_38b : Datum :=
  { id := "beavers_etal2021_38b"
    source := ⟨"beavers-etal-2021", "(38b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Maria eftiakse ke tin tileorasi."
    glossedTokens := [("I", "the"), ("Maria", "Mary"), ("eftiakse", "fixed"), ("ke", "also"), ("tin", "the"), ("tileorasi", "television")]
    glossedWords := [⟨[['I']], [['t', 'h', 'e']]⟩, ⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'y']]⟩, ⟨[['e', 'f', 't', 'i', 'a', 'k', 's', 'e']], [['f', 'i', 'x', 'e', 'd']]⟩, ⟨[['k', 'e']], [['a', 'l', 's', 'o']]⟩, ⟨[['t', 'i', 'n']], [['t', 'h', 'e']]⟩, ⟨[['t', 'i', 'l', 'e', 'o', 'r', 'a', 's', 'i']], [['t', 'e', 'l', 'e', 'v', 'i', 's', 'i', 'o', 'n']]⟩]
    lgrConformance := some .wordAligned
    context := "Mary bought a new TV and a new laptop. The laptop was working fine, but the TV was not. Mary brought her tools."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "additive restitutive"), ("root class", "result")] }

def all : List Datum := [beavers_etal2021_1c, beavers_etal2021_7a, beavers_etal2021_10a, beavers_etal2021_11c, beavers_etal2021_13, beavers_etal2021_15a, beavers_etal2021_16a, beavers_etal2021_25a, beavers_etal2021_26, beavers_etal2021_28a, beavers_etal2021_28b, beavers_etal2021_29b, beavers_etal2021_31, beavers_etal2021_32, beavers_etal2021_33b, beavers_etal2021_35b, beavers_etal2021_36b, beavers_etal2021_38b]

end BeaversEtAl2021.Examples
