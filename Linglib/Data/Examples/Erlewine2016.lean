module

public import Linglib.Data.Examples.Schema

/-!
# `Erlewine2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Erlewine2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Erlewine2016.Examples`.
-/

@[expose] public section

namespace Erlewine2016.Examples

def ex_8 : Datum :=
  { id := "erlewine2016_8"
    source := ⟨"erlewine-2016", "(8)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "X-at-ki-tz'ët."
    glossedTokens := [("X-at-ki-tz'ët", "COM-B2SG-A3PL-see")]
    glossedWords := [⟨[['X'], ['a', 't'], ['k', 'i'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '2', 'S', 'G'], ['A', '3', 'P', 'L'], ['s', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def ex_9 : Datum :=
  { id := "erlewine2016_9"
    source := ⟨"erlewine-2016", "(9)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "X-a-wär."
    glossedTokens := [("X-a-wär", "COM-B2SG-sleep")]
    glossedWords := [⟨[['X'], ['a'], ['w', 'ä', 'r']], [['C', 'O', 'M'], ['B', '2', 'S', 'G'], ['s', 'l', 'e', 'e', 'p']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "intransitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "2"), ("verb", "full")] }

def ex_14a : Datum :=
  { id := "erlewine2016_14a"
    source := ⟨"erlewine-2016", "(14a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-∅-tj-ö ri wäy?"
    glossedTokens := [("Achike", "who"), ("x-∅-tj-ö", "COM-B3SG-eat-AF"), ("ri", "the"), ("wäy", "tortilla")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['∅'], ['t', 'j'], ['ö']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['e', 'a', 't'], ['A', 'F']]⟩, ⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_14b : Datum :=
  { id := "erlewine2016_14b"
    source := ⟨"erlewine-2016", "(14b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-∅-u-tëj ri a Juan?"
    glossedTokens := [("Achike", "what"), ("x-∅-u-tëj", "COM-B3SG-A3SG-eat"), ("ri a Juan", "Juan")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'a', 't']]⟩, ⟨[['x'], ['∅'], ['u'], ['t', 'ë', 'j']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['e', 'a', 't']]⟩, ⟨[['r', 'i', ' ', 'a', ' ', 'J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "object"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_18a_emb : Datum :=
  { id := "erlewine2016_18a_emb"
    source := ⟨"erlewine-2016", "(18a), embedded clause"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-∅-a-b'ij rat chin x-oj-tz'et-ö roj?"
    glossedTokens := [("Achike", "who"), ("n-∅-a-b'ij", "INC-B3SG-A2SG-say"), ("rat", "2sg"), ("chin", "that"), ("x-oj-tz'et-ö", "COM-B1PL-see-AF"), ("roj", "1pl")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['n'], ['∅'], ['a'], ['b', '\'', 'i', 'j']], [['I', 'N', 'C'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['s', 'a', 'y']]⟩, ⟨[['r', 'a', 't']], [['2', 's', 'g']]⟩, ⟨[['c', 'h', 'i', 'n']], [['t', 'h', 'a', 't']]⟩, ⟨[['x'], ['o', 'j'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '1', 'P', 'L'], ['s', 'e', 'e'], ['A', 'F']]⟩, ⟨[['r', 'o', 'j']], [['1', 'p', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "1"), ("verb", "AF")] }

def ex_18a_mat : Datum :=
  { id := "erlewine2016_18a_mat"
    source := ⟨"erlewine-2016", "(18a), matrix clause"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-∅-a-b'ij rat chin x-oj-tz'et-ö roj?"
    glossedTokens := [("Achike", "who"), ("n-∅-a-b'ij", "INC-B3SG-A2SG-say"), ("rat", "2sg"), ("chin", "that"), ("x-oj-tz'et-ö", "COM-B1PL-see-AF"), ("roj", "1pl")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['n'], ['∅'], ['a'], ['b', '\'', 'i', 'j']], [['I', 'N', 'C'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['s', 'a', 'y']]⟩, ⟨[['r', 'a', 't']], [['2', 's', 'g']]⟩, ⟨[['c', 'h', 'i', 'n']], [['t', 'h', 'a', 't']]⟩, ⟨[['x'], ['o', 'j'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '1', 'P', 'L'], ['s', 'e', 'e'], ['A', 'F']]⟩, ⟨[['r', 'o', 'j']], [['1', 'p', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "2"), ("object", "3"), ("verb", "full")] }

def ex_18b : Datum :=
  { id := "erlewine2016_18b"
    source := ⟨"erlewine-2016", "(18b), matrix clause"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-a-b'i-n rat chin x-oj-tz'et-ö roj?"
    glossedTokens := [("Achike", "who"), ("n-a-b'i-n", "INC-B2SG-say-AF"), ("rat", "2sg"), ("chin", "that"), ("x-oj-tz'et-ö", "COM-B1PL-see-AF"), ("roj", "1pl")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['n'], ['a'], ['b', '\'', 'i'], ['n']], [['I', 'N', 'C'], ['B', '2', 'S', 'G'], ['s', 'a', 'y'], ['A', 'F']]⟩, ⟨[['r', 'a', 't']], [['2', 's', 'g']]⟩, ⟨[['c', 'h', 'i', 'n']], [['t', 'h', 'a', 't']]⟩, ⟨[['x'], ['o', 'j'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '1', 'P', 'L'], ['s', 'e', 'e'], ['A', 'F']]⟩, ⟨[['r', 'o', 'j']], [['1', 'p', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "2"), ("object", "3"), ("verb", "AF")] }

def ex_18c : Datum :=
  { id := "erlewine2016_18c"
    source := ⟨"erlewine-2016", "(18c), embedded clause"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-∅-a-b'ij rat chin x-oj-r-tz'ët roj?"
    glossedTokens := [("Achike", "who"), ("n-∅-a-b'ij", "INC-B3SG-A2SG-say"), ("rat", "2sg"), ("chin", "that"), ("x-oj-r-tz'ët", "COM-B1PL-A3SG-see"), ("roj", "1pl")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['n'], ['∅'], ['a'], ['b', '\'', 'i', 'j']], [['I', 'N', 'C'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['s', 'a', 'y']]⟩, ⟨[['r', 'a', 't']], [['2', 's', 'g']]⟩, ⟨[['c', 'h', 'i', 'n']], [['t', 'h', 'a', 't']]⟩, ⟨[['x'], ['o', 'j'], ['r'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '1', 'P', 'L'], ['A', '3', 'S', 'G'], ['s', 'e', 'e']]⟩, ⟨[['r', 'o', 'j']], [['1', 'p', 'l']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "1"), ("verb", "full")] }

def ex_27b : Datum :=
  { id := "erlewine2016_27b"
    source := ⟨"erlewine-2016", "(27b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kanqtzij x-∅-u-tëj ri wäy?"
    glossedTokens := [("Achike", "who"), ("kanqtzij", "actually"), ("x-∅-u-tëj", "COM-B3SG-A3SG-eat"), ("ri", "the"), ("wäy", "tortilla")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['k', 'a', 'n', 'q', 't', 'z', 'i', 'j']], [['a', 'c', 't', 'u', 'a', 'l', 'l', 'y']]⟩, ⟨[['x'], ['∅'], ['u'], ['t', 'ë', 'j']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['e', 'a', 't']]⟩, ⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_27c : Datum :=
  { id := "erlewine2016_27c"
    source := ⟨"erlewine-2016", "(27c)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kanqtzij x-∅-tj-ö ri wäy?"
    glossedTokens := [("Achike", "who"), ("kanqtzij", "actually"), ("x-∅-tj-ö", "COM-B3SG-eat-AF"), ("ri", "the"), ("wäy", "tortilla")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['k', 'a', 'n', 'q', 't', 'z', 'i', 'j']], [['a', 'c', 't', 'u', 'a', 'l', 'l', 'y']]⟩, ⟨[['x'], ['∅'], ['t', 'j'], ['ö']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['e', 'a', 't'], ['A', 'F']]⟩, ⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_28a : Datum :=
  { id := "erlewine2016_28a"
    source := ⟨"erlewine-2016", "(28a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri n-∅-tj-ö wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("n-∅-tj-ö", "NONPAST-B3SG-eat-AF"), ("wäy", "tortilla")]
    glossedWords := [⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['a', 'c', 'h', 'i', 'n']], [['m', 'a', 'n']]⟩, ⟨[['r', 'i']], [['R', 'C']]⟩, ⟨[['n'], ['∅'], ['t', 'j'], ['ö']], [['N', 'O', 'N', 'P', 'A', 'S', 'T'], ['B', '3', 'S', 'G'], ['e', 'a', 't'], ['A', 'F']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_28a_full : Datum :=
  { id := "erlewine2016_28a_full"
    source := ⟨"erlewine-2016", "(28a), full agreement"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri n-∅-u-tëj wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("n-∅-u-tëj", "NONPAST-B3SG-A3SG-eat"), ("wäy", "tortilla")]
    glossedWords := [⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['a', 'c', 'h', 'i', 'n']], [['m', 'a', 'n']]⟩, ⟨[['r', 'i']], [['R', 'C']]⟩, ⟨[['n'], ['∅'], ['u'], ['t', 'ë', 'j']], [['N', 'O', 'N', 'P', 'A', 'S', 'T'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['e', 'a', 't']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_28b : Datum :=
  { id := "erlewine2016_28b"
    source := ⟨"erlewine-2016", "(28b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri nojel mul n-∅-u-tëj wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("nojel", "all"), ("mul", "time"), ("n-∅-u-tëj", "NONPAST-B3SG-A3SG-eat"), ("wäy", "tortilla")]
    glossedWords := [⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['a', 'c', 'h', 'i', 'n']], [['m', 'a', 'n']]⟩, ⟨[['r', 'i']], [['R', 'C']]⟩, ⟨[['n', 'o', 'j', 'e', 'l']], [['a', 'l', 'l']]⟩, ⟨[['m', 'u', 'l']], [['t', 'i', 'm', 'e']]⟩, ⟨[['n'], ['∅'], ['u'], ['t', 'ë', 'j']], [['N', 'O', 'N', 'P', 'A', 'S', 'T'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['e', 'a', 't']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_28b_af : Datum :=
  { id := "erlewine2016_28b_af"
    source := ⟨"erlewine-2016", "(28b), AF"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri nojel mul n-∅-tj-ö wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("nojel", "all"), ("mul", "time"), ("n-∅-tj-ö", "NONPAST-B3SG-eat-AF"), ("wäy", "tortilla")]
    glossedWords := [⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['a', 'c', 'h', 'i', 'n']], [['m', 'a', 'n']]⟩, ⟨[['r', 'i']], [['R', 'C']]⟩, ⟨[['n', 'o', 'j', 'e', 'l']], [['a', 'l', 'l']]⟩, ⟨[['m', 'u', 'l']], [['t', 'i', 'm', 'e']]⟩, ⟨[['n'], ['∅'], ['t', 'j'], ['ö']], [['N', 'O', 'N', 'P', 'A', 'S', 'T'], ['B', '3', 'S', 'G'], ['e', 'a', 't'], ['A', 'F']]⟩, ⟨[['w', 'ä', 'y']], [['t', 'o', 'r', 't', 'i', 'l', 'l', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_29a : Datum :=
  { id := "erlewine2016_29a"
    source := ⟨"erlewine-2016", "(29a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-tz'et-ö?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-tz'et-ö", "COM-B3SG-see-AF")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['k', '\'', 'o']], [['∃']]⟩, ⟨[['x'], ['∅'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['s', 'e', 'e'], ['A', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_29a_other : Datum :=
  { id := "erlewine2016_29a_other"
    source := ⟨"erlewine-2016", "(29a), other reading"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-tz'et-ö?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-tz'et-ö", "COM-B3SG-see-AF")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['k', '\'', 'o']], [['∃']]⟩, ⟨[['x'], ['∅'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['s', 'e', 'e'], ['A', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_29b : Datum :=
  { id := "erlewine2016_29b"
    source := ⟨"erlewine-2016", "(29b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-u-tz'ët?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-u-tz'ët", "COM-B3SG-A3SG-see")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['k', '\'', 'o']], [['∃']]⟩, ⟨[['x'], ['∅'], ['u'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['s', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_29b_other : Datum :=
  { id := "erlewine2016_29b_other"
    source := ⟨"erlewine-2016", "(29b), other reading"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-u-tz'ët?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-u-tz'ët", "COM-B3SG-A3SG-see")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['k', '\'', 'o']], [['∃']]⟩, ⟨[['x'], ['∅'], ['u'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['s', 'e', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_53 : Datum :=
  { id := "erlewine2016_53"
    source := ⟨"erlewine-2016", "(53)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-∅-a-tz'ët rat?"
    glossedTokens := [("Achike", "who"), ("x-∅-a-tz'ët", "COM-B3SG-A2SG-see"), ("rat", "you")]
    glossedWords := [⟨[['A', 'c', 'h', 'i', 'k', 'e']], [['w', 'h', 'o']]⟩, ⟨[['x'], ['∅'], ['a'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['s', 'e', 'e']]⟩, ⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def ex_64a : Datum :=
  { id := "erlewine2016_64a"
    source := ⟨"erlewine-2016", "(64a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri a Pedro x-∅-u-ch'äk ri premio."
    glossedTokens := [("Ri a Pedro", "Pedro"), ("x-∅-u-ch'äk", "COM-B3SG-A3SG-win"), ("ri", "the"), ("premio", "prize")]
    glossedWords := [⟨[['R', 'i', ' ', 'a', ' ', 'P', 'e', 'd', 'r', 'o']], [['P', 'e', 'd', 'r', 'o']]⟩, ⟨[['x'], ['∅'], ['u'], ['c', 'h', '\'', 'ä', 'k']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '3', 'S', 'G'], ['w', 'i', 'n']]⟩, ⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['p', 'r', 'e', 'm', 'i', 'o']], [['p', 'r', 'i', 'z', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,TopP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_64b : Datum :=
  { id := "erlewine2016_64b"
    source := ⟨"erlewine-2016", "(64b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "(Ja) ri a Pedro x-∅-ch'ak-ö ri premio."
    glossedTokens := [("(Ja)", "FOC"), ("ri a Pedro", "Pedro"), ("x-∅-ch'ak-ö", "COM-B3SG-win-AF"), ("ri", "the"), ("premio", "prize")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['r', 'i', ' ', 'a', ' ', 'P', 'e', 'd', 'r', 'o']], [['P', 'e', 'd', 'r', 'o']]⟩, ⟨[['x'], ['∅'], ['c', 'h', '\'', 'a', 'k'], ['ö']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['w', 'i', 'n'], ['A', 'F']]⟩, ⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['p', 'r', 'e', 'm', 'i', 'o']], [['p', 'r', 'i', 'z', 'e']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_72a : Datum :=
  { id := "erlewine2016_72a"
    source := ⟨"erlewine-2016", "(72a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja rat x-at-axa-n ri achin."
    glossedTokens := [("Ja", "FOC"), ("rat", "you"), ("x-at-axa-n", "COM-B2SG-hear-AF"), ("ri", "the"), ("achin", "man")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩, ⟨[['x'], ['a', 't'], ['a', 'x', 'a'], ['n']], [['C', 'O', 'M'], ['B', '2', 'S', 'G'], ['h', 'e', 'a', 'r'], ['A', 'F']]⟩, ⟨[['r', 'i']], [['t', 'h', 'e']]⟩, ⟨[['a', 'c', 'h', 'i', 'n']], [['m', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ja rat x-∅-axa-n ri achin.", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "2"), ("object", "3"), ("verb", "AF")] }

def ex_72b : Datum :=
  { id := "erlewine2016_72b"
    source := ⟨"erlewine-2016", "(72b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri achin x-at-axa-n rat."
    glossedTokens := [("Ja", "FOC"), ("ri achin", "the man"), ("x-at-axa-n", "COM-B2SG-hear-AF"), ("rat", "you")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['r', 'i', ' ', 'a', 'c', 'h', 'i', 'n']], [['t', 'h', 'e', ' ', 'm', 'a', 'n']]⟩, ⟨[['x'], ['a', 't'], ['a', 'x', 'a'], ['n']], [['C', 'O', 'M'], ['B', '2', 'S', 'G'], ['h', 'e', 'a', 'r'], ['A', 'F']]⟩, ⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ja ri achin x-∅-axa-n rat.", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "AF")] }

def ex_77a : Datum :=
  { id := "erlewine2016_77a"
    source := ⟨"erlewine-2016", "(77a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-at-in-tz'ët rat."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-at-in-tz'ët", "COM-B2SG-A1SG-see"), ("rat", "you")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['y', 'ï', 'n']], [['m', 'e']]⟩, ⟨[['x'], ['a', 't'], ['i', 'n'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '2', 'S', 'G'], ['A', '1', 'S', 'G'], ['s', 'e', 'e']]⟩, ⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "2"), ("verb", "full")] }

def ex_77b : Datum :=
  { id := "erlewine2016_77b"
    source := ⟨"erlewine-2016", "(77b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-i-tz'et-ö rat."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-i-tz'et-ö", "COM-B1SG-see-AF"), ("rat", "you")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['y', 'ï', 'n']], [['m', 'e']]⟩, ⟨[['x'], ['i'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '1', 'S', 'G'], ['s', 'e', 'e'], ['A', 'F']]⟩, ⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "2"), ("verb", "AF")] }

def ex_78a : Datum :=
  { id := "erlewine2016_78a"
    source := ⟨"erlewine-2016", "(78a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri a Juan x-a-tz'et-ö rat."
    glossedTokens := [("Ja", "FOC"), ("ri a Juan", "Juan"), ("x-a-tz'et-ö", "COM-B2SG-see-AF"), ("rat", "you")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['r', 'i', ' ', 'a', ' ', 'J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['x'], ['a'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '2', 'S', 'G'], ['s', 'e', 'e'], ['A', 'F']]⟩, ⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "AF")] }

def ex_78b : Datum :=
  { id := "erlewine2016_78b"
    source := ⟨"erlewine-2016", "(78b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri a Juan x-a-r-tz'ët rat."
    glossedTokens := [("Ja", "FOC"), ("ri a Juan", "Juan"), ("x-a-r-tz'ët", "COM-B2SG-A3SG-see"), ("rat", "you")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['r', 'i', ' ', 'a', ' ', 'J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩, ⟨[['x'], ['a'], ['r'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '2', 'S', 'G'], ['A', '3', 'S', 'G'], ['s', 'e', 'e']]⟩, ⟨[['r', 'a', 't']], [['y', 'o', 'u']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def ex_79a : Datum :=
  { id := "erlewine2016_79a"
    source := ⟨"erlewine-2016", "(79a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-i-tz'et-ö ri a Juan."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-i-tz'et-ö", "COM-B1SG-see-AF"), ("ri a Juan", "Juan")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['y', 'ï', 'n']], [['m', 'e']]⟩, ⟨[['x'], ['i'], ['t', 'z', '\'', 'e', 't'], ['ö']], [['C', 'O', 'M'], ['B', '1', 'S', 'G'], ['s', 'e', 'e'], ['A', 'F']]⟩, ⟨[['r', 'i', ' ', 'a', ' ', 'J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "AF")] }

def ex_79b : Datum :=
  { id := "erlewine2016_79b"
    source := ⟨"erlewine-2016", "(79b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-∅-in-tz'ët ri a Juan."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-∅-in-tz'ët", "COM-B3SG-A1SG-see"), ("ri a Juan", "Juan")]
    glossedWords := [⟨[['J', 'a']], [['F', 'O', 'C']]⟩, ⟨[['y', 'ï', 'n']], [['m', 'e']]⟩, ⟨[['x'], ['∅'], ['i', 'n'], ['t', 'z', '\'', 'ë', 't']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '1', 'S', 'G'], ['s', 'e', 'e']]⟩, ⟨[['r', 'i', ' ', 'a', ' ', 'J', 'u', 'a', 'n']], [['J', 'u', 'a', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "full")] }

def ex_87b : Datum :=
  { id := "erlewine2016_87b"
    source := ⟨"erlewine-2016", "(87b)"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "Mac xc-ach 7il-ni?"
    glossedTokens := [("Mac", "who"), ("xc-ach", "COM-B2SG"), ("7il-ni", "see-AF")]
    glossedWords := [⟨[['M', 'a', 'c']], [['w', 'h', 'o']]⟩, ⟨[['x', 'c'], ['a', 'c', 'h']], [['C', 'O', 'M'], ['B', '2', 'S', 'G']]⟩, ⟨[['7', 'i', 'l'], ['n', 'i']], [['s', 'e', 'e'], ['A', 'F']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "AF")] }

def ex_88b : Datum :=
  { id := "erlewine2016_88b"
    source := ⟨"erlewine-2016", "(88b)"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "Ha-ch x-∅-7il-ni naj."
    glossedTokens := [("Ha-ch", "FOC-2sg"), ("x-∅-7il-ni", "COM-B3SG-see-AF"), ("naj", "3sg")]
    glossedWords := [⟨[['H', 'a'], ['c', 'h']], [['F', 'O', 'C'], ['2', 's', 'g']]⟩, ⟨[['x'], ['∅'], ['7', 'i', 'l'], ['n', 'i']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['s', 'e', 'e'], ['A', 'F']]⟩, ⟨[['n', 'a', 'j']], [['3', 's', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "2"), ("object", "3"), ("verb", "AF")] }

def ex_88c : Datum :=
  { id := "erlewine2016_88c"
    source := ⟨"erlewine-2016", "(88c)"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "Ha-ch x-∅-aw-(7)il naj."
    glossedTokens := [("Ha-ch", "FOC-2sg"), ("x-∅-aw-(7)il", "COM-B3SG-A2SG-see"), ("naj", "3sg")]
    glossedWords := [⟨[['H', 'a'], ['c', 'h']], [['F', 'O', 'C'], ['2', 's', 'g']]⟩, ⟨[['x'], ['∅'], ['a', 'w'], ['7', 'i', 'l']], [['C', 'O', 'M'], ['B', '3', 'S', 'G'], ['A', '2', 'S', 'G'], ['s', 'e', 'e']]⟩, ⟨[['n', 'a', 'j']], [['3', 's', 'g']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "2"), ("object", "3"), ("verb", "full")] }

def ex_91a : Datum :=
  { id := "erlewine2016_91a"
    source := ⟨"erlewine-2016", "(91a)"⟩
    reportedIn := none
    language := "west2635"
    primaryText := "Ja'-in ∅-ij-on-toj naj unin."
    glossedTokens := [("Ja'-in", "FOC-1sg"), ("∅-ij-on-toj", "B3SG-back.carry-AF-DIR"), ("naj unin", "boy")]
    glossedWords := [⟨[['J', 'a', '\''], ['i', 'n']], [['F', 'O', 'C'], ['1', 's', 'g']]⟩, ⟨[['∅'], ['i', 'j'], ['o', 'n'], ['t', 'o', 'j']], [['B', '3', 'S', 'G'], ['b', 'a', 'c', 'k', '.', 'c', 'a', 'r', 'r', 'y'], ['A', 'F'], ['D', 'I', 'R']]⟩, ⟨[['n', 'a', 'j', ' ', 'u', 'n', 'i', 'n']], [['b', 'o', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "AF")] }

def ex_91b : Datum :=
  { id := "erlewine2016_91b"
    source := ⟨"erlewine-2016", "(91b)"⟩
    reportedIn := none
    language := "west2635"
    primaryText := "Ja'-in ∅-w-ij-toj naj unin."
    glossedTokens := [("Ja'-in", "FOC-1sg"), ("∅-w-ij-toj", "B3SG-A1SG-back.carry-DIR"), ("naj unin", "boy")]
    glossedWords := [⟨[['J', 'a', '\''], ['i', 'n']], [['F', 'O', 'C'], ['1', 's', 'g']]⟩, ⟨[['∅'], ['w'], ['i', 'j'], ['t', 'o', 'j']], [['B', '3', 'S', 'G'], ['A', '1', 'S', 'G'], ['b', 'a', 'c', 'k', '.', 'c', 'a', 'r', 'r', 'y'], ['D', 'I', 'R']]⟩, ⟨[['n', 'a', 'j', ' ', 'u', 'n', 'i', 'n']], [['b', 'o', 'y']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "full")] }

def ex_93 : Datum :=
  { id := "erlewine2016_93"
    source := ⟨"erlewine-2016", "(93)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Maxki tyi y-il-ä-yety?"
    glossedTokens := [("Maxki", "who"), ("tyi", "ASP"), ("y-il-ä-yety", "A3-see-TV-B2")]
    glossedWords := [⟨[['M', 'a', 'x', 'k', 'i']], [['w', 'h', 'o']]⟩, ⟨[['t', 'y', 'i']], [['A', 'S', 'P']]⟩, ⟨[['y'], ['i', 'l'], ['ä'], ['y', 'e', 't', 'y']], [['A', '3'], ['s', 'e', 'e'], ['T', 'V'], ['B', '2']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def all : List Datum := [ex_8, ex_9, ex_14a, ex_14b, ex_18a_emb, ex_18a_mat, ex_18b, ex_18c, ex_27b, ex_27c, ex_28a, ex_28a_full, ex_28b, ex_28b_af, ex_29a, ex_29a_other, ex_29b, ex_29b_other, ex_53, ex_64a, ex_64b, ex_72a, ex_72b, ex_77a, ex_77b, ex_78a, ex_78b, ex_79a, ex_79b, ex_87b, ex_88b, ex_88c, ex_91a, ex_91b, ex_93]

end Erlewine2016.Examples
