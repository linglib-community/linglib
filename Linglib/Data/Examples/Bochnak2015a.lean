module

public import Linglib.Data.Examples.Schema

/-!
# `Bochnak2015a` — typed example data

Auto-generated from `Linglib/Data/Examples/Bochnak2015a.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bochnak2015a.Examples`.
-/

@[expose] public section

namespace Bochnak2015a.Examples

def ex10 : Datum :=
  { id := "bochnak2015a_ex10"
    source := ⟨"bochnak-2015a", "(10b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "bévali wí:diʔ lé:šɨl k’éʔi"
    glossedTokens := [("bevali", "Beverly"), ("wi:diʔ", "this"), ("le-išɨl", "1-give"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['b', 'e', 'v', 'a', 'l', 'i'], ['B', 'e', 'v', 'e', 'r', 'l', 'y'], [⟨['b', 'e', 'v', 'a', 'l', 'i'], ['B', 'e', 'v', 'e', 'r', 'l', 'y'], none⟩]⟩, ⟨['w', 'i', ':', 'd', 'i', 'ʔ'], ['t', 'h', 'i', 's'], [⟨['w', 'i', 'd', 'i', 'ʔ'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['l', 'e', '-', 'i', 'š', 'ɨ', 'l'], ['1', '-', 'g', 'i', 'v', 'e'], [⟨['l', 'e'], ['1'], none⟩, ⟨['i', 'š', 'ɨ', 'l'], ['g', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You borrowed a pot from Beverly, and now you need to give it back to her."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "deontic")] }

def ex11 : Datum :=
  { id := "bochnak2015a_ex11"
    source := ⟨"bochnak-2015a", "(11b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "súku baŋáya ʔéʔišgi k’éʔi"
    glossedTokens := [("suku", "dog"), ("baŋaya", "outside"), ("ʔ-eʔ-i-š-gi", "3-COP-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['s', 'u', 'k', 'u'], ['d', 'o', 'g'], [⟨['s', 'u', 'k', 'u'], ['d', 'o', 'g'], none⟩]⟩, ⟨['b', 'a', 'ŋ', 'a', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], [⟨['b', 'a', 'ŋ', 'a', 'y', 'a'], ['o', 'u', 't', 's', 'i', 'd', 'e'], none⟩]⟩, ⟨['ʔ', '-', 'e', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'i'], ['3', '-', 'C', 'O', 'P', '-', 'I', 'P', 'F', 'V', '-', 'S', 'R', '-', 'R', 'E', 'L'], [⟨['ʔ'], ['3'], none⟩, ⟨['e', 'ʔ'], ['C', 'O', 'P'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['š'], ['S', 'R'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A friend comes to visit, and brings her dog along. You don’t want the dog to come in the house."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "deontic")] }

def ex12 : Datum :=
  { id := "bochnak2015a_ex12"
    source := ⟨"bochnak-2015a", "(12b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát wútpɨda léʔgabigi Léʔi"
    glossedTokens := [("wat", "tomorrow"), ("wutpɨd-a", "Woodfords-LOC"), ("le-eʔ-gab-i-gi", "1-COP-FUT-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    glossedWords := [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['w', 'u', 't', 'p', 'ɨ', 'd', '-', 'a'], ['W', 'o', 'o', 'd', 'f', 'o', 'r', 'd', 's', '-', 'L', 'O', 'C'], [⟨['w', 'u', 't', 'p', 'ɨ', 'd'], ['W', 'o', 'o', 'd', 'f', 'o', 'r', 'd', 's'], none⟩, ⟨['a'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['l', 'e', '-', 'e', 'ʔ', '-', 'g', 'a', 'b', '-', 'i', '-', 'g', 'i'], ['1', '-', 'C', 'O', 'P', '-', 'F', 'U', 'T', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['l', 'e'], ['1'], none⟩, ⟨['e', 'ʔ'], ['C', 'O', 'P'], some '-'⟩, ⟨['g', 'a', 'b'], ['F', 'U', 'T'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['L', '-', 'e', 'ʔ', '-', 'i'], ['1', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['L'], ['1'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "I ask you where you will spend the day tomorrow. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "metaphysical")] }

def ex13 : Datum :=
  { id := "bochnak2015a_ex13"
    source := ⟨"bochnak-2015a", "(13b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu šáwlamhuhak’a wagayáyʔigi k’éʔi"
    glossedTokens := [("me:hu", "boy"), ("šawlamhu-hak’a", "girl-with"), ("wagayayʔ-i-gi", "talk-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['m', 'e', ':', 'h', 'u'], ['b', 'o', 'y'], [⟨['m', 'e', 'h', 'u'], ['b', 'o', 'y'], none⟩]⟩, ⟨['š', 'a', 'w', 'l', 'a', 'm', 'h', 'u', '-', 'h', 'a', 'k', '’', 'a'], ['g', 'i', 'r', 'l', '-', 'w', 'i', 't', 'h'], [⟨['š', 'a', 'w', 'l', 'a', 'm', 'h', 'u'], ['g', 'i', 'r', 'l'], none⟩, ⟨['h', 'a', 'k', '’', 'a'], ['w', 'i', 't', 'h'], some '-'⟩]⟩, ⟨['w', 'a', 'g', 'a', 'y', 'a', 'y', 'ʔ', '-', 'i', '-', 'g', 'i'], ['t', 'a', 'l', 'k', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['w', 'a', 'g', 'a', 'y', 'a', 'y', 'ʔ'], ['t', 'a', 'l', 'k'], none⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "At a school dance, you wonder whether a shy boy will talk to a girl he likes. Your friend says “Yes, …”"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "metaphysical")] }

def ex14 : Datum :=
  { id := "bochnak2015a_ex14"
    source := ⟨"bochnak-2015a", "(14b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "déʔešáŋawiš yéweš gumbeyéc’igigi k’éʔi"
    glossedTokens := [("deʔeš-aŋaw-i-š", "snow-good-IPFV-SR"), ("yeweš", "road"), ("gum-beyec’ig-i-gi", "REFL-close-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['d', 'e', 'ʔ', 'e', 'š', '-', 'a', 'ŋ', 'a', 'w', '-', 'i', '-', 'š'], ['s', 'n', 'o', 'w', '-', 'g', 'o', 'o', 'd', '-', 'I', 'P', 'F', 'V', '-', 'S', 'R'], [⟨['d', 'e', 'ʔ', 'e', 'š'], ['s', 'n', 'o', 'w'], none⟩, ⟨['a', 'ŋ', 'a', 'w'], ['g', 'o', 'o', 'd'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['š'], ['S', 'R'], some '-'⟩]⟩, ⟨['y', 'e', 'w', 'e', 'š'], ['r', 'o', 'a', 'd'], [⟨['y', 'e', 'w', 'e', 'š'], ['r', 'o', 'a', 'd'], none⟩]⟩, ⟨['g', 'u', 'm', '-', 'b', 'e', 'y', 'e', 'c', '’', 'i', 'g', '-', 'i', '-', 'g', 'i'], ['R', 'E', 'F', 'L', '-', 'c', 'l', 'o', 's', 'e', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['g', 'u', 'm'], ['R', 'E', 'F', 'L'], none⟩, ⟨['b', 'e', 'y', 'e', 'c', '’', 'i', 'g'], ['c', 'l', 'o', 's', 'e'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You are planning to drive over the mountains. It’s started to snow, and you know that whenever it snows, the road over the mountains is closed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "epistemic")] }

def ex15 : Datum :=
  { id := "bochnak2015a_ex15"
    source := ⟨"bochnak-2015a", "(15b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "ʔát’abi léʔwigi Léʔi"
    glossedTokens := [("ʔat’abi", "fish"), ("le-iʔiw-i-gi", "1-eat-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    glossedWords := [⟨['ʔ', 'a', 't', '’', 'a', 'b', 'i'], ['f', 'i', 's', 'h'], [⟨['ʔ', 'a', 't', '’', 'a', 'b', 'i'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['l', 'e', '-', 'i', 'ʔ', 'i', 'w', '-', 'i', '-', 'g', 'i'], ['1', '-', 'e', 'a', 't', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['l', 'e'], ['1'], none⟩, ⟨['i', 'ʔ', 'i', 'w'], ['e', 'a', 't'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['L', '-', 'e', 'ʔ', '-', 'i'], ['1', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['L'], ['1'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You are at a restaurant, and the waiter says that today’s special is fish, your favorite food. You say:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "necessity"), ("flavor", "bouletic")] }

def ex16 : Datum :=
  { id := "bochnak2015a_ex16"
    source := ⟨"bochnak-2015a", "(16b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu šáwlamhu wagayáŋaʔ k’éʔi"
    glossedTokens := [("me:hu", "boy"), ("šawlamhu", "girl"), ("wagayaŋaʔ", "talk"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['m', 'e', ':', 'h', 'u'], ['b', 'o', 'y'], [⟨['m', 'e', 'h', 'u'], ['b', 'o', 'y'], none⟩]⟩, ⟨['š', 'a', 'w', 'l', 'a', 'm', 'h', 'u'], ['g', 'i', 'r', 'l'], [⟨['š', 'a', 'w', 'l', 'a', 'm', 'h', 'u'], ['g', 'i', 'r', 'l'], none⟩]⟩, ⟨['w', 'a', 'g', 'a', 'y', 'a', 'ŋ', 'a', 'ʔ'], ['t', 'a', 'l', 'k'], [⟨['w', 'a', 'g', 'a', 'y', 'a', 'ŋ', 'a', 'ʔ'], ['t', 'a', 'l', 'k'], none⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "At a school dance, you tell your friend that a boy who is being shy should talk to a girl he likes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "weak necessity"), ("flavor", "bouletic")] }

def ex17 : Datum :=
  { id := "bochnak2015a_ex17"
    source := ⟨"bochnak-2015a", "(17)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "lí:nuya pú:luŋa deyéwamé:sha k’éʔi"
    glossedTokens := [("li:nu-a", "Reno-LOC"), ("pu:lul-ŋa", "car-NC"), ("de-yewam-e:s-ha", "NMLZ-drive-NEG-CAUS"), ("k’-eʔ-i", "3-COP-IPFV")]
    glossedWords := [⟨['l', 'i', ':', 'n', 'u', '-', 'a'], ['R', 'e', 'n', 'o', '-', 'L', 'O', 'C'], [⟨['l', 'i', 'n', 'u'], ['R', 'e', 'n', 'o'], none⟩, ⟨['a'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['p', 'u', ':', 'l', 'u', 'l', '-', 'ŋ', 'a'], ['c', 'a', 'r', '-', 'N', 'C'], [⟨['p', 'u', 'l', 'u', 'l'], ['c', 'a', 'r'], none⟩, ⟨['ŋ', 'a'], ['N', 'C'], some '-'⟩]⟩, ⟨['d', 'e', '-', 'y', 'e', 'w', 'a', 'm', '-', 'e', ':', 's', '-', 'h', 'a'], ['N', 'M', 'L', 'Z', '-', 'd', 'r', 'i', 'v', 'e', '-', 'N', 'E', 'G', '-', 'C', 'A', 'U', 'S'], [⟨['d', 'e'], ['N', 'M', 'L', 'Z'], none⟩, ⟨['y', 'e', 'w', 'a', 'm'], ['d', 'r', 'i', 'v', 'e'], some '-'⟩, ⟨['e', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['h', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'C', 'O', 'P', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['C', 'O', 'P'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("flavor", "generic")] }

def ex18 : Datum :=
  { id := "bochnak2015a_ex18"
    source := ⟨"bochnak-2015a", "(18b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wádiŋ hé:š ʔump’áyt’igišuweʔ k’éʔi"
    glossedTokens := [("wadiŋ", "now"), ("he:š", "Q"), ("ʔum-p’ayt’i-giš-uweʔ", "2-play-along-hence"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['w', 'a', 'd', 'i', 'ŋ'], ['n', 'o', 'w'], [⟨['w', 'a', 'd', 'i', 'ŋ'], ['n', 'o', 'w'], none⟩]⟩, ⟨['h', 'e', ':', 'š'], ['Q'], [⟨['h', 'e', 'š'], ['Q'], none⟩]⟩, ⟨['ʔ', 'u', 'm', '-', 'p', '’', 'a', 'y', 't', '’', 'i', '-', 'g', 'i', 'š', '-', 'u', 'w', 'e', 'ʔ'], ['2', '-', 'p', 'l', 'a', 'y', '-', 'a', 'l', 'o', 'n', 'g', '-', 'h', 'e', 'n', 'c', 'e'], [⟨['ʔ', 'u', 'm'], ['2'], none⟩, ⟨['p', '’', 'a', 'y', 't', '’', 'i'], ['p', 'l', 'a', 'y'], some '-'⟩, ⟨['g', 'i', 'š'], ['a', 'l', 'o', 'n', 'g'], some '-'⟩, ⟨['u', 'w', 'e', 'ʔ'], ['h', 'e', 'n', 'c', 'e'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Mary’s friends come over to see if she is allowed to come out to play."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "deontic")] }

def ex19 : Datum :=
  { id := "bochnak2015a_ex19"
    source := ⟨"bochnak-2015a", "(19b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "mé:hu šáwlamhuhak’a wagayáyʔigi k’éʔi"
    glossedTokens := [("me:hu", "boy"), ("šawlamhu-hak’a", "girl-with"), ("wagayayʔ-i-gi", "talk-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['m', 'e', ':', 'h', 'u'], ['b', 'o', 'y'], [⟨['m', 'e', 'h', 'u'], ['b', 'o', 'y'], none⟩]⟩, ⟨['š', 'a', 'w', 'l', 'a', 'm', 'h', 'u', '-', 'h', 'a', 'k', '’', 'a'], ['g', 'i', 'r', 'l', '-', 'w', 'i', 't', 'h'], [⟨['š', 'a', 'w', 'l', 'a', 'm', 'h', 'u'], ['g', 'i', 'r', 'l'], none⟩, ⟨['h', 'a', 'k', '’', 'a'], ['w', 'i', 't', 'h'], some '-'⟩]⟩, ⟨['w', 'a', 'g', 'a', 'y', 'a', 'y', 'ʔ', '-', 'i', '-', 'g', 'i'], ['t', 'a', 'l', 'k', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['w', 'a', 'g', 'a', 'y', 'a', 'y', 'ʔ'], ['t', 'a', 'l', 'k'], none⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "At a school dance, you see a shy boy who wants to talk to a girl but isn’t. You ask your friend if that boy is allowed to talk to that girl. Your friend responds: “Yes …”"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "deontic")] }

def ex20 : Datum :=
  { id := "bochnak2015a_ex20"
    source := ⟨"bochnak-2015a", "(20b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát didó:damamaʔišgi k’éʔi"
    glossedTokens := [("wat", "tomorrow"), ("di-do:da-mamaʔ-i-š-gi", "1-build-finish-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['d', 'i', '-', 'd', 'o', ':', 'd', 'a', '-', 'm', 'a', 'm', 'a', 'ʔ', '-', 'i', '-', 'š', '-', 'g', 'i'], ['1', '-', 'b', 'u', 'i', 'l', 'd', '-', 'f', 'i', 'n', 'i', 's', 'h', '-', 'I', 'P', 'F', 'V', '-', 'S', 'R', '-', 'R', 'E', 'L'], [⟨['d', 'i'], ['1'], none⟩, ⟨['d', 'o', 'd', 'a'], ['b', 'u', 'i', 'l', 'd'], some '-'⟩, ⟨['m', 'a', 'm', 'a', 'ʔ'], ['f', 'i', 'n', 'i', 's', 'h'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['š'], ['S', 'R'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You have been working on building a house for quite a while now. I ask when you will be finished. You say it’s possible you’ll finish tomorrow."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "metaphysical")] }

def ex21 : Datum :=
  { id := "bochnak2015a_ex21"
    source := ⟨"bochnak-2015a", "(21b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "bévali k’éheligi k’éʔi"
    glossedTokens := [("bevali", "Beverly"), ("k’-eʔ-hel-i-gi", "3-COP-SUBJ-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['b', 'e', 'v', 'a', 'l', 'i'], ['B', 'e', 'v', 'e', 'r', 'l', 'y'], [⟨['b', 'e', 'v', 'a', 'l', 'i'], ['B', 'e', 'v', 'e', 'r', 'l', 'y'], none⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'h', 'e', 'l', '-', 'i', '-', 'g', 'i'], ['3', '-', 'C', 'O', 'P', '-', 'S', 'U', 'B', 'J', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['C', 'O', 'P'], some '-'⟩, ⟨['h', 'e', 'l'], ['S', 'U', 'B', 'J'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You hear a knock at the door. You can’t see who it is, but can see that the person looks about the same height as Beverly."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "epistemic")] }

def ex22 : Datum :=
  { id := "bochnak2015a_ex22"
    source := ⟨"bochnak-2015a", "(22b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "déʔek hádigi t’í:yeliʔ dibípɨsišgi k’éʔi"
    glossedTokens := [("deʔeg", "rock"), ("hadigi", "that"), ("t’-i:yel-iʔ", "NMLZ-big-ATTR"), ("di-bips-i-š-gi", "1-pick.up-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['d', 'e', 'ʔ', 'e', 'g'], ['r', 'o', 'c', 'k'], [⟨['d', 'e', 'ʔ', 'e', 'g'], ['r', 'o', 'c', 'k'], none⟩]⟩, ⟨['h', 'a', 'd', 'i', 'g', 'i'], ['t', 'h', 'a', 't'], [⟨['h', 'a', 'd', 'i', 'g', 'i'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['t', '’', '-', 'i', ':', 'y', 'e', 'l', '-', 'i', 'ʔ'], ['N', 'M', 'L', 'Z', '-', 'b', 'i', 'g', '-', 'A', 'T', 'T', 'R'], [⟨['t', '’'], ['N', 'M', 'L', 'Z'], none⟩, ⟨['i', 'y', 'e', 'l'], ['b', 'i', 'g'], some '-'⟩, ⟨['i', 'ʔ'], ['A', 'T', 'T', 'R'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'b', 'i', 'p', 's', '-', 'i', '-', 'š', '-', 'g', 'i'], ['1', '-', 'p', 'i', 'c', 'k', '.', 'u', 'p', '-', 'I', 'P', 'F', 'V', '-', 'S', 'R', '-', 'R', 'E', 'L'], [⟨['d', 'i'], ['1'], none⟩, ⟨['b', 'i', 'p', 's'], ['p', 'i', 'c', 'k', '.', 'u', 'p'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['š'], ['S', 'R'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You see someone trying to pick up a very heavy rock. You are very strong, so you tell them that you can lift that rock."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "circumstantial")] }

def ex23 : Datum :=
  { id := "bochnak2015a_ex23"
    source := ⟨"bochnak-2015a", "(23b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "dawpáp’ɨl ʔíʔmiʔaŋawigi k’éʔi wáʔ ŋáwaya"
    glossedTokens := [("dawp’ap’ɨl", "flower"), ("ʔiʔimiʔ-aŋaw-i-gi", "grow-good-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV"), ("waʔ", "here"), ("ŋawa-a", "dirt-LOC")]
    glossedWords := [⟨['d', 'a', 'w', 'p', '’', 'a', 'p', '’', 'ɨ', 'l'], ['f', 'l', 'o', 'w', 'e', 'r'], [⟨['d', 'a', 'w', 'p', '’', 'a', 'p', '’', 'ɨ', 'l'], ['f', 'l', 'o', 'w', 'e', 'r'], none⟩]⟩, ⟨['ʔ', 'i', 'ʔ', 'i', 'm', 'i', 'ʔ', '-', 'a', 'ŋ', 'a', 'w', '-', 'i', '-', 'g', 'i'], ['g', 'r', 'o', 'w', '-', 'g', 'o', 'o', 'd', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['ʔ', 'i', 'ʔ', 'i', 'm', 'i', 'ʔ'], ['g', 'r', 'o', 'w'], none⟩, ⟨['a', 'ŋ', 'a', 'w'], ['g', 'o', 'o', 'd'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩, ⟨['w', 'a', 'ʔ'], ['h', 'e', 'r', 'e'], [⟨['w', 'a', 'ʔ'], ['h', 'e', 'r', 'e'], none⟩]⟩, ⟨['ŋ', 'a', 'w', 'a', '-', 'a'], ['d', 'i', 'r', 't', '-', 'L', 'O', 'C'], [⟨['ŋ', 'a', 'w', 'a'], ['d', 'i', 'r', 't'], none⟩, ⟨['a'], ['L', 'O', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You are discussing what could grow in the garden, given the type of soil."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("force", "possibility"), ("flavor", "circumstantial")] }

def ex30 : Datum :=
  { id := "bochnak2015a_ex30"
    source := ⟨"bochnak-2015a", "(30b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "déʔek t’í:yeliŋa dibípɨsé:sišgi k’éʔi"
    glossedTokens := [("deʔek", "rock"), ("t’-i:yel-iʔ-ŋa", "NMLZ-big-ATTR-NC"), ("di-bips-e:s-i-š-gi", "1-pick.up-NEG-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['d', 'e', 'ʔ', 'e', 'k'], ['r', 'o', 'c', 'k'], [⟨['d', 'e', 'ʔ', 'e', 'k'], ['r', 'o', 'c', 'k'], none⟩]⟩, ⟨['t', '’', '-', 'i', ':', 'y', 'e', 'l', '-', 'i', 'ʔ', '-', 'ŋ', 'a'], ['N', 'M', 'L', 'Z', '-', 'b', 'i', 'g', '-', 'A', 'T', 'T', 'R', '-', 'N', 'C'], [⟨['t', '’'], ['N', 'M', 'L', 'Z'], none⟩, ⟨['i', 'y', 'e', 'l'], ['b', 'i', 'g'], some '-'⟩, ⟨['i', 'ʔ'], ['A', 'T', 'T', 'R'], some '-'⟩, ⟨['ŋ', 'a'], ['N', 'C'], some '-'⟩]⟩, ⟨['d', 'i', '-', 'b', 'i', 'p', 's', '-', 'e', ':', 's', '-', 'i', '-', 'š', '-', 'g', 'i'], ['1', '-', 'p', 'i', 'c', 'k', '.', 'u', 'p', '-', 'N', 'E', 'G', '-', 'I', 'P', 'F', 'V', '-', 'S', 'R', '-', 'R', 'E', 'L'], [⟨['d', 'i'], ['1'], none⟩, ⟨['b', 'i', 'p', 's'], ['p', 'i', 'c', 'k', '.', 'u', 'p'], some '-'⟩, ⟨['e', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['š'], ['S', 'R'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You see someone trying to pick up a very heavy rock, but they can’t lift it. You are not very strong, so you say that you can’t pick up the rock either."
    judgment := .acceptable
    alternatives := [("deʔek t’-i:yel-iʔ-ŋa di-bips-i-š-gi k’-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "necessity"), ("flavor", "circumstantial"), ("prejacent", "negated")] }

def ex31 : Datum :=
  { id := "bochnak2015a_ex31"
    source := ⟨"bochnak-2015a", "(31b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát didó:damamaʔe:sgabišgi k’éʔi"
    glossedTokens := [("wat", "tomorrow"), ("di-do:da-mamaʔ-e:s-gab-i-š-gi", "1-build-finish-NEG-FUT-IPFV-SR-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['d', 'i', '-', 'd', 'o', ':', 'd', 'a', '-', 'm', 'a', 'm', 'a', 'ʔ', '-', 'e', ':', 's', '-', 'g', 'a', 'b', '-', 'i', '-', 'š', '-', 'g', 'i'], ['1', '-', 'b', 'u', 'i', 'l', 'd', '-', 'f', 'i', 'n', 'i', 's', 'h', '-', 'N', 'E', 'G', '-', 'F', 'U', 'T', '-', 'I', 'P', 'F', 'V', '-', 'S', 'R', '-', 'R', 'E', 'L'], [⟨['d', 'i'], ['1'], none⟩, ⟨['d', 'o', 'd', 'a'], ['b', 'u', 'i', 'l', 'd'], some '-'⟩, ⟨['m', 'a', 'm', 'a', 'ʔ'], ['f', 'i', 'n', 'i', 's', 'h'], some '-'⟩, ⟨['e', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['g', 'a', 'b'], ['F', 'U', 'T'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['š'], ['S', 'R'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You have been working on building a house for quite a while now, and you still won’t finish it by tomorrow."
    judgment := .acceptable
    alternatives := [("wat di-do:da-mamaʔ-gab-i-š-gi k’-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "necessity"), ("flavor", "metaphysical"), ("prejacent", "negated")] }

def ex32 : Datum :=
  { id := "bochnak2015a_ex32"
    source := ⟨"bochnak-2015a", "(32b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "demuc’úc’uŋa léʔwé:sigi Léʔi"
    glossedTokens := [("demuc’uc’u-ŋa", "sweet-NC"), ("le-iʔiw-e:s-i-gi", "1-eat-NEG-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    glossedWords := [⟨['d', 'e', 'm', 'u', 'c', '’', 'u', 'c', '’', 'u', '-', 'ŋ', 'a'], ['s', 'w', 'e', 'e', 't', '-', 'N', 'C'], [⟨['d', 'e', 'm', 'u', 'c', '’', 'u', 'c', '’', 'u'], ['s', 'w', 'e', 'e', 't'], none⟩, ⟨['ŋ', 'a'], ['N', 'C'], some '-'⟩]⟩, ⟨['l', 'e', '-', 'i', 'ʔ', 'i', 'w', '-', 'e', ':', 's', '-', 'i', '-', 'g', 'i'], ['1', '-', 'e', 'a', 't', '-', 'N', 'E', 'G', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['l', 'e'], ['1'], none⟩, ⟨['i', 'ʔ', 'i', 'w'], ['e', 'a', 't'], some '-'⟩, ⟨['e', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['L', '-', 'e', 'ʔ', '-', 'i'], ['1', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['L'], ['1'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Someone offers you some candy, but your doctor says you shouldn’t eat candy."
    judgment := .acceptable
    alternatives := [("demuc’uc’u-ŋa le-iʔiw-i-gi L-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "necessity"), ("flavor", "deontic"), ("prejacent", "negated")] }

def ex33 : Datum :=
  { id := "bochnak2015a_ex33"
    source := ⟨"bochnak-2015a", "(33b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát didó:damamaʔé:sheligi Léʔi"
    glossedTokens := [("wat", "tomorrow"), ("di-do:da-mamaʔ-e:s-hel-i-gi", "1-build-finish-NEG-SUBJ-IPFV-REL"), ("L-eʔ-i", "1-MOD-IPFV")]
    glossedWords := [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['d', 'i', '-', 'd', 'o', ':', 'd', 'a', '-', 'm', 'a', 'm', 'a', 'ʔ', '-', 'e', ':', 's', '-', 'h', 'e', 'l', '-', 'i', '-', 'g', 'i'], ['1', '-', 'b', 'u', 'i', 'l', 'd', '-', 'f', 'i', 'n', 'i', 's', 'h', '-', 'N', 'E', 'G', '-', 'S', 'U', 'B', 'J', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['d', 'i'], ['1'], none⟩, ⟨['d', 'o', 'd', 'a'], ['b', 'u', 'i', 'l', 'd'], some '-'⟩, ⟨['m', 'a', 'm', 'a', 'ʔ'], ['f', 'i', 'n', 'i', 's', 'h'], some '-'⟩, ⟨['e', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['h', 'e', 'l'], ['S', 'U', 'B', 'J'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['L', '-', 'e', 'ʔ', '-', 'i'], ['1', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['L'], ['1'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You have been working on building a house for quite a while now, and you’re not sure if you’ll finish it by tomorrow."
    judgment := .acceptable
    alternatives := [("wat di-do:da-mamaʔ-hel-i-gi L-eʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "possibility"), ("flavor", "metaphysical"), ("prejacent", "negated")] }

def ex34 : Datum :=
  { id := "bochnak2015a_ex34"
    source := ⟨"bochnak-2015a", "(34b)"⟩
    reportedIn := none
    language := "wash1253"
    primaryText := "wát háʔašé:sgabigi k’éʔi"
    glossedTokens := [("wat", "tomorrow"), ("haʔaš-e:s-gab-i-gi", "rain-NEG-FUT-IPFV-REL"), ("k’-eʔ-i", "3-MOD-IPFV")]
    glossedWords := [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['w', 'a', 't'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['h', 'a', 'ʔ', 'a', 'š', '-', 'e', ':', 's', '-', 'g', 'a', 'b', '-', 'i', '-', 'g', 'i'], ['r', 'a', 'i', 'n', '-', 'N', 'E', 'G', '-', 'F', 'U', 'T', '-', 'I', 'P', 'F', 'V', '-', 'R', 'E', 'L'], [⟨['h', 'a', 'ʔ', 'a', 'š'], ['r', 'a', 'i', 'n'], none⟩, ⟨['e', 's'], ['N', 'E', 'G'], some '-'⟩, ⟨['g', 'a', 'b'], ['F', 'U', 'T'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩, ⟨['g', 'i'], ['R', 'E', 'L'], some '-'⟩]⟩, ⟨['k', '’', '-', 'e', 'ʔ', '-', 'i'], ['3', '-', 'M', 'O', 'D', '-', 'I', 'P', 'F', 'V'], [⟨['k', '’'], ['3'], none⟩, ⟨['e', 'ʔ'], ['M', 'O', 'D'], some '-'⟩, ⟨['i'], ['I', 'P', 'F', 'V'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "We are discussing the weather for tomorrow. It might rain, but it might not."
    judgment := .acceptable
    alternatives := [("wát háʔaš-gab-i-gi k’-éʔ-e:s-i", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5"), ("force", "possibility"), ("flavor", "metaphysical"), ("prejacent", "negated")] }

def all : List Datum := [ex10, ex11, ex12, ex13, ex14, ex15, ex16, ex17, ex18, ex19, ex20, ex21, ex22, ex23, ex30, ex31, ex32, ex33, ex34]

end Bochnak2015a.Examples
