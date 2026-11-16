module

public import Linglib.Data.Examples.Schema

/-!
# `DalrympleHaug2024` — typed example data

Auto-generated from `Linglib/Data/Examples/DalrympleHaug2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DalrympleHaug2024.Examples`.
-/

@[expose] public section

namespace DalrympleHaug2024.Examples

def ex_1 : Datum :=
  { id := "dalrymplehaug2024_1"
    source := ⟨"dalrymple-haug-2024", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Tracy and Chris thought they saw each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .acceptable)]
    paperFeatures := [("section", "1"), ("antecedent", "plural pronoun")] }

def ex_10 : Datum :=
  { id := "dalrymplehaug2024_10"
    source := ⟨"dalrymple-haug-2024", "(10)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Péter és Éva az-t gondolja, hogy szereti egymás-t."
    glossedTokens := [("Péter", "Péter"), ("és", "and"), ("Éva", "Éva"), ("az-t", "that-ACC"), ("gondolja,", "think.3SG"), ("hogy", "that"), ("szereti", "love.3SG"), ("egymás-t.", "RECIP-ACC")]
    glossedWords := [⟨['P', 'é', 't', 'e', 'r'], ['P', 'é', 't', 'e', 'r'], [⟨['P', 'é', 't', 'e', 'r'], ['P', 'é', 't', 'e', 'r'], none⟩]⟩, ⟨['é', 's'], ['a', 'n', 'd'], [⟨['é', 's'], ['a', 'n', 'd'], none⟩]⟩, ⟨['É', 'v', 'a'], ['É', 'v', 'a'], [⟨['É', 'v', 'a'], ['É', 'v', 'a'], none⟩]⟩, ⟨['a', 'z', '-', 't'], ['t', 'h', 'a', 't', '-', 'A', 'C', 'C'], [⟨['a', 'z'], ['t', 'h', 'a', 't'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['g', 'o', 'n', 'd', 'o', 'l', 'j', 'a', ','], ['t', 'h', 'i', 'n', 'k', '.', '3', 'S', 'G'], [⟨['g', 'o', 'n', 'd', 'o', 'l', 'j', 'a'], ['t', 'h', 'i', 'n', 'k', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['h', 'o', 'g', 'y'], ['t', 'h', 'a', 't'], [⟨['h', 'o', 'g', 'y'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['s', 'z', 'e', 'r', 'e', 't', 'i'], ['l', 'o', 'v', 'e', '.', '3', 'S', 'G'], [⟨['s', 'z', 'e', 'r', 'e', 't', 'i'], ['l', 'o', 'v', 'e', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'g', 'y', 'm', 'á', 's', '-', 't', '.'], ['R', 'E', 'C', 'I', 'P', '-', 'A', 'C', 'C'], [⟨['e', 'g', 'y', 'm', 'á', 's'], ['R', 'E', 'C', 'I', 'P'], none⟩, ⟨['t'], ['A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .unacceptable), ("wide", .acceptable)]
    paperFeatures := [("section", "2"), ("antecedent", "bound singular null pronoun")] }

def ex_11 : Datum :=
  { id := "dalrymplehaug2024_11"
    source := ⟨"dalrymple-haug-2024", "(11)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John to Mary ga zibun-tati ga otagai o mi-ta to omow-ta."
    glossedTokens := [("John", "John"), ("to", "and"), ("Mary", "Mary"), ("ga", "NOM"), ("zibun-tati", "self-PL"), ("ga", "NOM"), ("otagai", "RECIP"), ("o", "ACC"), ("mi-ta", "see-PST"), ("to", "that"), ("omow-ta.", "think-PST")]
    glossedWords := [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['t', 'o'], ['a', 'n', 'd'], [⟨['t', 'o'], ['a', 'n', 'd'], none⟩]⟩, ⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], [⟨['M', 'a', 'r', 'y'], ['M', 'a', 'r', 'y'], none⟩]⟩, ⟨['g', 'a'], ['N', 'O', 'M'], [⟨['g', 'a'], ['N', 'O', 'M'], none⟩]⟩, ⟨['z', 'i', 'b', 'u', 'n', '-', 't', 'a', 't', 'i'], ['s', 'e', 'l', 'f', '-', 'P', 'L'], [⟨['z', 'i', 'b', 'u', 'n'], ['s', 'e', 'l', 'f'], none⟩, ⟨['t', 'a', 't', 'i'], ['P', 'L'], some '-'⟩]⟩, ⟨['g', 'a'], ['N', 'O', 'M'], [⟨['g', 'a'], ['N', 'O', 'M'], none⟩]⟩, ⟨['o', 't', 'a', 'g', 'a', 'i'], ['R', 'E', 'C', 'I', 'P'], [⟨['o', 't', 'a', 'g', 'a', 'i'], ['R', 'E', 'C', 'I', 'P'], none⟩]⟩, ⟨['o'], ['A', 'C', 'C'], [⟨['o'], ['A', 'C', 'C'], none⟩]⟩, ⟨['m', 'i', '-', 't', 'a'], ['s', 'e', 'e', '-', 'P', 'S', 'T'], [⟨['m', 'i'], ['s', 'e', 'e'], none⟩, ⟨['t', 'a'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'a', 't'], [⟨['t', 'o'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['o', 'm', 'o', 'w', '-', 't', 'a', '.'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['o', 'm', 'o', 'w'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['t', 'a'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("section", "2"), ("antecedent", "plural reflexive")] }

def ex_12 : Datum :=
  { id := "dalrymplehaug2024_12"
    source := ⟨"dalrymple-haug-2024", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girls hoped that they would meet at the tennis court and defeat each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("section", "3"), ("antecedent", "collective conjunct")] }

def ex_13 : Datum :=
  { id := "dalrymplehaug2024_13"
    source := ⟨"dalrymple-haug-2024", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They wanted to visit each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable)]
    paperFeatures := [("section", "4"), ("antecedent", "PRO, partial-control verb")] }

def ex_14 : Datum :=
  { id := "dalrymplehaug2024_14"
    source := ⟨"dalrymple-haug-2024", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They decided to keep each other's comments confidential."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .acceptable)]
    paperFeatures := [("section", "4"), ("antecedent", "PRO, collective controller")] }

def ex_15a : Datum :=
  { id := "dalrymplehaug2024_15a"
    source := ⟨"dalrymple-haug-2024", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I asked a girl who I liked if she wanted to get to know each other better and she said that she was already talking to someone else."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable)]
    paperFeatures := [("section", "4"), ("antecedent", "PRO, partial control"), ("attested", "web")] }

def ex_15b : Datum :=
  { id := "dalrymplehaug2024_15b"
    source := ⟨"dalrymple-haug-2024", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I vow to keep reminding you McDonald's is unhealthy and to go get that mole checked, because I want to live long, happy lives by each other's side."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable)]
    paperFeatures := [("section", "4"), ("antecedent", "PRO, partial control"), ("attested", "web")] }

def ex_16a : Datum :=
  { id := "dalrymplehaug2024_16a"
    source := ⟨"dalrymple-haug-2024", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw a girl I liked and tried to get to know each other better."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("antecedent", "PRO, exhaustive-control verb")] }

def ex_16b : Datum :=
  { id := "dalrymplehaug2024_16b"
    source := ⟨"dalrymple-haug-2024", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I try to live long, happy lives by each other's side."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("antecedent", "PRO, exhaustive-control verb")] }

def ex_17 : Datum :=
  { id := "dalrymplehaug2024_17"
    source := ⟨"dalrymple-haug-2024", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unbeknownst to each other, Tracy and Chris intended to help each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .unacceptable), ("wide", .acceptable)]
    paperFeatures := [("section", "4"), ("antecedent", "PRO, exhaustive control, distributive controller")] }

def ex_18a : Datum :=
  { id := "dalrymplehaug2024_18a"
    source := ⟨"dalrymple-haug-2024", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They each think they are taller than each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("section", "5"), ("antecedent", "matrix distributor")] }

def ex_18b : Datum :=
  { id := "dalrymplehaug2024_18b"
    source := ⟨"dalrymple-haug-2024", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They each examined each other."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("antecedent", "distributor, simple sentence")] }

def ex_19a : Datum :=
  { id := "dalrymplehaug2024_19a"
    source := ⟨"dalrymple-haug-2024", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They each liked each other but never said a word."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("antecedent", "distributor, simple sentence"), ("attested", "web")] }

def ex_19b : Datum :=
  { id := "dalrymplehaug2024_19b"
    source := ⟨"dalrymple-haug-2024", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At the end of the ceremony, they each kissed each other as husband and wife."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("antecedent", "distributor, simple sentence"), ("attested", "web")] }

def ex_20a : Datum :=
  { id := "dalrymplehaug2024_20a"
    source := ⟨"dalrymple-haug-2024", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If there are 12 persons in a party and each of them shakes hands with each other, how many handshakes do happen in the party?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("antecedent", "distributor 'each of them', simple sentence"), ("attested", "web")] }

def ex_20b : Datum :=
  { id := "dalrymplehaug2024_20b"
    source := ⟨"dalrymple-haug-2024", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Assertion: when a firefly hits a bus, each of them exerts the same force on each other."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("antecedent", "distributor 'each of them', simple sentence"), ("attested", "web")] }

def ex_21a : Datum :=
  { id := "dalrymplehaug2024_21a"
    source := ⟨"dalrymple-haug-2024", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The men told each girl a different story."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal", .acceptable), ("external", .acceptable)]
    paperFeatures := [("section", "5"), ("diagnostic", "internal reading of 'different'")] }

def ex_21b : Datum :=
  { id := "dalrymplehaug2024_21b"
    source := ⟨"dalrymple-haug-2024", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The men told each other a different story."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal", .unacceptable), ("external", .acceptable)]
    paperFeatures := [("section", "5"), ("diagnostic", "internal reading of 'different'")] }

def ex_22 : Datum :=
  { id := "dalrymplehaug2024_22"
    source := ⟨"dalrymple-haug-2024", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The men each told each other a different story."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal", .acceptable)]
    paperFeatures := [("section", "5"), ("diagnostic", "internal reading of 'different'")] }

def ex_23a : Datum :=
  { id := "dalrymplehaug2024_23a"
    source := ⟨"dalrymple-haug-2024", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We each gave each other a different perspective of life, and that provided the balance and a good marriage and parenting needs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal", .acceptable)]
    paperFeatures := [("section", "5"), ("diagnostic", "internal reading of 'different'"), ("attested", "web")] }

def ex_23b : Datum :=
  { id := "dalrymplehaug2024_23b"
    source := ⟨"dalrymple-haug-2024", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They parallel one another and complemented one another other because they each gave each other a different sort of intensity at least how that's how I fell into that music."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("internal", .acceptable)]
    paperFeatures := [("section", "5"), ("diagnostic", "internal reading of 'different'"), ("attested", "web")] }

def ex_24a : Datum :=
  { id := "dalrymplehaug2024_24a"
    source := ⟨"dalrymple-haug-2024", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Callie was an obvious one, as they were extremely close and both accepted that they each liked each other, but they didn't do anything about it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable)]
    paperFeatures := [("section", "5"), ("antecedent", "distributor in the complement clause"), ("attested", "web")] }

def ex_24b : Datum :=
  { id := "dalrymplehaug2024_24b"
    source := ⟨"dalrymple-haug-2024", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw in some rants it says that they just flirted a little or made out and were in love but they already established the fact that they each liked each other before the [sic] kissed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable)]
    paperFeatures := [("section", "5"), ("antecedent", "distributor in the complement clause"), ("attested", "web")] }

def ex_25 : Datum :=
  { id := "dalrymplehaug2024_25"
    source := ⟨"dalrymple-haug-2024", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "So many what ifs and in the end, they find out that they each liked each other before. But now, they each have their own lives to lead."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable)]
    paperFeatures := [("section", "5"), ("antecedent", "distributor in the complement clause"), ("attested", "web")] }

def ex_26a : Datum :=
  { id := "dalrymplehaug2024_26a"
    source := ⟨"dalrymple-haug-2024", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "While watching their movies, they each realize that they miss each other, make up and go to “Monkey Cars 3D” where the whole cast of So Random! and Chad is seen watching “Monkey Cars 3D”."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable)]
    paperFeatures := [("section", "5"), ("antecedent", "matrix distributor"), ("attested", "web")] }

def ex_26b : Datum :=
  { id := "dalrymplehaug2024_26b"
    source := ⟨"dalrymple-haug-2024", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "“And I'll be back,” she reassured him, even though neither of them wanted to admit that they enjoyed each other's company and, deep down, especially on her part, wanted to find out more about that wolf's past."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable)]
    paperFeatures := [("section", "5"), ("antecedent", "matrix distributor 'neither of them'"), ("attested", "web")] }

def ex_28 : Datum :=
  { id := "dalrymplehaug2024_28"
    source := ⟨"dalrymple-haug-2024", "(28)"⟩
    reportedIn := none
    language := "wann1242"
    primaryText := "wì mù tɛ̄ŋ̄ gé mɔ̄ á ē ɔ̄ŋ̄ lɔ̄ lé"
    glossedTokens := [("wì", "animal"), ("mù", "PL"), ("tɛ̄ŋ̄", "all"), ("gé", "say"), ("mɔ̄", "LOG.PL"), ("á", "COP"), ("ē", "REFL"), ("ɔ̄ŋ̄", "RECIP"), ("lɔ̄", "eat"), ("lé", "PROG")]
    glossedWords := [⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], [⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], none⟩]⟩, ⟨['m', 'ù'], ['P', 'L'], [⟨['m', 'ù'], ['P', 'L'], none⟩]⟩, ⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], [⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], none⟩]⟩, ⟨['g', 'é'], ['s', 'a', 'y'], [⟨['g', 'é'], ['s', 'a', 'y'], none⟩]⟩, ⟨['m', 'ɔ', '̄'], ['L', 'O', 'G', '.', 'P', 'L'], [⟨['m', 'ɔ', '̄'], ['L', 'O', 'G', '.', 'P', 'L'], none⟩]⟩, ⟨['á'], ['C', 'O', 'P'], [⟨['á'], ['C', 'O', 'P'], none⟩]⟩, ⟨['ē'], ['R', 'E', 'F', 'L'], [⟨['ē'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['ɔ', '̄', 'ŋ', '̄'], ['R', 'E', 'C', 'I', 'P'], [⟨['ɔ', '̄', 'ŋ', '̄'], ['R', 'E', 'C', 'I', 'P'], none⟩]⟩, ⟨['l', 'ɔ', '̄'], ['e', 'a', 't'], [⟨['l', 'ɔ', '̄'], ['e', 'a', 't'], none⟩]⟩, ⟨['l', 'é'], ['P', 'R', 'O', 'G'], [⟨['l', 'é'], ['P', 'R', 'O', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A hare visits the animals of a forest one by one; worried about infighting, each says to the hare 'We will eat each other'. Back home the hare reports what they said."
    judgment := .acceptable
    alternatives := []
    readings := [("narrow", .acceptable), ("wide", .unacceptable)]
    paperFeatures := [("section", "6"), ("antecedent", "logophor")] }

def ex_31 : Datum :=
  { id := "dalrymplehaug2024_31"
    source := ⟨"dalrymple-haug-2024", "(31)"⟩
    reportedIn := none
    language := "wann1242"
    primaryText := "wì mù é tɛ̄ŋ̄ gé dóō mɔ̄ á wì dɛ̀ŋ̀ mù é tɛ̄ŋ̄ lɔ̄ lé"
    glossedTokens := [("wì", "animal"), ("mù", "PL"), ("é", "DEF"), ("tɛ̄ŋ̄", "all"), ("gé", "say"), ("dóō", "QUOT"), ("mɔ̄", "LOG.PL"), ("á", "COP"), ("wì", "animal"), ("dɛ̀ŋ̀", "rest"), ("mù", "PL"), ("é", "DEF"), ("tɛ̄ŋ̄", "all"), ("lɔ̄", "eat"), ("lé", "PROG")]
    glossedWords := [⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], [⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], none⟩]⟩, ⟨['m', 'ù'], ['P', 'L'], [⟨['m', 'ù'], ['P', 'L'], none⟩]⟩, ⟨['é'], ['D', 'E', 'F'], [⟨['é'], ['D', 'E', 'F'], none⟩]⟩, ⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], [⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], none⟩]⟩, ⟨['g', 'é'], ['s', 'a', 'y'], [⟨['g', 'é'], ['s', 'a', 'y'], none⟩]⟩, ⟨['d', 'ó', 'ō'], ['Q', 'U', 'O', 'T'], [⟨['d', 'ó', 'ō'], ['Q', 'U', 'O', 'T'], none⟩]⟩, ⟨['m', 'ɔ', '̄'], ['L', 'O', 'G', '.', 'P', 'L'], [⟨['m', 'ɔ', '̄'], ['L', 'O', 'G', '.', 'P', 'L'], none⟩]⟩, ⟨['á'], ['C', 'O', 'P'], [⟨['á'], ['C', 'O', 'P'], none⟩]⟩, ⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], [⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], none⟩]⟩, ⟨['d', 'ɛ', '̀', 'ŋ', '̀'], ['r', 'e', 's', 't'], [⟨['d', 'ɛ', '̀', 'ŋ', '̀'], ['r', 'e', 's', 't'], none⟩]⟩, ⟨['m', 'ù'], ['P', 'L'], [⟨['m', 'ù'], ['P', 'L'], none⟩]⟩, ⟨['é'], ['D', 'E', 'F'], [⟨['é'], ['D', 'E', 'F'], none⟩]⟩, ⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], [⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], none⟩]⟩, ⟨['l', 'ɔ', '̄'], ['e', 'a', 't'], [⟨['l', 'ɔ', '̄'], ['e', 'a', 't'], none⟩]⟩, ⟨['l', 'é'], ['P', 'R', 'O', 'G'], [⟨['l', 'é'], ['P', 'R', 'O', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Each animal says 'I will eat the others'."
    judgment := .acceptable
    alternatives := []
    readings := [("bound logophor", .acceptable)]
    paperFeatures := [("section", "6"), ("antecedent", "logophor, no reciprocal")] }

def ex_32 : Datum :=
  { id := "dalrymplehaug2024_32"
    source := ⟨"dalrymple-haug-2024", "(32)"⟩
    reportedIn := none
    language := "wann1242"
    primaryText := "wì mù tɛ̄ŋ̄ tú gé à̰ ɔ̄ŋ̄ lɔ̄ lé"
    glossedTokens := [("wì", "animal"), ("mù", "PL"), ("tɛ̄ŋ̄", "all"), ("tú", "completely"), ("gé", "say"), ("à̰", "3PL"), ("ɔ̄ŋ̄", "RECIP"), ("lɔ̄", "eat"), ("lé", "PROG")]
    glossedWords := [⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], [⟨['w', 'ì'], ['a', 'n', 'i', 'm', 'a', 'l'], none⟩]⟩, ⟨['m', 'ù'], ['P', 'L'], [⟨['m', 'ù'], ['P', 'L'], none⟩]⟩, ⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], [⟨['t', 'ɛ', '̄', 'ŋ', '̄'], ['a', 'l', 'l'], none⟩]⟩, ⟨['t', 'ú'], ['c', 'o', 'm', 'p', 'l', 'e', 't', 'e', 'l', 'y'], [⟨['t', 'ú'], ['c', 'o', 'm', 'p', 'l', 'e', 't', 'e', 'l', 'y'], none⟩]⟩, ⟨['g', 'é'], ['s', 'a', 'y'], [⟨['g', 'é'], ['s', 'a', 'y'], none⟩]⟩, ⟨['à', '̰'], ['3', 'P', 'L'], [⟨['à', '̰'], ['3', 'P', 'L'], none⟩]⟩, ⟨['ɔ', '̄', 'ŋ', '̄'], ['R', 'E', 'C', 'I', 'P'], [⟨['ɔ', '̄', 'ŋ', '̄'], ['R', 'E', 'C', 'I', 'P'], none⟩]⟩, ⟨['l', 'ɔ', '̄'], ['e', 'a', 't'], [⟨['l', 'ɔ', '̄'], ['e', 'a', 't'], none⟩]⟩, ⟨['l', 'é'], ['P', 'R', 'O', 'G'], [⟨['l', 'é'], ['P', 'R', 'O', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Each animal says 'I will eat the others'."
    judgment := .acceptable
    alternatives := []
    readings := [("wide", .acceptable)]
    paperFeatures := [("section", "6"), ("antecedent", "ordinary plural pronoun")] }

def all : List Datum := [ex_1, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15a, ex_15b, ex_16a, ex_16b, ex_17, ex_18a, ex_18b, ex_19a, ex_19b, ex_20a, ex_20b, ex_21a, ex_21b, ex_22, ex_23a, ex_23b, ex_24a, ex_24b, ex_25, ex_26a, ex_26b, ex_28, ex_31, ex_32]

end DalrympleHaug2024.Examples
