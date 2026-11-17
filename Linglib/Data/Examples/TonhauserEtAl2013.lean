module

public import Linglib.Data.Examples.Schema

/-!
# `TonhauserEtAl2013` — typed example data

Auto-generated from `Linglib/Data/Examples/TonhauserEtAl2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TonhauserEtAl2013.Examples`.
-/

@[expose] public section

namespace TonhauserEtAl2013.Examples

def ex_1a : Datum :=
  { id := "tonhauseretal2013_1a"
    source := ⟨"chierchia-mcconnell-ginet-1990", "(28a)"⟩
    reportedIn := some ⟨"tonhauser-beaver-roberts-simons-2013", "(1a)"⟩
    language := "stan1293"
    primaryText := "The present queen of France lives in Ithaca."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "definite"), ("content", "existence of a unique queen of France"), ("environment", "atomic")] }

def ex_1b : Datum :=
  { id := "tonhauseretal2013_1b"
    source := ⟨"chierchia-mcconnell-ginet-1990", "(28b)"⟩
    reportedIn := some ⟨"tonhauser-beaver-roberts-simons-2013", "(1b)"⟩
    language := "stan1293"
    primaryText := "It is not the case that the present queen of France lives in Ithaca."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "definite"), ("content", "existence of a unique queen of France"), ("environment", "negation")] }

def ex_1c : Datum :=
  { id := "tonhauseretal2013_1c"
    source := ⟨"chierchia-mcconnell-ginet-1990", "(28c)"⟩
    reportedIn := some ⟨"tonhauser-beaver-roberts-simons-2013", "(1c)"⟩
    language := "stan1293"
    primaryText := "Does the present queen of France live in Ithaca?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "definite"), ("content", "existence of a unique queen of France"), ("environment", "question")] }

def ex_1d : Datum :=
  { id := "tonhauseretal2013_1d"
    source := ⟨"chierchia-mcconnell-ginet-1990", "(28d)"⟩
    reportedIn := some ⟨"tonhauser-beaver-roberts-simons-2013", "(1d)"⟩
    language := "stan1293"
    primaryText := "If the present queen of France lives in Ithaca, she has probably met Nelly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "definite"), ("content", "existence of a unique queen of France"), ("environment", "conditional antecedent")] }

def ex_13 : Datum :=
  { id := "tonhauseretal2013_13"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(13)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe aña memby Márko ko’ãga oi-pota a-mba’apo iñ-hermáno karnisería-pe."
    glossedTokens := [("Pe", "that"), ("aña", "devil"), ("memby", "child"), ("Márko", "Marko"), ("ko’ãga", "now"), ("oi-pota", "A3-want"), ("a-mba’apo", "A1SG-work"), ("iñ-hermáno", "B3-brother"), ("karnisería-pe", "butcher.shop-in")]
    glossedWords := [⟨['P', 'e'], ['t', 'h', 'a', 't'], [⟨['P', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['a', 'ñ', 'a'], ['d', 'e', 'v', 'i', 'l'], [⟨['a', 'ñ', 'a'], ['d', 'e', 'v', 'i', 'l'], none⟩]⟩, ⟨['m', 'e', 'm', 'b', 'y'], ['c', 'h', 'i', 'l', 'd'], [⟨['m', 'e', 'm', 'b', 'y'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['M', 'á', 'r', 'k', 'o'], ['M', 'a', 'r', 'k', 'o'], [⟨['M', 'á', 'r', 'k', 'o'], ['M', 'a', 'r', 'k', 'o'], none⟩]⟩, ⟨['k', 'o', '’', 'ã', 'g', 'a'], ['n', 'o', 'w'], [⟨['k', 'o', '’', 'ã', 'g', 'a'], ['n', 'o', 'w'], none⟩]⟩, ⟨['o', 'i', '-', 'p', 'o', 't', 'a'], ['A', '3', '-', 'w', 'a', 'n', 't'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['p', 'o', 't', 'a'], ['w', 'a', 'n', 't'], some '-'⟩]⟩, ⟨['a', '-', 'm', 'b', 'a', '’', 'a', 'p', 'o'], ['A', '1', 'S', 'G', '-', 'w', 'o', 'r', 'k'], [⟨['a'], ['A', '1', 'S', 'G'], none⟩, ⟨['m', 'b', 'a', '’', 'a', 'p', 'o'], ['w', 'o', 'r', 'k'], some '-'⟩]⟩, ⟨['i', 'ñ', '-', 'h', 'e', 'r', 'm', 'á', 'n', 'o'], ['B', '3', '-', 'b', 'r', 'o', 't', 'h', 'e', 'r'], [⟨['i', 'ñ'], ['B', '3'], none⟩, ⟨['h', 'e', 'r', 'm', 'á', 'n', 'o'], ['b', 'r', 'o', 't', 'h', 'e', 'r'], some '-'⟩]⟩, ⟨['k', 'a', 'r', 'n', 'i', 's', 'e', 'r', 'í', 'a', '-', 'p', 'e'], ['b', 'u', 't', 'c', 'h', 'e', 'r', '.', 's', 'h', 'o', 'p', '-', 'i', 'n'], [⟨['k', 'a', 'r', 'n', 'i', 's', 'e', 'r', 'í', 'a'], ['b', 'u', 't', 'c', 'h', 'e', 'r', '.', 's', 'h', 'o', 'p'], none⟩, ⟨['p', 'e'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Julia and Maria work in a bakery; their boss, who is generally strict but fair, is called Marko. One day, he calls Julia into his office; when she emerges, she says to Maria:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "expressive"), ("content", "negative evaluation"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_14a : Datum :=
  { id := "tonhauseretal2013_14a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(14a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Simon, che-kichiha-kue, o-ñe’ẽ Aleman."
    glossedTokens := [("Simon", "Simon"), ("che-kichiha-kue", "B1SG-boyfriend-NOM.TERM"), ("o-ñe’ẽ", "A3-speak"), ("Aleman", "German")]
    glossedWords := [⟨['S', 'i', 'm', 'o', 'n'], ['S', 'i', 'm', 'o', 'n'], [⟨['S', 'i', 'm', 'o', 'n'], ['S', 'i', 'm', 'o', 'n'], none⟩]⟩, ⟨['c', 'h', 'e', '-', 'k', 'i', 'c', 'h', 'i', 'h', 'a', '-', 'k', 'u', 'e'], ['B', '1', 'S', 'G', '-', 'b', 'o', 'y', 'f', 'r', 'i', 'e', 'n', 'd', '-', 'N', 'O', 'M', '.', 'T', 'E', 'R', 'M'], [⟨['c', 'h', 'e'], ['B', '1', 'S', 'G'], none⟩, ⟨['k', 'i', 'c', 'h', 'i', 'h', 'a'], ['b', 'o', 'y', 'f', 'r', 'i', 'e', 'n', 'd'], some '-'⟩, ⟨['k', 'u', 'e'], ['N', 'O', 'M', '.', 'T', 'E', 'R', 'M'], some '-'⟩]⟩, ⟨['o', '-', 'ñ', 'e', '’', 'ẽ'], ['A', '3', '-', 's', 'p', 'e', 'a', 'k'], [⟨['o'], ['A', '3'], none⟩, ⟨['ñ', 'e', '’', 'ẽ'], ['s', 'p', 'e', 'a', 'k'], some '-'⟩]⟩, ⟨['A', 'l', 'e', 'm', 'a', 'n'], ['G', 'e', 'r', 'm', 'a', 'n'], [⟨['A', 'l', 'e', 'm', 'a', 'n'], ['G', 'e', 'r', 'm', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Raul is new in town. His neighbor Simon invites him to his house for a party and introduces him to Maria. When Simon has walked away, Maria tells Raul:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "appositive"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_14b : Datum :=
  { id := "tonhauseretal2013_14b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(14b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Papa Benedícto 16, o-nasẽ-va’e-kue Alemánia-pe, oi-ko Róma-pe."
    glossedTokens := [("Papa", "Pope"), ("Benedícto", "Benedict"), ("16", "16"), ("o-nasẽ-va’e-kue", "A3-born-RC-NOM.TERM"), ("Alemánia-pe", "Germany-in"), ("oi-ko", "A3-live"), ("Róma-pe", "Rome-in")]
    glossedWords := [⟨['P', 'a', 'p', 'a'], ['P', 'o', 'p', 'e'], [⟨['P', 'a', 'p', 'a'], ['P', 'o', 'p', 'e'], none⟩]⟩, ⟨['B', 'e', 'n', 'e', 'd', 'í', 'c', 't', 'o'], ['B', 'e', 'n', 'e', 'd', 'i', 'c', 't'], [⟨['B', 'e', 'n', 'e', 'd', 'í', 'c', 't', 'o'], ['B', 'e', 'n', 'e', 'd', 'i', 'c', 't'], none⟩]⟩, ⟨['1', '6'], ['1', '6'], [⟨['1', '6'], ['1', '6'], none⟩]⟩, ⟨['o', '-', 'n', 'a', 's', 'ẽ', '-', 'v', 'a', '’', 'e', '-', 'k', 'u', 'e'], ['A', '3', '-', 'b', 'o', 'r', 'n', '-', 'R', 'C', '-', 'N', 'O', 'M', '.', 'T', 'E', 'R', 'M'], [⟨['o'], ['A', '3'], none⟩, ⟨['n', 'a', 's', 'ẽ'], ['b', 'o', 'r', 'n'], some '-'⟩, ⟨['v', 'a', '’', 'e'], ['R', 'C'], some '-'⟩, ⟨['k', 'u', 'e'], ['N', 'O', 'M', '.', 'T', 'E', 'R', 'M'], some '-'⟩]⟩, ⟨['A', 'l', 'e', 'm', 'á', 'n', 'i', 'a', '-', 'p', 'e'], ['G', 'e', 'r', 'm', 'a', 'n', 'y', '-', 'i', 'n'], [⟨['A', 'l', 'e', 'm', 'á', 'n', 'i', 'a'], ['G', 'e', 'r', 'm', 'a', 'n', 'y'], none⟩, ⟨['p', 'e'], ['i', 'n'], some '-'⟩]⟩, ⟨['o', 'i', '-', 'k', 'o'], ['A', '3', '-', 'l', 'i', 'v', 'e'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['k', 'o'], ['l', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['R', 'ó', 'm', 'a', '-', 'p', 'e'], ['R', 'o', 'm', 'e', '-', 'i', 'n'], [⟨['R', 'ó', 'm', 'a'], ['R', 'o', 'm', 'e'], none⟩, ⟨['p', 'e'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The children in a history class have to give presentations about famous people. Malena has to talk about the pope. She starts with:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_15a : Datum :=
  { id := "tonhauseretal2013_15a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(15a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Maléna hasy ra’e. Aimete o-gue’ẽ."
    glossedTokens := [("Maléna", "Malena"), ("hasy", "B3.sick"), ("ra’e", "it.seems"), ("Aimete", "almost"), ("o-gue’ẽ", "A3-vomit")]
    glossedWords := [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['h', 'a', 's', 'y'], ['B', '3', '.', 's', 'i', 'c', 'k'], [⟨['h', 'a', 's', 'y'], ['B', '3', '.', 's', 'i', 'c', 'k'], none⟩]⟩, ⟨['r', 'a', '’', 'e'], ['i', 't', '.', 's', 'e', 'e', 'm', 's'], [⟨['r', 'a', '’', 'e'], ['i', 't', '.', 's', 'e', 'e', 'm', 's'], none⟩]⟩, ⟨['A', 'i', 'm', 'e', 't', 'e'], ['a', 'l', 'm', 'o', 's', 't'], [⟨['A', 'i', 'm', 'e', 't', 'e'], ['a', 'l', 'm', 'o', 's', 't'], none⟩]⟩, ⟨['o', '-', 'g', 'u', 'e', '’', 'ẽ'], ['A', '3', '-', 'v', 'o', 'm', 'i', 't'], [⟨['o'], ['A', '3'], none⟩, ⟨['g', 'u', 'e', '’', 'ẽ'], ['v', 'o', 'm', 'i', 't'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A mother calls for her daughter to come down for dinner. Her daughter doesn’t appear so she goes upstairs to check on her. When she comes back down, she says to her husband:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "aimete ‘almost’"), ("content", "polar implication"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_15b : Datum :=
  { id := "tonhauseretal2013_15b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(15b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ché-nte a-mo-potĩ ñande-róga!"
    glossedTokens := [("Ché-nte", "PRON.S.1SG-only"), ("a-mo-potĩ", "A1SG-CAUS-clean"), ("ñande-róga", "B1PL.INCL-house")]
    glossedWords := [⟨['C', 'h', 'é', '-', 'n', 't', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '1', 'S', 'G', '-', 'o', 'n', 'l', 'y'], [⟨['C', 'h', 'é'], ['P', 'R', 'O', 'N', '.', 'S', '.', '1', 'S', 'G'], none⟩, ⟨['n', 't', 'e'], ['o', 'n', 'l', 'y'], some '-'⟩]⟩, ⟨['a', '-', 'm', 'o', '-', 'p', 'o', 't', 'ĩ'], ['A', '1', 'S', 'G', '-', 'C', 'A', 'U', 'S', '-', 'c', 'l', 'e', 'a', 'n'], [⟨['a'], ['A', '1', 'S', 'G'], none⟩, ⟨['m', 'o'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['p', 'o', 't', 'ĩ'], ['c', 'l', 'e', 'a', 'n'], some '-'⟩]⟩, ⟨['ñ', 'a', 'n', 'd', 'e', '-', 'r', 'ó', 'g', 'a'], ['B', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'h', 'o', 'u', 's', 'e'], [⟨['ñ', 'a', 'n', 'd', 'e'], ['B', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['r', 'ó', 'g', 'a'], ['h', 'o', 'u', 's', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Carla, a mother of three teenage daughters, falls on the way to the supermarket and breaks her leg. She’s been in the hospital for a week when her daughters come to visit her for the first time. When she asks them how they are doing, her youngest daughter blurts out:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "-nte ‘only’"), ("content", "prejacent implication"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_16a : Datum :=
  { id := "tonhauseretal2013_16a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(16a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe kuimba’e nde-ru."
    glossedTokens := [("Pe", "that"), ("kuimba’e", "man"), ("nde-ru", "B2SG-father")]
    glossedWords := [⟨['P', 'e'], ['t', 'h', 'a', 't'], [⟨['P', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], [⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], none⟩]⟩, ⟨['n', 'd', 'e', '-', 'r', 'u'], ['B', '2', 'S', 'G', '-', 'f', 'a', 't', 'h', 'e', 'r'], [⟨['n', 'd', 'e'], ['B', '2', 'S', 'G'], none⟩, ⟨['r', 'u'], ['f', 'a', 't', 'h', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "You and your friend Maria are walking across a meadow. Both of you can see something ahead, lying in the grass, but you can’t identify what it is, even whether it’s an object, an animal, or a person. You have much better vision than Maria (who can generally only recognize people when they stand right in front of her). As you approach, you recognize what is lying ahead and tell Maria:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "property attribution"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_16b : Datum :=
  { id := "tonhauseretal2013_16b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(16b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ha’e peteĩ kuimba’e."
    glossedTokens := [("Ha’e", "PRON.S.3"), ("peteĩ", "one"), ("kuimba’e", "man")]
    glossedWords := [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], [⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], [⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "You and your friend Maria are walking across a meadow. Both of you can see something ahead, lying in the grass, but you can’t identify what it is, even whether it’s an object, an animal, or a person. You have much better vision than Maria (who can generally only recognize people when they stand right in front of her). As you approach, you recognize what is lying ahead and tell Maria:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "human referent"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_17a : Datum :=
  { id := "tonhauseretal2013_17a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(17a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    glossedWords := [⟨['Ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['Ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩, ⟨['o', '-', 'k', 'a', 'r', 'u'], ['A', '3', '-', 'e', 'a', 't'], [⟨['o'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'u'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_17b : Datum :=
  { id := "tonhauseretal2013_17b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(17b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    glossedWords := [⟨['Ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['Ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩, ⟨['o', '-', 'k', 'a', 'r', 'u'], ['A', '3', '-', 'e', 'a', 't'], [⟨['o'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'u'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same as in (17a), except that Malena is eating empanadas."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_18a : Datum :=
  { id := "tonhauseretal2013_18a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(18a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe mitã-’i che-ryvy."
    glossedTokens := [("Pe", "that"), ("mitã-’i", "child-DIM"), ("che-ryvy", "B1SG-younger.brother")]
    glossedWords := [⟨['P', 'e'], ['t', 'h', 'a', 't'], [⟨['P', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'i', 't', 'ã', '-', '’', 'i'], ['c', 'h', 'i', 'l', 'd', '-', 'D', 'I', 'M'], [⟨['m', 'i', 't', 'ã'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['’', 'i'], ['D', 'I', 'M'], some '-'⟩]⟩, ⟨['c', 'h', 'e', '-', 'r', 'y', 'v', 'y'], ['B', '1', 'S', 'G', '-', 'y', 'o', 'u', 'n', 'g', 'e', 'r', '.', 'b', 'r', 'o', 't', 'h', 'e', 'r'], [⟨['c', 'h', 'e'], ['B', '1', 'S', 'G'], none⟩, ⟨['r', 'y', 'v', 'y'], ['y', 'o', 'u', 'n', 'g', 'e', 'r', '.', 'b', 'r', 'o', 't', 'h', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The children in a sociology class have to give presentations about their families. Marko is up first and he starts with:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_18b : Datum :=
  { id := "tonhauseretal2013_18b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(18b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe mitã-’i che-ryvy."
    glossedTokens := [("Pe", "that"), ("mitã-’i", "child-DIM"), ("che-ryvy", "B1SG-younger.brother")]
    glossedWords := [⟨['P', 'e'], ['t', 'h', 'a', 't'], [⟨['P', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'i', 't', 'ã', '-', '’', 'i'], ['c', 'h', 'i', 'l', 'd', '-', 'D', 'I', 'M'], [⟨['m', 'i', 't', 'ã'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['’', 'i'], ['D', 'I', 'M'], some '-'⟩]⟩, ⟨['c', 'h', 'e', '-', 'r', 'y', 'v', 'y'], ['B', '1', 'S', 'G', '-', 'y', 'o', 'u', 'n', 'g', 'e', 'r', '.', 'b', 'r', 'o', 't', 'h', 'e', 'r'], [⟨['c', 'h', 'e'], ['B', '1', 'S', 'G'], none⟩, ⟨['r', 'y', 'v', 'y'], ['y', 'o', 'u', 'n', 'g', 'e', 'r', '.', 'b', 'r', 'o', 't', 'h', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "As in (18a), but now Marko also brings to the presentation a picture of a person that he shows to the class."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_19a : Datum :=
  { id := "tonhauseretal2013_19a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(19a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ha’e chokokue."
    glossedTokens := [("Ha’e", "PRON.S.3"), ("chokokue", "farmer")]
    glossedWords := [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['c', 'h', 'o', 'k', 'o', 'k', 'u', 'e'], ['f', 'a', 'r', 'm', 'e', 'r'], [⟨['c', 'h', 'o', 'k', 'o', 'k', 'u', 'e'], ['f', 'a', 'r', 'm', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "The children in a sociology class have to give presentations about their families. Marko is up first and he starts with:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "existence of referent"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_19b : Datum :=
  { id := "tonhauseretal2013_19b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(19b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Che-ru réra Juan. Ha’e chokokue."
    glossedTokens := [("Che-ru", "B1SG-father"), ("réra", "name"), ("Juan", "Juan"), ("Ha’e", "PRON.S.3"), ("chokokue", "farmer")]
    glossedWords := [⟨['C', 'h', 'e', '-', 'r', 'u'], ['B', '1', 'S', 'G', '-', 'f', 'a', 't', 'h', 'e', 'r'], [⟨['C', 'h', 'e'], ['B', '1', 'S', 'G'], none⟩, ⟨['r', 'u'], ['f', 'a', 't', 'h', 'e', 'r'], some '-'⟩]⟩, ⟨['r', 'é', 'r', 'a'], ['n', 'a', 'm', 'e'], [⟨['r', 'é', 'r', 'a'], ['n', 'a', 'm', 'e'], none⟩]⟩, ⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['c', 'h', 'o', 'k', 'o', 'k', 'u', 'e'], ['f', 'a', 'r', 'm', 'e', 'r'], [⟨['c', 'h', 'o', 'k', 'o', 'k', 'u', 'e'], ['f', 'a', 'r', 'm', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The children in a sociology class have to give presentations about their families. Marko is up first and he starts with:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "existence of referent"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_20a : Datum :=
  { id := "tonhauseretal2013_20a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(20a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "A-ha-va’erã a-me’ẽ-ha-guã che-rymba jaguá-pe hembi’u-rã."
    glossedTokens := [("A-ha-va’erã", "A1SG-go-MUST"), ("a-me’ẽ-ha-guã", "A1SG-give-NOM-PURP"), ("che-rymba", "B1SG-domesticated.animal"), ("jaguá-pe", "dog-at"), ("hembi’u-rã", "3.food-NOM.PROSP")]
    glossedWords := [⟨['A', '-', 'h', 'a', '-', 'v', 'a', '’', 'e', 'r', 'ã'], ['A', '1', 'S', 'G', '-', 'g', 'o', '-', 'M', 'U', 'S', 'T'], [⟨['A'], ['A', '1', 'S', 'G'], none⟩, ⟨['h', 'a'], ['g', 'o'], some '-'⟩, ⟨['v', 'a', '’', 'e', 'r', 'ã'], ['M', 'U', 'S', 'T'], some '-'⟩]⟩, ⟨['a', '-', 'm', 'e', '’', 'ẽ', '-', 'h', 'a', '-', 'g', 'u', 'ã'], ['A', '1', 'S', 'G', '-', 'g', 'i', 'v', 'e', '-', 'N', 'O', 'M', '-', 'P', 'U', 'R', 'P'], [⟨['a'], ['A', '1', 'S', 'G'], none⟩, ⟨['m', 'e', '’', 'ẽ'], ['g', 'i', 'v', 'e'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩, ⟨['g', 'u', 'ã'], ['P', 'U', 'R', 'P'], some '-'⟩]⟩, ⟨['c', 'h', 'e', '-', 'r', 'y', 'm', 'b', 'a'], ['B', '1', 'S', 'G', '-', 'd', 'o', 'm', 'e', 's', 't', 'i', 'c', 'a', 't', 'e', 'd', '.', 'a', 'n', 'i', 'm', 'a', 'l'], [⟨['c', 'h', 'e'], ['B', '1', 'S', 'G'], none⟩, ⟨['r', 'y', 'm', 'b', 'a'], ['d', 'o', 'm', 'e', 's', 't', 'i', 'c', 'a', 't', 'e', 'd', '.', 'a', 'n', 'i', 'm', 'a', 'l'], some '-'⟩]⟩, ⟨['j', 'a', 'g', 'u', 'á', '-', 'p', 'e'], ['d', 'o', 'g', '-', 'a', 't'], [⟨['j', 'a', 'g', 'u', 'á'], ['d', 'o', 'g'], none⟩, ⟨['p', 'e'], ['a', 't'], some '-'⟩]⟩, ⟨['h', 'e', 'm', 'b', 'i', '’', 'u', '-', 'r', 'ã'], ['3', '.', 'f', 'o', 'o', 'd', '-', 'N', 'O', 'M', '.', 'P', 'R', 'O', 'S', 'P'], [⟨['h', 'e', 'm', 'b', 'i', '’', 'u'], ['3', '.', 'f', 'o', 'o', 'd'], none⟩, ⟨['r', 'ã'], ['N', 'O', 'M', '.', 'P', 'R', 'O', 'S', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A woman who is being interviewed by a school director for a job as a teacher suddenly interrupts and says:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "possessive NP"), ("content", "possessive relation"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_20b : Datum :=
  { id := "tonhauseretal2013_20b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(20b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Nd-a-je-droga-vé-i-ma."
    glossedTokens := [("Nd-a-je-droga-vé-i-ma", "NEG-A1SG-JE-drug-more-NEG-already")]
    glossedWords := [⟨['N', 'd', '-', 'a', '-', 'j', 'e', '-', 'd', 'r', 'o', 'g', 'a', '-', 'v', 'é', '-', 'i', '-', 'm', 'a'], ['N', 'E', 'G', '-', 'A', '1', 'S', 'G', '-', 'J', 'E', '-', 'd', 'r', 'u', 'g', '-', 'm', 'o', 'r', 'e', '-', 'N', 'E', 'G', '-', 'a', 'l', 'r', 'e', 'a', 'd', 'y'], [⟨['N', 'd'], ['N', 'E', 'G'], none⟩, ⟨['a'], ['A', '1', 'S', 'G'], some '-'⟩, ⟨['j', 'e'], ['J', 'E'], some '-'⟩, ⟨['d', 'r', 'o', 'g', 'a'], ['d', 'r', 'u', 'g'], some '-'⟩, ⟨['v', 'é'], ['m', 'o', 'r', 'e'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩, ⟨['m', 'a'], ['a', 'l', 'r', 'e', 'a', 'd', 'y'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Laura, who doesn’t live with her parents, visits them and asks them to sit down with her because she has to tell them something:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "n(d)(a)-…-vé-i-ma ‘not anymore’"), ("content", "prestate holds"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_20c : Datum :=
  { id := "tonhauseretal2013_20c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(20c)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ha’e oi-kuaa o-moĩ-va’erã-ha i-lénte o-maneja-ha-guã."
    glossedTokens := [("Ha’e", "PRON.S.3"), ("oi-kuaa", "A3-know"), ("o-moĩ-va’erã-ha", "A3-put-MUST-NOM"), ("i-lénte", "3-glasses"), ("o-maneja-ha-guã", "A3-drive-NOM-PURP")]
    glossedWords := [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['o', 'i', '-', 'k', 'u', 'a', 'a'], ['A', '3', '-', 'k', 'n', 'o', 'w'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['k', 'u', 'a', 'a'], ['k', 'n', 'o', 'w'], some '-'⟩]⟩, ⟨['o', '-', 'm', 'o', 'ĩ', '-', 'v', 'a', '’', 'e', 'r', 'ã', '-', 'h', 'a'], ['A', '3', '-', 'p', 'u', 't', '-', 'M', 'U', 'S', 'T', '-', 'N', 'O', 'M'], [⟨['o'], ['A', '3'], none⟩, ⟨['m', 'o', 'ĩ'], ['p', 'u', 't'], some '-'⟩, ⟨['v', 'a', '’', 'e', 'r', 'ã'], ['M', 'U', 'S', 'T'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['i', '-', 'l', 'é', 'n', 't', 'e'], ['3', '-', 'g', 'l', 'a', 's', 's', 'e', 's'], [⟨['i'], ['3'], none⟩, ⟨['l', 'é', 'n', 't', 'e'], ['g', 'l', 'a', 's', 's', 'e', 's'], some '-'⟩]⟩, ⟨['o', '-', 'm', 'a', 'n', 'e', 'j', 'a', '-', 'h', 'a', '-', 'g', 'u', 'ã'], ['A', '3', '-', 'd', 'r', 'i', 'v', 'e', '-', 'N', 'O', 'M', '-', 'P', 'U', 'R', 'P'], [⟨['o'], ['A', '3'], none⟩, ⟨['m', 'a', 'n', 'e', 'j', 'a'], ['d', 'r', 'i', 'v', 'e'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩, ⟨['g', 'u', 'ã'], ['P', 'U', 'R', 'P'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "A girl backs out of a driveway and hits Susi’s car. A woman comes running out of the house, apologizes that her daughter hit Susi’s car, and says:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "(oi)kuaa ‘know’"), ("content", "content of complement"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_22a : Datum :=
  { id := "tonhauseretal2013_22a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(22a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ko mburuvicha Fransia-gua oi-ko Lóndre-pe."
    glossedTokens := [("Ko", "this"), ("mburuvicha", "boss"), ("Fransia-gua", "France-from"), ("oi-ko", "A3-live"), ("Lóndre-pe", "London-in")]
    glossedWords := [⟨['K', 'o'], ['t', 'h', 'i', 's'], [⟨['K', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['F', 'r', 'a', 'n', 's', 'i', 'a', '-', 'g', 'u', 'a'], ['F', 'r', 'a', 'n', 'c', 'e', '-', 'f', 'r', 'o', 'm'], [⟨['F', 'r', 'a', 'n', 's', 'i', 'a'], ['F', 'r', 'a', 'n', 'c', 'e'], none⟩, ⟨['g', 'u', 'a'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['o', 'i', '-', 'k', 'o'], ['A', '3', '-', 'l', 'i', 'v', 'e'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['k', 'o'], ['l', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['L', 'ó', 'n', 'd', 'r', 'e', '-', 'p', 'e'], ['L', 'o', 'n', 'd', 'o', 'n', '-', 'i', 'n'], [⟨['L', 'ó', 'n', 'd', 'r', 'e'], ['L', 'o', 'n', 'd', 'o', 'n'], none⟩, ⟨['p', 'e'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "projection"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_22b : Datum :=
  { id := "tonhauseretal2013_22b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(22b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ko mburuvicha Fransia-gua nd-oi-kó-i Lóndre-pe."
    glossedTokens := [("Ko", "this"), ("mburuvicha", "boss"), ("Fransia-gua", "France-from"), ("nd-oi-kó-i", "NEG-A3-live-NEG"), ("Lóndre-pe", "London-in")]
    glossedWords := [⟨['K', 'o'], ['t', 'h', 'i', 's'], [⟨['K', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['F', 'r', 'a', 'n', 's', 'i', 'a', '-', 'g', 'u', 'a'], ['F', 'r', 'a', 'n', 'c', 'e', '-', 'f', 'r', 'o', 'm'], [⟨['F', 'r', 'a', 'n', 's', 'i', 'a'], ['F', 'r', 'a', 'n', 'c', 'e'], none⟩, ⟨['g', 'u', 'a'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩, ⟨['n', 'd', '-', 'o', 'i', '-', 'k', 'ó', '-', 'i'], ['N', 'E', 'G', '-', 'A', '3', '-', 'l', 'i', 'v', 'e', '-', 'N', 'E', 'G'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o', 'i'], ['A', '3'], some '-'⟩, ⟨['k', 'ó'], ['l', 'i', 'v', 'e'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['L', 'ó', 'n', 'd', 'r', 'e', '-', 'p', 'e'], ['L', 'o', 'n', 'd', 'o', 'n', '-', 'i', 'n'], [⟨['L', 'ó', 'n', 'd', 'r', 'e'], ['L', 'o', 'n', 'd', 'o', 'n'], none⟩, ⟨['p', 'e'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "projection"), ("environment", "negation"), ("context", "m-neutral")] }

def ex_30a : Datum :=
  { id := "tonhauseretal2013_30a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    glossedWords := [⟨['Ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['Ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩, ⟨['o', '-', 'k', 'a', 'r', 'u'], ['A', '3', '-', 'e', 'a', 't'], [⟨['o'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'u'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_30b : Datum :=
  { id := "tonhauseretal2013_30b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "I-katu o-karu empanáda avei ñande-chofeur."
    glossedTokens := [("I-katu", "B3-possible"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    glossedWords := [⟨['I', '-', 'k', 'a', 't', 'u'], ['B', '3', '-', 'p', 'o', 's', 's', 'i', 'b', 'l', 'e'], [⟨['I'], ['B', '3'], none⟩, ⟨['k', 'a', 't', 'u'], ['p', 'o', 's', 's', 'i', 'b', 'l', 'e'], some '-'⟩]⟩, ⟨['o', '-', 'k', 'a', 'r', 'u'], ['A', '3', '-', 'e', 'a', 't'], [⟨['o'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'u'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("context", "m-neutral")] }

def ex_30c : Datum :=
  { id := "tonhauseretal2013_30c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30c)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-ramo empanáda avei ñande-chofeur, a-sẽ-ta kolektívo-gui."
    glossedTokens := [("O-karú-ramo", "A3-eat-if"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver"), ("a-sẽ-ta", "A1SG-leave-PROSP"), ("kolektívo-gui", "bus-from")]
    glossedWords := [⟨['O', '-', 'k', 'a', 'r', 'ú', '-', 'r', 'a', 'm', 'o'], ['A', '3', '-', 'e', 'a', 't', '-', 'i', 'f'], [⟨['O'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'ú'], ['e', 'a', 't'], some '-'⟩, ⟨['r', 'a', 'm', 'o'], ['i', 'f'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩, ⟨['a', '-', 's', 'ẽ', '-', 't', 'a'], ['A', '1', 'S', 'G', '-', 'l', 'e', 'a', 'v', 'e', '-', 'P', 'R', 'O', 'S', 'P'], [⟨['a'], ['A', '1', 'S', 'G'], none⟩, ⟨['s', 'ẽ'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩, ⟨['t', 'a'], ['P', 'R', 'O', 'S', 'P'], some '-'⟩]⟩, ⟨['k', 'o', 'l', 'e', 'k', 't', 'í', 'v', 'o', '-', 'g', 'u', 'i'], ['b', 'u', 's', '-', 'f', 'r', 'o', 'm'], [⟨['k', 'o', 'l', 'e', 'k', 't', 'í', 'v', 'o'], ['b', 'u', 's'], none⟩, ⟨['g', 'u', 'i'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("context", "m-neutral")] }

def ex_30d : Datum :=
  { id := "tonhauseretal2013_30d"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30d)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-pa empanada avei ñande-chofeur?"
    glossedTokens := [("O-karú-pa", "A3-eat-Q"), ("empanada", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    glossedWords := [⟨['O', '-', 'k', 'a', 'r', 'ú', '-', 'p', 'a'], ['A', '3', '-', 'e', 'a', 't', '-', 'Q'], [⟨['O'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'ú'], ['e', 'a', 't'], some '-'⟩, ⟨['p', 'a'], ['Q'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "question"), ("context", "m-neutral")] }

def ex_31_30a : Datum :=
  { id := "tonhauseretal2013_31_30a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    glossedWords := [⟨['Ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['Ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩, ⟨['o', '-', 'k', 'a', 'r', 'u'], ['A', '3', '-', 'e', 'a', 't'], [⟨['o'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'u'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_31_30b : Datum :=
  { id := "tonhauseretal2013_31_30b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "I-katu o-karu empanáda avei ñande-chofeur."
    glossedTokens := [("I-katu", "B3-possible"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    glossedWords := [⟨['I', '-', 'k', 'a', 't', 'u'], ['B', '3', '-', 'p', 'o', 's', 's', 'i', 'b', 'l', 'e'], [⟨['I'], ['B', '3'], none⟩, ⟨['k', 'a', 't', 'u'], ['p', 'o', 's', 's', 'i', 'b', 'l', 'e'], some '-'⟩]⟩, ⟨['o', '-', 'k', 'a', 'r', 'u'], ['A', '3', '-', 'e', 'a', 't'], [⟨['o'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'u'], ['e', 'a', 't'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("context", "m-positive")] }

def ex_31_30c : Datum :=
  { id := "tonhauseretal2013_31_30c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-ramo empanáda avei ñande-chofeur, a-sẽ-ta kolektívo-gui."
    glossedTokens := [("O-karú-ramo", "A3-eat-if"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver"), ("a-sẽ-ta", "A1SG-leave-PROSP"), ("kolektívo-gui", "bus-from")]
    glossedWords := [⟨['O', '-', 'k', 'a', 'r', 'ú', '-', 'r', 'a', 'm', 'o'], ['A', '3', '-', 'e', 'a', 't', '-', 'i', 'f'], [⟨['O'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'ú'], ['e', 'a', 't'], some '-'⟩, ⟨['r', 'a', 'm', 'o'], ['i', 'f'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'á', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩, ⟨['a', '-', 's', 'ẽ', '-', 't', 'a'], ['A', '1', 'S', 'G', '-', 'l', 'e', 'a', 'v', 'e', '-', 'P', 'R', 'O', 'S', 'P'], [⟨['a'], ['A', '1', 'S', 'G'], none⟩, ⟨['s', 'ẽ'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩, ⟨['t', 'a'], ['P', 'R', 'O', 'S', 'P'], some '-'⟩]⟩, ⟨['k', 'o', 'l', 'e', 'k', 't', 'í', 'v', 'o', '-', 'g', 'u', 'i'], ['b', 'u', 's', '-', 'f', 'r', 'o', 'm'], [⟨['k', 'o', 'l', 'e', 'k', 't', 'í', 'v', 'o'], ['b', 'u', 's'], none⟩, ⟨['g', 'u', 'i'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("context", "m-positive")] }

def ex_31_30d : Datum :=
  { id := "tonhauseretal2013_31_30d"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-pa empanada avei ñande-chofeur?"
    glossedTokens := [("O-karú-pa", "A3-eat-Q"), ("empanada", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    glossedWords := [⟨['O', '-', 'k', 'a', 'r', 'ú', '-', 'p', 'a'], ['A', '3', '-', 'e', 'a', 't', '-', 'Q'], [⟨['O'], ['A', '3'], none⟩, ⟨['k', 'a', 'r', 'ú'], ['e', 'a', 't'], some '-'⟩, ⟨['p', 'a'], ['Q'], some '-'⟩]⟩, ⟨['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], [⟨['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], ['e', 'm', 'p', 'a', 'n', 'a', 'd', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['ñ', 'a', 'n', 'd', 'e', '-', 'c', 'h', 'o', 'f', 'e', 'u', 'r'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L', '-', 'd', 'r', 'i', 'v', 'e', 'r'], [⟨['ñ', 'a', 'n', 'd', 'e'], ['A', '1', 'P', 'L', '.', 'I', 'N', 'C', 'L'], none⟩, ⟨['c', 'h', 'o', 'f', 'e', 'u', 'r'], ['d', 'r', 'i', 'v', 'e', 'r'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "question"), ("context", "m-positive")] }

def ex_38a : Datum :=
  { id := "tonhauseretal2013_38a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane believes that Bill has stopped smoking (although he’s actually never been a smoker)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "stop"), ("content", "prestate holds"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-positive")] }

def ex_38b : Datum :=
  { id := "tonhauseretal2013_38b"
    source := ⟨"amaral-roberts-smith-2007", "pp. 735f."⟩
    reportedIn := some ⟨"tonhauser-beaver-roberts-simons-2013", "(38b)"⟩
    language := "stan1293"
    primaryText := "Joan is crazy. She’s hallucinating that some geniuses in Silicon Valley have invented a new brain chip that’s been installed in her left temporal lobe and permits her to speak any of a number of languages she’s never studied. Joan believes that her chip, which she had installed last month, has a twelve year guarantee."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-positive")] }

def ex_39a : Datum :=
  { id := "tonhauseretal2013_39a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane believes that Bill has stopped smoking and that he has never been a smoker."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "stop"), ("content", "prestate holds"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_39b : Datum :=
  { id := "tonhauseretal2013_39b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane believes that Bill, who is Sue’s cousin, is Sue’s brother."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_46a : Datum :=
  { id := "tonhauseretal2013_46a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(46a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Raul o-va Buénos Áires-pe, há=katu Juan nd-oi-kuáa-i. Ha’e oi-mo’ã Maléna avei o-va-ha Buénos Áires-pe."
    glossedTokens := [("Raul", "Raul"), ("o-va", "A3-move"), ("Buénos", "Buenos"), ("Áires-pe", "Aires-to"), ("há=katu", "and=CONTR"), ("Juan", "Juan"), ("nd-oi-kuáa-i", "NEG-A3-know-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("Maléna", "Malena"), ("avei", "too"), ("o-va-ha", "A3-move-NOM"), ("Buénos", "Buenos"), ("Áires-pe", "Aires-to")]
    glossedWords := [⟨['R', 'a', 'u', 'l'], ['R', 'a', 'u', 'l'], [⟨['R', 'a', 'u', 'l'], ['R', 'a', 'u', 'l'], none⟩]⟩, ⟨['o', '-', 'v', 'a'], ['A', '3', '-', 'm', 'o', 'v', 'e'], [⟨['o'], ['A', '3'], none⟩, ⟨['v', 'a'], ['m', 'o', 'v', 'e'], some '-'⟩]⟩, ⟨['B', 'u', 'é', 'n', 'o', 's'], ['B', 'u', 'e', 'n', 'o', 's'], [⟨['B', 'u', 'é', 'n', 'o', 's'], ['B', 'u', 'e', 'n', 'o', 's'], none⟩]⟩, ⟨['Á', 'i', 'r', 'e', 's', '-', 'p', 'e'], ['A', 'i', 'r', 'e', 's', '-', 't', 'o'], [⟨['Á', 'i', 'r', 'e', 's'], ['A', 'i', 'r', 'e', 's'], none⟩, ⟨['p', 'e'], ['t', 'o'], some '-'⟩]⟩, ⟨['h', 'á', '=', 'k', 'a', 't', 'u'], ['a', 'n', 'd', '=', 'C', 'O', 'N', 'T', 'R'], [⟨['h', 'á'], ['a', 'n', 'd'], none⟩, ⟨['k', 'a', 't', 'u'], ['C', 'O', 'N', 'T', 'R'], some '='⟩]⟩, ⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['n', 'd', '-', 'o', 'i', '-', 'k', 'u', 'á', 'a', '-', 'i'], ['N', 'E', 'G', '-', 'A', '3', '-', 'k', 'n', 'o', 'w', '-', 'N', 'E', 'G'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o', 'i'], ['A', '3'], some '-'⟩, ⟨['k', 'u', 'á', 'a'], ['k', 'n', 'o', 'w'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['o', '-', 'v', 'a', '-', 'h', 'a'], ['A', '3', '-', 'm', 'o', 'v', 'e', '-', 'N', 'O', 'M'], [⟨['o'], ['A', '3'], none⟩, ⟨['v', 'a'], ['m', 'o', 'v', 'e'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['B', 'u', 'é', 'n', 'o', 's'], ['B', 'u', 'e', 'n', 'o', 's'], [⟨['B', 'u', 'é', 'n', 'o', 's'], ['B', 'u', 'e', 'n', 'o', 's'], none⟩]⟩, ⟨['Á', 'i', 'r', 'e', 's', '-', 'p', 'e'], ['A', 'i', 'r', 'e', 's', '-', 't', 'o'], [⟨['Á', 'i', 'r', 'e', 's'], ['A', 'i', 'r', 'e', 's'], none⟩, ⟨['p', 'e'], ['t', 'o'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def ex_46b : Datum :=
  { id := "tonhauseretal2013_46b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(46b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "para1311"
    primaryText := "E-ma’ẽ-mi! Upépe o-ĩ peteĩ kuimba’e. Maléna nd-o-hechá-i. Ha’e oi-mo’ã ha’e hasy-ha."
    glossedTokens := [("E-ma’ẽ-mi", "A2SG-look-DIM"), ("Upépe", "there"), ("o-ĩ", "A3-be"), ("peteĩ", "one"), ("kuimba’e", "man"), ("Maléna", "Malena"), ("nd-o-hechá-i", "NEG-A3-see-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("ha’e", "PRON.S.3"), ("hasy-ha", "B3.sick-NOM")]
    glossedWords := [⟨['E', '-', 'm', 'a', '’', 'ẽ', '-', 'm', 'i'], ['A', '2', 'S', 'G', '-', 'l', 'o', 'o', 'k', '-', 'D', 'I', 'M'], [⟨['E'], ['A', '2', 'S', 'G'], none⟩, ⟨['m', 'a', '’', 'ẽ'], ['l', 'o', 'o', 'k'], some '-'⟩, ⟨['m', 'i'], ['D', 'I', 'M'], some '-'⟩]⟩, ⟨['U', 'p', 'é', 'p', 'e'], ['t', 'h', 'e', 'r', 'e'], [⟨['U', 'p', 'é', 'p', 'e'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['o', '-', 'ĩ'], ['A', '3', '-', 'b', 'e'], [⟨['o'], ['A', '3'], none⟩, ⟨['ĩ'], ['b', 'e'], some '-'⟩]⟩, ⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], [⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], [⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], none⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['n', 'd', '-', 'o', '-', 'h', 'e', 'c', 'h', 'á', '-', 'i'], ['N', 'E', 'G', '-', 'A', '3', '-', 's', 'e', 'e', '-', 'N', 'E', 'G'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o'], ['A', '3'], some '-'⟩, ⟨['h', 'e', 'c', 'h', 'á'], ['s', 'e', 'e'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['h', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['h', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['h', 'a', 's', 'y', '-', 'h', 'a'], ['B', '3', '.', 's', 'i', 'c', 'k', '-', 'N', 'O', 'M'], [⟨['h', 'a', 's', 'y'], ['B', '3', '.', 's', 'i', 'c', 'k'], none⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker, Ricardo, and Malena are lost in a city they’ve never visited before. The speaker, who, together with Ricardo, is a bit ahead of Malena, says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "existence of referent"), ("class", "A"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def ex_47a : Datum :=
  { id := "tonhauseretal2013_47a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(47a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Juan oi-mo’ã Maléna aimete o-pe-ha hetyma ha oi-mo’ã avei Maléna o-pe-ha hetyma."
    glossedTokens := [("Juan", "Juan"), ("oi-mo’ã", "A3-think"), ("Maléna", "Malena"), ("aimete", "almost"), ("o-pe-ha", "A3-break-NOM"), ("hetyma", "B3.leg"), ("ha", "and"), ("oi-mo’ã", "A3-think"), ("avei", "also"), ("Maléna", "Malena"), ("o-pe-ha", "A3-break-NOM"), ("hetyma", "B3.leg")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['a', 'i', 'm', 'e', 't', 'e'], ['a', 'l', 'm', 'o', 's', 't'], [⟨['a', 'i', 'm', 'e', 't', 'e'], ['a', 'l', 'm', 'o', 's', 't'], none⟩]⟩, ⟨['o', '-', 'p', 'e', '-', 'h', 'a'], ['A', '3', '-', 'b', 'r', 'e', 'a', 'k', '-', 'N', 'O', 'M'], [⟨['o'], ['A', '3'], none⟩, ⟨['p', 'e'], ['b', 'r', 'e', 'a', 'k'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], [⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], none⟩]⟩, ⟨['h', 'a'], ['a', 'n', 'd'], [⟨['h', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['a', 'l', 's', 'o'], [⟨['a', 'v', 'e', 'i'], ['a', 'l', 's', 'o'], none⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['o', '-', 'p', 'e', '-', 'h', 'a'], ['A', '3', '-', 'b', 'r', 'e', 'a', 'k', '-', 'N', 'O', 'M'], [⟨['o'], ['A', '3'], none⟩, ⟨['p', 'e'], ['b', 'r', 'e', 'a', 'k'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], [⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Juan is a doctor at the scene of an accident. His friend says about him:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "aimete ‘almost’"), ("content", "polar implication"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_47b : Datum :=
  { id := "tonhauseretal2013_47b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(47b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Juan oi-mo’ã Maléna-nte o-pe-ha hetyma ha oi-mo’ã avei Maléna nd-o-pe-i-ha hetyma."
    glossedTokens := [("Juan", "Juan"), ("oi-mo’ã", "A3-think"), ("Maléna-nte", "Malena-only"), ("o-pe-ha", "A3-break-NOM"), ("hetyma", "B3.leg"), ("ha", "and"), ("oi-mo’ã", "A3-think"), ("avei", "too"), ("Maléna", "Malena"), ("nd-o-pe-i-ha", "NEG-A3-break-NEG-NOM"), ("hetyma", "B3.leg")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a', '-', 'n', 't', 'e'], ['M', 'a', 'l', 'e', 'n', 'a', '-', 'o', 'n', 'l', 'y'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩, ⟨['n', 't', 'e'], ['o', 'n', 'l', 'y'], some '-'⟩]⟩, ⟨['o', '-', 'p', 'e', '-', 'h', 'a'], ['A', '3', '-', 'b', 'r', 'e', 'a', 'k', '-', 'N', 'O', 'M'], [⟨['o'], ['A', '3'], none⟩, ⟨['p', 'e'], ['b', 'r', 'e', 'a', 'k'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], [⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], none⟩]⟩, ⟨['h', 'a'], ['a', 'n', 'd'], [⟨['h', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['n', 'd', '-', 'o', '-', 'p', 'e', '-', 'i', '-', 'h', 'a'], ['N', 'E', 'G', '-', 'A', '3', '-', 'b', 'r', 'e', 'a', 'k', '-', 'N', 'E', 'G', '-', 'N', 'O', 'M'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o'], ['A', '3'], some '-'⟩, ⟨['p', 'e'], ['b', 'r', 'e', 'a', 'k'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], [⟨['h', 'e', 't', 'y', 'm', 'a'], ['B', '3', '.', 'l', 'e', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Juan is a doctor at the scene of an accident. His friend says about him:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "-nte ‘only’"), ("content", "prejacent implication"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_48 : Datum :=
  { id := "tonhauseretal2013_48"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(48)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ángel oi-mo’ã i-túva oi-kuaa-ha iñ-ermána o-guereko kichiha ha Ángel oi-mo’ã avei iñ-ermána nd-o-guerekó-i-ha kichiha."
    glossedTokens := [("Ángel", "Angel"), ("oi-mo’ã", "A3-think"), ("i-túva", "B3-father"), ("oi-kuaa-ha", "A3-know-NOM"), ("iñ-ermána", "B3-sister"), ("o-guereko", "A3-have"), ("kichiha", "boyfriend"), ("ha", "and"), ("Ángel", "Angel"), ("oi-mo’ã", "A3-think"), ("avei", "too"), ("iñ-ermána", "B3-sister"), ("nd-o-guerekó-i-ha", "NEG-A3-have-NEG-NOM"), ("kichiha", "boyfriend")]
    glossedWords := [⟨['Á', 'n', 'g', 'e', 'l'], ['A', 'n', 'g', 'e', 'l'], [⟨['Á', 'n', 'g', 'e', 'l'], ['A', 'n', 'g', 'e', 'l'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['i', '-', 't', 'ú', 'v', 'a'], ['B', '3', '-', 'f', 'a', 't', 'h', 'e', 'r'], [⟨['i'], ['B', '3'], none⟩, ⟨['t', 'ú', 'v', 'a'], ['f', 'a', 't', 'h', 'e', 'r'], some '-'⟩]⟩, ⟨['o', 'i', '-', 'k', 'u', 'a', 'a', '-', 'h', 'a'], ['A', '3', '-', 'k', 'n', 'o', 'w', '-', 'N', 'O', 'M'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['k', 'u', 'a', 'a'], ['k', 'n', 'o', 'w'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['i', 'ñ', '-', 'e', 'r', 'm', 'á', 'n', 'a'], ['B', '3', '-', 's', 'i', 's', 't', 'e', 'r'], [⟨['i', 'ñ'], ['B', '3'], none⟩, ⟨['e', 'r', 'm', 'á', 'n', 'a'], ['s', 'i', 's', 't', 'e', 'r'], some '-'⟩]⟩, ⟨['o', '-', 'g', 'u', 'e', 'r', 'e', 'k', 'o'], ['A', '3', '-', 'h', 'a', 'v', 'e'], [⟨['o'], ['A', '3'], none⟩, ⟨['g', 'u', 'e', 'r', 'e', 'k', 'o'], ['h', 'a', 'v', 'e'], some '-'⟩]⟩, ⟨['k', 'i', 'c', 'h', 'i', 'h', 'a'], ['b', 'o', 'y', 'f', 'r', 'i', 'e', 'n', 'd'], [⟨['k', 'i', 'c', 'h', 'i', 'h', 'a'], ['b', 'o', 'y', 'f', 'r', 'i', 'e', 'n', 'd'], none⟩]⟩, ⟨['h', 'a'], ['a', 'n', 'd'], [⟨['h', 'a'], ['a', 'n', 'd'], none⟩]⟩, ⟨['Á', 'n', 'g', 'e', 'l'], ['A', 'n', 'g', 'e', 'l'], [⟨['Á', 'n', 'g', 'e', 'l'], ['A', 'n', 'g', 'e', 'l'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], [⟨['a', 'v', 'e', 'i'], ['t', 'o', 'o'], none⟩]⟩, ⟨['i', 'ñ', '-', 'e', 'r', 'm', 'á', 'n', 'a'], ['B', '3', '-', 's', 'i', 's', 't', 'e', 'r'], [⟨['i', 'ñ'], ['B', '3'], none⟩, ⟨['e', 'r', 'm', 'á', 'n', 'a'], ['s', 'i', 's', 't', 'e', 'r'], some '-'⟩]⟩, ⟨['n', 'd', '-', 'o', '-', 'g', 'u', 'e', 'r', 'e', 'k', 'ó', '-', 'i', '-', 'h', 'a'], ['N', 'E', 'G', '-', 'A', '3', '-', 'h', 'a', 'v', 'e', '-', 'N', 'E', 'G', '-', 'N', 'O', 'M'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o'], ['A', '3'], some '-'⟩, ⟨['g', 'u', 'e', 'r', 'e', 'k', 'ó'], ['h', 'a', 'v', 'e'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['k', 'i', 'c', 'h', 'i', 'h', 'a'], ['b', 'o', 'y', 'f', 'r', 'i', 'e', 'n', 'd'], [⟨['k', 'i', 'c', 'h', 'i', 'h', 'a'], ['b', 'o', 'y', 'f', 'r', 'i', 'e', 'n', 'd'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "(oi)kuaa ‘know’"), ("content", "content of complement"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_49 : Datum :=
  { id := "tonhauseretal2013_49"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(49)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Juan oi-mo’ã Angéla Mérkel, Alemánia mburuvicha, ha’e-ha Argentína mburuvicha."
    glossedTokens := [("Juan", "Juan"), ("oi-mo’ã", "A3-think"), ("Angéla", "Angela"), ("Mérkel", "Merkel"), ("Alemánia", "Germany"), ("mburuvicha", "boss"), ("ha’e-ha", "PRON.S.3-NOM"), ("Argentína", "Argentina"), ("mburuvicha", "boss")]
    glossedWords := [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], [⟨['J', 'u', 'a', 'n'], ['J', 'u', 'a', 'n'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['A', 'n', 'g', 'é', 'l', 'a'], ['A', 'n', 'g', 'e', 'l', 'a'], [⟨['A', 'n', 'g', 'é', 'l', 'a'], ['A', 'n', 'g', 'e', 'l', 'a'], none⟩]⟩, ⟨['M', 'é', 'r', 'k', 'e', 'l'], ['M', 'e', 'r', 'k', 'e', 'l'], [⟨['M', 'é', 'r', 'k', 'e', 'l'], ['M', 'e', 'r', 'k', 'e', 'l'], none⟩]⟩, ⟨['A', 'l', 'e', 'm', 'á', 'n', 'i', 'a'], ['G', 'e', 'r', 'm', 'a', 'n', 'y'], [⟨['A', 'l', 'e', 'm', 'á', 'n', 'i', 'a'], ['G', 'e', 'r', 'm', 'a', 'n', 'y'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['h', 'a', '’', 'e', '-', 'h', 'a'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3', '-', 'N', 'O', 'M'], [⟨['h', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['A', 'r', 'g', 'e', 'n', 't', 'í', 'n', 'a'], ['A', 'r', 'g', 'e', 'n', 't', 'i', 'n', 'a'], [⟨['A', 'r', 'g', 'e', 'n', 't', 'í', 'n', 'a'], ['A', 'r', 'g', 'e', 'n', 't', 'i', 'n', 'a'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Sabine is from Germany and knows the politicians there very well. Angela Merkel, the chancellor of Germany, is currently visiting farmers in Paraguay, among them Juan. Sabine says:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "appositive"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_50a : Datum :=
  { id := "tonhauseretal2013_50a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(50a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "E-ma’ẽ-mi! Upépe o-ĩ peteĩ kuimba’e, há=katu Maléna nd-oi-kuáa-i. Ha’e oi-mo’ã ha’e-ha peteĩ ta’anga ita-guí-gua."
    glossedTokens := [("E-ma’ẽ-mi", "A2SG-look-DIM"), ("Upépe", "there"), ("o-ĩ", "A3-be"), ("peteĩ", "one"), ("kuimba’e", "man"), ("há=katu", "and=CONTR"), ("Maléna", "Malena"), ("nd-oi-kuáa-i", "NEG-A3-know-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("ha’e-ha", "PRON.S.3-NOM"), ("peteĩ", "one"), ("ta’anga", "figure"), ("ita-guí-gua", "stone-of-from")]
    glossedWords := [⟨['E', '-', 'm', 'a', '’', 'ẽ', '-', 'm', 'i'], ['A', '2', 'S', 'G', '-', 'l', 'o', 'o', 'k', '-', 'D', 'I', 'M'], [⟨['E'], ['A', '2', 'S', 'G'], none⟩, ⟨['m', 'a', '’', 'ẽ'], ['l', 'o', 'o', 'k'], some '-'⟩, ⟨['m', 'i'], ['D', 'I', 'M'], some '-'⟩]⟩, ⟨['U', 'p', 'é', 'p', 'e'], ['t', 'h', 'e', 'r', 'e'], [⟨['U', 'p', 'é', 'p', 'e'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['o', '-', 'ĩ'], ['A', '3', '-', 'b', 'e'], [⟨['o'], ['A', '3'], none⟩, ⟨['ĩ'], ['b', 'e'], some '-'⟩]⟩, ⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], [⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], none⟩]⟩, ⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], [⟨['k', 'u', 'i', 'm', 'b', 'a', '’', 'e'], ['m', 'a', 'n'], none⟩]⟩, ⟨['h', 'á', '=', 'k', 'a', 't', 'u'], ['a', 'n', 'd', '=', 'C', 'O', 'N', 'T', 'R'], [⟨['h', 'á'], ['a', 'n', 'd'], none⟩, ⟨['k', 'a', 't', 'u'], ['C', 'O', 'N', 'T', 'R'], some '='⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['n', 'd', '-', 'o', 'i', '-', 'k', 'u', 'á', 'a', '-', 'i'], ['N', 'E', 'G', '-', 'A', '3', '-', 'k', 'n', 'o', 'w', '-', 'N', 'E', 'G'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o', 'i'], ['A', '3'], some '-'⟩, ⟨['k', 'u', 'á', 'a'], ['k', 'n', 'o', 'w'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['h', 'a', '’', 'e', '-', 'h', 'a'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3', '-', 'N', 'O', 'M'], [⟨['h', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], [⟨['p', 'e', 't', 'e', 'ĩ'], ['o', 'n', 'e'], none⟩]⟩, ⟨['t', 'a', '’', 'a', 'n', 'g', 'a'], ['f', 'i', 'g', 'u', 'r', 'e'], [⟨['t', 'a', '’', 'a', 'n', 'g', 'a'], ['f', 'i', 'g', 'u', 'r', 'e'], none⟩]⟩, ⟨['i', 't', 'a', '-', 'g', 'u', 'í', '-', 'g', 'u', 'a'], ['s', 't', 'o', 'n', 'e', '-', 'o', 'f', '-', 'f', 'r', 'o', 'm'], [⟨['i', 't', 'a'], ['s', 't', 'o', 'n', 'e'], none⟩, ⟨['g', 'u', 'í'], ['o', 'f'], some '-'⟩, ⟨['g', 'u', 'a'], ['f', 'r', 'o', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker, Ricardo, and Malena are lost and looking for somebody to ask for directions. The speaker, who is walking ahead with Ricardo, says:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "human referent"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_51 : Datum :=
  { id := "tonhauseretal2013_51"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(51)"⟩
    reportedIn := none
    method := some .elicitation
    language := "para1311"
    primaryText := "Brian oi-mo’ã Carmen jagua i-ñaro-ha."
    glossedTokens := [("Brian", "Brian"), ("oi-mo’ã", "A3-think"), ("Carmen", "Carmen"), ("jagua", "dog"), ("i-ñaro-ha", "B3-fierce-NOM")]
    glossedWords := [⟨['B', 'r', 'i', 'a', 'n'], ['B', 'r', 'i', 'a', 'n'], [⟨['B', 'r', 'i', 'a', 'n'], ['B', 'r', 'i', 'a', 'n'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['C', 'a', 'r', 'm', 'e', 'n'], ['C', 'a', 'r', 'm', 'e', 'n'], [⟨['C', 'a', 'r', 'm', 'e', 'n'], ['C', 'a', 'r', 'm', 'e', 'n'], none⟩]⟩, ⟨['j', 'a', 'g', 'u', 'a'], ['d', 'o', 'g'], [⟨['j', 'a', 'g', 'u', 'a'], ['d', 'o', 'g'], none⟩]⟩, ⟨['i', '-', 'ñ', 'a', 'r', 'o', '-', 'h', 'a'], ['B', '3', '-', 'f', 'i', 'e', 'r', 'c', 'e', '-', 'N', 'O', 'M'], [⟨['i'], ['B', '3'], none⟩, ⟨['ñ', 'a', 'r', 'o'], ['f', 'i', 'e', 'r', 'c', 'e'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Brian and Pedro are strolling down the street. They see a dog chasing a cat. Brian comments to Pedro that the dog looks fierce. Pedro knows that the dog is Carmen’s, but Brian doesn’t know that. Pedro later says to his wife:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "possessive NP"), ("content", "possessive relation"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-neutral")] }

def ex_52_property : Datum :=
  { id := "tonhauseretal2013_52_property"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(52)"⟩
    reportedIn := none
    method := some .elicitation
    language := "para1311"
    primaryText := "Raul mburuvicha há=katu Maléna nd-oi-kuáa-i. Ha’e oi-mo’ã ko mburuvicha pa’i-ha."
    glossedTokens := [("Raul", "Raul"), ("mburuvicha", "boss"), ("há=katu", "and=CONTR"), ("Maléna", "Malena"), ("nd-oi-kuáa-i", "NEG-A3-know-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("ko", "this"), ("mburuvicha", "boss"), ("pa’i-ha", "priest-NOM")]
    glossedWords := [⟨['R', 'a', 'u', 'l'], ['R', 'a', 'u', 'l'], [⟨['R', 'a', 'u', 'l'], ['R', 'a', 'u', 'l'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['h', 'á', '=', 'k', 'a', 't', 'u'], ['a', 'n', 'd', '=', 'C', 'O', 'N', 'T', 'R'], [⟨['h', 'á'], ['a', 'n', 'd'], none⟩, ⟨['k', 'a', 't', 'u'], ['C', 'O', 'N', 'T', 'R'], some '='⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['n', 'd', '-', 'o', 'i', '-', 'k', 'u', 'á', 'a', '-', 'i'], ['N', 'E', 'G', '-', 'A', '3', '-', 'k', 'n', 'o', 'w', '-', 'N', 'E', 'G'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o', 'i'], ['A', '3'], some '-'⟩, ⟨['k', 'u', 'á', 'a'], ['k', 'n', 'o', 'w'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['k', 'o'], ['t', 'h', 'i', 's'], [⟨['k', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['p', 'a', '’', 'i', '-', 'h', 'a'], ['p', 'r', 'i', 'e', 's', 't', '-', 'N', 'O', 'M'], [⟨['p', 'a', '’', 'i'], ['p', 'r', 'i', 'e', 's', 't'], none⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker and her addressee are at a reception, with Raul standing at the next table. Malena is not present."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "property attribution"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-neutral")] }

def ex_52_indication : Datum :=
  { id := "tonhauseretal2013_52_indication"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(52)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Raul mburuvicha há=katu Maléna nd-oi-kuáa-i. Ha’e oi-mo’ã ko mburuvicha pa’i-ha."
    glossedTokens := [("Raul", "Raul"), ("mburuvicha", "boss"), ("há=katu", "and=CONTR"), ("Maléna", "Malena"), ("nd-oi-kuáa-i", "NEG-A3-know-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("ko", "this"), ("mburuvicha", "boss"), ("pa’i-ha", "priest-NOM")]
    glossedWords := [⟨['R', 'a', 'u', 'l'], ['R', 'a', 'u', 'l'], [⟨['R', 'a', 'u', 'l'], ['R', 'a', 'u', 'l'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['h', 'á', '=', 'k', 'a', 't', 'u'], ['a', 'n', 'd', '=', 'C', 'O', 'N', 'T', 'R'], [⟨['h', 'á'], ['a', 'n', 'd'], none⟩, ⟨['k', 'a', 't', 'u'], ['C', 'O', 'N', 'T', 'R'], some '='⟩]⟩, ⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], [⟨['M', 'a', 'l', 'é', 'n', 'a'], ['M', 'a', 'l', 'e', 'n', 'a'], none⟩]⟩, ⟨['n', 'd', '-', 'o', 'i', '-', 'k', 'u', 'á', 'a', '-', 'i'], ['N', 'E', 'G', '-', 'A', '3', '-', 'k', 'n', 'o', 'w', '-', 'N', 'E', 'G'], [⟨['n', 'd'], ['N', 'E', 'G'], none⟩, ⟨['o', 'i'], ['A', '3'], some '-'⟩, ⟨['k', 'u', 'á', 'a'], ['k', 'n', 'o', 'w'], some '-'⟩, ⟨['i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], [⟨['H', 'a', '’', 'e'], ['P', 'R', 'O', 'N', '.', 'S', '.', '3'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['k', 'o'], ['t', 'h', 'i', 's'], [⟨['k', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], [⟨['m', 'b', 'u', 'r', 'u', 'v', 'i', 'c', 'h', 'a'], ['b', 'o', 's', 's'], none⟩]⟩, ⟨['p', 'a', '’', 'i', '-', 'h', 'a'], ['p', 'r', 'i', 'e', 's', 't', '-', 'N', 'O', 'M'], [⟨['p', 'a', '’', 'i'], ['p', 'r', 'i', 'e', 's', 't'], none⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker and her addressee are at a reception, with Raul standing at the next table. Malena is not present."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def ex_53 : Datum :=
  { id := "tonhauseretal2013_53"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(53)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Sabína oi-mo’ã ai-ko-ha pe óga-pe."
    glossedTokens := [("Sabína", "Sabina"), ("oi-mo’ã", "A3-think"), ("ai-ko-ha", "A1SG-live-NOM"), ("pe", "that"), ("óga-pe", "house-in")]
    glossedWords := [⟨['S', 'a', 'b', 'í', 'n', 'a'], ['S', 'a', 'b', 'i', 'n', 'a'], [⟨['S', 'a', 'b', 'í', 'n', 'a'], ['S', 'a', 'b', 'i', 'n', 'a'], none⟩]⟩, ⟨['o', 'i', '-', 'm', 'o', '’', 'ã'], ['A', '3', '-', 't', 'h', 'i', 'n', 'k'], [⟨['o', 'i'], ['A', '3'], none⟩, ⟨['m', 'o', '’', 'ã'], ['t', 'h', 'i', 'n', 'k'], some '-'⟩]⟩, ⟨['a', 'i', '-', 'k', 'o', '-', 'h', 'a'], ['A', '1', 'S', 'G', '-', 'l', 'i', 'v', 'e', '-', 'N', 'O', 'M'], [⟨['a', 'i'], ['A', '1', 'S', 'G'], none⟩, ⟨['k', 'o'], ['l', 'i', 'v', 'e'], some '-'⟩, ⟨['h', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['p', 'e'], ['t', 'h', 'a', 't'], [⟨['p', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['ó', 'g', 'a', '-', 'p', 'e'], ['h', 'o', 'u', 's', 'e', '-', 'i', 'n'], [⟨['ó', 'g', 'a'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['p', 'e'], ['i', 'n'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Marko and Maria are walking down the street together when Marko points at a house; their school friend Sabina is not with them."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def ex_54a : Datum :=
  { id := "tonhauseretal2013_54a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma likes that car."
    glossedTokens := []
    context := "Barney and Fred are walking down the street. They haven’t been discussing cars. Barney does not point to or otherwise indicate any of the cars parked in the street. Barney says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "that N"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_54b : Datum :=
  { id := "tonhauseretal2013_54b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Wilma likes that car, she has good taste."
    glossedTokens := []
    context := "Barney and Fred are walking down the street. They haven’t been discussing cars. Barney does not point to or otherwise indicate any of the cars parked in the street. Barney says:"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "that N"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("context", "m-neutral")] }

def ex_54c : Datum :=
  { id := "tonhauseretal2013_54c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(54c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pebbles thinks Wilma likes that car, but of course Pebbles has no idea that I’m pointing to it."
    glossedTokens := []
    context := "Barney points at a car and says:"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("trigger", "that N"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1d, ex_13, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17a, ex_17b, ex_18a, ex_18b, ex_19a, ex_19b, ex_20a, ex_20b, ex_20c, ex_22a, ex_22b, ex_30a, ex_30b, ex_30c, ex_30d, ex_31_30a, ex_31_30b, ex_31_30c, ex_31_30d, ex_38a, ex_38b, ex_39a, ex_39b, ex_46a, ex_46b, ex_47a, ex_47b, ex_48, ex_49, ex_50a, ex_51, ex_52_property, ex_52_indication, ex_53, ex_54a, ex_54b, ex_54c]

end TonhauserEtAl2013.Examples
