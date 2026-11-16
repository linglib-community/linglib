module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Rakosi2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Rakosi2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rakosi2020.Examples`.
-/

@[expose] public section

namespace Rakosi2020.Examples

def ex_1a : Datum :=
  { id := "rakosi2020_1a"
    source := ⟨"rakosi-2020", "(1a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látták egymás-t a tükörben."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látták", "saw.3PL"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "plural"), ("anaphor", "egymás")] }

def ex_1b : Datum :=
  { id := "rakosi2020_1b"
    source := ⟨"rakosi-2020", "(1b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látták maguk-at a tükörben."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látták", "saw.3PL"), ("maguk-at", "themselves-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "plural"), ("anaphor", "maguk")] }

def ex_2a : Datum :=
  { id := "rakosi2020_2a"
    source := ⟨"rakosi-2020", "(2a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek látta egymás-t a tükörben."
    glossedTokens := [("A", "the"), ("gyerek", "child"), ("látta", "saw.3SG"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "atomic"), ("anaphor", "egymás")] }

def ex_2b : Datum :=
  { id := "rakosi2020_2b"
    source := ⟨"rakosi-2020", "(2b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek látta magá-t a tükörben."
    glossedTokens := [("A", "the"), ("gyerek", "child"), ("látta", "saw.3SG"), ("magá-t", "oneself-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "atomic"), ("anaphor", "maga")] }

def ex_3a : Datum :=
  { id := "rakosi2020_3a"
    source := ⟨"rakosi-2020", "(3a)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Látom magunk-at ülni az autóban."
    glossedTokens := [("Látom", "see.1SG"), ("magunk-at", "ourselves-ACC"), ("ülni", "sit.INF"), ("az", "the"), ("autóban.", "car.in")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "inclusive"), ("anaphor", "magunk")] }

def ex_3b : Datum :=
  { id := "rakosi2020_3b"
    source := ⟨"rakosi-2020", "(3b)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Sokszor sajnálom magunk-at."
    glossedTokens := [("Sokszor", "often"), ("sajnálom", "feel_sorry.1SG"), ("magunk-at.", "ourselves-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "inclusive"), ("anaphor", "magunk")] }

def ex_4a : Datum :=
  { id := "rakosi2020_4a"
    source := ⟨"rakosi-2020", "(4a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Csak én sajnálom magunk-at."
    glossedTokens := [("Csak", "only"), ("én", "I"), ("sajnálom", "feel_sorry.1SG"), ("magunk-at.", "ourselves-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("referential", .acceptable), ("bound variable", .ungrammatical)]
    paperFeatures := [("antecedent", "inclusive"), ("anaphor", "magunk")] }

def ex_4b : Datum :=
  { id := "rakosi2020_4b"
    source := ⟨"rakosi-2020", "(4b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Csak mi sajnáljuk magunk-at."
    glossedTokens := [("Csak", "only"), ("mi", "we"), ("sajnáljuk", "feel_sorry.1PL"), ("magunk-at.", "ourselves-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("bound variable", .acceptable)]
    paperFeatures := [("antecedent", "plural"), ("anaphor", "magunk")] }

def ex_4c : Datum :=
  { id := "rakosi2020_4c"
    source := ⟨"rakosi-2020", "(4c)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Csak mi sajnáljuk egymás-t."
    glossedTokens := [("Csak", "only"), ("mi", "we"), ("sajnáljuk", "feel_sorry.1PL"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("bound variable", .acceptable)]
    paperFeatures := [("antecedent", "plural"), ("anaphor", "egymás")] }

def ex_5a : Datum :=
  { id := "rakosi2020_5a"
    source := ⟨"rakosi-2020", "(5a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek jól viselték maguk-at."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("jól", "well"), ("viselték", "behave.3PL"), ("maguk-at.", "themselves-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "plural"), ("anaphor", "maguk")] }

def ex_5b : Datum :=
  { id := "rakosi2020_5b"
    source := ⟨"rakosi-2020", "(5b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek jól viselte maguk-at."
    glossedTokens := [("A", "the"), ("gyerek", "child"), ("jól", "well"), ("viselte", "behave.3SG"), ("maguk-at.", "themselves-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "atomic"), ("anaphor", "maguk")] }

def ex_6 : Datum :=
  { id := "rakosi2020_6"
    source := ⟨"rakosi-2020", "(6)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Sokszor sajnálom egymás-t."
    glossedTokens := [("Sokszor", "often"), ("sajnálom", "feel_sorry.1SG"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "inclusive"), ("anaphor", "egymás")] }

def ex_7a : Datum :=
  { id := "rakosi2020_7a"
    source := ⟨"rakosi-2020", "(7a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látták a kép-et."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látták", "saw.3PL"), ("a", "the"), ("kép-et.", "picture-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "plural")] }

def ex_7a_ : Datum :=
  { id := "rakosi2020_7a_"
    source := ⟨"rakosi-2020", "(7a')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A gyerek-ek látta a kép-et."
    glossedTokens := [("A", "the"), ("gyerek-ek", "child-PL"), ("látta", "saw.3SG"), ("a", "the"), ("kép-et.", "picture-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "plural")] }

def ex_7b : Datum :=
  { id := "rakosi2020_7b"
    source := ⟨"rakosi-2020", "(7b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Két gyerek látta a kép-et."
    glossedTokens := [("Két", "two"), ("gyerek", "child"), ("látta", "saw.3SG"), ("a", "the"), ("kép-et.", "picture-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := [("Minden gyerek látta a kép-et.", .acceptable), ("Néhány gyerek látta a kép-et.", .acceptable), ("Két gyerek-ek látta a kép-et.", .ungrammatical)]
    readings := []
    paperFeatures := [("antecedent", "quantified")] }

def ex_7b_ : Datum :=
  { id := "rakosi2020_7b_"
    source := ⟨"rakosi-2020", "(7b')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Két gyerek látták a kép-et."
    glossedTokens := [("Két", "two"), ("gyerek", "child"), ("látták", "saw.3PL"), ("a", "the"), ("kép-et.", "picture-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified")] }

def ex_8a : Datum :=
  { id := "rakosi2020_8a"
    source := ⟨"rakosi-2020", "(8a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A két gyerek jól érezte magá-t."
    glossedTokens := [("A", "the"), ("két", "two"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("magá-t.", "oneself-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "maga")] }

def ex_8a_ : Datum :=
  { id := "rakosi2020_8a_"
    source := ⟨"rakosi-2020", "(8a')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A két gyerek jól érezte maguk-at."
    glossedTokens := [("A", "the"), ("két", "two"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("maguk-at.", "themselves-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "maguk")] }

def ex_8b : Datum :=
  { id := "rakosi2020_8b"
    source := ⟨"rakosi-2020", "(8b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Néhány gyerek jól érezte magá-t."
    glossedTokens := [("Néhány", "some"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("magá-t.", "oneself-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "maga")] }

def ex_8b_ : Datum :=
  { id := "rakosi2020_8b_"
    source := ⟨"rakosi-2020", "(8b')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Néhány gyerek jól érezte maguk-at."
    glossedTokens := [("Néhány", "some"), ("gyerek", "child"), ("jól", "well"), ("érezte", "felt.3SG"), ("maguk-at.", "themselves-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "maguk")] }

def ex_9a : Datum :=
  { id := "rakosi2020_9a"
    source := ⟨"rakosi-2020", "(9a)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A szobában három kisgyerek kergeti egymás-t."
    glossedTokens := [("A", "the"), ("szobában", "room.in"), ("három", "three"), ("kisgyerek", "little.child"), ("kergeti", "chase.3SG"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "egymás")] }

def ex_9b : Datum :=
  { id := "rakosi2020_9b"
    source := ⟨"rakosi-2020", "(9b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Néhány szomszéd gyerek nagyon szereti egymás-t."
    glossedTokens := [("Néhány", "some"), ("szomszéd", "neighbour"), ("gyerek", "child"), ("nagyon", "much"), ("szereti", "love.3SG"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "egymás")] }

def ex_9c : Datum :=
  { id := "rakosi2020_9c"
    source := ⟨"rakosi-2020", "(9c)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Otthon mindenki szerette egymás-t."
    glossedTokens := [("Otthon", "home"), ("mindenki", "everyone"), ("szerette", "loved.3SG"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "egymás")] }

def ex_9d : Datum :=
  { id := "rakosi2020_9d"
    source := ⟨"rakosi-2020", "(9d)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A sokaságban senki se keresi egymás-t."
    glossedTokens := [("A", "the"), ("sokaságban", "crowd.in"), ("senki", "nobody"), ("se", "not"), ("keresi", "search_for.3SG"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "quantified"), ("anaphor", "egymás")] }

def ex_10 : Datum :=
  { id := "rakosi2020_10"
    source := ⟨"rakosi-2020", "(10)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látta a képet."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látta", "saw.3SG"), ("a", "the"), ("képet.", "picture-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate")] }

def ex_10_ : Datum :=
  { id := "rakosi2020_10_"
    source := ⟨"rakosi-2020", "(10')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látták a képet."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látták", "saw.3PL"), ("a", "the"), ("képet.", "picture-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate")] }

def ex_11a : Datum :=
  { id := "rakosi2020_11a"
    source := ⟨"rakosi-2020", "(11a)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzta magát."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzta", "out.drew.3SG"), ("magát.", "herself")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate"), ("anaphor", "maga")] }

def ex_11a_ : Datum :=
  { id := "rakosi2020_11a_"
    source := ⟨"rakosi-2020", "(11a')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzta magukat."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzta", "out.drew.3SG"), ("magukat.", "themselves")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate"), ("anaphor", "maguk")] }

def ex_11b : Datum :=
  { id := "rakosi2020_11b"
    source := ⟨"rakosi-2020", "(11b)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzták magukat."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzták", "out.drew.3PL"), ("magukat.", "themselves")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate"), ("anaphor", "maguk")] }

def ex_11b_ : Datum :=
  { id := "rakosi2020_11b_"
    source := ⟨"rakosi-2020", "(11b')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva kihúzták magát."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("kihúzták", "out.drew.3PL"), ("magát.", "herself")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate"), ("anaphor", "maga")] }

def ex_12 : Datum :=
  { id := "rakosi2020_12"
    source := ⟨"rakosi-2020", "(12)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látta egymás-t a tükörben."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látta", "saw.3SG"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate"), ("anaphor", "egymás")] }

def ex_12_ : Datum :=
  { id := "rakosi2020_12_"
    source := ⟨"rakosi-2020", "(12')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Kati és Éva látták egymás-t a tükörben."
    glossedTokens := [("Kati", "Kati"), ("és", "and"), ("Éva", "Éva"), ("látták", "saw.3PL"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("tükörben.", "mirror.in")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "coordinate"), ("anaphor", "egymás")] }

def ex_13 : Datum :=
  { id := "rakosi2020_13"
    source := ⟨"rakosi-2020", "(13)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A személyzet úgy gondolta, hogy ők már eleget dolgoztak."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("úgy", "so"), ("gondolta,", "thought.3SG"), ("hogy", "that"), ("ők", "they"), ("már", "already"), ("eleget", "enough"), ("dolgoztak.", "worked.3PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14 : Datum :=
  { id := "rakosi2020_14"
    source := ⟨"rakosi-2020", "(14)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A személyzet fáradt volt."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("fáradt", "tired"), ("volt.", "was.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "collective")] }

def ex_14_ : Datum :=
  { id := "rakosi2020_14_"
    source := ⟨"rakosi-2020", "(14')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "A személyzet fáradt voltak."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("fáradt", "tired"), ("voltak.", "were.3PL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "collective")] }

def ex_15a : Datum :=
  { id := "rakosi2020_15a"
    source := ⟨"rakosi-2020", "(15a)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A személyzet riadtan nézte egymás-t."
    glossedTokens := [("A", "the"), ("személyzet", "staff"), ("riadtan", "frightened"), ("nézte", "watch.3SG"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "collective"), ("anaphor", "egymás")] }

def ex_15b : Datum :=
  { id := "rakosi2020_15b"
    source := ⟨"rakosi-2020", "(15b)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A Facebookon szidta egymás-t a család."
    glossedTokens := [("A", "the"), ("Facebookon", "Facebook.on"), ("szidta", "cursed.3SG"), ("egymás-t", "each_other-ACC"), ("a", "the"), ("család.", "family")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "collective"), ("anaphor", "egymás")] }

def ex_15c : Datum :=
  { id := "rakosi2020_15c"
    source := ⟨"rakosi-2020", "(15c)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "A pár az interneten találta meg egymás-t."
    glossedTokens := [("A", "the"), ("pár", "couple"), ("az", "the"), ("interneten", "internet.on"), ("találta", "found.3SG"), ("meg", "PRT"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "collective"), ("anaphor", "egymás")] }

def ex_16 : Datum :=
  { id := "rakosi2020_16"
    source := ⟨"rakosi-2020", "(16)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Az egész család jól érezte magá-t."
    glossedTokens := [("Az", "the"), ("egész", "whole"), ("család", "family"), ("jól", "well"), ("érezte", "felt.3SG"), ("magá-t.", "itself-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "collective"), ("anaphor", "maga")] }

def ex_16_ : Datum :=
  { id := "rakosi2020_16_"
    source := ⟨"rakosi-2020", "(16')"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Az egész család jól érezte maguk-at."
    glossedTokens := [("Az", "the"), ("egész", "whole"), ("család", "family"), ("jól", "well"), ("érezte", "felt.3SG"), ("maguk-at.", "themselves-ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "collective"), ("anaphor", "maguk")] }

def ex_17 : Datum :=
  { id := "rakosi2020_17"
    source := ⟨"rakosi-2020", "(17)"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "Péter és Éva az-t gondolja, hogy szereti egymás-t."
    glossedTokens := [("Péter", "Péter"), ("és", "and"), ("Éva", "Éva"), ("az-t", "that-ACC"), ("gondolja,", "think.3SG"), ("hogy", "that"), ("szereti", "love.3SG"), ("egymás-t.", "each_other-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := [("Péter és Éva az-t gondolja, hogy ő szereti egymás-t.", .ungrammatical)]
    readings := [("broad scope", .acceptable)]
    paperFeatures := [("antecedent", "boundPro"), ("anaphor", "egymás")] }

def ex_18 : Datum :=
  { id := "rakosi2020_18"
    source := ⟨"rakosi-2020", "(18)"⟩
    reportedIn := none
    method := some .corpus
    language := "hung1274"
    primaryText := "Álmomban két macska voltam, és játszottam egymás-sal."
    glossedTokens := [("Álmomban", "dream.POSS.1SG.in"), ("két", "two"), ("macska", "cat"), ("voltam,", "was.1SG"), ("és", "and"), ("játszottam", "played.1SG"), ("egymás-sal.", "each_other-with")]
    context := ""
    judgment := .acceptable
    alternatives := [("Álmomban két macska voltam, és én játszottam egymás-sal.", .ungrammatical)]
    readings := []
    paperFeatures := [("antecedent", "boundPro"), ("anaphor", "egymás")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_6, ex_7a, ex_7a_, ex_7b, ex_7b_, ex_8a, ex_8a_, ex_8b, ex_8b_, ex_9a, ex_9b, ex_9c, ex_9d, ex_10, ex_10_, ex_11a, ex_11a_, ex_11b, ex_11b_, ex_12, ex_12_, ex_13, ex_14, ex_14_, ex_15a, ex_15b, ex_15c, ex_16, ex_16_, ex_17, ex_18]

/-- The subject antecedents the paper compares. -/
inductive Antecedent where
  /-- atomic: a singular noun phrase denoting one individual -/
  | atomic
  /-- plural: a plural noun phrase -/
  | plural
  /-- inclusive: a singular subject included in the reference of a plural reflexive (§2) -/
  | inclusive
  /-- quantified: a quantified noun phrase, whose noun head is singular (§3) -/
  | quantified
  /-- coordinate: two conjoined singular noun phrases (§4) -/
  | coordinate
  /-- collective: a singular collective noun (§5) -/
  | collective
  /-- boundPro: a singular null pronoun bound by a plural in a higher clause (§6) -/
  | boundPro
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `antecedent`. -/
def antecedent (e : Datum) : Option Antecedent :=
  e.parse? "antecedent" [("atomic", .atomic), ("plural", .plural), ("inclusive", .inclusive),
    ("quantified", .quantified), ("coordinate", .coordinate), ("collective", .collective),
    ("boundPro", .boundPro)]

end Rakosi2020.Examples
