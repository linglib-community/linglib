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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "definite"), ("content", "existence of a unique queen of France"), ("environment", "conditional antecedent")] }

def ex_13 : Datum :=
  { id := "tonhauseretal2013_13"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(13)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe aña memby Márko ko’ãga oi-pota a-mba’apo iñ-hermáno karnisería-pe."
    glossedTokens := [("Pe", "that"), ("aña", "devil"), ("memby", "child"), ("Márko", "Marko"), ("ko’ãga", "now"), ("oi-pota", "A3-want"), ("a-mba’apo", "A1SG-work"), ("iñ-hermáno", "B3-brother"), ("karnisería-pe", "butcher.shop-in")]
    context := "Julia and Maria work in a bakery; their boss, who is generally strict but fair, is called Marko. One day, he calls Julia into his office; when she emerges, she says to Maria:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "expressive"), ("content", "negative evaluation"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_14a : Datum :=
  { id := "tonhauseretal2013_14a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(14a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Simon, che-kichiha-kue, o-ñe’ẽ Aleman."
    glossedTokens := [("Simon", "Simon"), ("che-kichiha-kue", "B1SG-boyfriend-NOM.TERM"), ("o-ñe’ẽ", "A3-speak"), ("Aleman", "German")]
    context := "Raul is new in town. His neighbor Simon invites him to his house for a party and introduces him to Maria. When Simon has walked away, Maria tells Raul:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "appositive"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_14b : Datum :=
  { id := "tonhauseretal2013_14b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(14b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Papa Benedícto 16, o-nasẽ-va’e-kue Alemánia-pe, oi-ko Róma-pe."
    glossedTokens := [("Papa", "Pope"), ("Benedícto", "Benedict"), ("16", "16"), ("o-nasẽ-va’e-kue", "A3-born-RC-NOM.TERM"), ("Alemánia-pe", "Germany-in"), ("oi-ko", "A3-live"), ("Róma-pe", "Rome-in")]
    context := "The children in a history class have to give presentations about famous people. Malena has to talk about the pope. She starts with:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_15a : Datum :=
  { id := "tonhauseretal2013_15a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(15a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Maléna hasy ra’e. Aimete o-gue’ẽ."
    glossedTokens := [("Maléna", "Malena"), ("hasy", "B3.sick"), ("ra’e", "it.seems"), ("Aimete", "almost"), ("o-gue’ẽ", "A3-vomit")]
    context := "A mother calls for her daughter to come down for dinner. Her daughter doesn’t appear so she goes upstairs to check on her. When she comes back down, she says to her husband:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "aimete ‘almost’"), ("content", "polar implication"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_15b : Datum :=
  { id := "tonhauseretal2013_15b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(15b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ché-nte a-mo-potĩ ñande-róga!"
    glossedTokens := [("Ché-nte", "PRON.S.1SG-only"), ("a-mo-potĩ", "A1SG-CAUS-clean"), ("ñande-róga", "B1PL.INCL-house")]
    context := "Carla, a mother of three teenage daughters, falls on the way to the supermarket and breaks her leg. She’s been in the hospital for a week when her daughters come to visit her for the first time. When she asks them how they are doing, her youngest daughter blurts out:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "-nte ‘only’"), ("content", "prejacent implication"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_16a : Datum :=
  { id := "tonhauseretal2013_16a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(16a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe kuimba’e nde-ru."
    glossedTokens := [("Pe", "that"), ("kuimba’e", "man"), ("nde-ru", "B2SG-father")]
    context := "You and your friend Maria are walking across a meadow. Both of you can see something ahead, lying in the grass, but you can’t identify what it is, even whether it’s an object, an animal, or a person. You have much better vision than Maria (who can generally only recognize people when they stand right in front of her). As you approach, you recognize what is lying ahead and tell Maria:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "property attribution"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_16b : Datum :=
  { id := "tonhauseretal2013_16b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(16b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ha’e peteĩ kuimba’e."
    glossedTokens := [("Ha’e", "PRON.S.3"), ("peteĩ", "one"), ("kuimba’e", "man")]
    context := "You and your friend Maria are walking across a meadow. Both of you can see something ahead, lying in the grass, but you can’t identify what it is, even whether it’s an object, an animal, or a person. You have much better vision than Maria (who can generally only recognize people when they stand right in front of her). As you approach, you recognize what is lying ahead and tell Maria:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "human referent"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_17a : Datum :=
  { id := "tonhauseretal2013_17a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(17a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_17b : Datum :=
  { id := "tonhauseretal2013_17b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(17b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    context := "Same as in (17a), except that Malena is eating empanadas."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_18a : Datum :=
  { id := "tonhauseretal2013_18a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(18a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe mitã-’i che-ryvy."
    glossedTokens := [("Pe", "that"), ("mitã-’i", "child-DIM"), ("che-ryvy", "B1SG-younger.brother")]
    context := "The children in a sociology class have to give presentations about their families. Marko is up first and he starts with:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_18b : Datum :=
  { id := "tonhauseretal2013_18b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(18b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe mitã-’i che-ryvy."
    glossedTokens := [("Pe", "that"), ("mitã-’i", "child-DIM"), ("che-ryvy", "B1SG-younger.brother")]
    context := "As in (18a), but now Marko also brings to the presentation a picture of a person that he shows to the class."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_19a : Datum :=
  { id := "tonhauseretal2013_19a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(19a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ha’e chokokue."
    glossedTokens := [("Ha’e", "PRON.S.3"), ("chokokue", "farmer")]
    context := "The children in a sociology class have to give presentations about their families. Marko is up first and he starts with:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "existence of referent"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_19b : Datum :=
  { id := "tonhauseretal2013_19b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(19b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Che-ru réra Juan. Ha’e chokokue."
    glossedTokens := [("Che-ru", "B1SG-father"), ("réra", "name"), ("Juan", "Juan"), ("Ha’e", "PRON.S.3"), ("chokokue", "farmer")]
    context := "The children in a sociology class have to give presentations about their families. Marko is up first and he starts with:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "existence of referent"), ("class", "A"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_20a : Datum :=
  { id := "tonhauseretal2013_20a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(20a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "A-ha-va’erã a-me’ẽ-ha-guã che-rymba jaguá-pe hembi’u-rã."
    glossedTokens := [("A-ha-va’erã", "A1SG-go-MUST"), ("a-me’ẽ-ha-guã", "A1SG-give-NOM-PURP"), ("che-rymba", "B1SG-domesticated.animal"), ("jaguá-pe", "dog-at"), ("hembi’u-rã", "3.food-NOM.PROSP")]
    context := "A woman who is being interviewed by a school director for a job as a teacher suddenly interrupts and says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "possessive NP"), ("content", "possessive relation"), ("class", "B"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_20b : Datum :=
  { id := "tonhauseretal2013_20b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(20b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Nd-a-je-droga-vé-i-ma."
    glossedTokens := [("Nd-a-je-droga-vé-i-ma", "NEG-A1SG-JE-drug-more-NEG-already")]
    context := "Laura, who doesn’t live with her parents, visits them and asks them to sit down with her because she has to tell them something:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "n(d)(a)-…-vé-i-ma ‘not anymore’"), ("content", "prestate holds"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_20c : Datum :=
  { id := "tonhauseretal2013_20c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(20c)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ha’e oi-kuaa o-moĩ-va’erã-ha i-lénte o-maneja-ha-guã."
    glossedTokens := [("Ha’e", "PRON.S.3"), ("oi-kuaa", "A3-know"), ("o-moĩ-va’erã-ha", "A3-put-MUST-NOM"), ("i-lénte", "3-glasses"), ("o-maneja-ha-guã", "A3-drive-NOM-PURP")]
    context := "A girl backs out of a driveway and hits Susi’s car. A woman comes running out of the house, apologizes that her daughter hit Susi’s car, and says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "(oi)kuaa ‘know’"), ("content", "content of complement"), ("class", "C"), ("diagnostic", "strong contextual felicity"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_22a : Datum :=
  { id := "tonhauseretal2013_22a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(22a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ko mburuvicha Fransia-gua oi-ko Lóndre-pe."
    glossedTokens := [("Ko", "this"), ("mburuvicha", "boss"), ("Fransia-gua", "France-from"), ("oi-ko", "A3-live"), ("Lóndre-pe", "London-in")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "projection"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_22b : Datum :=
  { id := "tonhauseretal2013_22b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(22b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ko mburuvicha Fransia-gua nd-oi-kó-i Lóndre-pe."
    glossedTokens := [("Ko", "this"), ("mburuvicha", "boss"), ("Fransia-gua", "France-from"), ("nd-oi-kó-i", "NEG-A3-live-NEG"), ("Lóndre-pe", "London-in")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "projection"), ("environment", "negation"), ("context", "m-neutral")] }

def ex_30a : Datum :=
  { id := "tonhauseretal2013_30a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "atomic"), ("context", "m-neutral")] }

def ex_30b : Datum :=
  { id := "tonhauseretal2013_30b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "I-katu o-karu empanáda avei ñande-chofeur."
    glossedTokens := [("I-katu", "B3-possible"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("context", "m-neutral")] }

def ex_30c : Datum :=
  { id := "tonhauseretal2013_30c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30c)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-ramo empanáda avei ñande-chofeur, a-sẽ-ta kolektívo-gui."
    glossedTokens := [("O-karú-ramo", "A3-eat-if"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver"), ("a-sẽ-ta", "A1SG-leave-PROSP"), ("kolektívo-gui", "bus-from")]
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("context", "m-neutral")] }

def ex_30d : Datum :=
  { id := "tonhauseretal2013_30d"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30d)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-pa empanada avei ñande-chofeur?"
    glossedTokens := [("O-karú-pa", "A3-eat-Q"), ("empanada", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    context := "Malena is eating her lunch, a hamburger, on the bus going into town. A woman who she doesn’t know sits down next to her and says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "question"), ("context", "m-neutral")] }

def ex_31_30a : Datum :=
  { id := "tonhauseretal2013_31_30a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñande-chofeur o-karu empanáda avei."
    glossedTokens := [("Ñande-chofeur", "A1PL.INCL-driver"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too")]
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "atomic"), ("context", "m-positive")] }

def ex_31_30b : Datum :=
  { id := "tonhauseretal2013_31_30b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "I-katu o-karu empanáda avei ñande-chofeur."
    glossedTokens := [("I-katu", "B3-possible"), ("o-karu", "A3-eat"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "epistemic modal"), ("context", "m-positive")] }

def ex_31_30c : Datum :=
  { id := "tonhauseretal2013_31_30c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-ramo empanáda avei ñande-chofeur, a-sẽ-ta kolektívo-gui."
    glossedTokens := [("O-karú-ramo", "A3-eat-if"), ("empanáda", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver"), ("a-sẽ-ta", "A1SG-leave-PROSP"), ("kolektívo-gui", "bus-from")]
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei ‘too’"), ("content", "existence of alternative"), ("class", "A"), ("diagnostic", "projection"), ("environment", "conditional antecedent"), ("context", "m-positive")] }

def ex_31_30d : Datum :=
  { id := "tonhauseretal2013_31_30d"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(31)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "O-karú-pa empanada avei ñande-chofeur?"
    glossedTokens := [("O-karú-pa", "A3-eat-Q"), ("empanada", "empanada"), ("avei", "too"), ("ñande-chofeur", "A1PL.INCL-driver")]
    context := "Same as in (30), except that Malena is eating empanadas."
    judgment := .acceptable
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_46a : Datum :=
  { id := "tonhauseretal2013_46a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(46a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Raul o-va Buénos Áires-pe, há=katu Juan nd-oi-kuáa-i. Ha’e oi-mo’ã Maléna avei o-va-ha Buénos Áires-pe."
    glossedTokens := [("Raul", "Raul"), ("o-va", "A3-move"), ("Buénos", "Buenos"), ("Áires-pe", "Aires-to"), ("há=katu", "and=CONTR"), ("Juan", "Juan"), ("nd-oi-kuáa-i", "NEG-A3-know-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("Maléna", "Malena"), ("avei", "too"), ("o-va-ha", "A3-move-NOM"), ("Buénos", "Buenos"), ("Áires-pe", "Aires-to")]
    context := ""
    judgment := .unacceptable
    alternatives := []
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
    context := "The speaker, Ricardo, and Malena are lost in a city they’ve never visited before. The speaker, who, together with Ricardo, is a bit ahead of Malena, says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ha’e ‘3rd’"), ("content", "existence of referent"), ("class", "A"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def ex_47a : Datum :=
  { id := "tonhauseretal2013_47a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(47a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Juan oi-mo’ã Maléna aimete o-pe-ha hetyma ha oi-mo’ã avei Maléna o-pe-ha hetyma."
    glossedTokens := [("Juan", "Juan"), ("oi-mo’ã", "A3-think"), ("Maléna", "Malena"), ("aimete", "almost"), ("o-pe-ha", "A3-break-NOM"), ("hetyma", "B3.leg"), ("ha", "and"), ("oi-mo’ã", "A3-think"), ("avei", "also"), ("Maléna", "Malena"), ("o-pe-ha", "A3-break-NOM"), ("hetyma", "B3.leg")]
    context := "Juan is a doctor at the scene of an accident. His friend says about him:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "aimete ‘almost’"), ("content", "polar implication"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_47b : Datum :=
  { id := "tonhauseretal2013_47b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(47b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Juan oi-mo’ã Maléna-nte o-pe-ha hetyma ha oi-mo’ã avei Maléna nd-o-pe-i-ha hetyma."
    glossedTokens := [("Juan", "Juan"), ("oi-mo’ã", "A3-think"), ("Maléna-nte", "Malena-only"), ("o-pe-ha", "A3-break-NOM"), ("hetyma", "B3.leg"), ("ha", "and"), ("oi-mo’ã", "A3-think"), ("avei", "too"), ("Maléna", "Malena"), ("nd-o-pe-i-ha", "NEG-A3-break-NEG-NOM"), ("hetyma", "B3.leg")]
    context := "Juan is a doctor at the scene of an accident. His friend says about him:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "-nte ‘only’"), ("content", "prejacent implication"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_48 : Datum :=
  { id := "tonhauseretal2013_48"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(48)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ángel oi-mo’ã i-túva oi-kuaa-ha iñ-ermána o-guereko kichiha ha Ángel oi-mo’ã avei iñ-ermána nd-o-guerekó-i-ha kichiha."
    glossedTokens := [("Ángel", "Angel"), ("oi-mo’ã", "A3-think"), ("i-túva", "B3-father"), ("oi-kuaa-ha", "A3-know-NOM"), ("iñ-ermána", "B3-sister"), ("o-guereko", "A3-have"), ("kichiha", "boyfriend"), ("ha", "and"), ("Ángel", "Angel"), ("oi-mo’ã", "A3-think"), ("avei", "too"), ("iñ-ermána", "B3-sister"), ("nd-o-guerekó-i-ha", "NEG-A3-have-NEG-NOM"), ("kichiha", "boyfriend")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "(oi)kuaa ‘know’"), ("content", "content of complement"), ("class", "C"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_49 : Datum :=
  { id := "tonhauseretal2013_49"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(49)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Juan oi-mo’ã Angéla Mérkel, Alemánia mburuvicha, ha’e-ha Argentína mburuvicha."
    glossedTokens := [("Juan", "Juan"), ("oi-mo’ã", "A3-think"), ("Angéla", "Angela"), ("Mérkel", "Merkel"), ("Alemánia", "Germany"), ("mburuvicha", "boss"), ("ha’e-ha", "PRON.S.3-NOM"), ("Argentína", "Argentina"), ("mburuvicha", "boss")]
    context := "Sabine is from Germany and knows the politicians there very well. Angela Merkel, the chancellor of Germany, is currently visiting farmers in Paraguay, among them Juan. Sabine says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "appositive"), ("content", "descriptive content"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-negative")] }

def ex_50a : Datum :=
  { id := "tonhauseretal2013_50a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(50a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "E-ma’ẽ-mi! Upépe o-ĩ peteĩ kuimba’e, há=katu Maléna nd-oi-kuáa-i. Ha’e oi-mo’ã ha’e-ha peteĩ ta’anga ita-guí-gua."
    glossedTokens := [("E-ma’ẽ-mi", "A2SG-look-DIM"), ("Upépe", "there"), ("o-ĩ", "A3-be"), ("peteĩ", "one"), ("kuimba’e", "man"), ("há=katu", "and=CONTR"), ("Maléna", "Malena"), ("nd-oi-kuáa-i", "NEG-A3-know-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("ha’e-ha", "PRON.S.3-NOM"), ("peteĩ", "one"), ("ta’anga", "figure"), ("ita-guí-gua", "stone-of-from")]
    context := "The speaker, Ricardo, and Malena are lost and looking for somebody to ask for directions. The speaker, who is walking ahead with Ricardo, says:"
    judgment := .acceptable
    alternatives := []
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
    context := "Brian and Pedro are strolling down the street. They see a dog chasing a cat. Brian comments to Pedro that the dog looks fierce. Pedro knows that the dog is Carmen’s, but Brian doesn’t know that. Pedro later says to his wife:"
    judgment := .acceptable
    alternatives := []
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
    context := "The speaker and her addressee are at a reception, with Raul standing at the next table. Malena is not present."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "property attribution"), ("class", "B"), ("diagnostic", "obligatory local effect"), ("holder", "m-neutral")] }

def ex_52_indication : Datum :=
  { id := "tonhauseretal2013_52_indication"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(52)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Raul mburuvicha há=katu Maléna nd-oi-kuáa-i. Ha’e oi-mo’ã ko mburuvicha pa’i-ha."
    glossedTokens := [("Raul", "Raul"), ("mburuvicha", "boss"), ("há=katu", "and=CONTR"), ("Maléna", "Malena"), ("nd-oi-kuáa-i", "NEG-A3-know-NEG"), ("Ha’e", "PRON.S.3"), ("oi-mo’ã", "A3-think"), ("ko", "this"), ("mburuvicha", "boss"), ("pa’i-ha", "priest-NOM")]
    context := "The speaker and her addressee are at a reception, with Raul standing at the next table. Malena is not present."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def ex_53 : Datum :=
  { id := "tonhauseretal2013_53"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(53)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Sabína oi-mo’ã ai-ko-ha pe óga-pe."
    glossedTokens := [("Sabína", "Sabina"), ("oi-mo’ã", "A3-think"), ("ai-ko-ha", "A1SG-live-NOM"), ("pe", "that"), ("óga-pe", "house-in")]
    context := "Marko and Maria are walking down the street together when Marko points at a house; their school friend Sabina is not with them."
    judgment := .acceptable
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "that N"), ("content", "speaker indicates suitable entity"), ("class", "D"), ("diagnostic", "obligatory local effect"), ("context", "m-positive"), ("holder", "m-neutral")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1d, ex_13, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17a, ex_17b, ex_18a, ex_18b, ex_19a, ex_19b, ex_20a, ex_20b, ex_20c, ex_22a, ex_22b, ex_30a, ex_30b, ex_30c, ex_30d, ex_31_30a, ex_31_30b, ex_31_30c, ex_31_30d, ex_38a, ex_38b, ex_39a, ex_39b, ex_46a, ex_46b, ex_47a, ex_47b, ex_48, ex_49, ex_50a, ex_51, ex_52_property, ex_52_indication, ex_53, ex_54a, ex_54b, ex_54c]

end TonhauserEtAl2013.Examples
