module

public import Linglib.Data.Examples.Schema

/-!
# `Bale2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Bale2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bale2008.Examples`.
-/

@[expose] public section

namespace Bale2008.Examples

def ex_1a : Datum :=
  { id := "bale2008_1a"
    source := ⟨"bale-2008", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Esme is more beautiful than Marie Curie was intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("entails", "(1b)")] }

def ex_1b : Datum :=
  { id := "bale2008_1b"
    source := ⟨"bale-2008", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Marie Curie was very intelligent, then Esme is (at least) very beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_2a : Datum :=
  { id := "bale2008_2a"
    source := ⟨"bale-2008", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is taller than he is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct"), ("entails", "none")] }

def ex_2b : Datum :=
  { id := "bale2008_2b"
    source := ⟨"bale-2008", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Seymour is very wide, then he is (at least) very tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_3a : Datum :=
  { id := "bale2008_3a"
    source := ⟨"bale-2008", "(3a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Maria è più bella di quanto Marie Curie sia intelligente."
    glossedTokens := [("Maria", "Maria"), ("è", "is"), ("più", "more"), ("bella", "beautiful"), ("di", "than"), ("quanto", "how.much"), ("Marie", "Marie"), ("Curie", "Curie"), ("sia", "is"), ("intelligente", "intelligent")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("morpheme", "più")] }

def ex_3b : Datum :=
  { id := "bale2008_3b"
    source := ⟨"bale-2008", "(3b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La porta è più alta di quanto sia larga."
    glossedTokens := [("La", "the"), ("porta", "door"), ("è", "is"), ("più", "more"), ("alta", "high"), ("di", "than"), ("quanto", "how.much"), ("sia", "is"), ("larga", "wide")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct"), ("morpheme", "più")] }

def ex_4a : Datum :=
  { id := "bale2008_4a"
    source := ⟨"bale-2008", "(4a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Eva ist schöner als Einstein intelligent war."
    glossedTokens := [("Eva", "Eva"), ("ist", "is"), ("schöner", "more.beautiful"), ("als", "than"), ("Einstein", "Einstein"), ("intelligent", "intelligent"), ("war", "was")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("morpheme", "-er")] }

def ex_4b : Datum :=
  { id := "bale2008_4b"
    source := ⟨"bale-2008", "(4b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Tür ist höher als sie breit ist."
    glossedTokens := [("Die", "the"), ("Tür", "door"), ("ist", "is"), ("höher", "higher"), ("als", "than"), ("sie", "it"), ("breit", "wide"), ("ist", "is")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct"), ("morpheme", "-er")] }

def ex_5a : Datum :=
  { id := "bale2008_5a"
    source := ⟨"bale-2008", "(5a)"⟩
    reportedIn := none
    language := "queb1247"
    primaryText := "Charlotte est plus belle que Marie Curie est intelligente."
    glossedTokens := [("Charlotte", "Charlotte"), ("est", "is"), ("plus", "more"), ("belle", "beautiful"), ("que", "than"), ("Marie", "Marie"), ("Curie", "Curie"), ("est", "is"), ("intelligente", "intelligent")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("morpheme", "plus")] }

def ex_5b : Datum :=
  { id := "bale2008_5b"
    source := ⟨"bale-2008", "(5b)"⟩
    reportedIn := none
    language := "queb1247"
    primaryText := "La table est plus longue qu'elle est large."
    glossedTokens := [("La", "the"), ("table", "table"), ("est", "is"), ("plus", "more"), ("longue", "long"), ("qu'", "than"), ("elle", "it"), ("est", "is"), ("large", "wide")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct"), ("morpheme", "plus")] }

def ex_6a : Datum :=
  { id := "bale2008_6a"
    source := ⟨"bale-2008", "(6a)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Elena e mai frumoasa decit cit de inteligenta e Marie Curie."
    glossedTokens := [("Elena", "Elena"), ("e", "is"), ("mai", "more"), ("frumoasa", "beautiful"), ("decit", "than"), ("cit", "how"), ("de", "of"), ("inteligenta", "intelligent"), ("e", "is"), ("Marie", "Marie"), ("Curie", "Curie")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("morpheme", "mai")] }

def ex_6b : Datum :=
  { id := "bale2008_6b"
    source := ⟨"bale-2008", "(6b)"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "Masa e mai lunga decit cit de lata e usa."
    glossedTokens := [("Masa", "table-the"), ("e", "is"), ("mai", "more"), ("lunga", "long"), ("decit", "than"), ("cit", "how.much"), ("de", "of"), ("lata", "wide"), ("e", "is"), ("usa", "door-the")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct"), ("morpheme", "mai")] }

def ex_7a : Datum :=
  { id := "bale2008_7a"
    source := ⟨"bale-2008", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is more tall than he is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "metalinguistic")] }

def ex_7b : Datum :=
  { id := "bale2008_7b"
    source := ⟨"bale-2008", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is more intelligent than devious."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "metalinguistic")] }

def ex_7c : Datum :=
  { id := "bale2008_7c"
    source := ⟨"bale-2008", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is more tall now than he was short before."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "deviation")] }

def ex_8a : Datum :=
  { id := "bale2008_8a"
    source := ⟨"bale-2008", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Let me tell you how pretty Esme is. She's prettier than Einstein was clever."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("affix", "-er")] }

def ex_8c : Datum :=
  { id := "bale2008_8c"
    source := ⟨"bale-2008", "(8c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Although Seymour was both happy and angry, he was still happier than he was angry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("affix", "-er")] }

def ex_8d : Datum :=
  { id := "bale2008_8d"
    source := ⟨"bale-2008", "(8d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is taller for a man than he is wide for a man."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("affix", "-er")] }

def ex_9 : Datum :=
  { id := "bale2008_9"
    source := ⟨"bale-2008", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, Mary is more intelligent than I am beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_11a : Datum :=
  { id := "bale2008_11a"
    source := ⟨"bale-2008", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm more pretty than intelligent, although unfortunately I'm quite ugly."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "metalinguistic")] }

def ex_11b : Datum :=
  { id := "bale2008_11b"
    source := ⟨"bale-2008", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm prettier than I am intelligent, although unfortunately I'm quite ugly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_14a : Datum :=
  { id := "bale2008_14a"
    source := ⟨"bale-2008", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is taller than he is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct")] }

def ex_14b : Datum :=
  { id := "bale2008_14b"
    source := ⟨"bale-2008", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Esme is more beautiful than she is intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_18a : Datum :=
  { id := "bale2008_18a"
    source := ⟨"bale-2008", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Esme is more beautiful for a committee member than Seymour is intelligent for a committee member."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_18c : Datum :=
  { id := "bale2008_18c"
    source := ⟨"bale-2008", "(18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sidney Crosby is more talented for a hockey player than Medusa is ugly for a Gorgon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_18d : Datum :=
  { id := "bale2008_18d"
    source := ⟨"bale-2008", "(18d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sidney Crosby is a more talented hockey player than Medusa is an ugly Gorgon."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_19a : Datum :=
  { id := "bale2008_19a"
    source := ⟨"bale-2008", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Betty is more beautiful for a committee member than Heather is intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("model", "committee"), ("subject", "b"), ("subjectScale", "beauty"), ("standard", "h"), ("standardScale", "intelligence")] }

def ex_19b : Datum :=
  { id := "bale2008_19b"
    source := ⟨"bale-2008", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Betty is more intelligent for a committee member than Evelin is beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("model", "committee"), ("subject", "b"), ("subjectScale", "intelligence"), ("standard", "e"), ("standardScale", "beauty")] }

def ex_22a : Datum :=
  { id := "bale2008_22a"
    source := ⟨"bale-2008", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately Medusa is more beautiful than I am intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_22b : Datum :=
  { id := "bale2008_22b"
    source := ⟨"bale-2008", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sidney Crosby is more talented than Einstein was intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_25a : Datum :=
  { id := "bale2008_25a"
    source := ⟨"bale-2008", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seven feet is tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("measurePhrase", "subject")] }

def ex_25b : Datum :=
  { id := "bale2008_25b"
    source := ⟨"bale-2008", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seven feet are tall."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("measurePhrase", "subject")] }

def ex_25d : Datum :=
  { id := "bale2008_25d"
    source := ⟨"bale-2008", "(25d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Those seven feet is wide."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("measurePhrase", "subject")] }

def ex_26a : Datum :=
  { id := "bale2008_26a"
    source := ⟨"bale-2008", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is as tall as Brad and Brad is as tall as Seymour."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_30a : Datum :=
  { id := "bale2008_30a"
    source := ⟨"bale-2008", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "...I thought Seymour was six feet and five inches tall, but it turns out that he is only six feet and four inches. Still, six feet and four inches is quite tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("measurePhrase", "subject")] }

def ex_31a : Datum :=
  { id := "bale2008_31a"
    source := ⟨"bale-2008", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is taller than he is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct"), ("model", "measured"), ("subject", "s"), ("subjectScale", "height"), ("standard", "s"), ("standardScale", "width")] }

def ex_31b : Datum :=
  { id := "bale2008_31b"
    source := ⟨"bale-2008", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is wider than he is tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct"), ("model", "measured"), ("subject", "s"), ("subjectScale", "width"), ("standard", "s"), ("standardScale", "height")] }

def ex_34 : Datum :=
  { id := "bale2008_34"
    source := ⟨"bale-2008", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is taller than he is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct")] }

def ex_35 : Datum :=
  { id := "bale2008_35"
    source := ⟨"bale-2008", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is taller for a man than he is wide for a man."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("model", "men"), ("subject", "s"), ("subjectScale", "height"), ("standard", "s"), ("standardScale", "width")] }

def ex_37 : Datum :=
  { id := "bale2008_37"
    source := ⟨"bale-2008", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is a taller man than he is a wide man."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect"), ("model", "men"), ("subject", "s"), ("subjectScale", "height"), ("standard", "s"), ("standardScale", "width")] }

def ex_38a : Datum :=
  { id := "bale2008_38a"
    source := ⟨"bale-2008", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is very wide but he is not very tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_38b : Datum :=
  { id := "bale2008_38b"
    source := ⟨"bale-2008", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is wider than he is tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct")] }

def ex_39 : Datum :=
  { id := "bale2008_39"
    source := ⟨"bale-2008", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is a five foot tall man but he is not a five foot wide man."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_40 : Datum :=
  { id := "bale2008_40"
    source := ⟨"bale-2008", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Seymour is a taller man than he is a wide man."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_41a : Datum :=
  { id := "bale2008_41a"
    source := ⟨"bale-2008", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is more talented than Mary is beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_41b : Datum :=
  { id := "bale2008_41b"
    source := ⟨"bale-2008", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door is longer than the table is wide."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "direct")] }

def ex_42a : Datum :=
  { id := "bale2008_42a"
    source := ⟨"bale-2008", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is taller for a man than Mary is for a woman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def ex_42b : Datum :=
  { id := "bale2008_42b"
    source := ⟨"bale-2008", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is more intelligent than Marilyn Monroe was beautiful."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("comparison", "indirect")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b, ex_5a, ex_5b, ex_6a, ex_6b, ex_7a, ex_7b, ex_7c, ex_8a, ex_8c, ex_8d, ex_9, ex_11a, ex_11b, ex_14a, ex_14b, ex_18a, ex_18c, ex_18d, ex_19a, ex_19b, ex_22a, ex_22b, ex_25a, ex_25b, ex_25d, ex_26a, ex_30a, ex_31a, ex_31b, ex_34, ex_35, ex_37, ex_38a, ex_38b, ex_39, ex_40, ex_41a, ex_41b, ex_42a, ex_42b]

end Bale2008.Examples
