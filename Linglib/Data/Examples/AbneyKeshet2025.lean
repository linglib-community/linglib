module

public import Linglib.Data.Examples.Schema

/-!
# `AbneyKeshet2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AbneyKeshet2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AbneyKeshet2025.Examples`.
-/

@[expose] public section

namespace AbneyKeshet2025.Examples

def ex_10 : Datum :=
  { id := "abneykeshet2025_10"
    source := ⟨"abney-keshet-2025", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A dog appeared. It barked."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pronoun", "simple"), ("phenomenon", "cross-sentential anaphora")] }

def ex_15 : Datum :=
  { id := "abneykeshet2025_15"
    source := ⟨"geach-1962", "donkey sentence"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(15)"⟩
    language := "stan1293"
    primaryText := "Every farmer who owns a donkey pets it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "every"), ("pronoun", "donkey")] }

def ex_16 : Datum :=
  { id := "abneykeshet2025_16"
    source := ⟨"abney-keshet-2025", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most dogs bark."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "most")] }

def ex_20 : Datum :=
  { id := "abneykeshet2025_20"
    source := ⟨"abney-keshet-2025", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most farmers who own a donkey pet it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "most"), ("pronoun", "donkey")] }

def ex_45a : Datum :=
  { id := "abneykeshet2025_45a"
    source := ⟨"abney-keshet-2025", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Chris loves her."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pronoun", "simple")] }

def ex_47 : Datum :=
  { id := "abneykeshet2025_47"
    source := ⟨"abney-keshet-2025", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A red dog barked."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "indefinite")] }

def ex_66 : Datum :=
  { id := "abneykeshet2025_66"
    source := ⟨"abney-keshet-2025", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl wrote a paper."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "every")] }

def ex_80a : Datum :=
  { id := "abneykeshet2025_80a"
    source := ⟨"abney-keshet-2025", "(80a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most girls wrote a paper. All of them did something for a grade."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("them = the girls (the restriction set)", .acceptable)]
    paperFeatures := [("operator", "most"), ("pronoun", "summation"), ("antecedent", "restriction set")] }

def ex_80b : Datum :=
  { id := "abneykeshet2025_80b"
    source := ⟨"abney-keshet-2025", "(80b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most girls wrote a paper. But a few of them left it at home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("them = the girls that wrote a paper (the reference set)", .acceptable)]
    paperFeatures := [("operator", "most"), ("pronoun", "summation"), ("antecedent", "reference set")] }

def ex_80c : Datum :=
  { id := "abneykeshet2025_80c"
    source := ⟨"abney-keshet-2025", "(80c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most girls wrote a paper. In fact, they were mostly girls."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := [("they = the individuals that wrote a paper (the scope set)", .unacceptable)]
    paperFeatures := [("operator", "most"), ("pronoun", "summation"), ("antecedent", "scope set")] }

def ex_98 : Datum :=
  { id := "abneykeshet2025_98"
    source := ⟨"abney-keshet-2025", "(98)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl wrote a paper. They are on Ms. Marple's desk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("they = the papers the girls wrote", .acceptable)]
    paperFeatures := [("operator", "every"), ("pronoun", "summation")] }

def ex_101 : Datum :=
  { id := "abneykeshet2025_101"
    source := ⟨"abney-keshet-2025", "(101)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most dogs bark. They are loud."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("they = the dogs that bark", .acceptable)]
    paperFeatures := [("operator", "most"), ("pronoun", "summation")] }

def ex_105 : Datum :=
  { id := "abneykeshet2025_105"
    source := ⟨"nouwen-2003", "(5.8)"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(105)"⟩
    language := "stan1293"
    primaryText := "Three students each wrote exactly two papers. They each sent them to L&P."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("distributive: each student sent in their own two papers", .acceptable), ("collective over the papers: each student sent all six papers", .acceptable)]
    paperFeatures := [("operator", "each"), ("pronoun", "summation")] }

def ex_106 : Datum :=
  { id := "abneykeshet2025_106"
    source := ⟨"brasoveanu-2008", "(8)"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(106)"⟩
    language := "stan1293"
    primaryText := "Every parent who gives three balloons to two boys expects them to end up fighting (each other) for them."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("collective: all the boys, all the balloons", .marginal)]
    paperFeatures := [("operator", "every"), ("pronoun", "summation")] }

def ex_107a : Datum :=
  { id := "abneykeshet2025_107a"
    source := ⟨"abney-keshet-2025", "(107a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every parent who had two children at Tappan Middle School was pleased when they (all) formed a rock band, the Tappin' Twofers, just for kids with siblings at the school."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("collective: all the children", .acceptable)]
    paperFeatures := [("operator", "every"), ("pronoun", "summation")] }

def ex_107b : Datum :=
  { id := "abneykeshet2025_107b"
    source := ⟨"abney-keshet-2025", "(107b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who ordered two or more drinks decided it was easier to just split the bill for them (all) evenly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("collective: all the drinks", .acceptable)]
    paperFeatures := [("operator", "everyone"), ("pronoun", "summation")] }

def ex_108 : Datum :=
  { id := "abneykeshet2025_108"
    source := ⟨"abney-keshet-2025", "(108)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some girls were having lunch in the cafeteria. They waved to some boys having lunch there, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Some girls were having lunch in the cafeteria. They waved to some other girls having lunch there, too.", .acceptable)]
    readings := []
    paperFeatures := [("operator", "some"), ("pronoun", "simple")] }

def ex_109 : Datum :=
  { id := "abneykeshet2025_109"
    source := ⟨"abney-keshet-2025", "(109)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most girls were having lunch in the cafeteria. They waved to some boys having lunch there, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Most girls were having lunch in the cafeteria. They waved to some other girls having lunch there, too.", .unacceptable)]
    readings := []
    paperFeatures := [("operator", "most"), ("pronoun", "summation")] }

def ex_110 : Datum :=
  { id := "abneykeshet2025_110"
    source := ⟨"jacobson-2000", "paycheck sentence"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(110)"⟩
    language := "stan1293"
    primaryText := "The woman who saved her paycheck was wiser than the woman who spent it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("pronoun", "paycheck")] }

def ex_111 : Datum :=
  { id := "abneykeshet2025_111"
    source := ⟨"abney-keshet-2025", "(111)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Almost every girl brought the diorama she made to class. Very few of them forgot it at home."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = the diorama made by each of the few", .acceptable)]
    paperFeatures := [("operator", "almost every"), ("pronoun", "paycheck")] }

def ex_113 : Datum :=
  { id := "abneykeshet2025_113"
    source := ⟨"abney-keshet-2025", "(113)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who owns an umbrella brought it to school today."
    glossedTokens := []
    context := "Some people own more than one umbrella; each brought only one, or a few brought more than one."
    judgment := .acceptable
    contrasts := []
    readings := [("weak: one umbrella per owner suffices", .acceptable)]
    paperFeatures := [("operator", "everyone"), ("pronoun", "donkey")] }

def ex_114 : Datum :=
  { id := "abneykeshet2025_114"
    source := ⟨"abney-keshet-2025", "(114)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who owns an umbrella brought it to school today. They are in that rack."
    glossedTokens := []
    context := "At least one person brought more than one umbrella."
    judgment := .acceptable
    contrasts := []
    readings := [("they = all the umbrellas actually brought, not one per owner", .acceptable)]
    paperFeatures := [("operator", "everyone"), ("pronoun", "summation")] }

def ex_115 : Datum :=
  { id := "abneykeshet2025_115"
    source := ⟨"abney-keshet-2025", "(115)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone who brought something valuable locked it up."
    glossedTokens := []
    context := "A few people brought more than one valuable item."
    judgment := .acceptable
    contrasts := []
    readings := [("strong: each locked up all their valuables", .acceptable)]
    paperFeatures := [("operator", "everyone"), ("pronoun", "donkey")] }

def ex_117a : Datum :=
  { id := "abneykeshet2025_117a"
    source := ⟨"abney-keshet-2025", "(117a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Almost every student brought an umbrella today. Most (of them) used it, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "most"), ("pronoun", "donkey"), ("phenomenon", "quantificational subordination")] }

def ex_117b : Datum :=
  { id := "abneykeshet2025_117b"
    source := ⟨"abney-keshet-2025", "(117b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Almost every student brought an umbrella today. Every one (of them) who used it stayed dry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "every"), ("pronoun", "donkey"), ("phenomenon", "quantificational subordination")] }

def ex_130a : Datum :=
  { id := "abneykeshet2025_130a"
    source := ⟨"abney-keshet-2025", "(130a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If she has a pet, it must be a donkey."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "must"), ("pronoun", "donkey")] }

def ex_131a : Datum :=
  { id := "abneykeshet2025_131a"
    source := ⟨"abney-keshet-2025", "(131a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It might rain."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "might")] }

def ex_132 : Datum :=
  { id := "abneykeshet2025_132"
    source := ⟨"roberts-1987", "modal subordination"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(132)"⟩
    language := "stan1293"
    primaryText := "A wolf might enter. It would eat Tasty Tim first."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "might"), ("pronoun", "donkey"), ("phenomenon", "modal subordination")] }

def ex_134 : Datum :=
  { id := "abneykeshet2025_134"
    source := ⟨"abney-keshet-2025", "(134)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He doesn't have a pen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "negation")] }

def ex_135 : Datum :=
  { id := "abneykeshet2025_135"
    source := ⟨"sells-1985", "modal subordination from negation"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(135)"⟩
    language := "stan1293"
    primaryText := "He doesn't own a car. It would be too expensive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "negation"), ("phenomenon", "modal subordination")] }

def ex_138a : Datum :=
  { id := "abneykeshet2025_138a"
    source := ⟨"abney-keshet-2025", "(138a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not like he doesn't own a car. It is just in the shop."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("it = the car he owns", .acceptable)]
    paperFeatures := [("operator", "negation"), ("pronoun", "summation")] }

def ex_139 : Datum :=
  { id := "abneykeshet2025_139"
    source := ⟨"abney-keshet-2025", "(139)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He doesn't own a car. It is in the shop."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "negation"), ("pronoun", "summation")] }

def ex_140 : Datum :=
  { id := "abneykeshet2025_140"
    source := ⟨"abney-keshet-2025", "(140)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks I don't have a child, but I am a parent. He lives in England."
    glossedTokens := []
    context := "Suggested by Matthew Mandelkern as a possible overgeneration."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "negation"), ("pronoun", "summation")] }

def ex_141a : Datum :=
  { id := "abneykeshet2025_141a"
    source := ⟨"abney-keshet-2025", "(141a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks I don't have a son, but she's wrong. She just hasn't met him yet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "negation"), ("pronoun", "summation")] }

def ex_141b : Datum :=
  { id := "abneykeshet2025_141b"
    source := ⟨"abney-keshet-2025", "(141b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary thinks I don't have any children, but I am actually a father several times over. She just hasn't ever met any of them!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "negation"), ("pronoun", "summation")] }

def ex_142 : Datum :=
  { id := "abneykeshet2025_142"
    source := ⟨"roberts-1987", "bathroom sentence"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(142)"⟩
    language := "stan1293"
    primaryText := "Either there is no bathroom here or it's in a funny place."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "disjunction"), ("pronoun", "summation")] }

def ex_146a : Datum :=
  { id := "abneykeshet2025_146a"
    source := ⟨"abney-keshet-2025", "(146a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every monarchy cherishes its monarch."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "every"), ("phenomenon", "presupposition projection")] }

def ex_146b : Datum :=
  { id := "abneykeshet2025_146b"
    source := ⟨"abney-keshet-2025", "(146b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Some people in my apartment building who own a bicycle own a car, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "some"), ("phenomenon", "presupposition projection")] }

def ex_146c : Datum :=
  { id := "abneykeshet2025_146c"
    source := ⟨"abney-keshet-2025", "(146c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Most of my friends who used to smoke have quit smoking by now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "most"), ("phenomenon", "presupposition projection")] }

def ex_147 : Datum :=
  { id := "abneykeshet2025_147"
    source := ⟨"heim-1992", "(53)"⟩
    reportedIn := some ⟨"abney-keshet-2025", "(147)"⟩
    language := "stan1293"
    primaryText := "John believes that Mary is the only one here, but he wishes that Susan were here too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "believe"), ("phenomenon", "presupposition projection")] }

def ex_150a : Datum :=
  { id := "abneykeshet2025_150a"
    source := ⟨"abney-keshet-2025", "(150a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the 1700s, every European country was a monarchy. Most of them cherished their monarchs."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "most"), ("phenomenon", "presupposition projection"), ("phenomenon", "quantificational subordination")] }

def ex_150b : Datum :=
  { id := "abneykeshet2025_150b"
    source := ⟨"abney-keshet-2025", "(150b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone in my apartment building owns a bicycle. Some of them own a car, too."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "some"), ("phenomenon", "presupposition projection"), ("phenomenon", "quantificational subordination")] }

def ex_150c : Datum :=
  { id := "abneykeshet2025_150c"
    source := ⟨"abney-keshet-2025", "(150c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every friend of mine used to smoke. But most of them have quit smoking by now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("operator", "most"), ("phenomenon", "presupposition projection"), ("phenomenon", "quantificational subordination")] }

def all : List Datum := [ex_10, ex_15, ex_16, ex_20, ex_45a, ex_47, ex_66, ex_80a, ex_80b, ex_80c, ex_98, ex_101, ex_105, ex_106, ex_107a, ex_107b, ex_108, ex_109, ex_110, ex_111, ex_113, ex_114, ex_115, ex_117a, ex_117b, ex_130a, ex_131a, ex_132, ex_134, ex_135, ex_138a, ex_139, ex_140, ex_141a, ex_141b, ex_142, ex_146a, ex_146b, ex_146c, ex_147, ex_150a, ex_150b, ex_150c]

end AbneyKeshet2025.Examples
