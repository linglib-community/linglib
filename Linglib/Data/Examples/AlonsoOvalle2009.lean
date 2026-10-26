module

public import Linglib.Data.Examples.Schema

/-!
# `AlonsoOvalle2009` — typed example data

Auto-generated from `Linglib/Data/Examples/AlonsoOvalle2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlonsoOvalle2009.Examples`.
-/

@[expose] public section

namespace AlonsoOvalle2009.Examples

def ex_1 : Datum :=
  { id := "alonsoovalle2009_1"
    source := ⟨"alonso-ovalle-2009", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If we had had good weather this summer or the sun had grown cold, we would have had a bumper crop."
    glossedTokens := []
    context := "The summer is over; visiting a farm, the owner complains about the weather and points to a bunch of immature pumpkins and ruined pumpkin plants."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "bumperCrop"), ("antecedent", "good weather or sun cold"), ("modal", "would")] }

def ex_15a : Datum :=
  { id := "alonsoovalle2009_15a"
    source := ⟨"dayal-1996", "p. 188"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(15a)"⟩
    language := "hind1269"
    primaryText := "jo laRkii khaRii hai vo lambii hai"
    glossedTokens := [("jo", "which"), ("laRkii", "girl"), ("khaRii", "standing"), ("hai", "be-present"), ("vo", "she"), ("lambii", "tall"), ("hai", "be-present")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "correlative"), ("number", "singular")] }

def ex_15b : Datum :=
  { id := "alonsoovalle2009_15b"
    source := ⟨"dayal-1996", "p. 192"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(15b)"⟩
    language := "hind1269"
    primaryText := "jo laRkiyaaN khaRii haiN ve lambii haiN"
    glossedTokens := [("jo", "which"), ("laRkiyaaN", "girls"), ("khaRii", "standing"), ("haiN", "be-present"), ("ve", "they"), ("lambii", "tall"), ("haiN", "be-present")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "correlative"), ("number", "plural")] }

def ex_15c : Datum :=
  { id := "alonsoovalle2009_15c"
    source := ⟨"dayal-1996", "p. 192"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(15c)"⟩
    language := "hind1269"
    primaryText := "jo do laRkiyaaN khaRii haiN ve lambii haiN"
    glossedTokens := [("jo", "which"), ("do", "two"), ("laRkiyaaN", "girls"), ("khaRii", "standing"), ("haiN", "be-present"), ("ve", "they"), ("lambii", "tall"), ("haiN", "be-present")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "correlative"), ("number", "plural")] }

def ex_29 : Datum :=
  { id := "alonsoovalle2009_29"
    source := ⟨"alonso-ovalle-2009", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is plain false that Hitler would have been pleased if Spain had joined Germany or the U.S."
    glossedTokens := []
    context := "Kratzer, p.c., a variation on an example in Nute 1980."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "hitler"), ("antecedent", "joined Germany or the U.S."), ("modal", "would"), ("polarity", "negated")] }

def ex_30a : Datum :=
  { id := "alonsoovalle2009_30a"
    source := ⟨"alonso-ovalle-2009", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hitler would have been pleased if Spain had joined Germany."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "hitler"), ("antecedent", "joined Germany"), ("modal", "would")] }

def ex_30b : Datum :=
  { id := "alonsoovalle2009_30b"
    source := ⟨"alonso-ovalle-2009", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hitler would have been pleased if Spain had joined the U.S."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "hitler"), ("antecedent", "joined the U.S."), ("modal", "would")] }

def ex_31 : Datum :=
  { id := "alonsoovalle2009_31"
    source := ⟨"alonso-ovalle-2009", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "...There is enough evidence showing that he might have objected to Spain joining the U.S. If she had joined Germany, he would have been pleased, of course."
    glossedTokens := []
    context := "Continuation of (29) (Kratzer, p.c.)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "continuation")] }

def ex_32 : Datum :=
  { id := "alonsoovalle2009_32"
    source := ⟨"alonso-ovalle-2009", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy didn't see the cats."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Sandy saw none of the cats", .acceptable), ("Sandy didn't see every cat", .unacceptable)]
    paperFeatures := [("phenomenon", "homogeneity")] }

def ex_34 : Datum :=
  { id := "alonsoovalle2009_34"
    source := ⟨"alonso-ovalle-2009", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is plain false that Sandy saw the cats."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Sandy saw none of the cats", .unacceptable)]
    paperFeatures := [("phenomenon", "homogeneity"), ("polarity", "wide-scope negation")] }

def ex_36 : Datum :=
  { id := "alonsoovalle2009_36"
    source := ⟨"lewis-1973b", "p. 1"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(36)"⟩
    language := "stan1293"
    primaryText := "If kangaroos had no tails, they would topple over."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "strengthening the antecedent"), ("role", "premise")] }

def ex_41b : Datum :=
  { id := "alonsoovalle2009_41b"
    source := ⟨"lewis-1973b", "p. 9"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(41b)"⟩
    language := "stan1293"
    primaryText := "If kangaroos had no tails but used crutches, they would topple over."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "strengthening the antecedent"), ("role", "conclusion")] }

def ex_40a : Datum :=
  { id := "alonsoovalle2009_40a"
    source := ⟨"von-fintel-1999", "p. 33"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(40a)"⟩
    language := "stan1293"
    primaryText := "If you had left any earlier, you would have missed the plane."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "any")] }

def ex_40b : Datum :=
  { id := "alonsoovalle2009_40b"
    source := ⟨"alonso-ovalle-2009", "(40b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you had ever heard my album, you would know that I could never consider the music business."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("npi", "ever")] }

def ex_42a : Datum :=
  { id := "alonsoovalle2009_42a"
    source := ⟨"lewis-1973b", "p. 33"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(42a)"⟩
    language := "stan1293"
    primaryText := "If Hoover had been born in Russia, he would have been a Communist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "hypothetical syllogism"), ("role", "premise")] }

def ex_42b : Datum :=
  { id := "alonsoovalle2009_42b"
    source := ⟨"lewis-1973b", "p. 33"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(42b)"⟩
    language := "stan1293"
    primaryText := "If Hoover had been a Communist, he would have been a traitor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "hypothetical syllogism"), ("role", "premise")] }

def ex_42c : Datum :=
  { id := "alonsoovalle2009_42c"
    source := ⟨"lewis-1973b", "p. 33"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(42c)"⟩
    language := "stan1293"
    primaryText := "If Hoover had been born in Russia, he would have been a traitor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "hypothetical syllogism"), ("role", "conclusion")] }

def ex_43a : Datum :=
  { id := "alonsoovalle2009_43a"
    source := ⟨"kratzer-1979", "p. 128"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "(43a)"⟩
    language := "stan1293"
    primaryText := "If Goethe had survived the year 1832, he would nevertheless be dead by now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "contraposition"), ("role", "premise")] }

def ex_43b : Datum :=
  { id := "alonsoovalle2009_43b"
    source := ⟨"alonso-ovalle-2009", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Goethe were alive now, he would have died in 1832."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "contraposition"), ("role", "conclusion")] }

def ex_49a : Datum :=
  { id := "alonsoovalle2009_49a"
    source := ⟨"alonso-ovalle-2009", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If we had had good weather this summer, we would have had a bumper crop."
    glossedTokens := []
    context := "The summer is over; visiting a farm, the owner complains about the weather and points to a bunch of immature pumpkins and ruined pumpkin plants."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "bumperCrop"), ("antecedent", "good weather"), ("modal", "would")] }

def ex_49b : Datum :=
  { id := "alonsoovalle2009_49b"
    source := ⟨"alonso-ovalle-2009", "(49b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the sun had grown cold, we would have had a bumper crop."
    glossedTokens := []
    context := "The summer is over; visiting a farm, the owner complains about the weather and points to a bunch of immature pumpkins and ruined pumpkin plants."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "bumperCrop"), ("antecedent", "sun cold"), ("modal", "would")] }

def ex_51 : Datum :=
  { id := "alonsoovalle2009_51"
    source := ⟨"alonso-ovalle-2009", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you had had a good magic book or you had been a newborn baby, you might have bent that fork too."
    glossedTokens := []
    context := "After a magic show in which the magician bent a fork with the power of his mind."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "fork"), ("antecedent", "magic book or newborn baby"), ("modal", "might")] }

def ex_58a : Datum :=
  { id := "alonsoovalle2009_58a"
    source := ⟨"alonso-ovalle-2009", "(58a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you had had a good magic book, you might have bent that fork."
    glossedTokens := []
    context := "After a magic show in which the magician bent a fork with the power of his mind."
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "fork"), ("antecedent", "magic book"), ("modal", "might")] }

def ex_58b : Datum :=
  { id := "alonsoovalle2009_58b"
    source := ⟨"alonso-ovalle-2009", "(58b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you had been a newborn baby, you might have bent that fork."
    glossedTokens := []
    context := "After a magic show in which the magician bent a fork with the power of his mind."
    judgment := .acceptable
    verdict := some false
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "fork"), ("antecedent", "newborn baby"), ("modal", "might")] }

def ex_64 : Datum :=
  { id := "alonsoovalle2009_64"
    source := ⟨"alonso-ovalle-2009", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you had had a good magic book, you would have bent that fork."
    glossedTokens := []
    context := "After a magic show in which the magician bent a fork with the power of his mind."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "fork"), ("antecedent", "magic book"), ("modal", "would")] }

def ex_65 : Datum :=
  { id := "alonsoovalle2009_65"
    source := ⟨"alonso-ovalle-2009", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Sandy does her homework or yours, she may eat this ice cream."
    glossedTokens := []
    context := "Mom, to Dad."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "may"), ("antecedent", "disjunctive")] }

def ex_66a : Datum :=
  { id := "alonsoovalle2009_66a"
    source := ⟨"alonso-ovalle-2009", "(66a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Sandy does her homework, she may eat this ice cream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "may")] }

def ex_66b : Datum :=
  { id := "alonsoovalle2009_66b"
    source := ⟨"alonso-ovalle-2009", "(66b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Sandy does your homework, she may eat this ice cream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "may")] }

def ex_67 : Datum :=
  { id := "alonsoovalle2009_67"
    source := ⟨"alonso-ovalle-2009", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Sandy does her homework or her sister's, she may eat this ice cream, but if she does her homework, she may not eat it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "may")] }

def ex_68b : Datum :=
  { id := "alonsoovalle2009_68b"
    source := ⟨"alonso-ovalle-2009", "(68b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It might be the case that if Sandy does her homework, she must eat this ice cream."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "must")] }

def ex_77 : Datum :=
  { id := "alonsoovalle2009_77"
    source := ⟨"alonso-ovalle-2009", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you had a good magic book or you were a newborn child, you might have bent that fork; but, for all I know, it is possible that if you have a good magic book you might not have bent that fork."
    glossedTokens := []
    context := "After a magic show in which the magician bent a fork with the power of his mind."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "might")] }

def ex_79 : Datum :=
  { id := "alonsoovalle2009_79"
    source := ⟨"alonso-ovalle-2009", "(79)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If we had had good weather this summer or the sun had grown cold, we might have had a bumper crop."
    glossedTokens := []
    context := "The summer is over; visiting a farm, the owner complains about the weather and points to a bunch of immature pumpkins and ruined pumpkin plants."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "bumperCrop"), ("antecedent", "good weather or sun cold"), ("modal", "might")] }

def ex_80 : Datum :=
  { id := "alonsoovalle2009_80"
    source := ⟨"alonso-ovalle-2009", "(80)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the U.S. devoted more than half of its budget to defense or to education, it would devote more than half of its budget to defense."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    verdict := some true
    alternatives := []
    readings := []
    paperFeatures := [("scenario", "budget"), ("antecedent", "defense or education"), ("modal", "would"), ("closure", "existential")] }

def ex_83 : Datum :=
  { id := "alonsoovalle2009_83"
    source := ⟨"alonso-ovalle-2009", "(83)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I earned at most $30,000 or more than a billion, I would surely earn at most $30,000."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "would"), ("verdict", "contradictory")] }

def ex_84a : Datum :=
  { id := "alonsoovalle2009_84a"
    source := ⟨"alonso-ovalle-2009", "(84a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I were to earn at most $30,000 or more than a billion, I would earn at most $30,000."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "paraphrase of (83)")] }

def ex_84b : Datum :=
  { id := "alonsoovalle2009_84b"
    source := ⟨"alonso-ovalle-2009", "(84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I might earn at most $30,000 or more than a billion, I would earn at most $30,000."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "paraphrase of (83)")] }

def ex_84c : Datum :=
  { id := "alonsoovalle2009_84c"
    source := ⟨"alonso-ovalle-2009", "(84c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Even) if it were possible that I earned at most $30,000 and it were also possible that I earned more than a billion, I would nevertheless earn at most $30,000."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "paraphrase of (83)")] }

def ex_85a : Datum :=
  { id := "alonsoovalle2009_85a"
    source := ⟨"alonso-ovalle-2009", "(85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the U.S. were to devote more than half of its budget to defense or education, it would devote more than half of its budget to defense."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "paraphrase of (80)")] }

def ex_85b : Datum :=
  { id := "alonsoovalle2009_85b"
    source := ⟨"alonso-ovalle-2009", "(85b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it were the case that the U.S. might devote more than half of its budget to defense or to education, it would devote more than half of its budget to defense."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "paraphrase of (80)")] }

def ex_85c : Datum :=
  { id := "alonsoovalle2009_85c"
    source := ⟨"alonso-ovalle-2009", "(85c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(Even) if it were possible that the U.S. devoted more than half of its budget to defense and it were possible that the U.S. devoted more than half of its budget to education, the U.S. would nevertheless devote more than half of its budget to defense."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("role", "paraphrase of (80)")] }

def fn12 : Datum :=
  { id := "alonsoovalle2009_fn12"
    source := ⟨"alonso-ovalle-2009", "fn. 12 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Let us suppose that John Kerry or Hillary Clinton became president. Then Bill Clinton would / might become ambassador to the United Nations."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("anaphor", "then"), ("role", "intersentential")] }

def fn18 : Datum :=
  { id := "alonsoovalle2009_fn18"
    source := ⟨"stalnaker-1984", "p. 144"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "fn. 18 (i)"⟩
    language := "stan1293"
    primaryText := "Would President Carter have appointed a woman to the Supreme Court last year if a vacancy had occurred? No, certainly not, although he might have appointed a woman."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "might")] }

def fn22 : Datum :=
  { id := "alonsoovalle2009_fn22"
    source := ⟨"alonso-ovalle-2009", "fn. 22 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John had picked a black ball or a red ball, he would have had 30% chances of winning."
    glossedTokens := []
    context := "(81) John is playing a game of luck with white, black, and red balls. We know (but he doesn't) that none of the white balls has a winning number, but that taken together 30% of the black and red balls have a winning number. John picked a ball, and lost."
    judgment := .acceptable
    alternatives := []
    readings := [("If John had picked a ball that wasn't white, he would have had 30% chances of winning", .acceptable)]
    paperFeatures := [("closure", "existential")] }

def bennettD : Datum :=
  { id := "alonsoovalle2009_bennettD"
    source := ⟨"bennett-2003", "D, pp. 168–170"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "§4 D"⟩
    language := "stan1293"
    primaryText := "If there had been rain or frost, the game would have been called off."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "simplification"), ("role", "premise")] }

def bennettDr : Datum :=
  { id := "alonsoovalle2009_bennettDr"
    source := ⟨"bennett-2003", "Dr, pp. 168–170"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "§4 Dr"⟩
    language := "stan1293"
    primaryText := "If it had rained, the game would have been called off."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "simplification"), ("role", "conclusion")] }

def bennettDf : Datum :=
  { id := "alonsoovalle2009_bennettDf"
    source := ⟨"bennett-2003", "Df, pp. 168–170"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "§4 Df"⟩
    language := "stan1293"
    primaryText := "If there had been frost, the game would have been called off."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "simplification"), ("role", "conclusion")] }

def lewis1 : Datum :=
  { id := "alonsoovalle2009_lewis1"
    source := ⟨"lewis-1977", "(1), pp. 360–361"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "§6 (1)"⟩
    language := "stan1293"
    primaryText := "If either Oswald had not fired or Kennedy had been in a bullet-proof car, then Kennedy would be alive today."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "disjunctive")] }

def lewis4 : Datum :=
  { id := "alonsoovalle2009_lewis4"
    source := ⟨"lewis-1977", "(4), pp. 360–361"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "§6 (4)"⟩
    language := "stan1293"
    primaryText := "I can lick any man in the house, or drink the lot of you under the table."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "disjunction under a modal")] }

def lewis5 : Datum :=
  { id := "alonsoovalle2009_lewis5"
    source := ⟨"lewis-1977", "(5), pp. 360–361"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "§6 (5)"⟩
    language := "stan1293"
    primaryText := "It is legal for you to report this as taxable income or for me to claim you as a dependent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "disjunction under a modal")] }

def lewis6 : Datum :=
  { id := "alonsoovalle2009_lewis6"
    source := ⟨"lewis-1977", "(6), pp. 360–361"⟩
    reportedIn := some ⟨"alonso-ovalle-2009", "§6 (6)"⟩
    language := "stan1293"
    primaryText := "Holmes now knows whether the butler did it or the gardener did."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "disjunction under whether")] }

def all : List Datum := [ex_1, ex_15a, ex_15b, ex_15c, ex_29, ex_30a, ex_30b, ex_31, ex_32, ex_34, ex_36, ex_41b, ex_40a, ex_40b, ex_42a, ex_42b, ex_42c, ex_43a, ex_43b, ex_49a, ex_49b, ex_51, ex_58a, ex_58b, ex_64, ex_65, ex_66a, ex_66b, ex_67, ex_68b, ex_77, ex_79, ex_80, ex_83, ex_84a, ex_84b, ex_84c, ex_85a, ex_85b, ex_85c, fn12, fn18, fn22, bennettD, bennettDr, bennettDf, lewis1, lewis4, lewis5, lewis6]

end AlonsoOvalle2009.Examples
