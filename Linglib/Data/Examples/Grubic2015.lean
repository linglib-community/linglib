module

public import Linglib.Data.Examples.Schema

/-!
# `Grubic2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Grubic2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Grubic2015.Examples`.
-/

@[expose] public section

namespace Grubic2015.Examples

def ex_6_24 : Datum :=
  { id := "grubic2015_6_24"
    source := ⟨"grubic-2015", "ch. 6 (24)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ne sakatari yak'i."
    glossedTokens := [("Ne", "1SG.DEP"), ("sakatari", "secretary"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complement exclusion: I am nothing else in addition", .acceptable), ("rank order: I am nothing better", .acceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "predicate")] }

def ex_6_25a : Datum :=
  { id := "grubic2015_6_25a"
    source := ⟨"grubic-2015", "ch. 6 (25a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "ngam1282"
    primaryText := "Salko bano=i Dimza yak'i."
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Dimza", "Dimza"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedSubjectFocus"), ("inference", "Dimza built a house"), ("inference", "nobody else built a house")] }

def ex_6_25b : Datum :=
  { id := "grubic2015_6_25b"
    source := ⟨"grubic-2015", "ch. 6 (25b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Dimza yak'i bu."
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Dimza", "Dimza"), ("yak'i", "only"), ("bu.", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedSubjectFocus"), ("inference", "Dimza built a house"), ("inference", "other people also built a house")] }

def ex_6_25c : Datum :=
  { id := "grubic2015_6_25c"
    source := ⟨"grubic-2015", "ch. 6 (25c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "ngam1282"
    primaryText := "Salko bano=i Dimza yak'i ɗo?"
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Dimza", "Dimza"), ("yak'i", "only"), ("ɗo?", "Q")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedSubjectFocus"), ("inference", "Dimza built a house")] }

def ex_6_26 : Datum :=
  { id := "grubic2015_6_26"
    source := ⟨"grubic-2015", "ch. 6 (26)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Esha=i Sama yak'i nzono, ke esha Hawwa nzono."
    glossedTokens := [("Esha=i", "call.PFV=BM"), ("Sama", "Sama"), ("yak'i", "only"), ("nzono,", "yesterday"), ("ke", "also"), ("esha", "call.PFV"), ("Hawwa", "Hawwa"), ("nzono.", "yesterday")]
    context := "Who did Njelu call yesterday?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedObjectFocus")] }

def ex_6_28 : Datum :=
  { id := "grubic2015_6_28"
    source := ⟨"grubic-2015", "ch. 6 (28)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ne'e yak ne wa ampani yam ki korino bu."
    glossedTokens := [("Ne'e", "1SG"), ("yak", "only"), ("ne", "1SG"), ("wa", "get.PFV"), ("ampani", "harvest"), ("yam", "a.lot"), ("ki", "at"), ("korino", "farm=1SG.POSS"), ("bu.", "NEG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "predicate")] }

def ex_6_140 : Datum :=
  { id := "grubic2015_6_140"
    source := ⟨"grubic-2015", "ch. 6 (140)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule yak salko bano mano."
    glossedTokens := [("Kule", "Kule"), ("yak", "only"), ("salko", "build.PFV"), ("bano", "house"), ("mano.", "last.year")]
    context := "Kule wanted to build a house and a granary last year."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "unmarkedObjectFocus")] }

def ex_6_145a : Datum :=
  { id := "grubic2015_6_145a"
    source := ⟨"grubic-2015", "ch. 6 (145A)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "O'o, Kule yak onto agoggo."
    glossedTokens := [("O'o,", "no"), ("Kule", "Kule"), ("yak", "only"), ("onto", "give.PFV.3SG.F"), ("agoggo.", "watch")]
    context := "Did Kule give a watch to Dimza and Jajei?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "dependentPronoun")] }

def ex_6_145b : Datum :=
  { id := "grubic2015_6_145b"
    source := ⟨"grubic-2015", "ch. 6 (145A')"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "O'o, Kule onko agoggo=i ki te yak'i."
    glossedTokens := [("O'o,", "no"), ("Kule", "Kule"), ("onko", "give.PFV"), ("agoggo=i", "watch=BM"), ("ki", "to"), ("te", "3SG.F"), ("yak'i.", "only")]
    context := "Did Kule give a watch to Dimza and Jajei?"
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "independentPronoun")] }

def ex_6_148a : Datum :=
  { id := "grubic2015_6_148a"
    source := ⟨"grubic-2015", "ch. 6 (148a)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa=s, ne moishe Daho a esha=i te yak'i."
    glossedTokens := [("Hawwa=s,", "Hawwa=DEF.DET.F"), ("ne", "1SG"), ("moishe", "see.HAB"), ("Daho", "Daho"), ("a", "3SG.HAB"), ("esha=i", "call.HAB=BM"), ("te", "3SG.F"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the only person that Daho calls is Hawwa", .acceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "resumptivePronoun")] }

def ex_6_148b : Datum :=
  { id := "grubic2015_6_148b"
    source := ⟨"grubic-2015", "ch. 6 (148b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa=s, ne moishe Daho a esha yak'i."
    glossedTokens := [("Hawwa=s,", "Hawwa=DEF.DET.F"), ("ne", "1SG"), ("moishe", "see.HAB"), ("Daho", "Daho"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the only person that Daho calls is Hawwa", .unacceptable), ("Daho does nothing but call", .acceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "topicalizedGap")] }

def ex_6_149 : Datum :=
  { id := "grubic2015_6_149"
    source := ⟨"grubic-2015", "ch. 6 (149)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa=s, ne moishe Daho lei ki tomiya a esha."
    glossedTokens := [("Hawwa=s,", "Hawwa=DEF.DET.F"), ("ne", "1SG"), ("moishe", "see.HAB"), ("Daho", "Daho"), ("lei ki tomiya", "always"), ("a", "3SG.HAB"), ("esha.", "call.HAB")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("whenever Daho calls somebody, she calls Hawwa", .acceptable)]
    paperFeatures := [("particle", "leiKiTomiya"), ("configuration", "topicalizedGap")] }

def ex_6_150a : Datum :=
  { id := "grubic2015_6_150a"
    source := ⟨"grubic-2015", "ch. 6 (150a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "ngam1282"
    primaryText := "Hasha hoti maɗɗi a esha Lakka, Gamba me esha=i te yak'i."
    glossedTokens := [("Hasha", "Hasha"), ("hoti", "day"), ("maɗɗi", "some"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("Lakka,", "Lakka"), ("Gamba", "Gamba"), ("me", "but"), ("esha=i", "call.HAB=BM"), ("te", "3SG.F"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "focusedPronoun")] }

def ex_6_150b : Datum :=
  { id := "grubic2015_6_150b"
    source := ⟨"grubic-2015", "ch. 6 (150b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hasha hoti maɗɗi a esha Lakka, Gambo me a esha yak'i."
    glossedTokens := [("Hasha", "Hasha"), ("hoti", "day"), ("maɗɗi", "some"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("Lakka,", "Lakka"), ("Gambo", "Gamba"), ("me", "but"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("yak'i.", "only")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "elidedPronoun")] }

def ex_6_151 : Datum :=
  { id := "grubic2015_6_151"
    source := ⟨"grubic-2015", "ch. 6 (151)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hasha hoti maɗɗi a esha Lakka, Gambo me lei ki tomiya a esha."
    glossedTokens := [("Hasha", "Hasha"), ("hoti", "day"), ("maɗɗi", "some"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("Lakka,", "Lakka"), ("Gambo", "Gamba"), ("me", "but"), ("lei ki tomiya", "always"), ("a", "3SG.HAB"), ("esha.", "call.HAB")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "leiKiTomiya"), ("configuration", "elidedPronoun")] }

def ex_6_153 : Datum :=
  { id := "grubic2015_6_153"
    source := ⟨"grubic-2015", "ch. 6 (153)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Biya ma maranko shinkafa a tishe yak'i."
    glossedTokens := [("Biya", "people"), ("ma", "REL"), ("maranko", "farm.PL.PFV"), ("shinkafa", "rice"), ("a", "3SG.HAB"), ("tishe", "eat.HAB"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("they don't sell it or give it out", .acceptable), ("they eat nothing else", .unacceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "elidedObject")] }

def ex_6_158 : Datum :=
  { id := "grubic2015_6_158"
    source := ⟨"grubic-2015", "ch. 6 (158)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Samaye gitkok tishe=i jarabawa=to yak'i."
    glossedTokens := [("Samaye", "Samaye"), ("gitkok", "be.able.PFV.TOT"), ("tishe=i", "eat.HAB=BM"), ("jarabawa=to", "exam=3SG.F.POSS"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "presupposition")] }

def ex_6_159 : Datum :=
  { id := "grubic2015_6_159"
    source := ⟨"grubic-2015", "ch. 6 (159)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Samaye lei ki tomiya a gishentik tina=i jarabawa=to."
    glossedTokens := [("Samaye", "Samaye"), ("lei ki tomiya", "always"), ("a", "3SG.HAB"), ("gishentik", "be.able.HAB.TOT"), ("tina=i", "eat.FUT=BM"), ("jarabawa=to.", "exam=3SG.F.POSS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("whenever she tries, she passes", .acceptable)]
    paperFeatures := [("particle", "leiKiTomiya"), ("configuration", "presupposition")] }

def ex_6_160 : Datum :=
  { id := "grubic2015_6_160"
    source := ⟨"grubic-2015", "ch. 6 (160)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Si onko agoggo=i ki Shuwa, si ke ono."
    glossedTokens := [("Si", "3SG.M"), ("onko", "give.PFV"), ("agoggo=i", "watch=BM"), ("ki", "to"), ("Shuwa,", "Shuwa"), ("si", "3SG.M"), ("ke", "also"), ("ono.", "give.1SG.DEP")]
    context := "Whom did Kule give a watch?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "dependentPronoun")] }

def ex_6_162a : Datum :=
  { id := "grubic2015_6_162a"
    source := ⟨"grubic-2015", "ch. 6 (162A)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule esha=i Dimza, ke esha=i ne'e."
    glossedTokens := [("Kule", "Kule"), ("esha=i", "call.PFV=BM"), ("Dimza,", "Dimza"), ("ke", "also"), ("esha=i", "call.PFV=BM"), ("ne'e.", "1SG")]
    context := "Whom did Kule call?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "independentPronoun")] }

def ex_6_162b : Datum :=
  { id := "grubic2015_6_162b"
    source := ⟨"grubic-2015", "ch. 6 (162A')"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule esha=i Dimza ke eshino."
    glossedTokens := [("Kule", "Kule"), ("esha=i", "call.PFV=BM"), ("Dimza", "Dimza"), ("ke", "also"), ("eshino.", "call.PFV.TOT.1SG")]
    context := "Whom did Kule call?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "dependentPronoun")] }

def ex_6_163 : Datum :=
  { id := "grubic2015_6_163"
    source := ⟨"grubic-2015", "ch. 6 (163)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ke salko bano."
    glossedTokens := [("Ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    context := "I know that Hawwa built a house, but what about Kule? What did he build?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "elidedTopicalSubject")] }

def ex_6_164 : Datum :=
  { id := "grubic2015_6_164"
    source := ⟨"grubic-2015", "ch. 6 (164)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule onko agoggo=i ki Shuwa, ke har ono."
    glossedTokens := [("Kule", "Kule"), ("onko", "give.PFV"), ("agoggo=i", "watch=BM"), ("ki", "to"), ("Shuwa,", "Shuwa"), ("ke", "and"), ("har", "even"), ("ono.", "give.PFV.1SG.DEP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "har"), ("configuration", "dependentPronoun")] }

def ex_6_165 : Datum :=
  { id := "grubic2015_6_165"
    source := ⟨"grubic-2015", "ch. 6 (165)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa salko bano, Kule ke salko bano."
    glossedTokens := [("Hawwa", "Hawwa"), ("salko", "build.PFV"), ("bano,", "house"), ("Kule", "Kule"), ("ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "preverbalSubject")] }

def ex_6_166 : Datum :=
  { id := "grubic2015_6_166"
    source := ⟨"grubic-2015", "ch. 6 (166)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Dimza yak salko bano."
    glossedTokens := [("Dimza", "Dimza"), ("yak", "only"), ("salko", "build.PFV"), ("bano.", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "unmarkedObjectFocus"), ("inference", "Dimza didn't build anything else"), ("inference", "he was expected to build more"), ("inference", "Dimza built a house")] }

def ex_6_167 : Datum :=
  { id := "grubic2015_6_167"
    source := ⟨"grubic-2015", "ch. 6 (167)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Dimza ke salko bano."
    glossedTokens := [("Dimza", "Dimza"), ("ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "unmarkedObjectFocus"), ("inference", "Dimza built a house"), ("inference", "Dimza built something else")] }

def ex_6_168 : Datum :=
  { id := "grubic2015_6_168"
    source := ⟨"grubic-2015", "ch. 6 (168)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Dimza har salko bano."
    glossedTokens := [("Dimza", "Dimza"), ("har", "even"), ("salko", "build.PFV"), ("bano.", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "har"), ("configuration", "unmarkedObjectFocus"), ("inference", "Dimza built a house"), ("inference", "he was expected to build less"), ("inference", "Dimza built something else")] }

def ex_6_169 : Datum :=
  { id := "grubic2015_6_169"
    source := ⟨"grubic-2015", "ch. 6 (169)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ne sakatari yak'i."
    glossedTokens := [("Ne", "1SG"), ("sakatari", "secretary"), ("yak'i.", "only")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "predicate"), ("inference", "the speaker is nothing better than a secretary"), ("inference", "the speaker was expected to be something better")] }

def ex_6_170 : Datum :=
  { id := "grubic2015_6_170"
    source := ⟨"grubic-2015", "ch. 6 (170)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Bah malum har'i."
    glossedTokens := [("Bah", "Bah"), ("malum", "teacher"), ("har'i.", "even")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "har"), ("configuration", "predicate"), ("inference", "Bah is a teacher"), ("inference", "he was expected to be something worse")] }

def ex_7_41 : Datum :=
  { id := "grubic2015_7_41"
    source := ⟨"grubic-2015", "ch. 7 (41)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kaja mato=i Hawwa, salko bano=i ke Kule."
    glossedTokens := [("Kaja", "buy.PFV"), ("mato=i", "car=BM"), ("Hawwa,", "Hawwa"), ("salko", "build.PFV"), ("bano=i", "house=BM"), ("ke", "also"), ("Kule.", "Kule")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "distinctBackgroundDistinctFocus")] }

def ex_7_42 : Datum :=
  { id := "grubic2015_7_42"
    source := ⟨"grubic-2015", "ch. 7 (42)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Kule, kaja mato=i ke Kule."
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Kule,", "Kule"), ("kaja", "buy.PFV"), ("mato=i", "car=BM"), ("ke", "also"), ("Kule.", "Kule")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "distinctBackgroundParallelFocus")] }

def ex_7_43 : Datum :=
  { id := "grubic2015_7_43"
    source := ⟨"grubic-2015", "ch. 7 (43)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule salko makaranta mano, Kule ke salko bano mano."
    glossedTokens := [("Kule", "Kule"), ("salko", "build.PFV"), ("makaranta", "school"), ("mano,", "last.year"), ("Kule", "Kule"), ("ke", "also"), ("salko", "build.PFV"), ("bano", "house"), ("mano.", "last.year")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "parallelUnmarkedBackground")] }

def ex_7_44 : Datum :=
  { id := "grubic2015_7_44"
    source := ⟨"grubic-2015", "ch. 7 (44)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Hawwa, salko bano=i ke Kule."
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Hawwa,", "Hawwa"), ("salko", "build.PFV"), ("bano=i", "house=BM"), ("ke", "also"), ("Kule.", "Kule")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "parallelMarkedBackground")] }

def ex_7_46 : Datum :=
  { id := "grubic2015_7_46"
    source := ⟨"grubic-2015", "ch. 7 (46)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Bei a ina ham ɗoshi, ke a ina ham tuha ke'e."
    glossedTokens := [("Bei", "maybe"), ("a", "3SG"), ("ina", "do.FUT"), ("ham", "water"), ("ɗoshi,", "tomorrow"), ("ke", "and"), ("a", "3SG"), ("ina", "do.FUT"), ("ham", "water"), ("tuha", "day.after.tomorrow"), ("ke'e.", "also")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "modalizedAntecedent")] }

def ex_7_48 : Datum :=
  { id := "grubic2015_7_48"
    source := ⟨"grubic-2015", "ch. 7 (48)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Hawwa, Kule ke salko bano."
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Hawwa,", "Hawwa"), ("Kule", "Kule"), ("ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "nonParallel")] }

def ex_7_49 : Datum :=
  { id := "grubic2015_7_49"
    source := ⟨"grubic-2015", "ch. 7 (49)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Hawwa, ke salko bano=i ke Kule."
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Hawwa,", "Hawwa"), ("ke", "also"), ("salko", "build.PFV"), ("bano=i", "house=BM"), ("ke", "also"), ("Kule.", "Kule")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "parallelMarkedBackground")] }

def all : List Datum := [ex_6_24, ex_6_25a, ex_6_25b, ex_6_25c, ex_6_26, ex_6_28, ex_6_140, ex_6_145a, ex_6_145b, ex_6_148a, ex_6_148b, ex_6_149, ex_6_150a, ex_6_150b, ex_6_151, ex_6_153, ex_6_158, ex_6_159, ex_6_160, ex_6_162a, ex_6_162b, ex_6_163, ex_6_164, ex_6_165, ex_6_166, ex_6_167, ex_6_168, ex_6_169, ex_6_170, ex_7_41, ex_7_42, ex_7_43, ex_7_44, ex_7_46, ex_7_48, ex_7_49]

end Grubic2015.Examples
