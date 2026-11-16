module

public import Linglib.Data.Examples.Schema

/-!
# `DeMarneffeNivre2019` — typed example data

Auto-generated from `Linglib/Data/Examples/DeMarneffeNivre2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DeMarneffeNivre2019.Examples`.
-/

@[expose] public section

namespace DeMarneffeNivre2019.Examples

def fig1 : Datum :=
  { id := "demarneffenivre2019_fig1"
    source := ⟨"de-marneffe-nivre-2019", "Figure 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "small dogs chase cats happily"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "dependencyTree"), ("projective", "yes")] }

def fig2 : Datum :=
  { id := "demarneffenivre2019_fig2"
    source := ⟨"de-marneffe-nivre-2019", "Figure 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dogs chase cats and cars"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "coordination"), ("projective", "yes")] }

def fig3 : Datum :=
  { id := "demarneffenivre2019_fig3"
    source := ⟨"de-marneffe-nivre-2019", "Figure 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "bigger dogs than mine"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "projectivity"), ("projective", "no")] }

def fig4 : Datum :=
  { id := "demarneffenivre2019_fig4"
    source := ⟨"de-marneffe-nivre-2019", "Figure 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue believes that Kim will rely on her"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "headChoice"), ("projective", "yes")] }

def ex_1a : Datum :=
  { id := "demarneffenivre2019_1a"
    source := ⟨"de-marneffe-nivre-2019", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "While it was snowing, I went for a run."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "wordOrder"), ("adverbialClause", "initial")] }

def ex_1b : Datum :=
  { id := "demarneffenivre2019_1b"
    source := ⟨"de-marneffe-nivre-2019", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I went for a run, while it was snowing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "wordOrder"), ("adverbialClause", "final")] }

def ex_2a : Datum :=
  { id := "demarneffenivre2019_2a"
    source := ⟨"de-marneffe-nivre-2019", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She threw out the bin with old trash."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "dependencyLength"), ("particle", "adjacent"), ("preferred", "yes")] }

def ex_2b : Datum :=
  { id := "demarneffenivre2019_2b"
    source := ⟨"de-marneffe-nivre-2019", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She threw the bin with old trash out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "dependencyLength"), ("particle", "postposed"), ("preferred", "no")] }

def ex_3a : Datum :=
  { id := "demarneffenivre2019_3a"
    source := ⟨"de-marneffe-nivre-2019", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She threw out the bin."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "dependencyLength"), ("particle", "adjacent"), ("preferred", "neither")] }

def ex_3b : Datum :=
  { id := "demarneffenivre2019_3b"
    source := ⟨"de-marneffe-nivre-2019", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She threw the bin out."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "dependencyLength"), ("particle", "postposed"), ("preferred", "neither")] }

def ex_4a : Datum :=
  { id := "demarneffenivre2019_4a"
    source := ⟨"gibson-1998", "(1a)"⟩
    reportedIn := some ⟨"de-marneffe-nivre-2019", "(4a)"⟩
    language := "stan1293"
    primaryText := "The reporter who the senator attacked admitted the error."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "dependencyLength"), ("relativeClause", "object")] }

def ex_4b : Datum :=
  { id := "demarneffenivre2019_4b"
    source := ⟨"gibson-1998", "(1b)"⟩
    reportedIn := some ⟨"de-marneffe-nivre-2019", "(4b)"⟩
    language := "stan1293"
    primaryText := "The reporter who attacked the senator admitted the error."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "dependencyLength"), ("relativeClause", "subject")] }

def ex_5 : Datum :=
  { id := "demarneffenivre2019_5"
    source := ⟨"de-marneffe-nivre-2019", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter is her older brother, Oliver her youngest."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "ellipsis")] }

def fig5_en : Datum :=
  { id := "demarneffenivre2019_fig5_en"
    source := ⟨"de-marneffe-nivre-2019", "Figure 5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the houses are new"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "nonverbalPredication"), ("copula", "overt"), ("definiteness", "determiner")] }

def fig5_sv : Datum :=
  { id := "demarneffenivre2019_fig5_sv"
    source := ⟨"de-marneffe-nivre-2019", "Figure 5"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "husen är nya"
    glossedTokens := [("husen", "the-houses"), ("är", "are"), ("nya", "new")]
    glossedWords := [⟨['h', 'u', 's', 'e', 'n'], ['t', 'h', 'e', '-', 'h', 'o', 'u', 's', 'e', 's'], []⟩, ⟨['ä', 'r'], ['a', 'r', 'e'], [⟨['ä', 'r'], ['a', 'r', 'e'], none⟩]⟩, ⟨['n', 'y', 'a'], ['n', 'e', 'w'], [⟨['n', 'y', 'a'], ['n', 'e', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "nonverbalPredication"), ("copula", "overt"), ("definiteness", "inflection")] }

def fig5_wsk : Datum :=
  { id := "demarneffenivre2019_fig5_wsk"
    source := ⟨"de-marneffe-nivre-2019", "Figure 5"⟩
    reportedIn := none
    language := "wask1241"
    primaryText := "kawam mu ititi"
    glossedTokens := [("kawam", "houses"), ("mu", "the"), ("ititi", "new")]
    glossedWords := [⟨['k', 'a', 'w', 'a', 'm'], ['h', 'o', 'u', 's', 'e', 's'], [⟨['k', 'a', 'w', 'a', 'm'], ['h', 'o', 'u', 's', 'e', 's'], none⟩]⟩, ⟨['m', 'u'], ['t', 'h', 'e'], [⟨['m', 'u'], ['t', 'h', 'e'], none⟩]⟩, ⟨['i', 't', 'i', 't', 'i'], ['n', 'e', 'w'], [⟨['i', 't', 'i', 't', 'i'], ['n', 'e', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "nonverbalPredication"), ("copula", "zero"), ("definiteness", "determiner")] }

def fig5_ru : Datum :=
  { id := "demarneffenivre2019_fig5_ru"
    source := ⟨"de-marneffe-nivre-2019", "Figure 5"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Дома новые"
    glossedTokens := [("Дома", "houses"), ("новые", "new")]
    glossedWords := [⟨['Д', 'о', 'м', 'а'], ['h', 'o', 'u', 's', 'e', 's'], [⟨['Д', 'о', 'м', 'а'], ['h', 'o', 'u', 's', 'e', 's'], none⟩]⟩, ⟨['н', 'о', 'в', 'ы', 'е'], ['n', 'e', 'w'], [⟨['н', 'о', 'в', 'ы', 'е'], ['n', 'e', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "nonverbalPredication"), ("copula", "zero"), ("definiteness", "unmarked")] }

def fig6_sv : Datum :=
  { id := "demarneffenivre2019_fig6_sv"
    source := ⟨"de-marneffe-nivre-2019", "Figure 6"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "en katt jagar råttor och möss"
    glossedTokens := [("en", "a"), ("katt", "cat"), ("jagar", "chases"), ("råttor", "rats"), ("och", "and"), ("möss", "mice")]
    glossedWords := [⟨['e', 'n'], ['a'], [⟨['e', 'n'], ['a'], none⟩]⟩, ⟨['k', 'a', 't', 't'], ['c', 'a', 't'], [⟨['k', 'a', 't', 't'], ['c', 'a', 't'], none⟩]⟩, ⟨['j', 'a', 'g', 'a', 'r'], ['c', 'h', 'a', 's', 'e', 's'], [⟨['j', 'a', 'g', 'a', 'r'], ['c', 'h', 'a', 's', 'e', 's'], none⟩]⟩, ⟨['r', 'å', 't', 't', 'o', 'r'], ['r', 'a', 't', 's'], [⟨['r', 'å', 't', 't', 'o', 'r'], ['r', 'a', 't', 's'], none⟩]⟩, ⟨['o', 'c', 'h'], ['a', 'n', 'd'], [⟨['o', 'c', 'h'], ['a', 'n', 'd'], none⟩]⟩, ⟨['m', 'ö', 's', 's'], ['m', 'i', 'c', 'e'], [⟨['m', 'ö', 's', 's'], ['m', 'i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "annotationSchemes"), ("scheme", "SwedishTreebank")] }

def fig6_da : Datum :=
  { id := "demarneffenivre2019_fig6_da"
    source := ⟨"de-marneffe-nivre-2019", "Figure 6"⟩
    reportedIn := none
    language := "dani1285"
    primaryText := "en kat jager rotter og mus"
    glossedTokens := [("en", "a"), ("kat", "cat"), ("jager", "chases"), ("rotter", "rats"), ("og", "and"), ("mus", "mice")]
    glossedWords := [⟨['e', 'n'], ['a'], [⟨['e', 'n'], ['a'], none⟩]⟩, ⟨['k', 'a', 't'], ['c', 'a', 't'], [⟨['k', 'a', 't'], ['c', 'a', 't'], none⟩]⟩, ⟨['j', 'a', 'g', 'e', 'r'], ['c', 'h', 'a', 's', 'e', 's'], [⟨['j', 'a', 'g', 'e', 'r'], ['c', 'h', 'a', 's', 'e', 's'], none⟩]⟩, ⟨['r', 'o', 't', 't', 'e', 'r'], ['r', 'a', 't', 's'], [⟨['r', 'o', 't', 't', 'e', 'r'], ['r', 'a', 't', 's'], none⟩]⟩, ⟨['o', 'g'], ['a', 'n', 'd'], [⟨['o', 'g'], ['a', 'n', 'd'], none⟩]⟩, ⟨['m', 'u', 's'], ['m', 'i', 'c', 'e'], [⟨['m', 'u', 's'], ['m', 'i', 'c', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "annotationSchemes"), ("scheme", "DanishDependencyTreebank")] }

def fig6_en : Datum :=
  { id := "demarneffenivre2019_fig6_en"
    source := ⟨"de-marneffe-nivre-2019", "Figure 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "a cat chases rats and mice"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "annotationSchemes"), ("scheme", "StanfordTypedDependencies")] }

def fig7_en : Datum :=
  { id := "demarneffenivre2019_fig7_en"
    source := ⟨"de-marneffe-nivre-2019", "Figure 7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the dog will chase the cat out of the room"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "parallelism"), ("marking", "functionWords")] }

def fig7_fi : Datum :=
  { id := "demarneffenivre2019_fig7_fi"
    source := ⟨"de-marneffe-nivre-2019", "Figure 7"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "koira jahtaa kissan huoneesta"
    glossedTokens := [("koira", "dog.NOM"), ("jahtaa", "chase"), ("kissan", "cat.ACC"), ("huoneesta", "room.ELA")]
    glossedWords := [⟨['k', 'o', 'i', 'r', 'a'], ['d', 'o', 'g', '.', 'N', 'O', 'M'], [⟨['k', 'o', 'i', 'r', 'a'], ['d', 'o', 'g', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['j', 'a', 'h', 't', 'a', 'a'], ['c', 'h', 'a', 's', 'e'], [⟨['j', 'a', 'h', 't', 'a', 'a'], ['c', 'h', 'a', 's', 'e'], none⟩]⟩, ⟨['k', 'i', 's', 's', 'a', 'n'], ['c', 'a', 't', '.', 'A', 'C', 'C'], [⟨['k', 'i', 's', 's', 'a', 'n'], ['c', 'a', 't', '.', 'A', 'C', 'C'], none⟩]⟩, ⟨['h', 'u', 'o', 'n', 'e', 'e', 's', 't', 'a'], ['r', 'o', 'o', 'm', '.', 'E', 'L', 'A'], [⟨['h', 'u', 'o', 'n', 'e', 'e', 's', 't', 'a'], ['r', 'o', 'o', 'm', '.', 'E', 'L', 'A'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "parallelism"), ("marking", "case")] }

def fig8 : Datum :=
  { id := "demarneffenivre2019_fig8"
    source := ⟨"de-marneffe-nivre-2019", "Figure 8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mr. Smith did n't come to day."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "nonsyntacticRelations")] }

def fig9 : Datum :=
  { id := "demarneffenivre2019_fig9"
    source := ⟨"de-marneffe-nivre-2019", "Figure 9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Students who forgot to come failed the oral and written exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topic", "enhancedDependencies")] }

def all : List Datum := [fig1, fig2, fig3, fig4, ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4a, ex_4b, ex_5, fig5_en, fig5_sv, fig5_wsk, fig5_ru, fig6_sv, fig6_da, fig6_en, fig7_en, fig7_fi, fig8, fig9]

end DeMarneffeNivre2019.Examples
