module

public import Linglib.Data.Examples.Schema

/-!
# `VanTielEtAl2016` — typed example data

Auto-generated from `Linglib/Data/Examples/VanTielEtAl2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanTielEtAl2016.Examples`.
-/

@[expose] public section

namespace VanTielEtAl2016.Examples

def cheap_free : Datum :=
  { id := "vantieletal2016_cheap_free"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is cheap."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not free?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "cheap, free"), ("stronger term", "free"), ("class", "adjective"), ("bounded", "yes")] }

def sometimes_always : Datum :=
  { id := "vantieletal2016_sometimes_always"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is sometimes inside."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not always?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "sometimes, always"), ("stronger term", "always"), ("class", "adverb"), ("bounded", "yes")] }

def some_all : Datum :=
  { id := "vantieletal2016_some_all"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He saw some of them."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not all?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "some, all"), ("stronger term", "all"), ("class", "quantifier"), ("bounded", "yes")] }

def possible_certain : Datum :=
  { id := "vantieletal2016_possible_certain"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not certain?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "possible, certain"), ("stronger term", "certain"), ("class", "adjective"), ("bounded", "yes")] }

def may_will : Datum :=
  { id := "vantieletal2016_may_will"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may do it."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not will?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "may, will"), ("stronger term", "will"), ("class", "auxiliary verb"), ("bounded", "yes")] }

def difficult_impossible : Datum :=
  { id := "vantieletal2016_difficult_impossible"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is difficult."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not impossible?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "difficult, impossible"), ("stronger term", "impossible"), ("class", "adjective"), ("bounded", "yes")] }

def rare_extinct : Datum :=
  { id := "vantieletal2016_rare_extinct"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is rare."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not extinct?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "rare, extinct"), ("stronger term", "extinct"), ("class", "adjective"), ("bounded", "yes")] }

def may_haveto : Datum :=
  { id := "vantieletal2016_may_haveto"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He may do it."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not have to?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "may, have to"), ("stronger term", "have to"), ("class", "auxiliary verb"), ("bounded", "yes")] }

def warm_hot : Datum :=
  { id := "vantieletal2016_warm_hot"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That is warm."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not hot?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "warm, hot"), ("stronger term", "hot"), ("class", "adjective"), ("bounded", "no")] }

def few_none : Datum :=
  { id := "vantieletal2016_few_none"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He saw few of them."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not none?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "few, none"), ("stronger term", "none"), ("class", "quantifier"), ("bounded", "yes")] }

def low_depleted : Datum :=
  { id := "vantieletal2016_low_depleted"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is low."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not depleted?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "low, depleted"), ("stronger term", "depleted"), ("class", "adjective"), ("bounded", "yes")] }

def hard_unsolvable : Datum :=
  { id := "vantieletal2016_hard_unsolvable"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is hard."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not unsolvable?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "hard, unsolvable"), ("stronger term", "unsolvable"), ("class", "adjective"), ("bounded", "yes")] }

def allowed_obligatory : Datum :=
  { id := "vantieletal2016_allowed_obligatory"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is allowed."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not obligatory?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "allowed, obligatory"), ("stronger term", "obligatory"), ("class", "adjective"), ("bounded", "yes")] }

def scarce_unavailable : Datum :=
  { id := "vantieletal2016_scarce_unavailable"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is scarce."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not unavailable?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "scarce, unavailable"), ("stronger term", "unavailable"), ("class", "adjective"), ("bounded", "yes")] }

def try_succeed : Datum :=
  { id := "vantieletal2016_try_succeed"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He tried."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not succeed?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "try, succeed"), ("stronger term", "succeed"), ("class", "main verb"), ("bounded", "yes")] }

def palatable_delicious : Datum :=
  { id := "vantieletal2016_palatable_delicious"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is palatable."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not delicious?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "palatable, delicious"), ("stronger term", "delicious"), ("class", "adjective"), ("bounded", "no")] }

def memorable_unforgettable : Datum :=
  { id := "vantieletal2016_memorable_unforgettable"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is memorable."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not unforgettable?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "memorable, unforgettable"), ("stronger term", "unforgettable"), ("class", "adjective"), ("bounded", "yes")] }

def like_love : Datum :=
  { id := "vantieletal2016_like_love"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She likes it."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not love?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "like, love"), ("stronger term", "love"), ("class", "main verb"), ("bounded", "no")] }

def good_perfect : Datum :=
  { id := "vantieletal2016_good_perfect"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is good."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not perfect?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "good, perfect"), ("stronger term", "perfect"), ("class", "adjective"), ("bounded", "yes")] }

def good_excellent : Datum :=
  { id := "vantieletal2016_good_excellent"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is good."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not excellent?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "good, excellent"), ("stronger term", "excellent"), ("class", "adjective"), ("bounded", "no")] }

def cool_cold : Datum :=
  { id := "vantieletal2016_cool_cold"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That is cool."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not cold?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "cool, cold"), ("stronger term", "cold"), ("class", "adjective"), ("bounded", "no")] }

def hungry_starving : Datum :=
  { id := "vantieletal2016_hungry_starving"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is hungry."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not starving?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "hungry, starving"), ("stronger term", "starving"), ("class", "adjective"), ("bounded", "no")] }

def adequate_good : Datum :=
  { id := "vantieletal2016_adequate_good"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is adequate."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not good?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "adequate, good"), ("stronger term", "good"), ("class", "adjective"), ("bounded", "no")] }

def unsettling_horrific : Datum :=
  { id := "vantieletal2016_unsettling_horrific"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is unsettling."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not horrific?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "unsettling, horrific"), ("stronger term", "horrific"), ("class", "adjective"), ("bounded", "no")] }

def dislike_loathe : Datum :=
  { id := "vantieletal2016_dislike_loathe"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He dislikes it."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not loathe?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "dislike, loathe"), ("stronger term", "loathe"), ("class", "main verb"), ("bounded", "no")] }

def believe_know : Datum :=
  { id := "vantieletal2016_believe_know"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She believes it."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not know?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "believe, know"), ("stronger term", "know"), ("class", "main verb"), ("bounded", "yes")] }

def start_finish : Datum :=
  { id := "vantieletal2016_start_finish"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She started."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not finish?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "start, finish"), ("stronger term", "finish"), ("class", "main verb"), ("bounded", "yes")] }

def participate_win : Datum :=
  { id := "vantieletal2016_participate_win"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She participated."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not win?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "participate, win"), ("stronger term", "win"), ("class", "main verb"), ("bounded", "yes")] }

def wary_scared : Datum :=
  { id := "vantieletal2016_wary_scared"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is wary."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not scared?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "wary, scared"), ("stronger term", "scared"), ("class", "adjective"), ("bounded", "no")] }

def old_ancient : Datum :=
  { id := "vantieletal2016_old_ancient"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is old."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not ancient?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "old, ancient"), ("stronger term", "ancient"), ("class", "adjective"), ("bounded", "no")] }

def big_enormous : Datum :=
  { id := "vantieletal2016_big_enormous"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is big."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not enormous?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "big, enormous"), ("stronger term", "enormous"), ("class", "adjective"), ("bounded", "no")] }

def snug_tight : Datum :=
  { id := "vantieletal2016_snug_tight"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is snug."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not tight?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "snug, tight"), ("stronger term", "tight"), ("class", "adjective"), ("bounded", "no")] }

def attractive_stunning : Datum :=
  { id := "vantieletal2016_attractive_stunning"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is attractive."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not stunning?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "attractive, stunning"), ("stronger term", "stunning"), ("class", "adjective"), ("bounded", "no")] }

def special_unique : Datum :=
  { id := "vantieletal2016_special_unique"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is special."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not unique?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "special, unique"), ("stronger term", "unique"), ("class", "adjective"), ("bounded", "yes")] }

def pretty_beautiful : Datum :=
  { id := "vantieletal2016_pretty_beautiful"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is pretty."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not beautiful?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "pretty, beautiful"), ("stronger term", "beautiful"), ("class", "adjective"), ("bounded", "no")] }

def intelligent_brilliant : Datum :=
  { id := "vantieletal2016_intelligent_brilliant"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is intelligent."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not brilliant?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "intelligent, brilliant"), ("stronger term", "brilliant"), ("class", "adjective"), ("bounded", "no")] }

def funny_hilarious : Datum :=
  { id := "vantieletal2016_funny_hilarious"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is funny."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not hilarious?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "funny, hilarious"), ("stronger term", "hilarious"), ("class", "adjective"), ("bounded", "no")] }

def dark_black : Datum :=
  { id := "vantieletal2016_dark_black"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That is dark."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not black?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "dark, black"), ("stronger term", "black"), ("class", "adjective"), ("bounded", "yes")] }

def small_tiny : Datum :=
  { id := "vantieletal2016_small_tiny"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is small."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not tiny?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "small, tiny"), ("stronger term", "tiny"), ("class", "adjective"), ("bounded", "no")] }

def ugly_hideous : Datum :=
  { id := "vantieletal2016_ugly_hideous"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is ugly."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not hideous?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "ugly, hideous"), ("stronger term", "hideous"), ("class", "adjective"), ("bounded", "no")] }

def silly_ridiculous : Datum :=
  { id := "vantieletal2016_silly_ridiculous"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is silly."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not ridiculous?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "silly, ridiculous"), ("stronger term", "ridiculous"), ("class", "adjective"), ("bounded", "no")] }

def tired_exhausted : Datum :=
  { id := "vantieletal2016_tired_exhausted"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He is tired."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not exhausted?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "tired, exhausted"), ("stronger term", "exhausted"), ("class", "adjective"), ("bounded", "no")] }

def content_happy : Datum :=
  { id := "vantieletal2016_content_happy"
    source := ⟨"van-tiel-geurts-2016", "Table 3, Appendix A"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is content."
    glossedTokens := []
    context := "Experiment 1: Mary or John says the sentence; would you conclude that, according to the speaker, it is not happy?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("scale", "content, happy"), ("stronger term", "happy"), ("class", "adjective"), ("bounded", "no")] }

def all : List Datum := [cheap_free, sometimes_always, some_all, possible_certain, may_will, difficult_impossible, rare_extinct, may_haveto, warm_hot, few_none, low_depleted, hard_unsolvable, allowed_obligatory, scarce_unavailable, try_succeed, palatable_delicious, memorable_unforgettable, like_love, good_perfect, good_excellent, cool_cold, hungry_starving, adequate_good, unsettling_horrific, dislike_loathe, believe_know, start_finish, participate_win, wary_scared, old_ancient, big_enormous, snug_tight, attractive_stunning, special_unique, pretty_beautiful, intelligent_brilliant, funny_hilarious, dark_black, small_tiny, ugly_hideous, silly_ridiculous, tired_exhausted, content_happy]

end VanTielEtAl2016.Examples
