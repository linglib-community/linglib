module

public import Linglib.Data.Examples.Schema

/-!
# `Deal2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Deal2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deal2020.Examples`.
-/

@[expose] public section

namespace Deal2020.Examples

def ex_70 : Datum :=
  { id := "deal2020_70"
    source := ⟨"deal-2020", "(70)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Ne-’níc-em pee-∅-n-e ’in-haama-na, ’iin-im ciq’aamqal hi-twehkey’k-∅-e ’iin-e."
    glossedTokens := [("Ne-’níc-em", "1SG-older.sister-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("’in-haama-na,", "1SG-husband-ACC"), ("’iin-im", "1SG-GEN"), ("ciq’aamqal", "dog(ERG)"), ("hi-twehkey’k-∅-e", "3SUBJ-chase-P-REM.PAST"), ("’iin-e", "1SG-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("both utterance", .marginal), ("second reported only", .unacceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "I"), ("indexical", "I"), ("test", "shift_together")] }

def ex_73 : Datum :=
  { id := "deal2020_73"
    source := ⟨"deal-2020", "(73)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Ne-’níc-em pee-∅-n-e ’in-haama-na, ’im-im ciq’aamqal hi-twehkey’k-∅-e ’iin-e."
    glossedTokens := [("Ne-’níc-em", "1SG-older.sister-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("’in-haama-na,", "1SG-husband-ACC"), ("’im-im", "2SG-GEN"), ("ciq’aamqal", "dog(ERG)"), ("hi-twehkey’k-∅-e", "3SUBJ-chase-P-REM.PAST"), ("’iin-e", "1SG-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("both utterance", .marginal), ("second reported only", .unacceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "you"), ("indexical", "I"), ("test", "shift_together")] }

def ex_83 : Datum :=
  { id := "deal2020_83"
    source := ⟨"deal-2020", "(83)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Katie hi-hi-ce-∅ pro neki-se-∅ ’iin-k’u wees kine."
    glossedTokens := [("Katie", "Katie.NOM"), ("hi-hi-ce-∅", "3SUBJ-say-IMPERF-PRES"), ("pro", "1SG.NOM"), ("neki-se-∅", "think-IMPERF-PRES"), ("’iin-k’u", "1SG.NOM-too"), ("wees", "be.PRES"), ("kine", "here")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("both utterance", .acceptable), ("first reported only", .unacceptable), ("second reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "I"), ("indexical", "I"), ("test", "local_determination")] }

def ex_87 : Datum :=
  { id := "deal2020_87"
    source := ⟨"deal-2020", "(87)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Caan hi-neki-se-∅ Meeli-nm pee-∅-n-e Sue-ne ’ee wees qetu kuhet ’iin-im-kin’ix."
    glossedTokens := [("Caan", "John.NOM"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("Meeli-nm", "Mary-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("Sue-ne", "Sue-ACC"), ("’ee", "2SG.CL"), ("wees", "be.PRES"), ("qetu", "more"), ("kuhet", "tall"), ("’iin-im-kin’ix", "1SG-OBL-from")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("intermediate reported context", .unacceptable), ("lowest reported context", .acceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("lower_verb", "nezperce_say"), ("indexical", "I"), ("test", "local_determination"), ("lowest_shift", "yes")] }

def ex_111 : Datum :=
  { id := "deal2020_111"
    source := ⟨"deal-2020", "(111)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Talmaks-pa pro hi-pe-hi-n-e pro weet’u kíne wisiinu’ kii k’ay’x-pa."
    glossedTokens := [("Talmaks-pa", "Talmaks-LOC"), ("pro", "3PL"), ("hi-pe-hi-n-e", "3SUBJ-S.PL-say-P-REM.PAST"), ("pro", "1PL"), ("weet’u", "not"), ("kíne", "here"), ("wisiinu’", "be.PROSP.PL"), ("kii", "this"), ("k’ay’x-pa", "week-LOC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("first reported only", .acceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "I"), ("indexical", "here")] }

def ex_113 : Datum :=
  { id := "deal2020_113"
    source := ⟨"deal-2020", "(113)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’In-lawtiwaa-nm Boston-pa hi-nees-∅-n-e pro weet’u kine pro wees kii kaa."
    glossedTokens := [("’In-lawtiwaa-nm", "1SG-friend-ERG"), ("Boston-pa", "Boston-LOC"), ("hi-nees-∅-n-e", "3SUBJ-O.PL-say-P-REM.PAST"), ("pro", "3PL"), ("weet’u", "NEG"), ("kine", "here"), ("pro", "1SG"), ("wees", "be.PRES"), ("kii", "this"), ("kaa", "then")]
    context := "Taamsas is speaking."
    judgment := .acceptable
    alternatives := []
    readings := [("both reported", .acceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "here"), ("indexical", "I")] }

def ex_115 : Datum :=
  { id := "deal2020_115"
    source := ⟨"deal-2020", "(115)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Pay’s Harold hi-neki-se-∅ pro wees kine Clarkston-pa."
    glossedTokens := [("Pay’s", "maybe"), ("Harold", "Harold.NOM"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("pro", "1SG"), ("wees", "be.PRES"), ("kine", "here"), ("Clarkston-pa", "Clarkston-LOC")]
    context := "Harold is in Clarkston. I and my consultant are in Lapwai."
    judgment := .unacceptable
    alternatives := []
    readings := [("second reported only", .unacceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("indexical", "I"), ("indexical", "here")] }

def ex_118 : Datum :=
  { id := "deal2020_118"
    source := ⟨"deal-2020", "(118)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’Aayat hi-nek-saa-qa pro peeleey-ce-∅."
    glossedTokens := [("’Aayat", "woman.NOM"), ("hi-nek-saa-qa", "3SUBJ-think-IMPERF-REC.PAST"), ("pro", "1SG"), ("peeleey-ce-∅", "be.missing-IMPERF-PRES")]
    context := "A woman was on a group tour and she wandered off from the group and went back to the bus to take a nap. People noticed she was missing and started searching for her. She woke up, got back off the bus, and noticed everyone searching around. Of course, she didn’t know why they were searching. Someone said to her, “A woman is lost.” So she joined the search party to look for that woman, without knowing it was herself!"
    judgment := .unacceptable
    alternatives := []
    readings := [("non-de se", .unacceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("indexical", "I"), ("test", "de_se")] }

def ex_121 : Datum :=
  { id := "deal2020_121"
    source := ⟨"deal-2020", "(121)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Meeli-nm pee-∅-n-e Caan-e, ’ee cikliitoq-o’qa."
    glossedTokens := [("Meeli-nm", "Mary-ERG"), ("pee-∅-n-e", "3/3-say-P-REM.PAST"), ("Caan-e,", "John-ACC"), ("’ee", "2SG.CL"), ("cikliitoq-o’qa", "go.home-MODAL")]
    context := "Mary is organizing a big dinner at a restaurant with waiters to help serve food. She hears that a certain waiter named John is being a nuisance. She tells the nearest waiter, “John should go home.\" Unbeknowst to her, she’s talking to John."
    judgment := .unacceptable
    alternatives := []
    readings := [("non-de se", .unacceptable)]
    paperFeatures := [("verb", "nezperce_say"), ("indexical", "you"), ("test", "de_se")] }

def ex_124 : Datum :=
  { id := "deal2020_124"
    source := ⟨"deal-2020", "(124)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "’Aayat hii-wes Clarkston-pa, met’u pro hi-neki-se-∅ Asootin-pa, kaa pro hi-neki-se-∅ Costco hii-wes kine."
    glossedTokens := [("’Aayat", "woman.NOM"), ("hii-wes", "3SUBJ-be.PRES"), ("Clarkston-pa,", "Clarkston-LOC"), ("met’u", "but"), ("pro", "3SG"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("Asootin-pa,", "Asotin-LOC"), ("kaa", "and"), ("pro", "3SG"), ("hi-neki-se-∅", "3SUBJ-think-IMPERF-PRES"), ("Costco", "Costco"), ("hii-wes", "3SUBJ-be.PRES"), ("kine", "here")]
    context := "Elicited in Lapwai: Costco is a prominent store in Clarkston. Everyone knows where it is."
    judgment := .acceptable
    alternatives := []
    readings := [("non-de se", .acceptable)]
    paperFeatures := [("verb", "nezperce_think"), ("indexical", "here"), ("test", "de_se")] }

def ex_117 : Datum :=
  { id := "deal2020_117"
    source := ⟨"anand-2006", "p. 79"⟩
    reportedIn := some ⟨"deal-2020", "(117)"⟩
    language := "diml1238"
    primaryText := "Heseni va kɛ ɛz newɛsha."
    glossedTokens := [("Heseni", "Hesen.OBL"), ("va", "said"), ("kɛ", "that"), ("ɛz", "I"), ("newɛsha", "be.sick.PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "zazaki_say"), ("indexical", "I"), ("test", "de_se")] }

def ex_120 : Datum :=
  { id := "deal2020_120"
    source := ⟨"anand-2006", "p. 80"⟩
    reportedIn := some ⟨"deal-2020", "(120)"⟩
    language := "diml1238"
    primaryText := "Heseni va Ali-ra kɛ ti newɛsha."
    glossedTokens := [("Heseni", "Hesen.OBL"), ("va", "said"), ("Ali-ra", "Ali-to"), ("kɛ", "that"), ("ti", "you"), ("newɛsha", "be.sick.PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "zazaki_say"), ("indexical", "you"), ("test", "de_se")] }

def ex_123 : Datum :=
  { id := "deal2020_123"
    source := ⟨"anand-2006", "p. 80"⟩
    reportedIn := some ⟨"deal-2020", "(123)"⟩
    language := "diml1238"
    primaryText := "Waxto kɛ o London-de bime Pierri va kɛ o ita rindɛka."
    glossedTokens := [("Waxto", "when"), ("kɛ", "that"), ("o", "he"), ("London-de", "London-at"), ("bime", "be.PAST"), ("Pierri", "Pierre.OBL"), ("va", "said"), ("kɛ", "that"), ("o", "it"), ("ita", "here"), ("rindɛka", "be.pretty.PRES")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "zazaki_say"), ("indexical", "here"), ("test", "de_se")] }

def ex_103b : Datum :=
  { id := "deal2020_103b"
    source := ⟨"sudo-2012", "p. 244"⟩
    reportedIn := some ⟨"deal-2020", "(103b)"⟩
    language := "uigh1240"
    primaryText := "Muhemmet manga toqquzinji ay-din bašla-p (men) bu jer-de uqu-imen di-di."
    glossedTokens := [("Muhemmet", "Muhemmet"), ("manga", "1SG.DAT"), ("toqquzinji", "9th"), ("ay-din", "month-from"), ("bašla-p", "start-ing"), ("(men)", "1SG.NOM"), ("bu jer-de", "here-LOC"), ("uqu-imen", "study-IMPF.1SG"), ("di-di.", "say-PAST.3")]
    context := "This summer, I went to UCLA and met Muhemmet there. He told me, “I’m going to study here from this September.” Now I’m back in Cambridge, MA, talking to Ahmet."
    judgment := .unacceptable
    alternatives := [("Muhemmet manga toqquzinji ay-din bašla-p (men) u jer-de uqu-imen di-di.", .acceptable)]
    readings := [("both reported", .unacceptable)]
    paperFeatures := [("verb", "uyghur_say"), ("indexical", "I"), ("indexical", "here")] }

def ex_122 : Datum :=
  { id := "deal2020_122"
    source := ⟨"sudo-2012", "p. 225"⟩
    reportedIn := some ⟨"deal-2020", "(122)"⟩
    language := "uigh1240"
    primaryText := "Muhemmet John-gha pro öy-ge kit-sh-ing kirek di-di."
    glossedTokens := [("Muhemmet", "Muhemmet"), ("John-gha", "John-DAT"), ("pro", "2SG"), ("öy-ge", "home-DAT"), ("kit-sh-ing", "leave-GER-2SG"), ("kirek", "should"), ("di-di.", "say-PAST.3")]
    context := "Muhemmet is hosting a party. He hears that a certain waiter named John is being a nuisance. Muhemmet tells the nearest waiter, “John should go home.” Unbeknownst to him, he’s talking to John."
    judgment := .acceptable
    alternatives := []
    readings := [("non-de se", .acceptable)]
    paperFeatures := [("verb", "uyghur_say"), ("indexical", "you"), ("test", "de_se")] }

def ex_106 : Datum :=
  { id := "deal2020_106"
    source := ⟨"rice-1986", "p. 53"⟩
    reportedIn := some ⟨"deal-2020", "(106)"⟩
    language := "slav1253"
    primaryText := "Simon rásereyineht’u hadi."
    glossedTokens := [("Simon", "Simon"), ("rásereyineht’u", "2SG.hit.1SG"), ("hadi.", "3SG.say")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("second reported only", .acceptable)]
    paperFeatures := [("verb", "slave_say"), ("indexical", "you"), ("indexical", "I")] }

def ex_119 : Datum :=
  { id := "deal2020_119"
    source := ⟨"nishiguchi-2017", "p. 48"⟩
    reportedIn := some ⟨"deal-2020", "(119)"⟩
    language := "daas1238"
    primaryText := "Baali kiey-e sure-chu he jiet hi konye."
    glossedTokens := [("Baali", "Baali"), ("kiey-e", "say.3SG-PAST"), ("sure-chu", "1SG.GEN-pants"), ("he", "COPULA"), ("jiet", "fire"), ("hi", "RP"), ("konye.", "eat.3SG.PASS.PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("de se", .acceptable), ("non-de se", .acceptable)]
    paperFeatures := [("verb", "dhaasanac_say"), ("indexical", "I"), ("test", "de_se")] }

def ex_159 : Datum :=
  { id := "deal2020_159"
    source := ⟨"park-2016", "p. 29"⟩
    reportedIn := some ⟨"deal-2020", "(159)"⟩
    language := "kore1280"
    primaryText := "John-i cinancwu welyoil-ey Mary-ka onul ttenanta-ko malhayssta."
    glossedTokens := [("John-i", "John-NOM"), ("cinancwu", "last.week"), ("welyoil-ey", "Monday-on"), ("Mary-ka", "Mary-NOM"), ("onul", "today"), ("ttenanta-ko", "leave-C"), ("malhayssta.", "said")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("de se", .acceptable), ("non-de se", .unacceptable)]
    paperFeatures := [("verb", "korean_say"), ("indexical", "today"), ("test", "de_se")] }

def ex_161 : Datum :=
  { id := "deal2020_161"
    source := ⟨"park-2016", "fn. 10"⟩
    reportedIn := some ⟨"deal-2020", "(161)"⟩
    language := "kore1280"
    primaryText := "Cinan cwu-ey Mary-ka nwuka nayil ttenanta-ko sayngkakayss-ni?"
    glossedTokens := [("Cinan", "Last"), ("cwu-ey", "week-in"), ("Mary-ka", "Mary-NOM"), ("nwuka", "who-NOM"), ("nayil", "tomorrow"), ("ttenanta-ko", "leave-C"), ("sayngkakayss-ni?", "thought-Q")]
    context := "It is January 8th."
    judgment := .acceptable
    alternatives := []
    readings := [("reported context", .acceptable), ("utterance context", .acceptable)]
    paperFeatures := [("verb", "korean_think"), ("indexical", "tomorrow")] }

def ex_162 : Datum :=
  { id := "deal2020_162"
    source := ⟨"park-2016", "(30b)"⟩
    reportedIn := some ⟨"deal-2020", "(162)"⟩
    language := "kore1280"
    primaryText := "Mary-ka nwuka na-lul coahanta-ko sayngkakayss-ni?"
    glossedTokens := [("Mary-ka", "Mary-NOM"), ("nwuka", "who"), ("na-lul", "I-ACC"), ("coahanta-ko", "like-C"), ("sayngkakayss-ni?", "thought-Q")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("utterance context", .acceptable), ("reported context", .unacceptable)]
    paperFeatures := [("verb", "korean_think"), ("indexical", "I")] }

def ex_175 : Datum :=
  { id := "deal2020_175"
    source := ⟨"park-2016", "(25)"⟩
    reportedIn := some ⟨"deal-2020", "(175)"⟩
    language := "kore1280"
    primaryText := "Tom-i ece cenyek New York-eyse Sue-ka ece yeki-ey wassta-ko malhayssta."
    glossedTokens := [("Tom-i", "Tom-NOM"), ("ece", "yesterday"), ("cenyek", "night"), ("New York-eyse", "New York-at"), ("Sue-ka", "Sue-NOM"), ("ece", "yesterday"), ("yeki-ey", "here-at"), ("wassta-ko", "came-C"), ("malhayssta.", "said")]
    context := "John and Mary are having a conversation in Boston on July 3rd. John says:"
    judgment := .acceptable
    alternatives := []
    readings := [("both utterance", .acceptable), ("both reported", .acceptable), ("second reported only", .unacceptable), ("first reported only", .unacceptable)]
    paperFeatures := [("verb", "korean_say"), ("indexical", "yesterday"), ("indexical", "here")] }

def ex_176 : Datum :=
  { id := "deal2020_176"
    source := ⟨"park-2016", "(32)"⟩
    reportedIn := some ⟨"deal-2020", "(176)"⟩
    language := "kore1280"
    primaryText := "Tom-i New York-eyse nay-ka yeki-eyse thayenassta-ko malhayssta."
    glossedTokens := [("Tom-i", "Tom-NOM"), ("New York-eyse", "New York-at"), ("nay-ka", "I-NOM"), ("yeki-eyse", "here-at"), ("thayenassta-ko", "be.born-C"), ("malhayssta.", "said")]
    context := "John and Mary are having a conversation in Seoul. John says:"
    judgment := .acceptable
    alternatives := []
    readings := [("both utterance", .acceptable), ("second reported only", .acceptable), ("first reported only", .acceptable), ("both reported", .acceptable)]
    paperFeatures := [("verb", "korean_say"), ("indexical", "I"), ("indexical", "here")] }

def ex_165 : Datum :=
  { id := "deal2020_165"
    source := ⟨"deal-2020", "(165)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When I saw Kate a week ago, she said that she’d seen Star Wars yesterday."
    glossedTokens := []
    context := ""
    judgment := .variable
    alternatives := []
    readings := [("reported context", .acceptable)]
    paperFeatures := [("verb", "anderson_say"), ("indexical", "yesterday"), ("variety", "Anderson English")] }

def ex_166 : Datum :=
  { id := "deal2020_166"
    source := ⟨"deal-2020", "(166)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last Thursday, John said that he was going to come over tomorrow, but he showed up on Saturday instead!"
    glossedTokens := []
    context := "John is confused on Thursday and thinks the date is the 23rd, when it is really the 24th. On Thursday, John tells Sarah, “I’m coming on the 25th.” But he doesn’t show up until Saturday. A week later, Sarah is telling Bill what happened. She says:"
    judgment := .variable
    alternatives := []
    readings := [("non-de se", .acceptable)]
    paperFeatures := [("verb", "anderson_say"), ("indexical", "tomorrow"), ("variety", "Anderson English"), ("test", "de_se")] }

def all : List Datum := [ex_70, ex_73, ex_83, ex_87, ex_111, ex_113, ex_115, ex_118, ex_121, ex_124, ex_117, ex_120, ex_123, ex_103b, ex_122, ex_106, ex_119, ex_159, ex_161, ex_162, ex_175, ex_176, ex_165, ex_166]

end Deal2020.Examples
