module

public import Linglib.Data.Examples.Schema

/-!
# `Cumming2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Cumming2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cumming2026.Examples`.
-/

@[expose] public section

namespace Cumming2026.Examples

def ex_1 : Datum :=
  { id := "cumming2026_1"
    source := ⟨"cumming-2026", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alma will enjoy the meal."
    glossedTokens := []
    context := "Alma is about to eat a meal the speaker has good grounds for thinking she will enjoy: she enjoyed it when the speaker prepared it before, the speaker has sampled it, and it tastes good."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "future (will)"), ("acquisitionTime", "0"), ("speechTime", "1"), ("eventTime", "2")] }

def ex_2_prior : Datum :=
  { id := "cumming2026_2_prior"
    source := ⟨"cumming-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alma enjoyed the meal."
    glossedTokens := []
    context := "The next day, with only the prior inferential grounds of (1)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple past"), ("acquisitionTime", "0"), ("eventTime", "2"), ("speechTime", "3"), ("felicity", "infelicitous")] }

def ex_2_downstream : Datum :=
  { id := "cumming2026_2_downstream"
    source := ⟨"cumming-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alma enjoyed the meal."
    glossedTokens := []
    context := "Alma told the speaker after the meal that she enjoyed it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple past"), ("eventTime", "2"), ("acquisitionTime", "3"), ("speechTime", "4")] }

def ex_4a : Datum :=
  { id := "cumming2026_4a"
    source := ⟨"cumming-2026", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alma will have enjoyed the meal."
    glossedTokens := []
    context := "The next day, with only the prior inferential grounds of (1)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "will have V-ed"), ("acquisitionTime", "0"), ("eventTime", "2"), ("speechTime", "3")] }

def ex_11c : Datum :=
  { id := "cumming2026_11c"
    source := ⟨"cumming-2026", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alma will be enjoying the meal (right now)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "will now be V-ing"), ("acquisitionTime", "0"), ("eventTime", "2"), ("speechTime", "2")] }

def ex_12b : Datum :=
  { id := "cumming2026_12b"
    source := ⟨"cumming-2026", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alma is enjoying the meal (right now)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "present progressive"), ("acquisitionTime", "0"), ("eventTime", "2"), ("speechTime", "2"), ("felicity", "infelicitous")] }

def ex_21a_inferential : Datum :=
  { id := "cumming2026_21a_inferential"
    source := ⟨"cumming-2026", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Fed will have raised interest rates at today's meeting."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "will have V-ed"), ("acquisitionTime", "0"), ("eventTime", "1"), ("speechTime", "2")] }

def ex_21a_abductive : Datum :=
  { id := "cumming2026_21a_abductive"
    source := ⟨"cumming-2026", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Fed will have raised interest rates at today's meeting."
    glossedTokens := []
    context := "After the meeting, having just read in the evening paper that the rates were raised."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "will have V-ed"), ("eventTime", "1"), ("acquisitionTime", "2"), ("speechTime", "3"), ("felicity", "infelicitous")] }

def ex_13a : Datum :=
  { id := "cumming2026_13a"
    source := ⟨"lee-2013", "(1a)"⟩
    reportedIn := some ⟨"cumming-2026", "(13a)"⟩
    language := "kore1280"
    primaryText := "Pi-ka o-∅-te-la."
    glossedTokens := [("Pi-ka", "rain-NOM"), ("o-∅-te-la", "fall-PRES-TE-DECL")]
    glossedWords := [⟨[['P', 'i'], ['k', 'a']], [['r', 'a', 'i', 'n'], ['N', 'O', 'M']]⟩, ⟨[['o'], ['∅'], ['t', 'e'], ['l', 'a']], [['f', 'a', 'l', 'l'], ['P', 'R', 'E', 'S'], ['T', 'E'], ['D', 'E', 'C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Yenghi saw it raining yesterday; now she says."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "-te PRES"), ("eventTime", "1"), ("acquisitionTime", "1"), ("speechTime", "2")] }

def ex_13b : Datum :=
  { id := "cumming2026_13b"
    source := ⟨"lee-2013", "(1b)"⟩
    reportedIn := some ⟨"cumming-2026", "(13b)"⟩
    language := "kore1280"
    primaryText := "Pi-ka o-ass-te-la."
    glossedTokens := [("Pi-ka", "rain-NOM"), ("o-ass-te-la", "fall-PAST-TE-DECL")]
    glossedWords := [⟨[['P', 'i'], ['k', 'a']], [['r', 'a', 'i', 'n'], ['N', 'O', 'M']]⟩, ⟨[['o'], ['a', 's', 's'], ['t', 'e'], ['l', 'a']], [['f', 'a', 'l', 'l'], ['P', 'A', 'S', 'T'], ['T', 'E'], ['D', 'E', 'C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Yenghi saw yesterday that the ground was wet; now she says."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "-te PAST"), ("eventTime", "0"), ("acquisitionTime", "1"), ("speechTime", "2")] }

def ex_13c : Datum :=
  { id := "cumming2026_13c"
    source := ⟨"lee-2013", "(1c)"⟩
    reportedIn := some ⟨"cumming-2026", "(13c)"⟩
    language := "kore1280"
    primaryText := "Pi-ka o-kyess-te-la."
    glossedTokens := [("Pi-ka", "rain-NOM"), ("o-kyess-te-la", "fall-FUT-TE-DECL")]
    glossedWords := [⟨[['P', 'i'], ['k', 'a']], [['r', 'a', 'i', 'n'], ['N', 'O', 'M']]⟩, ⟨[['o'], ['k', 'y', 'e', 's', 's'], ['t', 'e'], ['l', 'a']], [['f', 'a', 'l', 'l'], ['F', 'U', 'T'], ['T', 'E'], ['D', 'E', 'C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Yenghi saw the overcast sky yesterday; now she says."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "-te FUT"), ("acquisitionTime", "1"), ("eventTime", "2"), ("speechTime", "3")] }

def ex_14a : Datum :=
  { id := "cumming2026_14a"
    source := ⟨"lee-2011", "(65b)"⟩
    reportedIn := some ⟨"cumming-2026", "(14a)"⟩
    language := "kore1280"
    primaryText := "Cikum pi-ka o-∅-ney."
    glossedTokens := [("Cikum", "now"), ("pi-ka", "rain-NOM"), ("o-∅-ney", "fall-PRES-NEY.DECL")]
    glossedWords := [⟨[['C', 'i', 'k', 'u', 'm']], [['n', 'o', 'w']]⟩, ⟨[['p', 'i'], ['k', 'a']], [['r', 'a', 'i', 'n'], ['N', 'O', 'M']]⟩, ⟨[['o'], ['∅'], ['n', 'e', 'y']], [['f', 'a', 'l', 'l'], ['P', 'R', 'E', 'S'], ['N', 'E', 'Y', '.', 'D', 'E', 'C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Chelswu sees it raining now and says."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "-ney PRES"), ("eventTime", "2"), ("acquisitionTime", "2"), ("speechTime", "2")] }

def ex_14b : Datum :=
  { id := "cumming2026_14b"
    source := ⟨"lee-2011", "(67b)"⟩
    reportedIn := some ⟨"cumming-2026", "(14b)"⟩
    language := "kore1280"
    primaryText := "Cokum cen-ey pi-ka o-ass-ney."
    glossedTokens := [("Cokum", "little"), ("cen-ey", "ago-at"), ("pi-ka", "rain-NOM"), ("o-ass-ney", "fall-PAST-NEY.DECL")]
    glossedWords := [⟨[['C', 'o', 'k', 'u', 'm']], [['l', 'i', 't', 't', 'l', 'e']]⟩, ⟨[['c', 'e', 'n'], ['e', 'y']], [['a', 'g', 'o'], ['a', 't']]⟩, ⟨[['p', 'i'], ['k', 'a']], [['r', 'a', 'i', 'n'], ['N', 'O', 'M']]⟩, ⟨[['o'], ['a', 's', 's'], ['n', 'e', 'y']], [['f', 'a', 'l', 'l'], ['P', 'A', 'S', 'T'], ['N', 'E', 'Y', '.', 'D', 'E', 'C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Chelswu sees the wet ground now and says."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "-ney PAST"), ("eventTime", "1"), ("acquisitionTime", "2"), ("speechTime", "2")] }

def ex_14c : Datum :=
  { id := "cumming2026_14c"
    source := ⟨"lee-2011", "(69b)"⟩
    reportedIn := some ⟨"cumming-2026", "(14c)"⟩
    language := "kore1280"
    primaryText := "Onul pam-ey pi-ka o-kyess-ney."
    glossedTokens := [("Onul", "today"), ("pam-ey", "night-at"), ("pi-ka", "rain-NOM"), ("o-kyess-ney", "fall-FUT-NEY.DECL")]
    glossedWords := [⟨[['O', 'n', 'u', 'l']], [['t', 'o', 'd', 'a', 'y']]⟩, ⟨[['p', 'a', 'm'], ['e', 'y']], [['n', 'i', 'g', 'h', 't'], ['a', 't']]⟩, ⟨[['p', 'i'], ['k', 'a']], [['r', 'a', 'i', 'n'], ['N', 'O', 'M']]⟩, ⟨[['o'], ['k', 'y', 'e', 's', 's'], ['n', 'e', 'y']], [['f', 'a', 'l', 'l'], ['F', 'U', 'T'], ['N', 'E', 'Y', '.', 'D', 'E', 'C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Chelswu sees the cloudy sky now and says."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "-ney FUT"), ("acquisitionTime", "2"), ("speechTime", "2"), ("eventTime", "3")] }

def ex_15_nfut : Datum :=
  { id := "cumming2026_15_nfut"
    source := ⟨"koev-2017", "(24)"⟩
    reportedIn := some ⟨"cumming-2026", "(15)"⟩
    language := "bulg1262"
    primaryText := "Včera v Pariž valja-∅-l-o."
    glossedTokens := [("Včera", "yesterday"), ("v", "in"), ("Pariž", "Paris"), ("valja-∅-l-o", "rain-NFUT-EV-NEUT")]
    glossedWords := [⟨[['V', 'č', 'e', 'r', 'a']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['v']], [['i', 'n']]⟩, ⟨[['P', 'a', 'r', 'i', 'ž']], [['P', 'a', 'r', 'i', 's']]⟩, ⟨[['v', 'a', 'l', 'j', 'a'], ['∅'], ['l'], ['o']], [['r', 'a', 'i', 'n'], ['N', 'F', 'U', 'T'], ['E', 'V'], ['N', 'E', 'U', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "You learned earlier today that it had rained yesterday in Paris."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "NFUT + -l"), ("eventTime", "1"), ("acquisitionTime", "2"), ("speechTime", "3")] }

def ex_15_fut : Datum :=
  { id := "cumming2026_15_fut"
    source := ⟨"koev-2017", "(24)"⟩
    reportedIn := some ⟨"cumming-2026", "(15)"⟩
    language := "bulg1262"
    primaryText := "Včera v Pariž štja-l-o da vali."
    glossedTokens := [("Včera", "yesterday"), ("v", "in"), ("Pariž", "Paris"), ("štja-l-o", "will-EV-NEUT"), ("da", "to"), ("vali", "rain")]
    glossedWords := [⟨[['V', 'č', 'e', 'r', 'a']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['v']], [['i', 'n']]⟩, ⟨[['P', 'a', 'r', 'i', 'ž']], [['P', 'a', 'r', 'i', 's']]⟩, ⟨[['š', 't', 'j', 'a'], ['l'], ['o']], [['w', 'i', 'l', 'l'], ['E', 'V'], ['N', 'E', 'U', 'T']]⟩, ⟨[['d', 'a']], [['t', 'o']]⟩, ⟨[['v', 'a', 'l', 'i']], [['r', 'a', 'i', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "You learned earlier today that it had rained yesterday in Paris."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "FUT + -l"), ("eventTime", "1"), ("acquisitionTime", "2"), ("speechTime", "3")] }

def ex_16_fut : Datum :=
  { id := "cumming2026_16_fut"
    source := ⟨"koev-2017", "(25)"⟩
    reportedIn := some ⟨"cumming-2026", "(16)"⟩
    language := "bulg1262"
    primaryText := "Včera v Pariž štja-l-o da vali."
    glossedTokens := [("Včera", "yesterday"), ("v", "in"), ("Pariž", "Paris"), ("štja-l-o", "will-EV-NEUT"), ("da", "to"), ("vali", "rain")]
    glossedWords := [⟨[['V', 'č', 'e', 'r', 'a']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['v']], [['i', 'n']]⟩, ⟨[['P', 'a', 'r', 'i', 'ž']], [['P', 'a', 'r', 'i', 's']]⟩, ⟨[['š', 't', 'j', 'a'], ['l'], ['o']], [['w', 'i', 'l', 'l'], ['E', 'V'], ['N', 'E', 'U', 'T']]⟩, ⟨[['d', 'a']], [['t', 'o']]⟩, ⟨[['v', 'a', 'l', 'i']], [['r', 'a', 'i', 'n']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The day before yesterday you watched the weather forecast and learned that it was going to rain yesterday in Paris."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "FUT + -l"), ("acquisitionTime", "0"), ("eventTime", "1"), ("speechTime", "2")] }

def ex_16_nfut : Datum :=
  { id := "cumming2026_16_nfut"
    source := ⟨"koev-2017", "(25)"⟩
    reportedIn := some ⟨"cumming-2026", "(16)"⟩
    language := "bulg1262"
    primaryText := "Včera v Pariž valja-∅-l-o."
    glossedTokens := [("Včera", "yesterday"), ("v", "in"), ("Pariž", "Paris"), ("valja-∅-l-o", "rain-NFUT-EV-NEUT")]
    glossedWords := [⟨[['V', 'č', 'e', 'r', 'a']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['v']], [['i', 'n']]⟩, ⟨[['P', 'a', 'r', 'i', 'ž']], [['P', 'a', 'r', 'i', 's']]⟩, ⟨[['v', 'a', 'l', 'j', 'a'], ['∅'], ['l'], ['o']], [['r', 'a', 'i', 'n'], ['N', 'F', 'U', 'T'], ['E', 'V'], ['N', 'E', 'U', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The day before yesterday you watched the weather forecast and learned that it was going to rain yesterday in Paris."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "NFUT + -l"), ("acquisitionTime", "0"), ("eventTime", "1"), ("speechTime", "2")] }

def ex_33a : Datum :=
  { id := "cumming2026_33a"
    source := ⟨"koev-2017", "(15)"⟩
    reportedIn := some ⟨"cumming-2026", "(33a)"⟩
    language := "bulg1262"
    primaryText := "Utre v Sofia valja-∅-l-o."
    glossedTokens := [("Utre", "tomorrow"), ("v", "in"), ("Sofia", "Sofia"), ("valja-∅-l-o", "rain-NFUT-EV-NEUT")]
    glossedWords := [⟨[['U', 't', 'r', 'e']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['v']], [['i', 'n']]⟩, ⟨[['S', 'o', 'f', 'i', 'a']], [['S', 'o', 'f', 'i', 'a']]⟩, ⟨[['v', 'a', 'l', 'j', 'a'], ['∅'], ['l'], ['o']], [['r', 'a', 'i', 'n'], ['N', 'F', 'U', 'T'], ['E', 'V'], ['N', 'E', 'U', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "NFUT + -l"), ("acquisitionTime", "2"), ("speechTime", "2"), ("eventTime", "3")] }

def ex_33b : Datum :=
  { id := "cumming2026_33b"
    source := ⟨"koev-2017", "(16)"⟩
    reportedIn := some ⟨"cumming-2026", "(33b)"⟩
    language := "bulg1262"
    primaryText := "Utre toj bi-∅-l v Sofia."
    glossedTokens := [("Utre", "tomorrow"), ("toj", "he"), ("bi-∅-l", "be-NFUT-EV"), ("v", "in"), ("Sofia", "Sofia")]
    glossedWords := [⟨[['U', 't', 'r', 'e']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['t', 'o', 'j']], [['h', 'e']]⟩, ⟨[['b', 'i'], ['∅'], ['l']], [['b', 'e'], ['N', 'F', 'U', 'T'], ['E', 'V']]⟩, ⟨[['v']], [['i', 'n']]⟩, ⟨[['S', 'o', 'f', 'i', 'a']], [['S', 'o', 'f', 'i', 'a']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker knows only of the plan."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "NFUT + -l"), ("acquisitionTime", "2"), ("speechTime", "2"), ("eventTime", "3"), ("scheduled", "true")] }

def ex_34 : Datum :=
  { id := "cumming2026_34"
    source := ⟨"lee-2013", "(9a)"⟩
    reportedIn := some ⟨"cumming-2026", "(34)"⟩
    language := "kore1280"
    primaryText := "Obama-ka naycwu-ey hankwuk-ey o-∅-te-la."
    glossedTokens := [("Obama-ka", "Obama-NOM"), ("naycwu-ey", "next.week-at"), ("hankwuk-ey", "Korea-to"), ("o-∅-te-la", "come-PRES-TE-DECL")]
    glossedWords := [⟨[['O', 'b', 'a', 'm', 'a'], ['k', 'a']], [['O', 'b', 'a', 'm', 'a'], ['N', 'O', 'M']]⟩, ⟨[['n', 'a', 'y', 'c', 'w', 'u'], ['e', 'y']], [['n', 'e', 'x', 't', '.', 'w', 'e', 'e', 'k'], ['a', 't']]⟩, ⟨[['h', 'a', 'n', 'k', 'w', 'u', 'k'], ['e', 'y']], [['K', 'o', 'r', 'e', 'a'], ['t', 'o']]⟩, ⟨[['o'], ['∅'], ['t', 'e'], ['l', 'a']], [['c', 'o', 'm', 'e'], ['P', 'R', 'E', 'S'], ['T', 'E'], ['D', 'E', 'C', 'L']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Yenghi read the newspaper yesterday, which mentioned Obama's visit to Korea next week; now she says."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "-te PRES"), ("acquisitionTime", "1"), ("speechTime", "2"), ("eventTime", "5"), ("scheduled", "true")] }

def ex_28b : Datum :=
  { id := "cumming2026_28b"
    source := ⟨"ninan-2022", "p. 433"⟩
    reportedIn := some ⟨"cumming-2026", "(28b)"⟩
    language := "stan1293"
    primaryText := "He's great. He spent the weekend in New York."
    glossedTokens := []
    context := "Jack told the speaker on Thursday that he was leaving the next day for a weekend in New York; on Monday, without having heard from him, the speaker is asked how Jack is doing."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple past"), ("acquisitionTime", "0"), ("eventTime", "1"), ("speechTime", "2"), ("scheduled", "true")] }

def ex_29 : Datum :=
  { id := "cumming2026_29"
    source := ⟨"cariani-2021", "p. 262"⟩
    reportedIn := some ⟨"cumming-2026", "(29)"⟩
    language := "stan1293"
    primaryText := "Simona returned them."
    glossedTokens := []
    context := "At 1 p.m. Simona told Akari she would be at the library at 2 p.m. to return some books; at 2:30 p.m. Jess asks Akari whether the books were returned."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "simple past"), ("acquisitionTime", "0"), ("eventTime", "1"), ("speechTime", "2"), ("scheduled", "true")] }

def ex_30 : Datum :=
  { id := "cumming2026_30"
    source := ⟨"cumming-2026", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alma is enjoying the meal tonight."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("form", "present progressive"), ("acquisitionTime", "2"), ("speechTime", "2"), ("eventTime", "3")] }

def ex_31a : Datum :=
  { id := "cumming2026_31a"
    source := ⟨"cumming-2026", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jack is spending next weekend in New York."
    glossedTokens := []
    context := "The scenario of (28)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "present progressive"), ("acquisitionTime", "0"), ("speechTime", "1"), ("eventTime", "2"), ("scheduled", "true")] }

def ex_31b : Datum :=
  { id := "cumming2026_31b"
    source := ⟨"cumming-2026", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Simona is returning the books later today."
    glossedTokens := []
    context := "The scenario of (29)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "present progressive"), ("acquisitionTime", "0"), ("speechTime", "1"), ("eventTime", "2"), ("scheduled", "true")] }

def all : List Datum := [ex_1, ex_2_prior, ex_2_downstream, ex_4a, ex_11c, ex_12b, ex_21a_inferential, ex_21a_abductive, ex_13a, ex_13b, ex_13c, ex_14a, ex_14b, ex_14c, ex_15_nfut, ex_15_fut, ex_16_fut, ex_16_nfut, ex_33a, ex_33b, ex_34, ex_28b, ex_29, ex_30, ex_31a, ex_31b]

end Cumming2026.Examples
