module

public import Linglib.Data.Examples.Schema

/-!
# `AlstottAravind2026` — typed example data

Auto-generated from `Linglib/Data/Examples/AlstottAravind2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlstottAravind2026.Examples`.
-/

@[expose] public section

namespace AlstottAravind2026.Examples

def ex_1a : Datum :=
  { id := "alstottaravind2026_1a"
    source := ⟨"alstott-aravind-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma was happy after Hector was happy."
    glossedTokens := []
    context := "Hector was happy from 6pm to 8pm; Emma was happy 5–5:30pm (Scenario A), 6:30–7pm (Scenario B), or 8–8:30pm (Scenario C)."
    judgment := .acceptable
    contrasts := []
    readings := [("after-start", .acceptable), ("after-finish", .acceptable)]
    paperFeatures := [("construction", "after"), ("telicity", "atelic")] }

def ex_1b : Datum :=
  { id := "alstottaravind2026_1b"
    source := ⟨"alstott-aravind-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma was happy before Hector was happy."
    glossedTokens := []
    context := "Hector was happy from 6pm to 8pm; Emma was happy 5–5:30pm (Scenario A), 6:30–7pm (Scenario B), or 8–8:30pm (Scenario C)."
    judgment := .acceptable
    contrasts := []
    readings := [("before-start", .acceptable), ("before-finish", .unacceptable)]
    paperFeatures := [("construction", "before"), ("telicity", "atelic")] }

def ex_2a : Datum :=
  { id := "alstottaravind2026_2a"
    source := ⟨"alstott-aravind-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma was nervous before Jackson climbed the mountain."
    glossedTokens := []
    context := "Jackson climbed a mountain from 9am to 9pm; Emma was nervous 5am–8pm (Scenario A), 12–3pm (Scenario B), or 10pm–1am (Scenario C)."
    judgment := .acceptable
    contrasts := []
    readings := [("before-start", .acceptable), ("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("telicity", "telic")] }

def ex_2b : Datum :=
  { id := "alstottaravind2026_2b"
    source := ⟨"alstott-aravind-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma was nervous after Jackson climbed the mountain."
    glossedTokens := []
    context := "Jackson climbed a mountain from 9am to 9pm; Emma was nervous 5am–8pm (Scenario A), 12–3pm (Scenario B), or 10pm–1am (Scenario C)."
    judgment := .acceptable
    contrasts := []
    readings := [("after-start", .unacceptable), ("after-finish", .acceptable)]
    paperFeatures := [("construction", "after"), ("telicity", "telic")] }

def ex_3a : Datum :=
  { id := "alstottaravind2026_3a"
    source := ⟨"alstott-aravind-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Within an hour, Hector was happy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("change of state", .acceptable)]
    paperFeatures := [("construction", "within"), ("telicity", "atelic")] }

def ex_3b : Datum :=
  { id := "alstottaravind2026_3b"
    source := ⟨"alstott-aravind-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jackson climbed the mountain at 7pm sharp."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("completive", .acceptable)]
    paperFeatures := [("construction", "at"), ("telicity", "telic")] }

def exp1a_coercion : Datum :=
  { id := "alstottaravind2026_exp1a_coercion"
    source := ⟨"alstott-aravind-2026", "Table 1 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Within fifteen minutes Jessica was mad in office hours."
    glossedTokens := []
    context := "(27a) Alex read one of his own articles to Jessica in full; by the fifteen-minute mark, Jessica voiced her annoyance."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1a"), ("trial", "aspectualCoercion"), ("construction", "within"), ("telicity", "atelic"), ("rtCost", "no"), ("naturalness", "null")] }

def exp1a_control : Datum :=
  { id := "alstottaravind2026_exp1a_control"
    source := ⟨"alstott-aravind-2026", "Table 1 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For fifteen minutes Jessica was mad in office hours."
    glossedTokens := []
    context := "(27b) Alex read his article during the first fifteen minutes, which annoyed Jessica the whole time."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1a"), ("trial", "aspectualControl"), ("construction", "for"), ("telicity", "atelic")] }

def exp1a_complement : Datum :=
  { id := "alstottaravind2026_exp1a_complement"
    source := ⟨"alstott-aravind-2026", "Table 1 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex continued his article despite Jessica's protest."
    glossedTokens := []
    context := "(27a) or (27b)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1a"), ("trial", "complementCoercion"), ("construction", "complement"), ("rtCost", "yes"), ("region", "noun+1"), ("naturalness", "lower")] }

def exp1a_complementControl : Datum :=
  { id := "alstottaravind2026_exp1a_complementControl"
    source := ⟨"alstott-aravind-2026", "Table 1 (d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex read his article despite Jessica's protest."
    glossedTokens := []
    context := "(27a) or (27b)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1a"), ("trial", "complementControl"), ("construction", "complement")] }

def exp1b_coercion : Datum :=
  { id := "alstottaravind2026_exp1b_coercion"
    source := ⟨"alstott-aravind-2026", "Table 2 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "At 9pm sharp Hector built the humble tent."
    glossedTokens := []
    context := "(28) Hector started building the tent at 8:55pm, and the tent was fully set up at 9pm."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1b"), ("trial", "aspectualCoercion"), ("construction", "at"), ("telicity", "telic"), ("rtCost", "yes"), ("region", "verb+1"), ("naturalness", "lower")] }

def exp1b_control : Datum :=
  { id := "alstottaravind2026_exp1b_control"
    source := ⟨"alstott-aravind-2026", "Table 2 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In five minutes Hector built the humble tent."
    glossedTokens := []
    context := "(28) Hector started building the tent at 8:55pm, and the tent was fully set up five minutes after Emma made the bet."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1b"), ("trial", "aspectualControl"), ("construction", "in"), ("telicity", "telic")] }

def exp1b_complement : Datum :=
  { id := "alstottaravind2026_exp1b_complement"
    source := ⟨"alstott-aravind-2026", "Table 2 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hector finished the tent in front of Emma."
    glossedTokens := []
    context := "(28), both endings."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1b"), ("trial", "complementCoercion"), ("construction", "complement"), ("rtCost", "yes"), ("region", "noun+1"), ("naturalness", "lower")] }

def exp1b_complementControl : Datum :=
  { id := "alstottaravind2026_exp1b_complementControl"
    source := ⟨"alstott-aravind-2026", "Table 2 (d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hector built the tent in front of Emma."
    glossedTokens := []
    context := "(28), both endings."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "1b"), ("trial", "complementControl"), ("construction", "complement")] }

def exp2_noCoercion : Datum :=
  { id := "alstottaravind2026_exp2_noCoercion"
    source := ⟨"alstott-aravind-2026", "Table 3 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma was irritable before Hector built the tent in the woods."
    glossedTokens := []
    context := "(29a) Hector pulled out the camping equipment at 4pm and the tent was fully up by 4:30pm; Emma had become irritable when the wind started (2pm) and regained her composure at 4:30pm."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2"), ("trial", "aspectualControl"), ("construction", "before"), ("telicity", "telic"), ("context", "beforeStart")] }

def exp2_completive : Datum :=
  { id := "alstottaravind2026_exp2_completive"
    source := ⟨"alstott-aravind-2026", "Table 3 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma was irritable before Hector built the tent in the woods."
    glossedTokens := []
    context := "(29b) Same as (29a), but Emma became irritable when Hector had to start over at 4:15pm and regained her composure at 4:30pm."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2"), ("trial", "aspectualCoercion"), ("construction", "before"), ("telicity", "telic"), ("context", "beforeFinish"), ("rtCost", "yes"), ("region", "verb+2"), ("preregistered", "no"), ("naturalness", "lower")] }

def exp2_complement : Datum :=
  { id := "alstottaravind2026_exp2_complement"
    source := ⟨"alstott-aravind-2026", "Table 3 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma was irritable before Hector finished the tent in the woods."
    glossedTokens := []
    context := "(29b)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "2"), ("trial", "complementCoercion"), ("construction", "complement"), ("rtCost", "yes"), ("region", "noun"), ("naturalness", "lower")] }

def exp3_coercion : Datum :=
  { id := "alstottaravind2026_exp3_coercion"
    source := ⟨"alstott-aravind-2026", "Table 4 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Within fifteen minutes Jessica tolerated the unhelpful professor."
    glossedTokens := []
    context := "(30a) Jessica voiced her annoyance at first, but by the fifteen-minute mark had given up and decided to tolerate Alex."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3"), ("trial", "aspectualCoercion"), ("construction", "within"), ("telicity", "atelic"), ("rtCost", "no"), ("naturalness", "null")] }

def exp3_control : Datum :=
  { id := "alstottaravind2026_exp3_control"
    source := ⟨"alstott-aravind-2026", "Table 4 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For fifteen minutes Jessica tolerated the unhelpful professor."
    glossedTokens := []
    context := "(30b) Jessica tolerated Alex during the first fifteen minutes, then snapped."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3"), ("trial", "aspectualControl"), ("construction", "for"), ("telicity", "atelic")] }

def exp3_complement : Datum :=
  { id := "alstottaravind2026_exp3_complement"
    source := ⟨"alstott-aravind-2026", "Table 4 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex continued his article despite Jessica's protest."
    glossedTokens := []
    context := "(30a) or (30b)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "3"), ("trial", "complementCoercion"), ("construction", "complement"), ("rtCost", "yes"), ("region", "noun+1"), ("naturalness", "lower")] }

def exp4_coercion : Datum :=
  { id := "alstottaravind2026_exp4_coercion"
    source := ⟨"alstott-aravind-2026", "Table 5 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dave was regretful after Lara feared the large dog."
    glossedTokens := []
    context := "(31a) Lara felt fear towards the dog 10–10:15am; Dave felt regretful from 10:05 until Lara regained her composure at 10:15."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "4"), ("trial", "aspectualCoercion"), ("construction", "after"), ("telicity", "atelic"), ("context", "afterStart"), ("rtCost", "yes"), ("region", "verb+2"), ("preregistered", "no"), ("naturalness", "lower")] }

def exp4_control : Datum :=
  { id := "alstottaravind2026_exp4_control"
    source := ⟨"alstott-aravind-2026", "Table 5 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dave was regretful after Lara feared the large dog."
    glossedTokens := []
    context := "(31b) Same as (31a), but Dave's regret lasted for many days."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "4"), ("trial", "aspectualControl"), ("construction", "after"), ("telicity", "atelic"), ("context", "afterFinish")] }

def exp4_complement : Datum :=
  { id := "alstottaravind2026_exp4_complement"
    source := ⟨"alstott-aravind-2026", "Table 5 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dave was regretful after Lara enjoyed a cigarette outside the building."
    glossedTokens := []
    context := "(31c) Lara smoked a cigarette outside 9:50–9:55am; Dave passed by at 9:56, smelled the smoke, and felt regretful."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "4"), ("trial", "complementCoercion"), ("construction", "complement"), ("rtCost", "no"), ("naturalness", "lower")] }

def exp4_complementControl : Datum :=
  { id := "alstottaravind2026_exp4_complementControl"
    source := ⟨"alstott-aravind-2026", "Table 5 (d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dave was regretful after Lara smoked a cigarette outside the building."
    glossedTokens := []
    context := "(31c)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("experiment", "4"), ("trial", "complementControl"), ("construction", "complement")] }

def ex_32a : Datum :=
  { id := "alstottaravind2026_32a"
    source := ⟨"alstott-aravind-2026", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Within an hour, Ben was sick."
    glossedTokens := []
    context := "Ben was exposed to a virus at 6pm."
    judgment := .acceptable
    contrasts := []
    readings := [("became sick during 6–7pm", .acceptable)]
    paperFeatures := [("construction", "within"), ("telicity", "atelic")] }

def ex_35a : Datum :=
  { id := "alstottaravind2026_35a"
    source := ⟨"alstott-aravind-2026", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Within forty-five minutes, Ben was sick."
    glossedTokens := []
    context := "Ben was exposed to a virus at 6pm."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "within"), ("telicity", "atelic"), ("alternativeOf", "(32a)")] }

def ex_36a : Datum :=
  { id := "alstottaravind2026_36a"
    source := ⟨"alstott-aravind-2026", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Within half an hour, Hector ate the burrito."
    glossedTokens := []
    context := "Hector bought a burrito at 6pm."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "within"), ("telicity", "telic")] }

def ex_17a : Datum :=
  { id := "alstottaravind2026_17a"
    source := ⟨"rett-2020a", "(12a)"⟩
    reportedIn := some ⟨"alstott-aravind-2026", "(17a)"⟩
    language := "taga1270"
    primaryText := "Um-alis siya bago niya w<in>alisan ang-sahig"
    glossedTokens := [("Um-alis", "PFV.NEUT-leave"), ("siya", "3SG"), ("bago", "before"), ("niya", "3SG"), ("w<in>alisan", "<PFV.NEUT>-sweep"), ("ang-sahig", "floor")]
    glossedWords := [⟨['U', 'm', '-', 'a', 'l', 'i', 's'], ['P', 'F', 'V', '.', 'N', 'E', 'U', 'T', '-', 'l', 'e', 'a', 'v', 'e'], [⟨['U', 'm'], ['P', 'F', 'V', '.', 'N', 'E', 'U', 'T'], none⟩, ⟨['a', 'l', 'i', 's'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩]⟩, ⟨['s', 'i', 'y', 'a'], ['3', 'S', 'G'], [⟨['s', 'i', 'y', 'a'], ['3', 'S', 'G'], none⟩]⟩, ⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['n', 'i', 'y', 'a'], ['3', 'S', 'G'], [⟨['n', 'i', 'y', 'a'], ['3', 'S', 'G'], none⟩]⟩, ⟨['w', '<', 'i', 'n', '>', 'a', 'l', 'i', 's', 'a', 'n'], ['<', 'P', 'F', 'V', '.', 'N', 'E', 'U', 'T', '>', '-', 's', 'w', 'e', 'e', 'p'], []⟩, ⟨['a', 'n', 'g', '-', 's', 'a', 'h', 'i', 'g'], ['f', 'l', 'o', 'o', 'r'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("before-start", .acceptable), ("before-finish", .unacceptable)]
    paperFeatures := [("construction", "before"), ("aspect", "pfv.neut")] }

def ex_17b : Datum :=
  { id := "alstottaravind2026_17b"
    source := ⟨"rett-2020a", "(12b)"⟩
    reportedIn := some ⟨"alstott-aravind-2026", "(17b)"⟩
    language := "taga1270"
    primaryText := "Um-alis siya bago niya na-walisan ang-sahig"
    glossedTokens := [("Um-alis", "PFV.NEUT-leave"), ("siya", "3SG"), ("bago", "before"), ("niya", "3SG"), ("na-walisan", "AIA-sweep"), ("ang-sahig", "floor")]
    glossedWords := [⟨['U', 'm', '-', 'a', 'l', 'i', 's'], ['P', 'F', 'V', '.', 'N', 'E', 'U', 'T', '-', 'l', 'e', 'a', 'v', 'e'], [⟨['U', 'm'], ['P', 'F', 'V', '.', 'N', 'E', 'U', 'T'], none⟩, ⟨['a', 'l', 'i', 's'], ['l', 'e', 'a', 'v', 'e'], some '-'⟩]⟩, ⟨['s', 'i', 'y', 'a'], ['3', 'S', 'G'], [⟨['s', 'i', 'y', 'a'], ['3', 'S', 'G'], none⟩]⟩, ⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], [⟨['b', 'a', 'g', 'o'], ['b', 'e', 'f', 'o', 'r', 'e'], none⟩]⟩, ⟨['n', 'i', 'y', 'a'], ['3', 'S', 'G'], [⟨['n', 'i', 'y', 'a'], ['3', 'S', 'G'], none⟩]⟩, ⟨['n', 'a', '-', 'w', 'a', 'l', 'i', 's', 'a', 'n'], ['A', 'I', 'A', '-', 's', 'w', 'e', 'e', 'p'], [⟨['n', 'a'], ['A', 'I', 'A'], none⟩, ⟨['w', 'a', 'l', 'i', 's', 'a', 'n'], ['s', 'w', 'e', 'e', 'p'], some '-'⟩]⟩, ⟨['a', 'n', 'g', '-', 's', 'a', 'h', 'i', 'g'], ['f', 'l', 'o', 'o', 'r'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("before-finish", .acceptable)]
    paperFeatures := [("construction", "before"), ("aspect", "aia")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, exp1a_coercion, exp1a_control, exp1a_complement, exp1a_complementControl, exp1b_coercion, exp1b_control, exp1b_complement, exp1b_complementControl, exp2_noCoercion, exp2_completive, exp2_complement, exp3_coercion, exp3_control, exp3_complement, exp4_coercion, exp4_control, exp4_complement, exp4_complementControl, ex_32a, ex_35a, ex_36a, ex_17a, ex_17b]

end AlstottAravind2026.Examples
