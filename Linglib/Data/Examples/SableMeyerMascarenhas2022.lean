module

public import Linglib.Data.Examples.Schema

/-!
# `SableMeyerMascarenhas2022` — typed example data

Auto-generated from `Linglib/Data/Examples/SableMeyerMascarenhas2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SableMeyerMascarenhas2022.Examples`.
-/

@[expose] public section

namespace SableMeyerMascarenhas2022.Examples

def sm2022_1_classical : Datum :=
  { id := "sm2022_1_classical"
    source := ⟨"sable-meyer-mascarenhas-2022", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary speaks French."
    glossedTokens := []
    context := "Reasoning task: does the conclusion follow? Adapted from Walsh and Johnson-Laird's items."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("kind", "classical"), ("acceptance", "85%")] }

def sm2022_2_indirect : Datum :=
  { id := "sm2022_2_indirect"
    source := ⟨"sable-meyer-mascarenhas-2022", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The guitar was out of tune."
    glossedTokens := []
    context := "Reasoning task: the hint does not match any conjunct of the first premise; it is causally connected to 'the car slowed down'."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("kind", "indirect, hint step"), ("link", "the brake was depressed causes the car slowed down")] }

def sm2022_3_walsh_johnson_laird : Datum :=
  { id := "sm2022_3_walsh_johnson_laird"
    source := ⟨"walsh-johnson-laird-2004", "items"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(3)"⟩
    language := "stan1293"
    primaryText := "She is looking at the TV."
    glossedTokens := []
    context := "The original four-proposition items."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("kind", "classical"), ("acceptance", "85%")] }

def sm2022_11_conclusion_step : Datum :=
  { id := "sm2022_11_conclusion_step"
    source := ⟨"sable-meyer-mascarenhas-2022", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The car slowed down."
    glossedTokens := []
    context := "Experiment 2: the hint matches a conjunct exactly; the causal link does its work at the conclusion step."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("mark", "fallacious"), ("kind", "indirect, conclusion step")] }

def sm2022_13_two_conclusions : Datum :=
  { id := "sm2022_13_two_conclusions"
    source := ⟨"sable-meyer-mascarenhas-2022", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ccl. 1: Mary speaks French. Ccl. 2: Bill speaks German."
    glossedTokens := []
    context := "The asymmetry between the two candidate conclusions: the revised mental model theory's weak necessity certifies both."
    judgment := .acceptable
    contrasts := [("Bill speaks German. (Ccl. 2)", .acceptable)]
    readings := []
    paperFeatures := [("conclusion1", "Mary speaks French: attractive, acceptance about 85%"), ("conclusion2", "Bill speaks German: either not at all a compelling fallacy, or a very weak illusion; original mental model theory predicts not-c")] }

def sm2022_17_linda : Datum :=
  { id := "sm2022_17_linda"
    source := ⟨"tversky-kahneman-1983", "Linda task"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(17)"⟩
    language := "stan1293"
    primaryText := "Which of these two options is the most probable?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := [("Linda is a bank teller.", .acceptable), ("Linda is a bank teller and she is active in the feminist movement.", .acceptable)]
    readings := []
    paperFeatures := [("puzzle", "conjunction fallacy"), ("parallel", "the options are the disjunctive premise (f and b) or b; the description is the hint pointing to f (18)")] }

def sm2022_9_0_fertilizer : Datum :=
  { id := "sm2022_9_0_fertilizer"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 0"⟩
    language := "stan1293"
    primaryText := "If fertilizer was put on the plants, then the plants grew quickly."
    glossedTokens := []
    context := "Norming study, d-to-a block."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "0"), ("removed", "excluded from the inference tasks: the d-to-b control block showed an effect driven by this item")] }

def sm2022_9_1_brake : Datum :=
  { id := "sm2022_9_1_brake"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 1"⟩
    language := "stan1293"
    primaryText := "If the brake was depressed, then the car slowed down."
    glossedTokens := []
    context := "Norming study, d-to-a block."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "1")] }

def sm2022_9_2_pool : Datum :=
  { id := "sm2022_9_2_pool"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 2"⟩
    language := "stan1293"
    primaryText := "If Mary jumped into the swimming pool, then Mary got wet."
    glossedTokens := []
    context := "Norming study, d-to-a block."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "2")] }

def sm2022_9_3_trigger : Datum :=
  { id := "sm2022_9_3_trigger"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 3"⟩
    language := "stan1293"
    primaryText := "If the trigger was pulled, then the gun fired."
    glossedTokens := []
    context := "Norming study, d-to-a block; also the (8i) exemplar."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "3")] }

def sm2022_9_4_fingerprints : Datum :=
  { id := "sm2022_9_4_fingerprints"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 4"⟩
    language := "stan1293"
    primaryText := "If Larry grasped the glass with his bare hands, then Larry left fingerprints on his glass."
    glossedTokens := []
    context := "Norming study, d-to-a block."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "4")] }

def sm2022_9_5_gong : Datum :=
  { id := "sm2022_9_5_gong"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 5"⟩
    language := "stan1293"
    primaryText := "If the gong was struck, then the gong sounded."
    glossedTokens := []
    context := "Norming study, d-to-a block."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "5")] }

def sm2022_9_6_studied : Datum :=
  { id := "sm2022_9_6_studied"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 6"⟩
    language := "stan1293"
    primaryText := "If John studied hard, then John did well on the test."
    glossedTokens := []
    context := "Norming study, d-to-a block."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "6")] }

def sm2022_9_7_apples : Datum :=
  { id := "sm2022_9_7_apples"
    source := ⟨"cummins-1995", "materials"⟩
    reportedIn := some ⟨"sable-meyer-mascarenhas-2022", "(9), item 7"⟩
    language := "stan1293"
    primaryText := "If the apples were ripe, then the apples fell from the tree."
    glossedTokens := []
    context := "Norming study, d-to-a block."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "d to a"), ("item", "7")] }

def sm2022_7_instructions : Datum :=
  { id := "sm2022_7_instructions"
    source := ⟨"sable-meyer-mascarenhas-2022", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The principal was worried."
    glossedTokens := []
    context := "The instructions' example of an invalid but inductively attractive conclusion; the paper's printed correct answer is no."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("role", "instructions example"), ("validity", "invalid")] }

def sm2022_8i_trigger_gun : Datum :=
  { id := "sm2022_8i_trigger_gun"
    source := ⟨"sable-meyer-mascarenhas-2022", "(8i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the trigger was pulled, then the gun fired."
    glossedTokens := []
    context := "Norming block (i), the crucial d-to-a dependence; ratings are not printed."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "(i) d to a")] }

def sm2022_8ii_gun_guitar : Datum :=
  { id := "sm2022_8ii_gun_guitar"
    source := ⟨"sable-meyer-mascarenhas-2022", "(8ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the gun fired, then the guitar was out of tune."
    glossedTokens := []
    context := "Norming block (ii), the a-to-b control; ratings are not printed."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "(ii) a to b")] }

def sm2022_8iii_trigger_guitar : Datum :=
  { id := "sm2022_8iii_trigger_guitar"
    source := ⟨"sable-meyer-mascarenhas-2022", "(8iii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the trigger was pulled, then the guitar was out of tune."
    glossedTokens := []
    context := "Norming block (iii), the d-to-b control; ratings are not printed."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("block", "(iii) d to b")] }

def all : List Datum := [sm2022_1_classical, sm2022_2_indirect, sm2022_3_walsh_johnson_laird, sm2022_11_conclusion_step, sm2022_13_two_conclusions, sm2022_17_linda, sm2022_9_0_fertilizer, sm2022_9_1_brake, sm2022_9_2_pool, sm2022_9_3_trigger, sm2022_9_4_fingerprints, sm2022_9_5_gong, sm2022_9_6_studied, sm2022_9_7_apples, sm2022_7_instructions, sm2022_8i_trigger_gun, sm2022_8ii_gun_guitar, sm2022_8iii_trigger_guitar]

end SableMeyerMascarenhas2022.Examples
