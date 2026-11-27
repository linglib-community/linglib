module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Mizuno2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Mizuno2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Mizuno2024.Examples`.
-/

@[expose] public section

namespace Mizuno2024.Examples

def en1a : Datum :=
  { id := "mizuno2024_en1a"
    source := ⟨"mizuno-2024", "(1a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "You're right. If Jones had taken arsenic last night, he would show those symptoms which he is now showing."
    glossedTokens := []
    context := "Jones is in the ER with poisoning symptoms; the investigation team is figuring out which chemical was used. One shrewd member suggests that, given the symptoms, he must have taken arsenic. The boss then says (1a) and the follow-up (1b) 'So, it looks like he did take arsenic' in a row: an Anderson conditional arguing FOR the truth of its antecedent."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "X-marking")] }

def en2 : Datum :=
  { id := "mizuno2024_en2"
    source := ⟨"mizuno-2024", "(2)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "If Jones took arsenic, he shows just exactly those symptoms which he does in fact show."
    glossedTokens := []
    context := "Same scenario as (1). The O-marked (simple-past indicative / present) counterpart of (1a)."
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "O-marking")] }

def ja3 : Datum :=
  { id := "mizuno2024_ja3"
    source := ⟨"mizuno-2024", "(3)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "John-ga ima kono siai-no naka-ni ir-eba, syoohai-wa mada wakar-ana-katta daroo."
    glossedTokens := [("John-ga", "John-NOM"), ("ima", "now"), ("kono", "this"), ("siai-no", "game-GEN"), ("naka-ni", "inside-LOC"), ("ir-eba", "be-COND"), ("syoohai-wa", "outcome-TOP"), ("mada", "yet"), ("wakar-ana-katta", "be.clear-NEG-PAST"), ("daroo", "MOD")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'g', 'a'], ['J', 'o', 'h', 'n', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['i', 'm', 'a'], ['n', 'o', 'w'], [⟨['i', 'm', 'a'], ['n', 'o', 'w'], none⟩]⟩, ⟨['k', 'o', 'n', 'o'], ['t', 'h', 'i', 's'], [⟨['k', 'o', 'n', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['s', 'i', 'a', 'i', '-', 'n', 'o'], ['g', 'a', 'm', 'e', '-', 'G', 'E', 'N'], [⟨['s', 'i', 'a', 'i'], ['g', 'a', 'm', 'e'], none⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['n', 'a', 'k', 'a', '-', 'n', 'i'], ['i', 'n', 's', 'i', 'd', 'e', '-', 'L', 'O', 'C'], [⟨['n', 'a', 'k', 'a'], ['i', 'n', 's', 'i', 'd', 'e'], none⟩, ⟨['n', 'i'], ['L', 'O', 'C'], some '-'⟩]⟩, ⟨['i', 'r', '-', 'e', 'b', 'a'], ['b', 'e', '-', 'C', 'O', 'N', 'D'], [⟨['i', 'r'], ['b', 'e'], none⟩, ⟨['e', 'b', 'a'], ['C', 'O', 'N', 'D'], some '-'⟩]⟩, ⟨['s', 'y', 'o', 'o', 'h', 'a', 'i', '-', 'w', 'a'], ['o', 'u', 't', 'c', 'o', 'm', 'e', '-', 'T', 'O', 'P'], [⟨['s', 'y', 'o', 'o', 'h', 'a', 'i'], ['o', 'u', 't', 'c', 'o', 'm', 'e'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['m', 'a', 'd', 'a'], ['y', 'e', 't'], [⟨['m', 'a', 'd', 'a'], ['y', 'e', 't'], none⟩]⟩, ⟨['w', 'a', 'k', 'a', 'r', '-', 'a', 'n', 'a', '-', 'k', 'a', 't', 't', 'a'], ['b', 'e', '.', 'c', 'l', 'e', 'a', 'r', '-', 'N', 'E', 'G', '-', 'P', 'A', 'S', 'T'], [⟨['w', 'a', 'k', 'a', 'r'], ['b', 'e', '.', 'c', 'l', 'e', 'a', 'r'], none⟩, ⟨['a', 'n', 'a'], ['N', 'E', 'G'], some '-'⟩, ⟨['k', 'a', 't', 't', 'a'], ['P', 'A', 'S', 'T'], some '-'⟩]⟩, ⟨['d', 'a', 'r', 'o', 'o'], ['M', 'O', 'D'], [⟨['d', 'a', 'r', 'o', 'o'], ['M', 'O', 'D'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "John, an ace player, has recently left the team for better pay. The team weakens considerably after losing their mainstay, and their defeat in today's game is already certain during the first half. A fan who is currently watching the game says the following."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "counterfactual"), ("strategy", "X-marking")] }

def ja4a : Datum :=
  { id := "mizuno2024_ja4a"
    source := ⟨"mizuno-2024", "(4a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ru hazuda."
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-si-ga", "Jones-Mr.-NOM"), ("sakuya", "last.night"), ("hiso-o", "arsenic-ACC"), ("nom-eba", "drink-COND"), ("kare-ga", "he-NOM"), ("ima", "now"), ("mise-tei-ru", "show-ASP-NPST"), ("syoozyoo-to", "symptom-as"), ("mattaku", "exactly"), ("onazi", "same"), ("syoozyoo-o", "symptom-ACC"), ("ima", "now"), ("mise-ru", "show-NPST"), ("hazuda", "MOD")]
    glossedWords := [⟨['T', 'a', 's', 'i', 'k', 'a', 'n', 'i'], ['y', 'o', 'u', '\'', 'r', 'e', '.', 'r', 'i', 'g', 'h', 't'], [⟨['T', 'a', 's', 'i', 'k', 'a', 'n', 'i'], ['y', 'o', 'u', '\'', 'r', 'e', '.', 'r', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['J', 'o', 'n', 'e', 's', '-', 's', 'i', '-', 'g', 'a'], ['J', 'o', 'n', 'e', 's', '-', 'M', 'r', '.', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'n', 'e', 's'], ['J', 'o', 'n', 'e', 's'], none⟩, ⟨['s', 'i'], ['M', 'r', '.'], some '-'⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['s', 'a', 'k', 'u', 'y', 'a'], ['l', 'a', 's', 't', '.', 'n', 'i', 'g', 'h', 't'], [⟨['s', 'a', 'k', 'u', 'y', 'a'], ['l', 'a', 's', 't', '.', 'n', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['h', 'i', 's', 'o', '-', 'o'], ['a', 'r', 's', 'e', 'n', 'i', 'c', '-', 'A', 'C', 'C'], [⟨['h', 'i', 's', 'o'], ['a', 'r', 's', 'e', 'n', 'i', 'c'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['n', 'o', 'm', '-', 'e', 'b', 'a'], ['d', 'r', 'i', 'n', 'k', '-', 'C', 'O', 'N', 'D'], [⟨['n', 'o', 'm'], ['d', 'r', 'i', 'n', 'k'], none⟩, ⟨['e', 'b', 'a'], ['C', 'O', 'N', 'D'], some '-'⟩]⟩, ⟨['k', 'a', 'r', 'e', '-', 'g', 'a'], ['h', 'e', '-', 'N', 'O', 'M'], [⟨['k', 'a', 'r', 'e'], ['h', 'e'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['i', 'm', 'a'], ['n', 'o', 'w'], [⟨['i', 'm', 'a'], ['n', 'o', 'w'], none⟩]⟩, ⟨['m', 'i', 's', 'e', '-', 't', 'e', 'i', '-', 'r', 'u'], ['s', 'h', 'o', 'w', '-', 'A', 'S', 'P', '-', 'N', 'P', 'S', 'T'], [⟨['m', 'i', 's', 'e'], ['s', 'h', 'o', 'w'], none⟩, ⟨['t', 'e', 'i'], ['A', 'S', 'P'], some '-'⟩, ⟨['r', 'u'], ['N', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['s', 'y', 'o', 'o', 'z', 'y', 'o', 'o', '-', 't', 'o'], ['s', 'y', 'm', 'p', 't', 'o', 'm', '-', 'a', 's'], [⟨['s', 'y', 'o', 'o', 'z', 'y', 'o', 'o'], ['s', 'y', 'm', 'p', 't', 'o', 'm'], none⟩, ⟨['t', 'o'], ['a', 's'], some '-'⟩]⟩, ⟨['m', 'a', 't', 't', 'a', 'k', 'u'], ['e', 'x', 'a', 'c', 't', 'l', 'y'], [⟨['m', 'a', 't', 't', 'a', 'k', 'u'], ['e', 'x', 'a', 'c', 't', 'l', 'y'], none⟩]⟩, ⟨['o', 'n', 'a', 'z', 'i'], ['s', 'a', 'm', 'e'], [⟨['o', 'n', 'a', 'z', 'i'], ['s', 'a', 'm', 'e'], none⟩]⟩, ⟨['s', 'y', 'o', 'o', 'z', 'y', 'o', 'o', '-', 'o'], ['s', 'y', 'm', 'p', 't', 'o', 'm', '-', 'A', 'C', 'C'], [⟨['s', 'y', 'o', 'o', 'z', 'y', 'o', 'o'], ['s', 'y', 'm', 'p', 't', 'o', 'm'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['i', 'm', 'a'], ['n', 'o', 'w'], [⟨['i', 'm', 'a'], ['n', 'o', 'w'], none⟩]⟩, ⟨['m', 'i', 's', 'e', '-', 'r', 'u'], ['s', 'h', 'o', 'w', '-', 'N', 'P', 'S', 'T'], [⟨['m', 'i', 's', 'e'], ['s', 'h', 'o', 'w'], none⟩, ⟨['r', 'u'], ['N', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['h', 'a', 'z', 'u', 'd', 'a'], ['M', 'O', 'D'], [⟨['h', 'a', 'z', 'u', 'd', 'a'], ['M', 'O', 'D'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    contrasts := [("Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ta hazuda.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "O-marking")] }

def ja7a : Datum :=
  { id := "mizuno2024_ja7a"
    source := ⟨"mizuno-2024", "(7a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, kare-no zissai-no nyuukoku geeto-to mattaku onazi geeto-o, kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-uru (hazuda)."
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-ga", "Jones-NOM"), ("ototoi", "two.days.ago"), ("Manila-o", "Manila-ACC"), ("syuppatusu-reba", "leave-COND"), ("kare-no", "he-GEN"), ("zissai-no", "actual-GEN"), ("nyuukoku", "immigration"), ("geeto-to", "gate-as"), ("mattaku", "exactly"), ("onazi", "same"), ("geeto-o", "gate-ACC"), ("kinoo-no", "yesterday-GEN"), ("tuuka", "passage"), ("zikoku-to", "time-as"), ("mattaku", "exactly"), ("onazi", "same"), ("zikoku-ni", "time-at"), ("tuukas-uru", "pass-NPST"), ("(hazuda)", "MOD")]
    glossedWords := [⟨['T', 'a', 's', 'i', 'k', 'a', 'n', 'i'], ['y', 'o', 'u', '\'', 'r', 'e', '.', 'r', 'i', 'g', 'h', 't'], [⟨['T', 'a', 's', 'i', 'k', 'a', 'n', 'i'], ['y', 'o', 'u', '\'', 'r', 'e', '.', 'r', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['J', 'o', 'n', 'e', 's', '-', 'g', 'a'], ['J', 'o', 'n', 'e', 's', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'n', 'e', 's'], ['J', 'o', 'n', 'e', 's'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['o', 't', 'o', 't', 'o', 'i'], ['t', 'w', 'o', '.', 'd', 'a', 'y', 's', '.', 'a', 'g', 'o'], [⟨['o', 't', 'o', 't', 'o', 'i'], ['t', 'w', 'o', '.', 'd', 'a', 'y', 's', '.', 'a', 'g', 'o'], none⟩]⟩, ⟨['M', 'a', 'n', 'i', 'l', 'a', '-', 'o'], ['M', 'a', 'n', 'i', 'l', 'a', '-', 'A', 'C', 'C'], [⟨['M', 'a', 'n', 'i', 'l', 'a'], ['M', 'a', 'n', 'i', 'l', 'a'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['s', 'y', 'u', 'p', 'p', 'a', 't', 'u', 's', 'u', '-', 'r', 'e', 'b', 'a'], ['l', 'e', 'a', 'v', 'e', '-', 'C', 'O', 'N', 'D'], [⟨['s', 'y', 'u', 'p', 'p', 'a', 't', 'u', 's', 'u'], ['l', 'e', 'a', 'v', 'e'], none⟩, ⟨['r', 'e', 'b', 'a'], ['C', 'O', 'N', 'D'], some '-'⟩]⟩, ⟨['k', 'a', 'r', 'e', '-', 'n', 'o'], ['h', 'e', '-', 'G', 'E', 'N'], [⟨['k', 'a', 'r', 'e'], ['h', 'e'], none⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['z', 'i', 's', 's', 'a', 'i', '-', 'n', 'o'], ['a', 'c', 't', 'u', 'a', 'l', '-', 'G', 'E', 'N'], [⟨['z', 'i', 's', 's', 'a', 'i'], ['a', 'c', 't', 'u', 'a', 'l'], none⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['n', 'y', 'u', 'u', 'k', 'o', 'k', 'u'], ['i', 'm', 'm', 'i', 'g', 'r', 'a', 't', 'i', 'o', 'n'], [⟨['n', 'y', 'u', 'u', 'k', 'o', 'k', 'u'], ['i', 'm', 'm', 'i', 'g', 'r', 'a', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['g', 'e', 'e', 't', 'o', '-', 't', 'o'], ['g', 'a', 't', 'e', '-', 'a', 's'], [⟨['g', 'e', 'e', 't', 'o'], ['g', 'a', 't', 'e'], none⟩, ⟨['t', 'o'], ['a', 's'], some '-'⟩]⟩, ⟨['m', 'a', 't', 't', 'a', 'k', 'u'], ['e', 'x', 'a', 'c', 't', 'l', 'y'], [⟨['m', 'a', 't', 't', 'a', 'k', 'u'], ['e', 'x', 'a', 'c', 't', 'l', 'y'], none⟩]⟩, ⟨['o', 'n', 'a', 'z', 'i'], ['s', 'a', 'm', 'e'], [⟨['o', 'n', 'a', 'z', 'i'], ['s', 'a', 'm', 'e'], none⟩]⟩, ⟨['g', 'e', 'e', 't', 'o', '-', 'o'], ['g', 'a', 't', 'e', '-', 'A', 'C', 'C'], [⟨['g', 'e', 'e', 't', 'o'], ['g', 'a', 't', 'e'], none⟩, ⟨['o'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['k', 'i', 'n', 'o', 'o', '-', 'n', 'o'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y', '-', 'G', 'E', 'N'], [⟨['k', 'i', 'n', 'o', 'o'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩, ⟨['n', 'o'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'u', 'u', 'k', 'a'], ['p', 'a', 's', 's', 'a', 'g', 'e'], [⟨['t', 'u', 'u', 'k', 'a'], ['p', 'a', 's', 's', 'a', 'g', 'e'], none⟩]⟩, ⟨['z', 'i', 'k', 'o', 'k', 'u', '-', 't', 'o'], ['t', 'i', 'm', 'e', '-', 'a', 's'], [⟨['z', 'i', 'k', 'o', 'k', 'u'], ['t', 'i', 'm', 'e'], none⟩, ⟨['t', 'o'], ['a', 's'], some '-'⟩]⟩, ⟨['m', 'a', 't', 't', 'a', 'k', 'u'], ['e', 'x', 'a', 'c', 't', 'l', 'y'], [⟨['m', 'a', 't', 't', 'a', 'k', 'u'], ['e', 'x', 'a', 'c', 't', 'l', 'y'], none⟩]⟩, ⟨['o', 'n', 'a', 'z', 'i'], ['s', 'a', 'm', 'e'], [⟨['o', 'n', 'a', 'z', 'i'], ['s', 'a', 'm', 'e'], none⟩]⟩, ⟨['z', 'i', 'k', 'o', 'k', 'u', '-', 'n', 'i'], ['t', 'i', 'm', 'e', '-', 'a', 't'], [⟨['z', 'i', 'k', 'o', 'k', 'u'], ['t', 'i', 'm', 'e'], none⟩, ⟨['n', 'i'], ['a', 't'], some '-'⟩]⟩, ⟨['t', 'u', 'u', 'k', 'a', 's', '-', 'u', 'r', 'u'], ['p', 'a', 's', 's', '-', 'N', 'P', 'S', 'T'], [⟨['t', 'u', 'u', 'k', 'a', 's'], ['p', 'a', 's', 's'], none⟩, ⟨['u', 'r', 'u'], ['N', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['(', 'h', 'a', 'z', 'u', 'd', 'a', ')'], ['M', 'O', 'D'], [⟨['h', 'a', 'z', 'u', 'd', 'a'], ['M', 'O', 'D'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Jones is a fugitive who reportedly entered Korea via Incheon yesterday; the team infers the country he flew from. The consequent event lies overtly in the past (adverbial kinoo 'yesterday'), yet Non-Past is still required."
    judgment := .acceptable
    contrasts := [("Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, kare-no zissai-no nyuukoku geeto-to mattaku onazi geeto-o, kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-ita (hazuda).", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "O-marking"), ("hp_type", "radical")] }

def ma13a : Datum :=
  { id := "mizuno2024_ma13a"
    source := ⟨"mizuno-2024", "(13a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang."
    glossedTokens := [("Ruguo", "if"), ("Jones", "Jones"), ("zuotian", "yesterday"), ("he", "drink"), ("le", "PERF"), ("pishuang", "arsenic"), ("jiu", "then"), ("hui", "MOD"), ("chuxian", "show"), ("ta", "he"), ("xianzai", "now"), ("shiji", "actually"), ("chuxian", "show"), ("de", "REL"), ("zheyangde", "such"), ("zhengzhuang", "symptoms")]
    glossedWords := [⟨['R', 'u', 'g', 'u', 'o'], ['i', 'f'], [⟨['R', 'u', 'g', 'u', 'o'], ['i', 'f'], none⟩]⟩, ⟨['J', 'o', 'n', 'e', 's'], ['J', 'o', 'n', 'e', 's'], [⟨['J', 'o', 'n', 'e', 's'], ['J', 'o', 'n', 'e', 's'], none⟩]⟩, ⟨['z', 'u', 'o', 't', 'i', 'a', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['z', 'u', 'o', 't', 'i', 'a', 'n'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['h', 'e'], ['d', 'r', 'i', 'n', 'k'], [⟨['h', 'e'], ['d', 'r', 'i', 'n', 'k'], none⟩]⟩, ⟨['l', 'e'], ['P', 'E', 'R', 'F'], [⟨['l', 'e'], ['P', 'E', 'R', 'F'], none⟩]⟩, ⟨['p', 'i', 's', 'h', 'u', 'a', 'n', 'g'], ['a', 'r', 's', 'e', 'n', 'i', 'c'], [⟨['p', 'i', 's', 'h', 'u', 'a', 'n', 'g'], ['a', 'r', 's', 'e', 'n', 'i', 'c'], none⟩]⟩, ⟨['j', 'i', 'u'], ['t', 'h', 'e', 'n'], [⟨['j', 'i', 'u'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['h', 'u', 'i'], ['M', 'O', 'D'], [⟨['h', 'u', 'i'], ['M', 'O', 'D'], none⟩]⟩, ⟨['c', 'h', 'u', 'x', 'i', 'a', 'n'], ['s', 'h', 'o', 'w'], [⟨['c', 'h', 'u', 'x', 'i', 'a', 'n'], ['s', 'h', 'o', 'w'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['x', 'i', 'a', 'n', 'z', 'a', 'i'], ['n', 'o', 'w'], [⟨['x', 'i', 'a', 'n', 'z', 'a', 'i'], ['n', 'o', 'w'], none⟩]⟩, ⟨['s', 'h', 'i', 'j', 'i'], ['a', 'c', 't', 'u', 'a', 'l', 'l', 'y'], [⟨['s', 'h', 'i', 'j', 'i'], ['a', 'c', 't', 'u', 'a', 'l', 'l', 'y'], none⟩]⟩, ⟨['c', 'h', 'u', 'x', 'i', 'a', 'n'], ['s', 'h', 'o', 'w'], [⟨['c', 'h', 'u', 'x', 'i', 'a', 'n'], ['s', 'h', 'o', 'w'], none⟩]⟩, ⟨['d', 'e'], ['R', 'E', 'L'], [⟨['d', 'e'], ['R', 'E', 'L'], none⟩]⟩, ⟨['z', 'h', 'e', 'y', 'a', 'n', 'g', 'd', 'e'], ['s', 'u', 'c', 'h'], [⟨['z', 'h', 'e', 'y', 'a', 'n', 'g', 'd', 'e'], ['s', 'u', 'c', 'h'], none⟩]⟩, ⟨['z', 'h', 'e', 'n', 'g', 'z', 'h', 'u', 'a', 'n', 'g'], ['s', 'y', 'm', 'p', 't', 'o', 'm', 's'], [⟨['z', 'h', 'e', 'n', 'g', 'z', 'h', 'u', 'a', 'n', 'g'], ['s', 'y', 'm', 'p', 't', 'o', 'm', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    contrasts := [("Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang le.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "O-marking")] }

def en8 : Datum :=
  { id := "mizuno2024_en8"
    source := ⟨"mizuno-2024", "(8)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1293"
    primaryText := "If John came tomorrow, the party would be fun, but he probably won't come tomorrow, I think."
    glossedTokens := []
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "X-marking")] }

def ja9 : Datum :=
  { id := "mizuno2024_ja9"
    source := ⟨"mizuno-2024", "(9)"⟩
    reportedIn := none
    method := some .elicitation
    language := "nucl1643"
    primaryText := "John-ga asita kur-eba, paatii-wa totemo moriagar-u daroo, kedo, tabun kare-wa asita ko-na-i to omou."
    glossedTokens := [("John-ga", "John-NOM"), ("asita", "tomorrow"), ("kur-eba", "come-COND"), ("paatii-wa", "party-TOP"), ("totemo", "very"), ("moriagar-u", "be.fun-NPST"), ("daroo", "MOD"), ("kedo", "but"), ("tabun", "probably"), ("kare-wa", "he-TOP"), ("asita", "tomorrow"), ("ko-na-i", "come-NEG-NPST"), ("to", "COMP"), ("omou", "think")]
    glossedWords := [⟨['J', 'o', 'h', 'n', '-', 'g', 'a'], ['J', 'o', 'h', 'n', '-', 'N', 'O', 'M'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩, ⟨['g', 'a'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['a', 's', 'i', 't', 'a'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['a', 's', 'i', 't', 'a'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['k', 'u', 'r', '-', 'e', 'b', 'a'], ['c', 'o', 'm', 'e', '-', 'C', 'O', 'N', 'D'], [⟨['k', 'u', 'r'], ['c', 'o', 'm', 'e'], none⟩, ⟨['e', 'b', 'a'], ['C', 'O', 'N', 'D'], some '-'⟩]⟩, ⟨['p', 'a', 'a', 't', 'i', 'i', '-', 'w', 'a'], ['p', 'a', 'r', 't', 'y', '-', 'T', 'O', 'P'], [⟨['p', 'a', 'a', 't', 'i', 'i'], ['p', 'a', 'r', 't', 'y'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['t', 'o', 't', 'e', 'm', 'o'], ['v', 'e', 'r', 'y'], [⟨['t', 'o', 't', 'e', 'm', 'o'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['m', 'o', 'r', 'i', 'a', 'g', 'a', 'r', '-', 'u'], ['b', 'e', '.', 'f', 'u', 'n', '-', 'N', 'P', 'S', 'T'], [⟨['m', 'o', 'r', 'i', 'a', 'g', 'a', 'r'], ['b', 'e', '.', 'f', 'u', 'n'], none⟩, ⟨['u'], ['N', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['d', 'a', 'r', 'o', 'o'], ['M', 'O', 'D'], [⟨['d', 'a', 'r', 'o', 'o'], ['M', 'O', 'D'], none⟩]⟩, ⟨['k', 'e', 'd', 'o'], ['b', 'u', 't'], [⟨['k', 'e', 'd', 'o'], ['b', 'u', 't'], none⟩]⟩, ⟨['t', 'a', 'b', 'u', 'n'], ['p', 'r', 'o', 'b', 'a', 'b', 'l', 'y'], [⟨['t', 'a', 'b', 'u', 'n'], ['p', 'r', 'o', 'b', 'a', 'b', 'l', 'y'], none⟩]⟩, ⟨['k', 'a', 'r', 'e', '-', 'w', 'a'], ['h', 'e', '-', 'T', 'O', 'P'], [⟨['k', 'a', 'r', 'e'], ['h', 'e'], none⟩, ⟨['w', 'a'], ['T', 'O', 'P'], some '-'⟩]⟩, ⟨['a', 's', 'i', 't', 'a'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['a', 's', 'i', 't', 'a'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['k', 'o', '-', 'n', 'a', '-', 'i'], ['c', 'o', 'm', 'e', '-', 'N', 'E', 'G', '-', 'N', 'P', 'S', 'T'], [⟨['k', 'o'], ['c', 'o', 'm', 'e'], none⟩, ⟨['n', 'a'], ['N', 'E', 'G'], some '-'⟩, ⟨['i'], ['N', 'P', 'S', 'T'], some '-'⟩]⟩, ⟨['t', 'o'], ['C', 'O', 'M', 'P'], [⟨['t', 'o'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['o', 'm', 'o', 'u'], ['t', 'h', 'i', 'n', 'k'], [⟨['o', 'm', 'o', 'u'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    contrasts := [("John-ga asita kur-eba, paatii-wa totemo moriagat-ta daroo, kedo, tabun kare-wa asita ko-na-i to omou.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "O-marking")] }

def ma11 : Datum :=
  { id := "mizuno2024_ma11"
    source := ⟨"mizuno-2024", "(11)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai, danshi wo juede ta mingtian bu hui lai."
    glossedTokens := [("Ruguo", "if"), ("mingtian", "tomorrow"), ("John", "John"), ("lai", "come"), ("paidui", "party"), ("de", "GEN"), ("qifen", "atmosphere"), ("jiu", "then"), ("neng", "MOD"), ("huoyue", "be.lively"), ("qilai", "get"), ("danshi", "but"), ("wo", "I"), ("juede", "think"), ("ta", "he"), ("mingtian", "tomorrow"), ("bu", "not"), ("hui", "will"), ("lai", "come")]
    glossedWords := [⟨['R', 'u', 'g', 'u', 'o'], ['i', 'f'], [⟨['R', 'u', 'g', 'u', 'o'], ['i', 'f'], none⟩]⟩, ⟨['m', 'i', 'n', 'g', 't', 'i', 'a', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'i', 'n', 'g', 't', 'i', 'a', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], [⟨['J', 'o', 'h', 'n'], ['J', 'o', 'h', 'n'], none⟩]⟩, ⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], [⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['p', 'a', 'i', 'd', 'u', 'i'], ['p', 'a', 'r', 't', 'y'], [⟨['p', 'a', 'i', 'd', 'u', 'i'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩, ⟨['d', 'e'], ['G', 'E', 'N'], [⟨['d', 'e'], ['G', 'E', 'N'], none⟩]⟩, ⟨['q', 'i', 'f', 'e', 'n'], ['a', 't', 'm', 'o', 's', 'p', 'h', 'e', 'r', 'e'], [⟨['q', 'i', 'f', 'e', 'n'], ['a', 't', 'm', 'o', 's', 'p', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['j', 'i', 'u'], ['t', 'h', 'e', 'n'], [⟨['j', 'i', 'u'], ['t', 'h', 'e', 'n'], none⟩]⟩, ⟨['n', 'e', 'n', 'g'], ['M', 'O', 'D'], [⟨['n', 'e', 'n', 'g'], ['M', 'O', 'D'], none⟩]⟩, ⟨['h', 'u', 'o', 'y', 'u', 'e'], ['b', 'e', '.', 'l', 'i', 'v', 'e', 'l', 'y'], [⟨['h', 'u', 'o', 'y', 'u', 'e'], ['b', 'e', '.', 'l', 'i', 'v', 'e', 'l', 'y'], none⟩]⟩, ⟨['q', 'i', 'l', 'a', 'i'], ['g', 'e', 't'], [⟨['q', 'i', 'l', 'a', 'i'], ['g', 'e', 't'], none⟩]⟩, ⟨['d', 'a', 'n', 's', 'h', 'i'], ['b', 'u', 't'], [⟨['d', 'a', 'n', 's', 'h', 'i'], ['b', 'u', 't'], none⟩]⟩, ⟨['w', 'o'], ['I'], [⟨['w', 'o'], ['I'], none⟩]⟩, ⟨['j', 'u', 'e', 'd', 'e'], ['t', 'h', 'i', 'n', 'k'], [⟨['j', 'u', 'e', 'd', 'e'], ['t', 'h', 'i', 'n', 'k'], none⟩]⟩, ⟨['t', 'a'], ['h', 'e'], [⟨['t', 'a'], ['h', 'e'], none⟩]⟩, ⟨['m', 'i', 'n', 'g', 't', 'i', 'a', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['m', 'i', 'n', 'g', 't', 'i', 'a', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['b', 'u'], ['n', 'o', 't'], [⟨['b', 'u'], ['n', 'o', 't'], none⟩]⟩, ⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], [⟨['h', 'u', 'i'], ['w', 'i', 'l', 'l'], none⟩]⟩, ⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], [⟨['l', 'a', 'i'], ['c', 'o', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    contrasts := [("Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai le, danshi wo juede ta mingtian bu hui lai.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "O-marking")] }

def all : List Datum := [en1a, en2, ja3, ja4a, ja7a, ma13a, en8, ja9, ma11]

/-- The constructions whose marking the paper compares. -/
inductive Construction where
  /-- anderson: an Anderson conditional, whose consequent is an observed fact (§2) -/
  | anderson
  /-- counterfactual: a conditional whose antecedent is taken to be false (§3.1) -/
  | counterfactual
  /-- flv: a future-less-vivid conditional (§4.2) -/
  | flv
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `construction`. -/
def construction (e : Datum) : Option Construction :=
  e.parse? "construction" [("anderson", .anderson), ("counterfactual", .counterfactual), ("flv", .flv)]

/-- The marking of the row's primary text, in the terms of von Fintel and Iatridou. -/
inductive Strategy where
  /-- X-marking: the morphology of a counterfactual conditional -/
  | xMarking
  /-- O-marking: the absence of X-marking -/
  | oMarking
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `strategy`. -/
def strategy (e : Datum) : Option Strategy :=
  e.parse? "strategy" [("X-marking", .xMarking), ("O-marking", .oMarking)]

end Mizuno2024.Examples
