module

public import Linglib.Data.Examples.Schema

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
    language := "stan1293"
    primaryText := "You're right. If Jones had taken arsenic last night, he would show those symptoms which he is now showing."
    glossedTokens := []
    context := "Jones is in the ER with poisoning symptoms; the investigation team is figuring out which chemical was used. One shrewd member suggests that, given the symptoms, he must have taken arsenic. The boss then says (1a) and the follow-up (1b) 'So, it looks like he did take arsenic' in a row: an Anderson conditional arguing FOR the truth of its antecedent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "x-marking")] }

def en2 : Datum :=
  { id := "mizuno2024_en2"
    source := ⟨"mizuno-2024", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Jones took arsenic, he shows just exactly those symptoms which he does in fact show."
    glossedTokens := []
    context := "Same scenario as (1). The O-marked (simple-past indicative / present) counterpart of (1a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")] }

def ja3 : Datum :=
  { id := "mizuno2024_ja3"
    source := ⟨"mizuno-2024", "(3)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga ima kono siai-no naka-ni ir-eba, syoohai-wa mada wakar-ana-katta daroo."
    glossedTokens := [("John-ga", "John-NOM"), ("ima", "now"), ("kono", "this"), ("siai-no", "game-GEN"), ("naka-ni", "inside-LOC"), ("ir-eba", "be-COND"), ("syoohai-wa", "outcome-TOP"), ("mada", "yet"), ("wakar-ana-katta", "be.clear-NEG-PAST"), ("daroo", "MOD")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['g', 'a']], [['J', 'o', 'h', 'n'], ['N', 'O', 'M']]⟩, ⟨[['i', 'm', 'a']], [['n', 'o', 'w']]⟩, ⟨[['k', 'o', 'n', 'o']], [['t', 'h', 'i', 's']]⟩, ⟨[['s', 'i', 'a', 'i'], ['n', 'o']], [['g', 'a', 'm', 'e'], ['G', 'E', 'N']]⟩, ⟨[['n', 'a', 'k', 'a'], ['n', 'i']], [['i', 'n', 's', 'i', 'd', 'e'], ['L', 'O', 'C']]⟩, ⟨[['i', 'r'], ['e', 'b', 'a']], [['b', 'e'], ['C', 'O', 'N', 'D']]⟩, ⟨[['s', 'y', 'o', 'o', 'h', 'a', 'i'], ['w', 'a']], [['o', 'u', 't', 'c', 'o', 'm', 'e'], ['T', 'O', 'P']]⟩, ⟨[['m', 'a', 'd', 'a']], [['y', 'e', 't']]⟩, ⟨[['w', 'a', 'k', 'a', 'r'], ['a', 'n', 'a'], ['k', 'a', 't', 't', 'a']], [['b', 'e', '.', 'c', 'l', 'e', 'a', 'r'], ['N', 'E', 'G'], ['P', 'A', 'S', 'T']]⟩, ⟨[['d', 'a', 'r', 'o', 'o']], [['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "John, an ace player, has recently left the team for better pay. The team weakens considerably after losing their mainstay, and their defeat in today's game is already certain during the first half. A fan who is currently watching the game says the following."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "fake-past"), ("x_exponent", "-ta")] }

def ja4a : Datum :=
  { id := "mizuno2024_ja4a"
    source := ⟨"mizuno-2024", "(4a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ru hazuda."
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-si-ga", "Jones-Mr.-NOM"), ("sakuya", "last.night"), ("hiso-o", "arsenic-ACC"), ("nom-eba", "drink-COND"), ("kare-ga", "he-NOM"), ("ima", "now"), ("mise-tei-ru", "show-ASP-NPST"), ("syoozyoo-to", "symptom-as"), ("mattaku", "exactly"), ("onazi", "same"), ("syoozyoo-o", "symptom-ACC"), ("ima", "now"), ("mise-ru", "show-NPST"), ("hazuda", "MOD")]
    glossedWords := [⟨[['T', 'a', 's', 'i', 'k', 'a', 'n', 'i']], [['y', 'o', 'u', '\'', 'r', 'e', '.', 'r', 'i', 'g', 'h', 't']]⟩, ⟨[['J', 'o', 'n', 'e', 's'], ['s', 'i'], ['g', 'a']], [['J', 'o', 'n', 'e', 's'], ['M', 'r', '.'], ['N', 'O', 'M']]⟩, ⟨[['s', 'a', 'k', 'u', 'y', 'a']], [['l', 'a', 's', 't', '.', 'n', 'i', 'g', 'h', 't']]⟩, ⟨[['h', 'i', 's', 'o'], ['o']], [['a', 'r', 's', 'e', 'n', 'i', 'c'], ['A', 'C', 'C']]⟩, ⟨[['n', 'o', 'm'], ['e', 'b', 'a']], [['d', 'r', 'i', 'n', 'k'], ['C', 'O', 'N', 'D']]⟩, ⟨[['k', 'a', 'r', 'e'], ['g', 'a']], [['h', 'e'], ['N', 'O', 'M']]⟩, ⟨[['i', 'm', 'a']], [['n', 'o', 'w']]⟩, ⟨[['m', 'i', 's', 'e'], ['t', 'e', 'i'], ['r', 'u']], [['s', 'h', 'o', 'w'], ['A', 'S', 'P'], ['N', 'P', 'S', 'T']]⟩, ⟨[['s', 'y', 'o', 'o', 'z', 'y', 'o', 'o'], ['t', 'o']], [['s', 'y', 'm', 'p', 't', 'o', 'm'], ['a', 's']]⟩, ⟨[['m', 'a', 't', 't', 'a', 'k', 'u']], [['e', 'x', 'a', 'c', 't', 'l', 'y']]⟩, ⟨[['o', 'n', 'a', 'z', 'i']], [['s', 'a', 'm', 'e']]⟩, ⟨[['s', 'y', 'o', 'o', 'z', 'y', 'o', 'o'], ['o']], [['s', 'y', 'm', 'p', 't', 'o', 'm'], ['A', 'C', 'C']]⟩, ⟨[['i', 'm', 'a']], [['n', 'o', 'w']]⟩, ⟨[['m', 'i', 's', 'e'], ['r', 'u']], [['s', 'h', 'o', 'w'], ['N', 'P', 'S', 'T']]⟩, ⟨[['h', 'a', 'z', 'u', 'd', 'a']], [['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    alternatives := [("Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru syoozyoo-to mattaku onazi syoozyoo-o ima mise-ta hazuda.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")] }

def ja7a : Datum :=
  { id := "mizuno2024_ja7a"
    source := ⟨"mizuno-2024", "(7a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, kare-no zissai-no nyuukoku geeto-to mattaku onazi geeto-o, kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-uru (hazuda)."
    glossedTokens := [("Tasikani", "you're.right"), ("Jones-ga", "Jones-NOM"), ("ototoi", "two.days.ago"), ("Manila-o", "Manila-ACC"), ("syuppatusu-reba", "leave-COND"), ("kare-no", "he-GEN"), ("zissai-no", "actual-GEN"), ("nyuukoku", "immigration"), ("geeto-to", "gate-as"), ("mattaku", "exactly"), ("onazi", "same"), ("geeto-o", "gate-ACC"), ("kinoo-no", "yesterday-GEN"), ("tuuka", "passage"), ("zikoku-to", "time-as"), ("mattaku", "exactly"), ("onazi", "same"), ("zikoku-ni", "time-at"), ("tuukas-uru", "pass-NPST"), ("(hazuda)", "MOD")]
    glossedWords := [⟨[['T', 'a', 's', 'i', 'k', 'a', 'n', 'i']], [['y', 'o', 'u', '\'', 'r', 'e', '.', 'r', 'i', 'g', 'h', 't']]⟩, ⟨[['J', 'o', 'n', 'e', 's'], ['g', 'a']], [['J', 'o', 'n', 'e', 's'], ['N', 'O', 'M']]⟩, ⟨[['o', 't', 'o', 't', 'o', 'i']], [['t', 'w', 'o', '.', 'd', 'a', 'y', 's', '.', 'a', 'g', 'o']]⟩, ⟨[['M', 'a', 'n', 'i', 'l', 'a'], ['o']], [['M', 'a', 'n', 'i', 'l', 'a'], ['A', 'C', 'C']]⟩, ⟨[['s', 'y', 'u', 'p', 'p', 'a', 't', 'u', 's', 'u'], ['r', 'e', 'b', 'a']], [['l', 'e', 'a', 'v', 'e'], ['C', 'O', 'N', 'D']]⟩, ⟨[['k', 'a', 'r', 'e'], ['n', 'o']], [['h', 'e'], ['G', 'E', 'N']]⟩, ⟨[['z', 'i', 's', 's', 'a', 'i'], ['n', 'o']], [['a', 'c', 't', 'u', 'a', 'l'], ['G', 'E', 'N']]⟩, ⟨[['n', 'y', 'u', 'u', 'k', 'o', 'k', 'u']], [['i', 'm', 'm', 'i', 'g', 'r', 'a', 't', 'i', 'o', 'n']]⟩, ⟨[['g', 'e', 'e', 't', 'o'], ['t', 'o']], [['g', 'a', 't', 'e'], ['a', 's']]⟩, ⟨[['m', 'a', 't', 't', 'a', 'k', 'u']], [['e', 'x', 'a', 'c', 't', 'l', 'y']]⟩, ⟨[['o', 'n', 'a', 'z', 'i']], [['s', 'a', 'm', 'e']]⟩, ⟨[['g', 'e', 'e', 't', 'o'], ['o']], [['g', 'a', 't', 'e'], ['A', 'C', 'C']]⟩, ⟨[['k', 'i', 'n', 'o', 'o'], ['n', 'o']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], ['G', 'E', 'N']]⟩, ⟨[['t', 'u', 'u', 'k', 'a']], [['p', 'a', 's', 's', 'a', 'g', 'e']]⟩, ⟨[['z', 'i', 'k', 'o', 'k', 'u'], ['t', 'o']], [['t', 'i', 'm', 'e'], ['a', 's']]⟩, ⟨[['m', 'a', 't', 't', 'a', 'k', 'u']], [['e', 'x', 'a', 'c', 't', 'l', 'y']]⟩, ⟨[['o', 'n', 'a', 'z', 'i']], [['s', 'a', 'm', 'e']]⟩, ⟨[['z', 'i', 'k', 'o', 'k', 'u'], ['n', 'i']], [['t', 'i', 'm', 'e'], ['a', 't']]⟩, ⟨[['t', 'u', 'u', 'k', 'a', 's'], ['u', 'r', 'u']], [['p', 'a', 's', 's'], ['N', 'P', 'S', 'T']]⟩, ⟨[['h', 'a', 'z', 'u', 'd', 'a']], [['M', 'O', 'D']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Jones is a fugitive who reportedly entered Korea via Incheon yesterday; the team infers the country he flew from. The consequent event lies overtly in the past (adverbial kinoo 'yesterday'), yet Non-Past is still required."
    judgment := .acceptable
    alternatives := [("Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, kare-no zissai-no nyuukoku geeto-to mattaku onazi geeto-o, kinoo-no tuuka zikoku-to mattaku onazi zikoku-ni tuukas-ita (hazuda).", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking"), ("hp_type", "radical")] }

def ma13a : Datum :=
  { id := "mizuno2024_ma13a"
    source := ⟨"mizuno-2024", "(13a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang."
    glossedTokens := [("Ruguo", "if"), ("Jones", "Jones"), ("zuotian", "yesterday"), ("he", "drink"), ("le", "PERF"), ("pishuang", "arsenic"), ("jiu", "then"), ("hui", "MOD"), ("chuxian", "show"), ("ta", "he"), ("xianzai", "now"), ("shiji", "actually"), ("chuxian", "show"), ("de", "REL"), ("zheyangde", "such"), ("zhengzhuang", "symptoms")]
    glossedWords := [⟨[['R', 'u', 'g', 'u', 'o']], [['i', 'f']]⟩, ⟨[['J', 'o', 'n', 'e', 's']], [['J', 'o', 'n', 'e', 's']]⟩, ⟨[['z', 'u', 'o', 't', 'i', 'a', 'n']], [['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y']]⟩, ⟨[['h', 'e']], [['d', 'r', 'i', 'n', 'k']]⟩, ⟨[['l', 'e']], [['P', 'E', 'R', 'F']]⟩, ⟨[['p', 'i', 's', 'h', 'u', 'a', 'n', 'g']], [['a', 'r', 's', 'e', 'n', 'i', 'c']]⟩, ⟨[['j', 'i', 'u']], [['t', 'h', 'e', 'n']]⟩, ⟨[['h', 'u', 'i']], [['M', 'O', 'D']]⟩, ⟨[['c', 'h', 'u', 'x', 'i', 'a', 'n']], [['s', 'h', 'o', 'w']]⟩, ⟨[['t', 'a']], [['h', 'e']]⟩, ⟨[['x', 'i', 'a', 'n', 'z', 'a', 'i']], [['n', 'o', 'w']]⟩, ⟨[['s', 'h', 'i', 'j', 'i']], [['a', 'c', 't', 'u', 'a', 'l', 'l', 'y']]⟩, ⟨[['c', 'h', 'u', 'x', 'i', 'a', 'n']], [['s', 'h', 'o', 'w']]⟩, ⟨[['d', 'e']], [['R', 'E', 'L']]⟩, ⟨[['z', 'h', 'e', 'y', 'a', 'n', 'g', 'd', 'e']], [['s', 'u', 'c', 'h']]⟩, ⟨[['z', 'h', 'e', 'n', 'g', 'z', 'h', 'u', 'a', 'n', 'g']], [['s', 'y', 'm', 'p', 't', 'o', 'm', 's']]⟩]
    lgrConformance := some .wordAligned
    context := "Uttered in the context in (1) — the Anderson scenario."
    judgment := .acceptable
    alternatives := [("Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang le.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "anderson"), ("strategy", "o-marking")] }

def en8 : Datum :=
  { id := "mizuno2024_en8"
    source := ⟨"mizuno-2024", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John came tomorrow, the party would be fun, but he probably won't come tomorrow, I think."
    glossedTokens := []
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "x-marking"), ("flv_xmarking", "available")] }

def ja9 : Datum :=
  { id := "mizuno2024_ja9"
    source := ⟨"mizuno-2024", "(9)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga asita kur-eba, paatii-wa totemo moriagar-u daroo, kedo, tabun kare-wa asita ko-na-i to omou."
    glossedTokens := [("John-ga", "John-NOM"), ("asita", "tomorrow"), ("kur-eba", "come-COND"), ("paatii-wa", "party-TOP"), ("totemo", "very"), ("moriagar-u", "be.fun-NPST"), ("daroo", "MOD"), ("kedo", "but"), ("tabun", "probably"), ("kare-wa", "he-TOP"), ("asita", "tomorrow"), ("ko-na-i", "come-NEG-NPST"), ("to", "COMP"), ("omou", "think")]
    glossedWords := [⟨[['J', 'o', 'h', 'n'], ['g', 'a']], [['J', 'o', 'h', 'n'], ['N', 'O', 'M']]⟩, ⟨[['a', 's', 'i', 't', 'a']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['k', 'u', 'r'], ['e', 'b', 'a']], [['c', 'o', 'm', 'e'], ['C', 'O', 'N', 'D']]⟩, ⟨[['p', 'a', 'a', 't', 'i', 'i'], ['w', 'a']], [['p', 'a', 'r', 't', 'y'], ['T', 'O', 'P']]⟩, ⟨[['t', 'o', 't', 'e', 'm', 'o']], [['v', 'e', 'r', 'y']]⟩, ⟨[['m', 'o', 'r', 'i', 'a', 'g', 'a', 'r'], ['u']], [['b', 'e', '.', 'f', 'u', 'n'], ['N', 'P', 'S', 'T']]⟩, ⟨[['d', 'a', 'r', 'o', 'o']], [['M', 'O', 'D']]⟩, ⟨[['k', 'e', 'd', 'o']], [['b', 'u', 't']]⟩, ⟨[['t', 'a', 'b', 'u', 'n']], [['p', 'r', 'o', 'b', 'a', 'b', 'l', 'y']]⟩, ⟨[['k', 'a', 'r', 'e'], ['w', 'a']], [['h', 'e'], ['T', 'O', 'P']]⟩, ⟨[['a', 's', 'i', 't', 'a']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['k', 'o'], ['n', 'a'], ['i']], [['c', 'o', 'm', 'e'], ['N', 'E', 'G'], ['N', 'P', 'S', 'T']]⟩, ⟨[['t', 'o']], [['C', 'O', 'M', 'P']]⟩, ⟨[['o', 'm', 'o', 'u']], [['t', 'h', 'i', 'n', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := [("John-ga asita kur-eba, paatii-wa totemo moriagat-ta daroo, kedo, tabun kare-wa asita ko-na-i to omou.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "o-marking"), ("flv_xmarking", "unavailable")] }

def ma11 : Datum :=
  { id := "mizuno2024_ma11"
    source := ⟨"mizuno-2024", "(11)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai, danshi wo juede ta mingtian bu hui lai."
    glossedTokens := [("Ruguo", "if"), ("mingtian", "tomorrow"), ("John", "John"), ("lai", "come"), ("paidui", "party"), ("de", "GEN"), ("qifen", "atmosphere"), ("jiu", "then"), ("neng", "MOD"), ("huoyue", "be.lively"), ("qilai", "get"), ("danshi", "but"), ("wo", "I"), ("juede", "think"), ("ta", "he"), ("mingtian", "tomorrow"), ("bu", "not"), ("hui", "will"), ("lai", "come")]
    glossedWords := [⟨[['R', 'u', 'g', 'u', 'o']], [['i', 'f']]⟩, ⟨[['m', 'i', 'n', 'g', 't', 'i', 'a', 'n']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['J', 'o', 'h', 'n']], [['J', 'o', 'h', 'n']]⟩, ⟨[['l', 'a', 'i']], [['c', 'o', 'm', 'e']]⟩, ⟨[['p', 'a', 'i', 'd', 'u', 'i']], [['p', 'a', 'r', 't', 'y']]⟩, ⟨[['d', 'e']], [['G', 'E', 'N']]⟩, ⟨[['q', 'i', 'f', 'e', 'n']], [['a', 't', 'm', 'o', 's', 'p', 'h', 'e', 'r', 'e']]⟩, ⟨[['j', 'i', 'u']], [['t', 'h', 'e', 'n']]⟩, ⟨[['n', 'e', 'n', 'g']], [['M', 'O', 'D']]⟩, ⟨[['h', 'u', 'o', 'y', 'u', 'e']], [['b', 'e', '.', 'l', 'i', 'v', 'e', 'l', 'y']]⟩, ⟨[['q', 'i', 'l', 'a', 'i']], [['g', 'e', 't']]⟩, ⟨[['d', 'a', 'n', 's', 'h', 'i']], [['b', 'u', 't']]⟩, ⟨[['w', 'o']], [['I']]⟩, ⟨[['j', 'u', 'e', 'd', 'e']], [['t', 'h', 'i', 'n', 'k']]⟩, ⟨[['t', 'a']], [['h', 'e']]⟩, ⟨[['m', 'i', 'n', 'g', 't', 'i', 'a', 'n']], [['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w']]⟩, ⟨[['b', 'u']], [['n', 'o', 't']]⟩, ⟨[['h', 'u', 'i']], [['w', 'i', 'l', 'l']]⟩, ⟨[['l', 'a', 'i']], [['c', 'o', 'm', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := "Future Less Vivid conditional with an unlikeliness follow-up."
    judgment := .acceptable
    alternatives := [("Ruguo mingtian John lai, paidui de qifen jiu neng huoyue qilai le, danshi wo juede ta mingtian bu hui lai.", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "flv"), ("strategy", "o-marking"), ("flv_xmarking", "unavailable")] }

def all : List Datum := [en1a, en2, ja3, ja4a, ja7a, ma13a, en8, ja9, ma11]

end Mizuno2024.Examples
