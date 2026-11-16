module

public import Linglib.Data.Examples.Schema

/-!
# `Lassiter2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Lassiter2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Lassiter2025.Examples`.
-/

@[expose] public section

namespace Lassiter2025.Examples

def lass2025_gibbard : Datum :=
  { id := "lass2025_gibbard"
    source := ⟨"gibbard-1981", "p. 235"⟩
    reportedIn := some ⟨"lassiter-2025", "(4)"⟩
    language := "stan1293"
    primaryText := "If Kripke was there if Strawson was, then Anscomb was there"
    glossedTokens := []
    context := "Said of a conference the addressee doesn't know much about."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("antecedent_given", "false"), ("interpretation", "PC"), ("diagnostic", "discourse_anchoring"), ("felicity", "infelicitous")] }

def lass2025_ex6 : Datum :=
  { id := "lass2025_ex6"
    source := ⟨"iatridou-1991", "p. 93"⟩
    reportedIn := some ⟨"lassiter-2025", "(6)"⟩
    language := "stan1293"
    primaryText := "If he is so unhappy, he should leave"
    glossedTokens := []
    context := "Alf: Bill is unhappy here."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "false"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "PC"), ("diagnostic", "discourse_anchoring"), ("polarity_item", "ppi")] }

def lass2025_ex11 : Datum :=
  { id := "lass2025_ex11"
    source := ⟨"lassiter-2025", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Kripke was there if Strawson was, then Anscomb was there too"
    glossedTokens := []
    context := "Alf: Kripke was there if Strawson was."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "PC"), ("diagnostic", "discourse_anchoring")] }

def lass2025_ex12 : Datum :=
  { id := "lass2025_ex12"
    source := ⟨"lassiter-2025", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Aha. If Mary came if John did, they are friends"
    glossedTokens := []
    context := "Neither Alf nor Barbara was at the party. Alf: Mary came to the party if John did."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "PC"), ("diagnostic", "discourse_anchoring")] }

def lass2025_ex13 : Datum :=
  { id := "lass2025_ex13"
    source := ⟨"lassiter-2025", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you'll cancel the camping trip if it rains, you're not from Scotland"
    glossedTokens := []
    context := "Carl: We'll cancel the camping trip if it rains."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "PC"), ("diagnostic", "discourse_anchoring")] }

def lass2025_ex14 : Datum :=
  { id := "lass2025_ex14"
    source := ⟨"lassiter-2025", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Given that/Since you'll cancel the camping trip if it rains, you're not from Scotland"
    glossedTokens := []
    context := "Carl: We'll cancel the camping trip if it rains."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "PC"), ("diagnostic", "given_that_paraphrase")] }

def lass2025_ex18 : Datum :=
  { id := "lass2025_ex18"
    source := ⟨"lassiter-2025", "(18)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Moshi meari-ga kita-{nara/ra} jon-ga kita-nara karera-wa tomodati-da"
    glossedTokens := [("Moshi", "If"), ("meari-ga", "M-NOM"), ("kita-{nara/ra}", "came-{NARA/RA}"), ("jon-ga", "J-NOM"), ("kita-nara", "came-NARA"), ("karera-wa", "they-TOP"), ("tomodati-da", "friends-COP")]
    glossedWords := [⟨[['M', 'o', 's', 'h', 'i']], [['I', 'f']]⟩, ⟨[['m', 'e', 'a', 'r', 'i'], ['g', 'a']], [['M'], ['N', 'O', 'M']]⟩, ⟨[['k', 'i', 't', 'a'], ['{', 'n', 'a', 'r', 'a', '/', 'r', 'a', '}']], [['c', 'a', 'm', 'e'], ['{', 'N', 'A', 'R', 'A', '/', 'R', 'A', '}']]⟩, ⟨[['j', 'o', 'n'], ['g', 'a']], [['J'], ['N', 'O', 'M']]⟩, ⟨[['k', 'i', 't', 'a'], ['n', 'a', 'r', 'a']], [['c', 'a', 'm', 'e'], ['N', 'A', 'R', 'A']]⟩, ⟨[['k', 'a', 'r', 'e', 'r', 'a'], ['w', 'a']], [['t', 'h', 'e', 'y'], ['T', 'O', 'P']]⟩, ⟨[['t', 'o', 'm', 'o', 'd', 'a', 't', 'i'], ['d', 'a']], [['f', 'r', 'i', 'e', 'n', 'd', 's'], ['C', 'O', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "PC"), ("diagnostic", "marker"), ("marker", "nara")] }

def lass2025_ex19 : Datum :=
  { id := "lass2025_ex19"
    source := ⟨"lassiter-2025", "(19)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Moshi meari-ga kita-{nara/ra} jon-ga kita-ra karera-wa tomodati-da"
    glossedTokens := [("Moshi", "If"), ("meari-ga", "M-NOM"), ("kita-{nara/ra}", "came-{NARA/RA}"), ("jon-ga", "J-NOM"), ("kita-ra", "came-RA"), ("karera-wa", "they-TOP"), ("tomodati-da", "friends-COP")]
    glossedWords := [⟨[['M', 'o', 's', 'h', 'i']], [['I', 'f']]⟩, ⟨[['m', 'e', 'a', 'r', 'i'], ['g', 'a']], [['M'], ['N', 'O', 'M']]⟩, ⟨[['k', 'i', 't', 'a'], ['{', 'n', 'a', 'r', 'a', '/', 'r', 'a', '}']], [['c', 'a', 'm', 'e'], ['{', 'N', 'A', 'R', 'A', '/', 'R', 'A', '}']]⟩, ⟨[['j', 'o', 'n'], ['g', 'a']], [['J'], ['N', 'O', 'M']]⟩, ⟨[['k', 'i', 't', 'a'], ['r', 'a']], [['c', 'a', 'm', 'e'], ['R', 'A']]⟩, ⟨[['k', 'a', 'r', 'e', 'r', 'a'], ['w', 'a']], [['t', 'h', 'e', 'y'], ['T', 'O', 'P']]⟩, ⟨[['t', 'o', 'm', 'o', 'd', 'a', 't', 'i'], ['d', 'a']], [['f', 'r', 'i', 'e', 'n', 'd', 's'], ['C', 'O', 'P']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "blocked"), ("diagnostic", "marker"), ("marker", "ra")] }

def lass2025_ex23 : Datum :=
  { id := "lass2025_ex23"
    source := ⟨"lassiter-2025", "(23)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wenn ihr das Spiel absagt, wenn/falls es regnet, seid ihr keine echten Göttinger"
    glossedTokens := [("Wenn", "WENN"), ("ihr", "you"), ("das", "the"), ("Spiel", "game"), ("absagt", "cancel"), ("wenn/falls", "WENN/FALLS"), ("es", "it"), ("regnet", "rains"), ("seid", "are"), ("ihr", "you"), ("keine", "no"), ("echten", "true"), ("Göttinger", "Göttinger")]
    glossedWords := [⟨[['W', 'e', 'n', 'n']], [['W', 'E', 'N', 'N']]⟩, ⟨[['i', 'h', 'r']], [['y', 'o', 'u']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['S', 'p', 'i', 'e', 'l']], [['g', 'a', 'm', 'e']]⟩, ⟨[['a', 'b', 's', 'a', 'g', 't']], [['c', 'a', 'n', 'c', 'e', 'l']]⟩, ⟨[['w', 'e', 'n', 'n', '/', 'f', 'a', 'l', 'l', 's']], [['W', 'E', 'N', 'N', '/', 'F', 'A', 'L', 'L', 'S']]⟩, ⟨[['e', 's']], [['i', 't']]⟩, ⟨[['r', 'e', 'g', 'n', 'e', 't']], [['r', 'a', 'i', 'n', 's']]⟩, ⟨[['s', 'e', 'i', 'd']], [['a', 'r', 'e']]⟩, ⟨[['i', 'h', 'r']], [['y', 'o', 'u']]⟩, ⟨[['k', 'e', 'i', 'n', 'e']], [['n', 'o']]⟩, ⟨[['e', 'c', 'h', 't', 'e', 'n']], [['t', 'r', 'u', 'e']]⟩, ⟨[['G', 'ö', 't', 't', 'i', 'n', 'g', 'e', 'r']], [['G', 'ö', 't', 't', 'i', 'n', 'g', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "PC"), ("diagnostic", "marker"), ("marker", "wenn")] }

def lass2025_ex24 : Datum :=
  { id := "lass2025_ex24"
    source := ⟨"lassiter-2025", "(24)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Falls ihr das Spiel absagt, wenn/falls es regnet, seid ihr keine echten Göttinger"
    glossedTokens := [("Falls", "FALLS"), ("ihr", "you"), ("das", "the"), ("Spiel", "game"), ("absagt", "cancel"), ("wenn/falls", "WENN/FALLS"), ("es", "it"), ("regnet", "rains"), ("seid", "are"), ("ihr", "you"), ("keine", "no"), ("echten", "true"), ("Göttinger", "Göttinger")]
    glossedWords := [⟨[['F', 'a', 'l', 'l', 's']], [['F', 'A', 'L', 'L', 'S']]⟩, ⟨[['i', 'h', 'r']], [['y', 'o', 'u']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['S', 'p', 'i', 'e', 'l']], [['g', 'a', 'm', 'e']]⟩, ⟨[['a', 'b', 's', 'a', 'g', 't']], [['c', 'a', 'n', 'c', 'e', 'l']]⟩, ⟨[['w', 'e', 'n', 'n', '/', 'f', 'a', 'l', 'l', 's']], [['W', 'E', 'N', 'N', '/', 'F', 'A', 'L', 'L', 'S']]⟩, ⟨[['e', 's']], [['i', 't']]⟩, ⟨[['r', 'e', 'g', 'n', 'e', 't']], [['r', 'a', 'i', 'n', 's']]⟩, ⟨[['s', 'e', 'i', 'd']], [['a', 'r', 'e']]⟩, ⟨[['i', 'h', 'r']], [['y', 'o', 'u']]⟩, ⟨[['k', 'e', 'i', 'n', 'e']], [['n', 'o']]⟩, ⟨[['e', 'c', 'h', 't', 'e', 'n']], [['t', 'r', 'u', 'e']]⟩, ⟨[['G', 'ö', 't', 't', 'i', 'n', 'g', 'e', 'r']], [['G', 'ö', 't', 't', 'i', 'n', 'g', 'e', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "blocked"), ("diagnostic", "marker"), ("marker", "falls")] }

def lass2025_ex29 : Datum :=
  { id := "lass2025_ex29"
    source := ⟨"lassiter-2025", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary was rather pleased if Bill was involved, her expectations are too low"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "PC"), ("diagnostic", "polarity"), ("polarity_item", "ppi"), ("item", "rather"), ("item_position", "embedded_consequent")] }

def lass2025_ex30 : Datum :=
  { id := "lass2025_ex30"
    source := ⟨"lassiter-2025", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary lifted a finger if Bill was involved, the job got done"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "blocked"), ("diagnostic", "polarity"), ("polarity_item", "npi"), ("item", "lift a finger"), ("item_position", "embedded_consequent")] }

def lass2025_ex31 : Datum :=
  { id := "lass2025_ex31"
    source := ⟨"lassiter-2025", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary lifted a finger if Bill was involved"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "false"), ("content", "bare"), ("interpretation", "blocked"), ("diagnostic", "polarity"), ("polarity_item", "npi"), ("item", "lift a finger"), ("item_position", "consequent")] }

def lass2025_ex32b : Datum :=
  { id := "lass2025_ex32b"
    source := ⟨"lassiter-2025", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary was pleased if Bill lifted a finger to help, her expectations are too low"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "PC"), ("diagnostic", "polarity"), ("polarity_item", "npi"), ("item", "lift a finger"), ("item_position", "embedded_antecedent")] }

def lass2025_ex33 : Datum :=
  { id := "lass2025_ex33"
    source := ⟨"lassiter-2025", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill is so unhappy, and if Mary loses her job, they'll be in trouble"
    glossedTokens := []
    context := "Ed and Fran have no idea whether Mary's job is at risk. Ed: Bill is very unhappy here."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "false"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "blocked"), ("diagnostic", "coordination"), ("coordinated_antecedent_given", "false")] }

def lass2025_ex34 : Datum :=
  { id := "lass2025_ex34"
    source := ⟨"lassiter-2025", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John came if Mary did, and if the food was bad, it was a lousy party"
    glossedTokens := []
    context := "Alf: John came to the party if Mary did. Barbara: The food wasn't very good."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "PC"), ("diagnostic", "coordination"), ("coordinated_antecedent_given", "true")] }

def lass2025_ex35 : Datum :=
  { id := "lass2025_ex35"
    source := ⟨"lassiter-2025", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John came if Mary did, and if the food was bad, it was a lousy party"
    glossedTokens := []
    context := "Alf: John came to the party if Mary did. Barbara: I have no idea about the food — sometimes it's great, sometimes it's terrible."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "blocked"), ("diagnostic", "coordination"), ("coordinated_antecedent_given", "false")] }

def lass2025_ex36 : Datum :=
  { id := "lass2025_ex36"
    source := ⟨"lassiter-2025", "(36)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only if you have the courage to follow your heart will you succeed on the path of love"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "false"), ("content", "bare"), ("interpretation", "HC"), ("diagnostic", "only_inversion"), ("only_inversion", "true")] }

def lass2025_ex37b : Datum :=
  { id := "lass2025_ex37b"
    source := ⟨"lassiter-2025", "(37b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only if the chocolate manufacturers are pleased are they not satisfied"
    glossedTokens := []
    context := "The chocolate manufacturers looked with pleasure at the statistics. If the chocolate manufacturers are pleased, they are not satisfied."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "false"), ("content", "bare"), ("antecedent_given", "true"), ("interpretation", "blocked"), ("diagnostic", "only_inversion"), ("only_inversion", "true"), ("felicity", "infelicitous")] }

def lass2025_ex38a : Datum :=
  { id := "lass2025_ex38a"
    source := ⟨"lassiter-2025", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary was distressed if Bill left, Sue will be annoyed"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "PC"), ("diagnostic", "only_inversion"), ("only_inversion", "false")] }

def lass2025_ex38b : Datum :=
  { id := "lass2025_ex38b"
    source := ⟨"lassiter-2025", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only if Mary was distressed if Bill left will Sue be annoyed"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "blocked"), ("diagnostic", "only_inversion"), ("only_inversion", "true")] }

def lass2025_ex39b : Datum :=
  { id := "lass2025_ex39b"
    source := ⟨"lassiter-2025", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only if the game is canceled if it rains are the organizers too nervous"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "bare"), ("interpretation", "blocked"), ("diagnostic", "only_inversion"), ("only_inversion", "true")] }

def lass2025_ex40 : Datum :=
  { id := "lass2025_ex40"
    source := ⟨"lassiter-2025", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the boss rarely yells at employees if they make a mistake, I'm going to be happier working here"
    glossedTokens := []
    context := "I don't know how things work in my new workplace, but I hope people are kinder than in my previous one."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "quantAdv"), ("antecedent_given", "false"), ("interpretation", "HC"), ("diagnostic", "content_exception")] }

def lass2025_ex41 : Datum :=
  { id := "lass2025_ex41"
    source := ⟨"lassiter-2025", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Bill is obliged to stop writing if the timer has gone off, he's breaking the rules by continuing"
    glossedTokens := []
    context := "I don't know what the rules of this test are, but it seems like something's not right here."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "modal"), ("antecedent_given", "false"), ("interpretation", "HC"), ("diagnostic", "content_exception")] }

def lass2025_ex42 : Datum :=
  { id := "lass2025_ex42"
    source := ⟨"lassiter-2025", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a female bear attacks if a human approaches, she has cubs"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "generic"), ("antecedent_given", "false"), ("interpretation", "HC"), ("diagnostic", "content_exception")] }

def lass2025_ex43a : Datum :=
  { id := "lass2025_ex43a"
    source := ⟨"lassiter-2025", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If this switch will fail if it is submerged in water, it will be discarded"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "modal"), ("antecedent_given", "false"), ("interpretation", "HC"), ("diagnostic", "content_exception")] }

def lass2025_ex43b : Datum :=
  { id := "lass2025_ex43b"
    source := ⟨"lassiter-2025", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If this material becomes soft if it gets hot, it is not suited for our purposes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("is_lnc", "true"), ("content", "generic"), ("antecedent_given", "false"), ("interpretation", "HC"), ("diagnostic", "content_exception")] }

def all : List Datum := [lass2025_gibbard, lass2025_ex6, lass2025_ex11, lass2025_ex12, lass2025_ex13, lass2025_ex14, lass2025_ex18, lass2025_ex19, lass2025_ex23, lass2025_ex24, lass2025_ex29, lass2025_ex30, lass2025_ex31, lass2025_ex32b, lass2025_ex33, lass2025_ex34, lass2025_ex35, lass2025_ex36, lass2025_ex37b, lass2025_ex38a, lass2025_ex38b, lass2025_ex39b, lass2025_ex40, lass2025_ex41, lass2025_ex42, lass2025_ex43a, lass2025_ex43b]

end Lassiter2025.Examples
