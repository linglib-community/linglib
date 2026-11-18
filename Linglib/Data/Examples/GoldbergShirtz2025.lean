module

public import Linglib.Data.Examples.Schema

/-!
# `GoldbergShirtz2025` — typed example data

Auto-generated from `Linglib/Data/Examples/GoldbergShirtz2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GoldbergShirtz2025.Examples`.
-/

@[expose] public section

namespace GoldbergShirtz2025.Examples

def gs2025_1a : Datum :=
  { id := "gs2025_1a"
    source := ⟨"goldberg-shirtz-2025", "(1a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "a trickle-down policy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "prenominal modifier")] }

def gs2025_1b : Datum :=
  { id := "gs2025_1b"
    source := ⟨"goldberg-shirtz-2025", "(1b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "a must-do task"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "prenominal modifier")] }

def gs2025_1c : Datum :=
  { id := "gs2025_1c"
    source := ⟨"goldberg-shirtz-2025", "(1c)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "the 'both sides do it' argument"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "prenominal modifier")] }

def gs2025_t2_simple : Datum :=
  { id := "gs2025_t2_simple"
    source := ⟨"goldberg-shirtz-2025", "Table 2"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Could've tried a simple 'I'm sorry.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "head noun")] }

def gs2025_t2_old : Datum :=
  { id := "gs2025_t2_old"
    source := ⟨"goldberg-shirtz-2025", "Table 2"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "my dad pulled the old 'I'm going to the store for smokes, be back in five'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "head noun")] }

def gs2025_t2_mustsee : Datum :=
  { id := "gs2025_t2_mustsee"
    source := ⟨"goldberg-shirtz-2025", "Table 2"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "This show is a must see."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "head noun")] }

def gs2025_t2_romney : Datum :=
  { id := "gs2025_t2_romney"
    source := ⟨"goldberg-shirtz-2025", "Table 2"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "Romney's slogan should be more 'I'm nothing like you.'"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "predicative adjective")] }

def gs2025_t2_honey : Datum :=
  { id := "gs2025_t2_honey"
    source := ⟨"goldberg-shirtz-2025", "Table 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "[he was] carrying on like a television husband, honey-I'm-home-ing her from the doorway."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "verb"), ("inflection", "gerund")] }

def gs2025_t2_welcome : Datum :=
  { id := "gs2025_t2_welcome"
    source := ⟨"goldberg-shirtz-2025", "Table 2"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "A: you're welcome. B: No, don't 'you're welcome' me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "verb")] }

def gs2025_t3_jespersen : Datum :=
  { id := "gs2025_t3_jespersen"
    source := ⟨"goldberg-shirtz-2025", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "his speech abounded in I told you so's"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "head noun"), ("inflection", "plural")] }

def gs2025_t3_diy : Datum :=
  { id := "gs2025_t3_diy"
    source := ⟨"goldberg-shirtz-2025", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Their parents were do-it-yourselfers."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "head noun"), ("inflection", "agentive -er + plural")] }

def gs2025_t3_nyt : Datum :=
  { id := "gs2025_t3_nyt"
    source := ⟨"goldberg-shirtz-2025", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "few people want to be memorialized 'um'-ing, 'you know'-ing, and 'remember that time when we got drunk'-ing their way into ignominy."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("position", "verb"), ("inflection", "gerund")] }

def gs2025_8a : Datum :=
  { id := "gs2025_8a"
    source := ⟨"meibauer-2007", "p. 250"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(8a)"⟩
    language := "stan1295"
    primaryText := "Kaufe-Ihr-Auto-Kärtchen"
    glossedTokens := [("Kaufe-Ihr-Auto-Kärtchen", "buy.prs.1sg-2pl.poss-car-card.dim")]
    glossedWords := [⟨['K', 'a', 'u', 'f', 'e', '-', 'I', 'h', 'r', '-', 'A', 'u', 't', 'o', '-', 'K', 'ä', 'r', 't', 'c', 'h', 'e', 'n'], ['b', 'u', 'y', '.', 'p', 'r', 's', '.', '1', 's', 'g', '-', '2', 'p', 'l', '.', 'p', 'o', 's', 's', '-', 'c', 'a', 'r', '-', 'c', 'a', 'r', 'd', '.', 'd', 'i', 'm'], [⟨['K', 'a', 'u', 'f', 'e'], ['b', 'u', 'y', '.', 'p', 'r', 's', '.', '1', 's', 'g'], none⟩, ⟨['I', 'h', 'r'], ['2', 'p', 'l', '.', 'p', 'o', 's', 's'], some '-'⟩, ⟨['A', 'u', 't', 'o'], ['c', 'a', 'r'], some '-'⟩, ⟨['K', 'ä', 'r', 't', 'c', 'h', 'e', 'n'], ['c', 'a', 'r', 'd', '.', 'd', 'i', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_15a : Datum :=
  { id := "gs2025_15a"
    source := ⟨"meibauer-2007", "p. 235"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(15a)"⟩
    language := "dutc1256"
    primaryText := "lach of ik schiet humor"
    glossedTokens := [("lach", "laugh.imp"), ("of", "or"), ("ik", "1sg"), ("schiet", "shoot.prs.sg"), ("humor", "humor")]
    glossedWords := [⟨['l', 'a', 'c', 'h'], ['l', 'a', 'u', 'g', 'h', '.', 'i', 'm', 'p'], [⟨['l', 'a', 'c', 'h'], ['l', 'a', 'u', 'g', 'h', '.', 'i', 'm', 'p'], none⟩]⟩, ⟨['o', 'f'], ['o', 'r'], [⟨['o', 'f'], ['o', 'r'], none⟩]⟩, ⟨['i', 'k'], ['1', 's', 'g'], [⟨['i', 'k'], ['1', 's', 'g'], none⟩]⟩, ⟨['s', 'c', 'h', 'i', 'e', 't'], ['s', 'h', 'o', 'o', 't', '.', 'p', 'r', 's', '.', 's', 'g'], [⟨['s', 'c', 'h', 'i', 'e', 't'], ['s', 'h', 'o', 'o', 't', '.', 'p', 'r', 's', '.', 's', 'g'], none⟩]⟩, ⟨['h', 'u', 'm', 'o', 'r'], ['h', 'u', 'm', 'o', 'r'], [⟨['h', 'u', 'm', 'o', 'r'], ['h', 'u', 'm', 'o', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_15b : Datum :=
  { id := "gs2025_15b"
    source := ⟨"meibauer-2007", "p. 235"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(15b)"⟩
    language := "afri1274"
    primaryText := "God is dod theologie"
    glossedTokens := [("God", "god"), ("is", "cop.prs.3sg"), ("dod", "dead"), ("theologie", "theology")]
    glossedWords := [⟨['G', 'o', 'd'], ['g', 'o', 'd'], [⟨['G', 'o', 'd'], ['g', 'o', 'd'], none⟩]⟩, ⟨['i', 's'], ['c', 'o', 'p', '.', 'p', 'r', 's', '.', '3', 's', 'g'], [⟨['i', 's'], ['c', 'o', 'p', '.', 'p', 'r', 's', '.', '3', 's', 'g'], none⟩]⟩, ⟨['d', 'o', 'd'], ['d', 'e', 'a', 'd'], [⟨['d', 'o', 'd'], ['d', 'e', 'a', 'd'], none⟩]⟩, ⟨['t', 'h', 'e', 'o', 'l', 'o', 'g', 'i', 'e'], ['t', 'h', 'e', 'o', 'l', 'o', 'g', 'y'], [⟨['t', 'h', 'e', 'o', 'l', 'o', 'g', 'i', 'e'], ['t', 'h', 'e', 'o', 'l', 'o', 'g', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_15c : Datum :=
  { id := "gs2025_15c"
    source := ⟨"trips-kornfilt-2015", "p. 307"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(15c)"⟩
    language := "nucl1301"
    primaryText := "'iç çamasir-ın-ı göster' oyun-u"
    glossedTokens := [("iç", "internal"), ("çamasir-ın-ı", "laundry-3sg-acc"), ("göster", "show"), ("oyun-u", "game-cm")]
    glossedWords := [⟨['i', 'ç'], ['i', 'n', 't', 'e', 'r', 'n', 'a', 'l'], [⟨['i', 'ç'], ['i', 'n', 't', 'e', 'r', 'n', 'a', 'l'], none⟩]⟩, ⟨['ç', 'a', 'm', 'a', 's', 'i', 'r', '-', 'ı', 'n', '-', 'ı'], ['l', 'a', 'u', 'n', 'd', 'r', 'y', '-', '3', 's', 'g', '-', 'a', 'c', 'c'], [⟨['ç', 'a', 'm', 'a', 's', 'i', 'r'], ['l', 'a', 'u', 'n', 'd', 'r', 'y'], none⟩, ⟨['ı', 'n'], ['3', 's', 'g'], some '-'⟩, ⟨['ı'], ['a', 'c', 'c'], some '-'⟩]⟩, ⟨['g', 'ö', 's', 't', 'e', 'r'], ['s', 'h', 'o', 'w'], [⟨['g', 'ö', 's', 't', 'e', 'r'], ['s', 'h', 'o', 'w'], none⟩]⟩, ⟨['o', 'y', 'u', 'n', '-', 'u'], ['g', 'a', 'm', 'e', '-', 'c', 'm'], [⟨['o', 'y', 'u', 'n'], ['g', 'a', 'm', 'e'], none⟩, ⟨['u'], ['c', 'm'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_16b : Datum :=
  { id := "gs2025_16b"
    source := ⟨"goldberg-shirtz-2025", "(16b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "keta ʃel mi=ʃe yodea yodea"
    glossedTokens := [("keta", "section"), ("ʃel", "of"), ("mi=ʃe", "who=sbj"), ("yodea", "know.prs.3.m.sg"), ("yodea", "know.prs.3.m.sg")]
    glossedWords := [⟨['k', 'e', 't', 'a'], ['s', 'e', 'c', 't', 'i', 'o', 'n'], [⟨['k', 'e', 't', 'a'], ['s', 'e', 'c', 't', 'i', 'o', 'n'], none⟩]⟩, ⟨['ʃ', 'e', 'l'], ['o', 'f'], [⟨['ʃ', 'e', 'l'], ['o', 'f'], none⟩]⟩, ⟨['m', 'i', '=', 'ʃ', 'e'], ['w', 'h', 'o', '=', 's', 'b', 'j'], [⟨['m', 'i'], ['w', 'h', 'o'], none⟩, ⟨['ʃ', 'e'], ['s', 'b', 'j'], some '='⟩]⟩, ⟨['y', 'o', 'd', 'e', 'a'], ['k', 'n', 'o', 'w', '.', 'p', 'r', 's', '.', '3', '.', 'm', '.', 's', 'g'], [⟨['y', 'o', 'd', 'e', 'a'], ['k', 'n', 'o', 'w', '.', 'p', 'r', 's', '.', '3', '.', 'm', '.', 's', 'g'], none⟩]⟩, ⟨['y', 'o', 'd', 'e', 'a'], ['k', 'n', 'o', 'w', '.', 'p', 'r', 's', '.', '3', '.', 'm', '.', 's', 'g'], [⟨['y', 'o', 'd', 'e', 'a'], ['k', 'n', 'o', 'w', '.', 'p', 'r', 's', '.', '3', '.', 'm', '.', 's', 'g'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hostFrame", "preposition complement")] }

def gs2025_17b : Datum :=
  { id := "gs2025_17b"
    source := ⟨"goldberg-shirtz-2025", "(17b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ani mitʁageʃet be=ʁama ʃel ani od ʁega boxa kan"
    glossedTokens := [("ani", "1sg"), ("mitʁageʃet", "be.excited.prs.f.sg"), ("be=ʁama", "in=level"), ("ʃel", "of"), ("ani", "I"), ("od", "more"), ("ʁega", "moment"), ("boxa", "cry.prs.f.sg"), ("kan", "here")]
    glossedWords := [⟨['a', 'n', 'i'], ['1', 's', 'g'], [⟨['a', 'n', 'i'], ['1', 's', 'g'], none⟩]⟩, ⟨['m', 'i', 't', 'ʁ', 'a', 'g', 'e', 'ʃ', 'e', 't'], ['b', 'e', '.', 'e', 'x', 'c', 'i', 't', 'e', 'd', '.', 'p', 'r', 's', '.', 'f', '.', 's', 'g'], [⟨['m', 'i', 't', 'ʁ', 'a', 'g', 'e', 'ʃ', 'e', 't'], ['b', 'e', '.', 'e', 'x', 'c', 'i', 't', 'e', 'd', '.', 'p', 'r', 's', '.', 'f', '.', 's', 'g'], none⟩]⟩, ⟨['b', 'e', '=', 'ʁ', 'a', 'm', 'a'], ['i', 'n', '=', 'l', 'e', 'v', 'e', 'l'], [⟨['b', 'e'], ['i', 'n'], none⟩, ⟨['ʁ', 'a', 'm', 'a'], ['l', 'e', 'v', 'e', 'l'], some '='⟩]⟩, ⟨['ʃ', 'e', 'l'], ['o', 'f'], [⟨['ʃ', 'e', 'l'], ['o', 'f'], none⟩]⟩, ⟨['a', 'n', 'i'], ['I'], [⟨['a', 'n', 'i'], ['I'], none⟩]⟩, ⟨['o', 'd'], ['m', 'o', 'r', 'e'], [⟨['o', 'd'], ['m', 'o', 'r', 'e'], none⟩]⟩, ⟨['ʁ', 'e', 'g', 'a'], ['m', 'o', 'm', 'e', 'n', 't'], [⟨['ʁ', 'e', 'g', 'a'], ['m', 'o', 'm', 'e', 'n', 't'], none⟩]⟩, ⟨['b', 'o', 'x', 'a'], ['c', 'r', 'y', '.', 'p', 'r', 's', '.', 'f', '.', 's', 'g'], [⟨['b', 'o', 'x', 'a'], ['c', 'r', 'y', '.', 'p', 'r', 's', '.', 'f', '.', 's', 'g'], none⟩]⟩, ⟨['k', 'a', 'n'], ['h', 'e', 'r', 'e'], [⟨['k', 'a', 'n'], ['h', 'e', 'r', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hostFrame", "preposition complement")] }

def gs2025_18b : Datum :=
  { id := "gs2025_18b"
    source := ⟨"goldberg-shirtz-2025", "(18b)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "o clima ameno de 'eu te ajudo você me ajuda e está tudo bem'"
    glossedTokens := [("o", "def.m.sg"), ("clima", "climate"), ("ameno", "pleasant"), ("de", "of"), ("eu", "I"), ("te", "you"), ("ajudo", "help.prs.1sg"), ("você", "you"), ("me", "me"), ("ajuda", "help.prs.2sg"), ("e", "and"), ("está", "cop.prs.3sg"), ("tudo", "all"), ("bem", "good")]
    glossedWords := [⟨['o'], ['d', 'e', 'f', '.', 'm', '.', 's', 'g'], [⟨['o'], ['d', 'e', 'f', '.', 'm', '.', 's', 'g'], none⟩]⟩, ⟨['c', 'l', 'i', 'm', 'a'], ['c', 'l', 'i', 'm', 'a', 't', 'e'], [⟨['c', 'l', 'i', 'm', 'a'], ['c', 'l', 'i', 'm', 'a', 't', 'e'], none⟩]⟩, ⟨['a', 'm', 'e', 'n', 'o'], ['p', 'l', 'e', 'a', 's', 'a', 'n', 't'], [⟨['a', 'm', 'e', 'n', 'o'], ['p', 'l', 'e', 'a', 's', 'a', 'n', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['e', 'u'], ['I'], [⟨['e', 'u'], ['I'], none⟩]⟩, ⟨['t', 'e'], ['y', 'o', 'u'], [⟨['t', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['a', 'j', 'u', 'd', 'o'], ['h', 'e', 'l', 'p', '.', 'p', 'r', 's', '.', '1', 's', 'g'], [⟨['a', 'j', 'u', 'd', 'o'], ['h', 'e', 'l', 'p', '.', 'p', 'r', 's', '.', '1', 's', 'g'], none⟩]⟩, ⟨['v', 'o', 'c', 'ê'], ['y', 'o', 'u'], [⟨['v', 'o', 'c', 'ê'], ['y', 'o', 'u'], none⟩]⟩, ⟨['m', 'e'], ['m', 'e'], [⟨['m', 'e'], ['m', 'e'], none⟩]⟩, ⟨['a', 'j', 'u', 'd', 'a'], ['h', 'e', 'l', 'p', '.', 'p', 'r', 's', '.', '2', 's', 'g'], [⟨['a', 'j', 'u', 'd', 'a'], ['h', 'e', 'l', 'p', '.', 'p', 'r', 's', '.', '2', 's', 'g'], none⟩]⟩, ⟨['e'], ['a', 'n', 'd'], [⟨['e'], ['a', 'n', 'd'], none⟩]⟩, ⟨['e', 's', 't', 'á'], ['c', 'o', 'p', '.', 'p', 'r', 's', '.', '3', 's', 'g'], [⟨['e', 's', 't', 'á'], ['c', 'o', 'p', '.', 'p', 'r', 's', '.', '3', 's', 'g'], none⟩]⟩, ⟨['t', 'u', 'd', 'o'], ['a', 'l', 'l'], [⟨['t', 'u', 'd', 'o'], ['a', 'l', 'l'], none⟩]⟩, ⟨['b', 'e', 'm'], ['g', 'o', 'o', 'd'], [⟨['b', 'e', 'm'], ['g', 'o', 'o', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("hostFrame", "preposition complement")] }

def all : List Datum := [gs2025_1a, gs2025_1b, gs2025_1c, gs2025_t2_simple, gs2025_t2_old, gs2025_t2_mustsee, gs2025_t2_romney, gs2025_t2_honey, gs2025_t2_welcome, gs2025_t3_jespersen, gs2025_t3_diy, gs2025_t3_nyt, gs2025_8a, gs2025_15a, gs2025_15b, gs2025_15c, gs2025_16b, gs2025_17b, gs2025_18b]

end GoldbergShirtz2025.Examples
