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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
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
    alternatives := []
    readings := []
    paperFeatures := [("position", "verb"), ("inflection", "gerund")] }

def gs2025_8a : Datum :=
  { id := "gs2025_8a"
    source := ⟨"meibauer-2007", "p. 250"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(8a)"⟩
    language := "stan1295"
    primaryText := "Kaufe-Ihr-Auto-Kärtchen"
    glossedTokens := [("Kaufe-Ihr-Auto-Kärtchen", "buy.prs.1sg-2pl.poss-car-card.dim")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_15a : Datum :=
  { id := "gs2025_15a"
    source := ⟨"meibauer-2007", "p. 235"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(15a)"⟩
    language := "dutc1256"
    primaryText := "lach of ik schiet humor"
    glossedTokens := [("lach", "laugh.imp"), ("of", "or"), ("ik", "1sg"), ("schiet", "shoot.prs.sg"), ("humor", "humor")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_15b : Datum :=
  { id := "gs2025_15b"
    source := ⟨"meibauer-2007", "p. 235"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(15b)"⟩
    language := "afri1274"
    primaryText := "God is dod theologie"
    glossedTokens := [("God", "god"), ("is", "cop.prs.3sg"), ("dod", "dead"), ("theologie", "theology")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_15c : Datum :=
  { id := "gs2025_15c"
    source := ⟨"trips-kornfilt-2015", "p. 307"⟩
    reportedIn := some ⟨"goldberg-shirtz-2025", "(15c)"⟩
    language := "nucl1301"
    primaryText := "'iç çamasir-ın-ı göster' oyun-u"
    glossedTokens := [("iç", "internal"), ("çamasir-ın-ı", "laundry-3sg-acc"), ("göster", "show"), ("oyun-u", "game-cm")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hostFrame", "compound")] }

def gs2025_16b : Datum :=
  { id := "gs2025_16b"
    source := ⟨"goldberg-shirtz-2025", "(16b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "keta ʃel mi=ʃe yodea yodea"
    glossedTokens := [("keta", "section"), ("ʃel", "of"), ("mi=ʃe", "who=sbj"), ("yodea", "know.prs.3.m.sg"), ("yodea", "know.prs.3.m.sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hostFrame", "preposition complement")] }

def gs2025_17b : Datum :=
  { id := "gs2025_17b"
    source := ⟨"goldberg-shirtz-2025", "(17b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ani mitʁageʃet be=ʁama ʃel ani od ʁega boxa kan"
    glossedTokens := [("ani", "1sg"), ("mitʁageʃet", "be.excited.prs.f.sg"), ("be=ʁama", "in=level"), ("ʃel", "of"), ("ani", "I"), ("od", "more"), ("ʁega", "moment"), ("boxa", "cry.prs.f.sg"), ("kan", "here")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hostFrame", "preposition complement")] }

def gs2025_18b : Datum :=
  { id := "gs2025_18b"
    source := ⟨"goldberg-shirtz-2025", "(18b)"⟩
    reportedIn := none
    language := "braz1246"
    primaryText := "o clima ameno de 'eu te ajudo você me ajuda e está tudo bem'"
    glossedTokens := [("o", "def.m.sg"), ("clima", "climate"), ("ameno", "pleasant"), ("de", "of"), ("eu", "I"), ("te", "you"), ("ajudo", "help.prs.1sg"), ("você", "you"), ("me", "me"), ("ajuda", "help.prs.2sg"), ("e", "and"), ("está", "cop.prs.3sg"), ("tudo", "all"), ("bem", "good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("hostFrame", "preposition complement")] }

def all : List Datum := [gs2025_1a, gs2025_1b, gs2025_1c, gs2025_t2_simple, gs2025_t2_old, gs2025_t2_mustsee, gs2025_t2_romney, gs2025_t2_honey, gs2025_t2_welcome, gs2025_t3_jespersen, gs2025_t3_diy, gs2025_t3_nyt, gs2025_8a, gs2025_15a, gs2025_15b, gs2025_15c, gs2025_16b, gs2025_17b, gs2025_18b]

end GoldbergShirtz2025.Examples
