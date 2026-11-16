module

public import Linglib.Data.Examples.Schema

/-!
# `Glass2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Glass2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Glass2025.Examples`.
-/

@[expose] public section

namespace Glass2025.Examples

def ex_1a : Datum :=
  { id := "glass2025_1a"
    source := ⟨"glass-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex knows there's a meeting."
    glossedTokens := []
    context := "There is a meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "know"), ("state", "p")] }

def ex_2a_p : Datum :=
  { id := "glass2025_2a_p"
    source := ⟨"glass-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex thinks there's a meeting."
    glossedTokens := []
    context := "There is a meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "think"), ("state", "p")] }

def ex_2a_unsettled : Datum :=
  { id := "glass2025_2a_unsettled"
    source := ⟨"glass-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex thinks there's a meeting."
    glossedTokens := []
    context := "It is open whether there is a meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "think"), ("state", "unsettled")] }

def ex_2a_notP : Datum :=
  { id := "glass2025_2a_notP"
    source := ⟨"glass-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex thinks there's a meeting."
    glossedTokens := []
    context := "There is no meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "think"), ("state", "notP")] }

def ex_4_notP : Datum :=
  { id := "glass2025_4_notP"
    source := ⟨"glass-2023", "(4)"⟩
    reportedIn := some ⟨"glass-2025", "(4)"⟩
    language := "mand1415"
    primaryText := "Māma yǐwéi wǒ bìng le"
    glossedTokens := [("Māma", "mom"), ("yǐwéi", "yǐwéi"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    glossedWords := [⟨[['M', 'ā', 'm', 'a']], [['m', 'o', 'm']]⟩, ⟨[['y', 'ǐ', 'w', 'é', 'i']], [['y', 'ǐ', 'w', 'é', 'i']]⟩, ⟨[['w', 'ǒ']], [['1', 's', 'g']]⟩, ⟨[['b', 'ì', 'n', 'g']], [['s', 'i', 'c', 'k']]⟩, ⟨[['l', 'e']], [['a', 's', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker faked illness to avoid school."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yiwei"), ("state", "notP")] }

def ex_4_p : Datum :=
  { id := "glass2025_4_p"
    source := ⟨"glass-2023", "(4)"⟩
    reportedIn := some ⟨"glass-2025", "(4)"⟩
    language := "mand1415"
    primaryText := "Māma yǐwéi wǒ bìng le"
    glossedTokens := [("Māma", "mom"), ("yǐwéi", "yǐwéi"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    glossedWords := [⟨[['M', 'ā', 'm', 'a']], [['m', 'o', 'm']]⟩, ⟨[['y', 'ǐ', 'w', 'é', 'i']], [['y', 'ǐ', 'w', 'é', 'i']]⟩, ⟨[['w', 'ǒ']], [['1', 's', 'g']]⟩, ⟨[['b', 'ì', 'n', 'g']], [['s', 'i', 'c', 'k']]⟩, ⟨[['l', 'e']], [['a', 's', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker is definitely sick."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yiwei"), ("state", "p")] }

def ex_5_notP : Datum :=
  { id := "glass2025_5_notP"
    source := ⟨"glass-2023", "(5)"⟩
    reportedIn := some ⟨"glass-2025", "(5)"⟩
    language := "mand1415"
    primaryText := "Māma rènwéi wǒ bìng le"
    glossedTokens := [("Māma", "mom"), ("rènwéi", "think"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    glossedWords := [⟨[['M', 'ā', 'm', 'a']], [['m', 'o', 'm']]⟩, ⟨[['r', 'è', 'n', 'w', 'é', 'i']], [['t', 'h', 'i', 'n', 'k']]⟩, ⟨[['w', 'ǒ']], [['1', 's', 'g']]⟩, ⟨[['b', 'ì', 'n', 'g']], [['s', 'i', 'c', 'k']]⟩, ⟨[['l', 'e']], [['a', 's', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker faked illness to avoid school."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "renwei"), ("state", "notP")] }

def ex_5_unsettled : Datum :=
  { id := "glass2025_5_unsettled"
    source := ⟨"glass-2023", "(5)"⟩
    reportedIn := some ⟨"glass-2025", "(5)"⟩
    language := "mand1415"
    primaryText := "Māma rènwéi wǒ bìng le"
    glossedTokens := [("Māma", "mom"), ("rènwéi", "think"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    glossedWords := [⟨[['M', 'ā', 'm', 'a']], [['m', 'o', 'm']]⟩, ⟨[['r', 'è', 'n', 'w', 'é', 'i']], [['t', 'h', 'i', 'n', 'k']]⟩, ⟨[['w', 'ǒ']], [['1', 's', 'g']]⟩, ⟨[['b', 'ì', 'n', 'g']], [['s', 'i', 'c', 'k']]⟩, ⟨[['l', 'e']], [['a', 's', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := "The speaker feels exhausted and thinks she may indeed be sick, citing her mother's belief as evidence."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "renwei"), ("state", "unsettled")] }

def ex_7 : Datum :=
  { id := "glass2025_7"
    source := ⟨"glass-2023", "(7)"⟩
    reportedIn := some ⟨"glass-2025", "(7)"⟩
    language := "mand1415"
    primaryText := "wǒ bù zhīdào yǒu-méi-yǒu défēn, dànshì zhège qiúyuán yǐwéi défēn le"
    glossedTokens := [("wǒ", "I"), ("bù", "not"), ("zhīdào", "know"), ("yǒu-méi-yǒu", "have-not-have"), ("défēn", "score"), ("dànshì", "but"), ("zhège", "this-cl"), ("qiúyuán", "ball-player"), ("yǐwéi", "yǐwéi"), ("défēn", "score"), ("le", "asp")]
    glossedWords := [⟨[['w', 'ǒ']], [['I']]⟩, ⟨[['b', 'ù']], [['n', 'o', 't']]⟩, ⟨[['z', 'h', 'ī', 'd', 'à', 'o']], [['k', 'n', 'o', 'w']]⟩, ⟨[['y', 'ǒ', 'u'], ['m', 'é', 'i'], ['y', 'ǒ', 'u']], [['h', 'a', 'v', 'e'], ['n', 'o', 't'], ['h', 'a', 'v', 'e']]⟩, ⟨[['d', 'é', 'f', 'ē', 'n']], [['s', 'c', 'o', 'r', 'e']]⟩, ⟨[['d', 'à', 'n', 's', 'h', 'ì']], [['b', 'u', 't']]⟩, ⟨[['z', 'h', 'è', 'g', 'e']], [['t', 'h', 'i', 's'], ['c', 'l']]⟩, ⟨[['q', 'i', 'ú', 'y', 'u', 'á', 'n']], [['b', 'a', 'l', 'l'], ['p', 'l', 'a', 'y', 'e', 'r']]⟩, ⟨[['y', 'ǐ', 'w', 'é', 'i']], [['y', 'ǐ', 'w', 'é', 'i']]⟩, ⟨[['d', 'é', 'f', 'ē', 'n']], [['s', 'c', 'o', 'r', 'e']]⟩, ⟨[['l', 'e']], [['a', 's', 'p']]⟩]
    lgrConformance := some .wordAligned
    context := "The athlete caught the ball on the edge of the end zone and celebrates while the referees debate the catch; the speaker does not know whether he scored."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yiwei"), ("state", "unsettled")] }

def all : List Datum := [ex_1a, ex_2a_p, ex_2a_unsettled, ex_2a_notP, ex_4_notP, ex_4_p, ex_5_notP, ex_5_unsettled, ex_7]

end Glass2025.Examples
