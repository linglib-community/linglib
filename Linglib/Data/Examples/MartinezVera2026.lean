module

public import Linglib.Data.Examples.Schema

/-!
# `MartinezVera2026` — typed example data

Auto-generated from `Linglib/Data/Examples/MartinezVera2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MartinezVera2026.Examples`.
-/

@[expose] public section

namespace MartinezVera2026.Examples

def ex_6 : Datum :=
  { id := "martinezvera2026_6"
    source := ⟨"martinez-vera-2026", "(6)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka mana mayu-man ri-rka. Mana, Maria-ka mayu-man ri-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("mana", "no"), ("mayu-man", "river-DIR"), ("ri-rka", "go-PST1"), ("Mana", "no"), ("Maria-ka", "Maria-TOP"), ("mayu-man", "river-DIR"), ("ri-rka=mi", "go-PST1=mi")]
    context := "Two individuals are discussing Maria's whereabouts."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "assertedNegation"), ("focus", "clause")] }

def ex_7 : Datum :=
  { id := "martinezvera2026_7"
    source := ⟨"martinez-vera-2026", "(7)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka oveja-ta ranti-rka=mi."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("oveja-ta", "sheep-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    context := "A couple is on its house entrance seeing people passing by. One individual says (7)."
    judgment := .unacceptable
    alternatives := [("Juanchu-ka oveja-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("focus", "clause")] }

def ex_8b : Datum :=
  { id := "martinezvera2026_8b"
    source := ⟨"martinez-vera-2026", "(8b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka wakra-ta ranti-rka-chu? Ari, Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka-chu", "buy-PST1-POL"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    context := "One individual asks a question about Maria's whereabouts and another individual replies. There is no bias or expectations as to what Maria would be doing."
    judgment := .unacceptable
    alternatives := [("Ari, Maria-ka wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "polar"), ("focus", "clause")] }

def ex_8c : Datum :=
  { id := "martinezvera2026_8c"
    source := ⟨"martinez-vera-2026", "(8c)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka wakra-ta ranti-rka-chu? Mana, Maria-ka mana wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka-chu", "buy-PST1-POL"), ("Mana", "no"), ("Maria-ka", "Maria-TOP"), ("mana", "no"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    context := "One individual asks a question about Maria's whereabouts and another individual replies. There is no bias or expectations as to what Maria would be doing."
    judgment := .unacceptable
    alternatives := [("Mana, Maria-ka mana wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "polar"), ("focus", "clause"), ("polarity", "negative")] }

def fn5_i : Datum :=
  { id := "martinezvera2026_fn5_i"
    source := ⟨"martinez-vera-2026", "fn. 5 (i)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-manta ima tuku-shka? Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-manta", "Maria-ABL"), ("ima", "what"), ("tuku-shka", "happen-PST2"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    context := ""
    judgment := .unacceptable
    alternatives := [("Maria-ka wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "constituent"), ("focus", "clause")] }

def ex_9 : Datum :=
  { id := "martinezvera2026_9"
    source := ⟨"martinez-vera-2026", "(9)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka wakra-ta ranti-rka-chu, na? Ari, Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka-chu", "buy-PST1-POL"), ("na", "in.fact"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "debate"), ("question", "polar"), ("focus", "clause")] }

def ex_10 : Datum :=
  { id := "martinezvera2026_10"
    source := ⟨"martinez-vera-2026", "(10)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Maria-ka mana mayu-man ri-rka-chu? Ari, Maria-ka mayu-man ri-rka=mi."
    glossedTokens := [("Maria-ka", "Maria-TOP"), ("mana", "no"), ("mayu-man", "river-DIR"), ("ri-rka-chu", "go-PST1-POL"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("mayu-man", "river-DIR"), ("ri-rka=mi", "go-PST1=mi")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "none"), ("question", "negativeBiased"), ("focus", "clause")] }

def ex_11 : Datum :=
  { id := "martinezvera2026_11"
    source := ⟨"martinez-vera-2026", "(11)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Ciertu-chu wakra-ta ranti-rka? Ari, Maria-ka wakra-ta ranti-rka=mi."
    glossedTokens := [("Ciertu-chu", "in.fact-POL"), ("wakra-ta", "cow-ACC"), ("ranti-rka", "buy-PST1"), ("Ari", "yes"), ("Maria-ka", "Maria-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    context := "One individual asks a question about Maria's whereabouts and another individual replies. There has been some discussion about Maria's whereabouts, with it being suggested that Maria didn't buy a cow in addition to it being suggested that she did buy one, but the discussion is still open. The individual wants to settle the matter, so they ask the second individual to do so."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "debate"), ("question", "positiveBiased"), ("focus", "clause")] }

def ex_18a : Datum :=
  { id := "martinezvera2026_18a"
    source := ⟨"martinez-vera-2026", "(18a)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-rka, chay-ka mana shina-chu."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-rka", "go-PST1"), ("chay-ka", "that-TOP"), ("mana", "no"), ("shina-chu", "like.that-POL")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "direct"), ("continuation", "deniesScope")] }

def ex_18b : Datum :=
  { id := "martinezvera2026_18b"
    source := ⟨"martinez-vera-2026", "(18b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-rka, mana riku-rka-ni."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-rka", "go-PST1"), ("mana", "no"), ("riku-rka-ni", "see-PST1-1SG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "direct"), ("continuation", "deniesEvidence")] }

def ex_19a : Datum :=
  { id := "martinezvera2026_19a"
    source := ⟨"martinez-vera-2026", "(19a)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-shka, chay-ka mana shina-chu."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-shka", "go-PST2"), ("chay-ka", "that-TOP"), ("mana", "no"), ("shina-chu", "like.that-POL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("continuation", "deniesScope")] }

def ex_19b : Datum :=
  { id := "martinezvera2026_19b"
    source := ⟨"martinez-vera-2026", "(19b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mayu-man ri-shka, pi-pash chay-ta mana ni-rka-chu."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mayu-man", "river-DIR"), ("ri-shka", "go-PST2"), ("pi-pash", "no-one"), ("chay-ta", "that-ACC"), ("mana", "no"), ("ni-rka-chu", "say-PST1-POL")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("continuation", "deniesEvidence")] }

def ex_20 : Datum :=
  { id := "martinezvera2026_20"
    source := ⟨"martinez-vera-2026", "(20)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka shuk wakra-ta shuwa-rka; chashna=mi."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("shuk", "one"), ("wakra-ta", "cow-ACC"), ("shuwa-rka", "steal-PST1"), ("chashna=mi", "like.this=mi")]
    context := "Two individuals are discussing Juan's whereabouts. One of them shares the news that Juan stole a cow. They saw Juan doing so, but could not intervene."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "directEvidential"), ("focus", "clause")] }

def ex_21 : Datum :=
  { id := "martinezvera2026_21"
    source := ⟨"martinez-vera-2026", "(21)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka shuk wakra-ta shuwa-shka; chashna=mi."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("shuk", "one"), ("wakra-ta", "cow-ACC"), ("shuwa-shka", "steal-PST2"), ("chashna=mi", "like.this=mi")]
    context := "Two individuals are discussing Juan's whereabouts. One of them shares the news that Juan stole a cow. They were told that Juan did so, and they trust the source."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "reportativeEvidential"), ("focus", "clause")] }

def fn9_i : Datum :=
  { id := "martinezvera2026_fn9_i"
    source := ⟨"martinez-vera-2026", "fn. 9 (i)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka mayu-man ri-shka; mana shina=mi ka-shka-nka."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("mayu-man", "river-DIR"), ("ri-shka", "go-PST2"), ("mana", "no"), ("shina=mi", "like.this=mi"), ("ka-shka-nka", "be-PST2-CONJ")]
    context := "Two individuals are discussing Juan's whereabouts. One of them shares the news that Juan went to the river. They were told that Juan did so, but they don't trust the source."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "reportativeEvidential"), ("focus", "clause"), ("polarity", "negative")] }

def fn10_i : Datum :=
  { id := "martinezvera2026_fn10_i"
    source := ⟨"martinez-vera-2026", "fn. 10 (i)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka shuk wakra-ta shuwa-shka; chashna=mi, chay-ka mana shina-chu."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("shuk", "one"), ("wakra-ta", "cow-ACC"), ("shuwa-shka", "steal-PST2"), ("chashna=mi", "like.this=mi"), ("chay-ka", "that-TOP"), ("mana", "no"), ("shina-chu", "like.that-POL")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "reportative"), ("continuation", "confirmsThenDeniesScope")] }

def ex_22 : Datum :=
  { id := "martinezvera2026_22"
    source := ⟨"martinez-vera-2026", "(22)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu-ka wakra-ta ranti-rka. Mana, kuchi-ta=mi ranti-rka."
    glossedTokens := [("Juanchu-ka", "Juan-TOP"), ("wakra-ta", "cow-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("kuchi-ta=mi", "pig-ACC=mi"), ("ranti-rka", "buy-PST1")]
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def ex_23 : Datum :=
  { id := "martinezvera2026_23"
    source := ⟨"martinez-vera-2026", "(23)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Juanchu oveja-ta ranti-rka. Mana, Maria=mi oveja-ta ranti-rka."
    glossedTokens := [("Juanchu", "Juan"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Maria=mi", "Maria=mi"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1")]
    context := "Two discourse participants are discussing the issue of who bought a sheep at the Sunday market."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "subject"), ("contrast", "subject")] }

def ex_25 : Datum :=
  { id := "martinezvera2026_25"
    source := ⟨"martinez-vera-2026", "(25)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mina-man ri-rka. Mana, Pedro-ka mayu-man=mi ri-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mina-man", "mine-DIR"), ("ri-rka", "go-PST1"), ("Mana", "no"), ("Pedro-ka", "Pedro-TOP"), ("mayu-man=mi", "river-DIR=mi"), ("ri-rka", "go-PST1")]
    context := "Two discourse participants are discussing Pedro's whereabouts, in particular, where he went for the day."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "goal"), ("contrast", "goal")] }

def ex_26 : Datum :=
  { id := "martinezvera2026_26"
    source := ⟨"martinez-vera-2026", "(26)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mina-man ri-rka. Mana, Pedro-ka mikuna-kuna-ta mercado-pi ranti-chi-rka=mi."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mina-man", "mine-DIR"), ("ri-rka", "go-PST1"), ("Mana", "no"), ("Pedro-ka", "Pedro-TOP"), ("mikuna-kuna-ta", "food-PL-ACC"), ("mercado-pi", "market-LOC"), ("ranti-chi-rka=mi", "buy-CAUS-PST1=mi")]
    context := "Two individuals are discussing Pedro's whereabouts. Since heading to the mine is an activity that takes all day, it excludes any other activity."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "verbPhrase"), ("contrast", "verbPhrase")] }

def ex_27b : Datum :=
  { id := "martinezvera2026_27b"
    source := ⟨"martinez-vera-2026", "(27b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Segundo kuchita-ta ranti-rka. Mana, Segundo wakra-ta=mi ranti-rka."
    glossedTokens := [("Segundo", "Segundo"), ("kuchita-ta", "pig-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Segundo", "Segundo"), ("wakra-ta=mi", "cow-ACC=mi"), ("ranti-rka", "buy-PST1")]
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def ex_27c : Datum :=
  { id := "martinezvera2026_27c"
    source := ⟨"martinez-vera-2026", "(27c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "loja1235"
    primaryText := "Segundo kuchita-ta ranti-rka. Mana, Segundo=mi wakra-ta ranti-rka."
    glossedTokens := [("Segundo", "Segundo"), ("kuchita-ta", "pig-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Segundo=mi", "Segundo=mi"), ("wakra-ta", "cow-ACC"), ("ranti-rka", "buy-PST1")]
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .unacceptable
    alternatives := [("Mana, Segundo wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "subject"), ("contrast", "object")] }

def ex_27d : Datum :=
  { id := "martinezvera2026_27d"
    source := ⟨"martinez-vera-2026", "(27d)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Segundo kuchita-ta ranti-rka. Mana, Segundo wakra-ta ranti-rka=mi."
    glossedTokens := [("Segundo", "Segundo"), ("kuchita-ta", "pig-ACC"), ("ranti-rka", "buy-PST1"), ("Mana", "no"), ("Segundo", "Segundo"), ("wakra-ta", "cow-ACC"), ("ranti-rka=mi", "buy-PST1=mi")]
    context := "Two discourse participants are discussing the issue of what it was (i.e., what farm animal) that Juan bought, e.g., at the Sunday market."
    judgment := .unacceptable
    alternatives := [("Mana, Segundo wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "verb"), ("contrast", "object")] }

def ex_28_modifier : Datum :=
  { id := "martinezvera2026_28_modifier"
    source := ⟨"martinez-vera-2026", "(28)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Shuk Estados Unidos-manta ashpapi llankak Canada-manta=mi ashpapi llankak-wan tupanaku-n."
    glossedTokens := [("Shuk", "a"), ("Estados", "United"), ("Unidos-manta", "States-ABL"), ("ashpapi", "land.LOC"), ("llankak", "work.NMLZ"), ("Canada-manta=mi", "Canada-ABL=mi"), ("ashpapi", "land.LOC"), ("llankak-wan", "work.NMLZ-INST"), ("tupanaku-n", "meet-3")]
    context := ""
    judgment := .unacceptable
    alternatives := [("Shuk Estados Unidos-manta ashpapi llankak Canada-manta ashpapi llankak-wan tupanaku-n.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("focus", "modifier")] }

def ex_28_object : Datum :=
  { id := "martinezvera2026_28_object"
    source := ⟨"martinez-vera-2026", "(28)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Shuk Estados Unidos-manta ashpapi llankak Canada-manta ashpapi llankak-wan=mi tupanaku-n."
    glossedTokens := [("Shuk", "a"), ("Estados", "United"), ("Unidos-manta", "States-ABL"), ("ashpapi", "land.LOC"), ("llankak", "work.NMLZ"), ("Canada-manta", "Canada-ABL"), ("ashpapi", "land.LOC"), ("llankak-wan=mi", "work.NMLZ-INST=mi"), ("tupanaku-n", "meet-3")]
    context := ""
    judgment := .unacceptable
    alternatives := [("Shuk Estados Unidos-manta ashpapi llankak Canada-manta ashpapi llankak-wan tupanaku-n.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("focus", "object")] }

def ex_29b : Datum :=
  { id := "martinezvera2026_29b"
    source := ⟨"martinez-vera-2026", "(29b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka ima-ta ranti-rka? Pedro-ka oveja-ta=mi ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("ima-ta", "what-ACC"), ("ranti-rka", "buy-PST1"), ("Pedro-ka", "Pedro-TOP"), ("oveja-ta=mi", "sheep-ACC=mi"), ("ranti-rka", "buy-PST1")]
    context := "An individual asks another one about the farm animal that Pedro bought at the Sunday market."
    judgment := .unacceptable
    alternatives := [("Pedro-ka oveja-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "constituent"), ("focus", "object")] }

def ex_29c : Datum :=
  { id := "martinezvera2026_29c"
    source := ⟨"martinez-vera-2026", "(29c)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka ima-ta ranti-rka? Oveja-ta=mi Pedro-ka ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("ima-ta", "what-ACC"), ("ranti-rka", "buy-PST1"), ("Oveja-ta=mi", "sheep-ACC=mi"), ("Pedro-ka", "Pedro-TOP"), ("ranti-rka", "buy-PST1")]
    context := "An individual asks another one about the farm animal that Pedro bought at the Sunday market."
    judgment := .unacceptable
    alternatives := [("Oveja-ta Pedro-ka ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "none"), ("question", "constituent"), ("focus", "object")] }

def ex_30a : Datum :=
  { id := "martinezvera2026_30a"
    source := ⟨"martinez-vera-2026", "(30a)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mana oveja-ta ranti-rka; Pedro-ka wakra-ta=mi ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mana", "no"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1"), ("Pedro-ka", "Pedro-TOP"), ("wakra-ta=mi", "cow-ACC=mi"), ("ranti-rka", "buy-PST1")]
    context := "An individual communicates that the farm animal that Pedro bought was a cow, contrary to what was first thought, namely, that he bought a sheep."
    judgment := .acceptable
    alternatives := [("Pedro-ka mana oveja-ta ranti-rka; Pedro-ka wakra-ta ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def ex_30b : Datum :=
  { id := "martinezvera2026_30b"
    source := ⟨"martinez-vera-2026", "(30b)"⟩
    reportedIn := none
    language := "loja1235"
    primaryText := "Pedro-ka mana oveja-ta ranti-rka; wakra-ta=mi Pedro-ka ranti-rka."
    glossedTokens := [("Pedro-ka", "Pedro-TOP"), ("mana", "no"), ("oveja-ta", "sheep-ACC"), ("ranti-rka", "buy-PST1"), ("wakra-ta=mi", "cow-ACC=mi"), ("Pedro-ka", "Pedro-TOP"), ("ranti-rka", "buy-PST1")]
    context := "An individual communicates that the farm animal that Pedro bought was a cow, contrary to what was first thought, namely, that he bought a sheep."
    judgment := .acceptable
    alternatives := [("Pedro-ka mana oveja-ta ranti-rka; wakra-ta Pedro-ka ranti-rka.", .acceptable)]
    readings := []
    paperFeatures := [("prior", "correction"), ("focus", "object"), ("contrast", "object")] }

def all : List Datum := [ex_6, ex_7, ex_8b, ex_8c, fn5_i, ex_9, ex_10, ex_11, ex_18a, ex_18b, ex_19a, ex_19b, ex_20, ex_21, fn9_i, fn10_i, ex_22, ex_23, ex_25, ex_26, ex_27b, ex_27c, ex_27d, ex_28_modifier, ex_28_object, ex_29b, ex_29c, ex_30a, ex_30b]

end MartinezVera2026.Examples
