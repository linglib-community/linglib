module

public import Linglib.Data.Examples.Schema

/-!
# `Declerck1991` — typed example data

Auto-generated from `Linglib/Data/Examples/Declerck1991.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Declerck1991.Examples`.
-/

@[expose] public section

namespace Declerck1991.Examples

def domainShift1a : Datum :=
  { id := "declerck1991_domainShift1a"
    source := ⟨"declerck-1991-grammar", "ch. 3 ex (1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I left while Bill was sleeping and Mary was having a bath."
    glossedTokens := []
    context := "Declerck's example of three situations simultaneous within one temporal domain. `left` is an absolute past establishing a past domain; the two `was`-progressives are relative tenses expressing simultaneity with the central situation. All three are in the same temporal domain."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def domainShift1b : Datum :=
  { id := "declerck1991_domainShift1b"
    source := ⟨"declerck-1991-grammar", "ch. 3 ex (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suddenly the phone rang. Jill stood up from her chair, went over to the telephone and picked up the receiver."
    glossedTokens := []
    context := "Declerck's example of domain shift via absolute preterites. Each clause uses an absolute past tense — no relative tense forms like past perfect (anteriority) or conditional (posteriority). Temporal ordering recovered from clause order alone, not from tense composition."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def domainShift3a : Datum :=
  { id := "declerck1991_domainShift3a"
    source := ⟨"declerck-1991-grammar", "ch. 3 ex (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The soldier got seriously wounded. He died shortly afterwards."
    glossedTokens := []
    context := "Declerck's example (3a): domain shift with `died` as absolute preterite. Temporal posteriority of dying relative to wounding comes from the adverbial `shortly afterwards`, not from any relative tense form."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def modalPastWish : Datum :=
  { id := "declerck1991_modalPastWish"
    source := ⟨"declerck-1991-grammar", "ch. 1 §1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I didn't know his number."
    glossedTokens := []
    context := "Declerck's example of modal past: `didn't know` is past in form but simultaneous in interpretation (the not-knowing is at the wishing time, which is now, not in the past). Contrasts with `He says I didn't know his number` (nonmodal past, true past reference)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def modalPastIfWas : Datum :=
  { id := "declerck1991_modalPastIfWas"
    source := ⟨"declerck-1991-grammar", "ch. 1 §1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I was a rich man, I would travel a lot."
    glossedTokens := []
    context := "Declerck's example of modal past in conditional: `was` is past in form but the reference is to the present (the hypothetical speaker now), not to the past."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def futurePerfect : Datum :=
  { id := "declerck1991_futurePerfect"
    source := ⟨"declerck-1991-grammar", "ch. 1 §1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will have left by then."
    glossedTokens := []
    context := "Declerck's example of the future perfect form. The leaving event precedes a reference point `by then` which is itself future relative to utterance."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def whenPresent : Datum :=
  { id := "declerck1991_whenPresent"
    source := ⟨"declerck-1991-grammar", "ch. 1 §1.6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You will have to tell him (the news) when he comes home."
    glossedTokens := []
    context := "Declerck's example of adverbial time clause with present-tense morphology referring to future. `when he comes home` uses present `comes` despite future reference — typical of when-/before-/after-clauses with future reference."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def perfectHaveCome : Datum :=
  { id := "declerck1991_perfectHaveCome"
    source := ⟨"declerck-1991-grammar", "ch. 1 §1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've come here."
    glossedTokens := []
    context := "Declerck's basic present perfect example. The coming event is in the pre-present sector; the reference frame is present (R = P at TU). Contrasts with a past-tense counterpart that would locate the event in the past time-sphere proper."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [] }

def perfectOverslept : Datum :=
  { id := "declerck1991_perfectOverslept"
    source := ⟨"declerck-1991-grammar", "ch. 3 fn 49"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have overslept this morning."
    glossedTokens := []
    context := "Declerck's example showing the present-perfect time-sphere effect: `I have overslept this morning` REQUIRES that the morning is not yet over (present time-sphere). Its preterit counterpart `I overslept this morning` does not require that the morning is over: it can be used in the morning if the speaker is concerned not with the structure of the world at TU but with the situation itself, which is completely over."
    judgment := .acceptable
    contrasts := [("I overslept this morning.", .acceptable)]
    readings := []
    paperFeatures := [] }

def all : List Datum := [domainShift1a, domainShift1b, domainShift3a, modalPastWish, modalPastIfWas, futurePerfect, whenPresent, perfectHaveCome, perfectOverslept]

end Declerck1991.Examples
