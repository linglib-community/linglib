module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Iatridou2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Iatridou2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Iatridou2000.Examples`.
-/

@[expose] public section

namespace Iatridou2000.Examples

def ex1a : Datum :=
  { id := "iatridou2000_ex1a"
    source := ⟨"iatridou-2000", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I had a car."
    glossedTokens := []
    context := "Present counterfactual wish. Conveys: I don't have a car now. Past morphology (`had`) but present-time reference."
    judgment := .acceptable
    contrasts := []
    readings := [("present-CF (car absent now)", .acceptable)]
    paperFeatures := [("construction", "wish"), ("cf_type", "presCF")] }

def ex1b : Datum :=
  { id := "iatridou2000_ex1b"
    source := ⟨"iatridou-2000", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I had had a car when I was a student."
    glossedTokens := []
    context := "Past counterfactual wish. Conveys: I didn't have a car then (student days). Says nothing about whether I have a car now. Past-on-past morphology (`had had`) — the doubling encodes BOTH counterfactuality AND past temporal reference."
    judgment := .acceptable
    contrasts := []
    readings := [("past-CF (no car as student)", .acceptable)]
    paperFeatures := [("construction", "wish"), ("cf_type", "pastCF")] }

def ex2a : Datum :=
  { id := "iatridou2000_ex2a"
    source := ⟨"iatridou-2000", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he were smart, he would be rich."
    glossedTokens := []
    context := "Present counterfactual conditional. Conveys: he is not smart AND he is not rich. Past morphology (`were`, `would`) with present reference."
    judgment := .acceptable
    contrasts := []
    readings := [("present-CF (he is not smart and not rich)", .acceptable)]
    paperFeatures := [("construction", "conditional"), ("cf_type", "presCF")] }

def ex2b : Datum :=
  { id := "iatridou2000_ex2b"
    source := ⟨"iatridou-2000", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he had been smart, he would have been rich."
    glossedTokens := []
    context := "Past counterfactual conditional. Conveys: he was not smart (in general or on one specific occasion) AND he was not rich. Past-perfect morphology (`had been`, `would have been`) encodes BOTH counterfactuality AND past reference."
    judgment := .acceptable
    contrasts := []
    readings := [("past-CF (he was not smart and not rich)", .acceptable)]
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF")] }

def en_flv : Datum :=
  { id := "iatridou2000_en_flv"
    source := ⟨"iatridou-2000", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he took the syrup, he would get better."
    glossedTokens := []
    context := "Future Less Vivid conditional with a telic predicate (take the syrup). One (modal) ExclF; the past morphology is fake."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "flv"), ("past_layers", "1"), ("impf", "no"), ("subj", "no")] }

def en_presCF : Datum :=
  { id := "iatridou2000_en_presCF"
    source := ⟨"iatridou-2000", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I believed in ghosts, I would be afraid now."
    glossedTokens := []
    context := "Present counterfactual with an individual-level stative predicate (believe in ghosts). Same morphology as the FLV; the PresCF reading arises from the predicate's Aktionsart."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "presCF"), ("past_layers", "1"), ("impf", "no"), ("subj", "no")] }

def en_pastCF : Datum :=
  { id := "iatridou2000_en_pastCF"
    source := ⟨"iatridou-2000", "(48c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Napoleon had been tall, he would have defeated Wellington."
    glossedTokens := []
    context := "Past counterfactual conditional. The pluperfect antecedent has two past layers: one fake (modal ExclF), one real (temporal). Conveys Napoleon was not tall."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF"), ("past_layers", "2"), ("impf", "no"), ("subj", "no")] }

def gr_flv : Datum :=
  { id := "iatridou2000_gr_flv"
    source := ⟨"iatridou-2000", "(8)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An eperne afto to siropi θa γ₁inotan kala."
    glossedTokens := [("An", "if"), ("eperne", "take.PST.IPFV"), ("afto", "this"), ("to", ""), ("siropi", "syrup"), ("θa", "FUT"), ("γ₁inotan", "become.PST.IPFV"), ("kala", "well")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['e', 'p', 'e', 'r', 'n', 'e'], ['t', 'a', 'k', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], [⟨['e', 'p', 'e', 'r', 'n', 'e'], ['t', 'a', 'k', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], none⟩]⟩, ⟨['a', 'f', 't', 'o'], ['t', 'h', 'i', 's'], [⟨['a', 'f', 't', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], [⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['γ', '₁', 'i', 'n', 'o', 't', 'a', 'n'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], [⟨['γ', '₁', 'i', 'n', 'o', 't', 'a', 'n'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], none⟩]⟩, ⟨['k', 'a', 'l', 'a'], ['w', 'e', 'l', 'l'], [⟨['k', 'a', 'l', 'a'], ['w', 'e', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Modern Greek FLV with a telic predicate. The verbs carry past + imperfective morphology, both fake (future-oriented reading). Contrasts with the FNV (7), which has nonpast + perfective."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "flv"), ("past_layers", "1"), ("impf", "yes"), ("subj", "no")] }

def gr_pastCF : Datum :=
  { id := "iatridou2000_gr_pastCF"
    source := ⟨"iatridou-2000", "(5)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An iχ₁e pari to siropi θa iχ₁e γ₁ini kala."
    glossedTokens := [("An", "if"), ("iχ₁e", "had"), ("pari", "taken"), ("to", "the"), ("siropi", "syrup"), ("θa", "FUT"), ("iχ₁e", "had"), ("γ₁ini", "become"), ("kala", "better")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['i', 'χ', '₁', 'e'], ['h', 'a', 'd'], [⟨['i', 'χ', '₁', 'e'], ['h', 'a', 'd'], none⟩]⟩, ⟨['p', 'a', 'r', 'i'], ['t', 'a', 'k', 'e', 'n'], [⟨['p', 'a', 'r', 'i'], ['t', 'a', 'k', 'e', 'n'], none⟩]⟩, ⟨['t', 'o'], ['t', 'h', 'e'], [⟨['t', 'o'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], [⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['i', 'χ', '₁', 'e'], ['h', 'a', 'd'], [⟨['i', 'χ', '₁', 'e'], ['h', 'a', 'd'], none⟩]⟩, ⟨['γ', '₁', 'i', 'n', 'i'], ['b', 'e', 'c', 'o', 'm', 'e'], [⟨['γ', '₁', 'i', 'n', 'i'], ['b', 'e', 'c', 'o', 'm', 'e'], none⟩]⟩, ⟨['k', 'a', 'l', 'a'], ['b', 'e', 't', 't', 'e', 'r'], [⟨['k', 'a', 'l', 'a'], ['b', 'e', 't', 't', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Modern Greek PastCF. Like English, MG uses the pluperfect in the antecedent of a PastCF; the future is an undeclinable particle (θa), so the highest verb (the perfect auxiliary) carries past morphology."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF"), ("past_layers", "2"), ("impf", "yes"), ("subj", "no")] }

def fr_flv : Datum :=
  { id := "iatridou2000_fr_flv"
    source := ⟨"iatridou-2000", "(100)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si Pierre partait demain, il arriverait là-bas la semaine prochaine."
    glossedTokens := [("Si", "if"), ("Pierre", "Pierre"), ("partait", "left"), ("demain", "tomorrow"), ("il", "he"), ("arriverait", "would arrive"), ("là-bas", "there"), ("la", "the"), ("semaine", "week"), ("prochaine", "next")]
    glossedWords := [⟨['S', 'i'], ['i', 'f'], [⟨['S', 'i'], ['i', 'f'], none⟩]⟩, ⟨['P', 'i', 'e', 'r', 'r', 'e'], ['P', 'i', 'e', 'r', 'r', 'e'], [⟨['P', 'i', 'e', 'r', 'r', 'e'], ['P', 'i', 'e', 'r', 'r', 'e'], none⟩]⟩, ⟨['p', 'a', 'r', 't', 'a', 'i', 't'], ['l', 'e', 'f', 't'], [⟨['p', 'a', 'r', 't', 'a', 'i', 't'], ['l', 'e', 'f', 't'], none⟩]⟩, ⟨['d', 'e', 'm', 'a', 'i', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['d', 'e', 'm', 'a', 'i', 'n'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['i', 'l'], ['h', 'e'], [⟨['i', 'l'], ['h', 'e'], none⟩]⟩, ⟨['a', 'r', 'r', 'i', 'v', 'e', 'r', 'a', 'i', 't'], ['w', 'o', 'u', 'l', 'd', ' ', 'a', 'r', 'r', 'i', 'v', 'e'], [⟨['a', 'r', 'r', 'i', 'v', 'e', 'r', 'a', 'i', 't'], ['w', 'o', 'u', 'l', 'd', ' ', 'a', 'r', 'r', 'i', 'v', 'e'], none⟩]⟩, ⟨['l', 'à', '-', 'b', 'a', 's'], ['t', 'h', 'e', 'r', 'e'], []⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'e', 'm', 'a', 'i', 'n', 'e'], ['w', 'e', 'e', 'k'], [⟨['s', 'e', 'm', 'a', 'i', 'n', 'e'], ['w', 'e', 'e', 'k'], none⟩]⟩, ⟨['p', 'r', 'o', 'c', 'h', 'a', 'i', 'n', 'e'], ['n', 'e', 'x', 't'], [⟨['p', 'r', 'o', 'c', 'h', 'a', 'i', 'n', 'e'], ['n', 'e', 'x', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "French FLV: imparfait in the antecedent, conditionnel in the consequent. Iatridou argues the conditionnel is imparfait morphology on a future stem (ExclF + Imp over a future), not a separate `conditional mood`."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "flv"), ("past_layers", "1"), ("impf", "yes"), ("subj", "no")] }

def fr_presCF : Datum :=
  { id := "iatridou2000_fr_presCF"
    source := ⟨"iatridou-2000", "(101)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si je savais que c'était du chocolat, je le mangerais."
    glossedTokens := [("Si", "if"), ("je", "I"), ("savais", "knew"), ("que", "that"), ("c'était", "this were"), ("du", "of.the"), ("chocolat", "chocolate"), ("je", "I"), ("le", "it"), ("mangerais", "would eat")]
    glossedWords := [⟨['S', 'i'], ['i', 'f'], [⟨['S', 'i'], ['i', 'f'], none⟩]⟩, ⟨['j', 'e'], ['I'], [⟨['j', 'e'], ['I'], none⟩]⟩, ⟨['s', 'a', 'v', 'a', 'i', 's'], ['k', 'n', 'e', 'w'], [⟨['s', 'a', 'v', 'a', 'i', 's'], ['k', 'n', 'e', 'w'], none⟩]⟩, ⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], [⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['c', '\'', 'é', 't', 'a', 'i', 't'], ['t', 'h', 'i', 's', ' ', 'w', 'e', 'r', 'e'], [⟨['c', '\'', 'é', 't', 'a', 'i', 't'], ['t', 'h', 'i', 's', ' ', 'w', 'e', 'r', 'e'], none⟩]⟩, ⟨['d', 'u'], ['o', 'f', '.', 't', 'h', 'e'], [⟨['d', 'u'], ['o', 'f', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['c', 'h', 'o', 'c', 'o', 'l', 'a', 't'], ['c', 'h', 'o', 'c', 'o', 'l', 'a', 't', 'e'], [⟨['c', 'h', 'o', 'c', 'o', 'l', 'a', 't'], ['c', 'h', 'o', 'c', 'o', 'l', 'a', 't', 'e'], none⟩]⟩, ⟨['j', 'e'], ['I'], [⟨['j', 'e'], ['I'], none⟩]⟩, ⟨['l', 'e'], ['i', 't'], [⟨['l', 'e'], ['i', 't'], none⟩]⟩, ⟨['m', 'a', 'n', 'g', 'e', 'r', 'a', 'i', 's'], ['w', 'o', 'u', 'l', 'd', ' ', 'e', 'a', 't'], [⟨['m', 'a', 'n', 'g', 'e', 'r', 'a', 'i', 's'], ['w', 'o', 'u', 'l', 'd', ' ', 'e', 'a', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "French PresCF: morphologically identical to the FLV (imparfait/conditionnel); the PresCF reading arises from the individual-level stative predicate."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "presCF"), ("past_layers", "1"), ("impf", "yes"), ("subj", "no")] }

def fr_pastCF : Datum :=
  { id := "iatridou2000_fr_pastCF"
    source := ⟨"iatridou-2000", "(102)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si Pierre était venu, je l'aurais vu."
    glossedTokens := [("Si", "if"), ("Pierre", "Pierre"), ("était", "had"), ("venu", "come"), ("je", "I"), ("l'aurais", "him would have"), ("vu", "seen")]
    glossedWords := [⟨['S', 'i'], ['i', 'f'], [⟨['S', 'i'], ['i', 'f'], none⟩]⟩, ⟨['P', 'i', 'e', 'r', 'r', 'e'], ['P', 'i', 'e', 'r', 'r', 'e'], [⟨['P', 'i', 'e', 'r', 'r', 'e'], ['P', 'i', 'e', 'r', 'r', 'e'], none⟩]⟩, ⟨['é', 't', 'a', 'i', 't'], ['h', 'a', 'd'], [⟨['é', 't', 'a', 'i', 't'], ['h', 'a', 'd'], none⟩]⟩, ⟨['v', 'e', 'n', 'u'], ['c', 'o', 'm', 'e'], [⟨['v', 'e', 'n', 'u'], ['c', 'o', 'm', 'e'], none⟩]⟩, ⟨['j', 'e'], ['I'], [⟨['j', 'e'], ['I'], none⟩]⟩, ⟨['l', '\'', 'a', 'u', 'r', 'a', 'i', 's'], ['h', 'i', 'm', ' ', 'w', 'o', 'u', 'l', 'd', ' ', 'h', 'a', 'v', 'e'], [⟨['l', '\'', 'a', 'u', 'r', 'a', 'i', 's'], ['h', 'i', 'm', ' ', 'w', 'o', 'u', 'l', 'd', ' ', 'h', 'a', 'v', 'e'], none⟩]⟩, ⟨['v', 'u'], ['s', 'e', 'e', 'n'], [⟨['v', 'u'], ['s', 'e', 'e', 'n'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "French PastCF: plus-que-parfait in the antecedent, conditionnel passé in the consequent. Two past layers."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF"), ("past_layers", "2"), ("impf", "yes"), ("subj", "no")] }

def ex7 : Datum :=
  { id := "iatridou2000_ex7"
    source := ⟨"iatridou-2000", "(7)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An pari afto to siropi θa γ₁ini kala."
    glossedTokens := [("An", "if"), ("pari", "take.NPST.PFV"), ("afto", "this"), ("to", ""), ("siropi", "syrup"), ("θa", "FUT"), ("γ₁ini", "become.NPST.PFV"), ("kala", "well")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['p', 'a', 'r', 'i'], ['t', 'a', 'k', 'e', '.', 'N', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['p', 'a', 'r', 'i'], ['t', 'a', 'k', 'e', '.', 'N', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['a', 'f', 't', 'o'], ['t', 'h', 'i', 's'], [⟨['a', 'f', 't', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], [⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['γ', '₁', 'i', 'n', 'i'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'N', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['γ', '₁', 'i', 'n', 'i'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'N', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['k', 'a', 'l', 'a'], ['w', 'e', 'l', 'l'], [⟨['k', 'a', 'l', 'a'], ['w', 'e', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("construction", "conditional"), ("cf_type", "fnv"), ("past_layers", "0"), ("impf", "no")] }

def ex10a : Datum :=
  { id := "iatridou2000_ex10a"
    source := ⟨"iatridou-2000", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John comes to the party, and I think he will, we will have a great time."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("cf_type", "fnv")] }

def ex10b : Datum :=
  { id := "iatridou2000_ex10b"
    source := ⟨"iatridou-2000", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John came to the party, and I think he will, we would have a great time."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("cf_type", "flv"), ("implicature", "the actual world is more likely to become a not-p world")] }

def ex11 : Datum :=
  { id := "iatridou2000_ex11"
    source := ⟨"iatridou-2000", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that if he took the syrup, he would get better."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("cf_type", "flv"), ("implicature", "survives negation")] }

def ex13b : Datum :=
  { id := "iatridou2000_ex13b"
    source := ⟨"iatridou-2000", "(13b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An efevγ₁es avrio θa eftanes eki tin ali evδomaδa."
    glossedTokens := [("An", "if"), ("efevγ₁es", "leave.PST.IPFV"), ("avrio", "tomorrow"), ("θa", "FUT"), ("eftanes", "arrive.PST.IPFV"), ("eki", "there"), ("tin", "the"), ("ali", "other"), ("evδomaδa", "week")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['e', 'f', 'e', 'v', 'γ', '₁', 'e', 's'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], [⟨['e', 'f', 'e', 'v', 'γ', '₁', 'e', 's'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], none⟩]⟩, ⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['e', 'f', 't', 'a', 'n', 'e', 's'], ['a', 'r', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], [⟨['e', 'f', 't', 'a', 'n', 'e', 's'], ['a', 'r', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], none⟩]⟩, ⟨['e', 'k', 'i'], ['t', 'h', 'e', 'r', 'e'], [⟨['e', 'k', 'i'], ['t', 'h', 'e', 'r', 'e'], none⟩]⟩, ⟨['t', 'i', 'n'], ['t', 'h', 'e'], [⟨['t', 'i', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'l', 'i'], ['o', 't', 'h', 'e', 'r'], [⟨['a', 'l', 'i'], ['o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['e', 'v', 'δ', 'o', 'm', 'a', 'δ', 'a'], ['w', 'e', 'e', 'k'], [⟨['e', 'v', 'δ', 'o', 'm', 'a', 'δ', 'a'], ['w', 'e', 'e', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("cf_type", "flv"), ("adverbial", "future-oriented"), ("impf", "yes")] }

def ex20 : Datum :=
  { id := "iatridou2000_ex20"
    source := ⟨"iatridou-2000", "(20)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An ipχ₁e afto to siropi θa eγ₁ine kala."
    glossedTokens := [("An", "if"), ("ipχ₁e", "drink.PST.PFV"), ("afto", "this"), ("to", ""), ("siropi", "syrup"), ("θa", "MOD"), ("eγ₁ine", "become.PST.PFV"), ("kala", "well")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['i', 'p', 'χ', '₁', 'e'], ['d', 'r', 'i', 'n', 'k', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['i', 'p', 'χ', '₁', 'e'], ['d', 'r', 'i', 'n', 'k', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['a', 'f', 't', 'o'], ['t', 'h', 'i', 's'], [⟨['a', 'f', 't', 'o'], ['t', 'h', 'i', 's'], none⟩]⟩, ⟨['t', 'o'], [], [⟨['t', 'o'], [], none⟩]⟩, ⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], [⟨['s', 'i', 'r', 'o', 'p', 'i'], ['s', 'y', 'r', 'u', 'p'], none⟩]⟩, ⟨['θ', 'a'], ['M', 'O', 'D'], [⟨['θ', 'a'], ['M', 'O', 'D'], none⟩]⟩, ⟨['e', 'γ', '₁', 'i', 'n', 'e'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['e', 'γ', '₁', 'i', 'n', 'e'], ['b', 'e', 'c', 'o', 'm', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['k', 'a', 'l', 'a'], ['w', 'e', 'l', 'l'], [⟨['k', 'a', 'l', 'a'], ['w', 'e', 'l', 'l'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("construction", "epistemic conditional"), ("past_layers", "1 real"), ("impf", "no")] }

def ex21b : Datum :=
  { id := "iatridou2000_ex21b"
    source := ⟨"iatridou-2000", "(21b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An efiγ₁e avrio θa eftase tin ali evδomaδa."
    glossedTokens := [("An", "if"), ("efiγ₁e", "leave.PST.PFV"), ("avrio", "tomorrow"), ("θa", "FUT"), ("eftase", "arrive.PST.PFV"), ("tin", "the"), ("ali", "other"), ("evδomaδa", "week")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['e', 'f', 'i', 'γ', '₁', 'e'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['e', 'f', 'i', 'γ', '₁', 'e'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['e', 'f', 't', 'a', 's', 'e'], ['a', 'r', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['e', 'f', 't', 'a', 's', 'e'], ['a', 'r', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['t', 'i', 'n'], ['t', 'h', 'e'], [⟨['t', 'i', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['a', 'l', 'i'], ['o', 't', 'h', 'e', 'r'], [⟨['a', 'l', 'i'], ['o', 't', 'h', 'e', 'r'], none⟩]⟩, ⟨['e', 'v', 'δ', 'o', 'm', 'a', 'δ', 'a'], ['w', 'e', 'e', 'k'], [⟨['e', 'v', 'δ', 'o', 'm', 'a', 'δ', 'a'], ['w', 'e', 'e', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("adverbial", "future-oriented"), ("impf", "no")] }

def ex21c : Datum :=
  { id := "iatridou2000_ex21c"
    source := ⟨"iatridou-2000", "(21c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An efiγ₁e proχtes θa eftase χθes."
    glossedTokens := [("An", "if"), ("efiγ₁e", "leave.PST.PFV"), ("proχtes", "day.before.yesterday"), ("θa", "MOD"), ("eftase", "arrive.PST.PFV"), ("χθes", "yesterday")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['e', 'f', 'i', 'γ', '₁', 'e'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['e', 'f', 'i', 'γ', '₁', 'e'], ['l', 'e', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['p', 'r', 'o', 'χ', 't', 'e', 's'], ['d', 'a', 'y', '.', 'b', 'e', 'f', 'o', 'r', 'e', '.', 'y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['p', 'r', 'o', 'χ', 't', 'e', 's'], ['d', 'a', 'y', '.', 'b', 'e', 'f', 'o', 'r', 'e', '.', 'y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['θ', 'a'], ['M', 'O', 'D'], [⟨['θ', 'a'], ['M', 'O', 'D'], none⟩]⟩, ⟨['e', 'f', 't', 'a', 's', 'e'], ['a', 'r', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], [⟨['e', 'f', 't', 'a', 's', 'e'], ['a', 'r', 'r', 'i', 'v', 'e', '.', 'P', 'S', 'T', '.', 'P', 'F', 'V'], none⟩]⟩, ⟨['χ', 'θ', 'e', 's'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['χ', 'θ', 'e', 's'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "2.1"), ("adverbial", "past-oriented"), ("impf", "no")] }

def ex47a : Datum :=
  { id := "iatridou2000_ex47a"
    source := ⟨"iatridou-2000", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Fred was drunk, he would be louder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("cf_type", "presCF"), ("aktionsart", "stage-level stative")] }

def ex47b : Datum :=
  { id := "iatridou2000_ex47b"
    source := ⟨"iatridou-2000", "(47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Mary knew the answer, she would be the only one."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("cf_type", "presCF"), ("aktionsart", "individual-level stative")] }

def ex47d : Datum :=
  { id := "iatridou2000_ex47d"
    source := ⟨"iatridou-2000", "(47d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I had green eyes, I would be prettier."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("cf_type", "presCF"), ("aktionsart", "individual-level stative")] }

def ex48a : Datum :=
  { id := "iatridou2000_ex48a"
    source := ⟨"iatridou-2000", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Napoleon had been tall."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("pluperfect", "temporal")] }

def ex48b : Datum :=
  { id := "iatridou2000_ex48b"
    source := ⟨"iatridou-2000", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Napoleon was tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("past", "temporal")] }

def ex53 : Datum :=
  { id := "iatridou2000_ex53"
    source := ⟨"iatridou-2000", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She walked into the room and saw a table. It was wooden."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("past", "topic time precedes utterance time"), ("situation", "may include utterance time")] }

def ex54 : Datum :=
  { id := "iatridou2000_ex54"
    source := ⟨"iatridou-2000", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She walked into the room and saw Peter lying on the floor. He was drunk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("past", "topic time precedes utterance time"), ("situation", "stage-level, not extended")] }

def ex59 : Datum :=
  { id := "iatridou2000_ex59"
    source := ⟨"iatridou-2000", "(59)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was in the classroom. In fact, he still is."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("past", "topic time excludes utterance time"), ("situation", "includes both")] }

def ex60a : Datum :=
  { id := "iatridou2000_ex60a"
    source := ⟨"iatridou-2000", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he took that syrup, he would get better."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("cf_type", "flv"), ("reading", "feature over worlds")] }

def ex60b : Datum :=
  { id := "iatridou2000_ex60b"
    source := ⟨"iatridou-2000", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he took that syrup, he must be better now."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3"), ("construction", "epistemic conditional"), ("reading", "feature over times")] }

def ex62b : Datum :=
  { id := "iatridou2000_ex62b"
    source := ⟨"iatridou-2000", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you gave him that book, he would read it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("cf_type", "flv"), ("aktionsart", "telic")] }

def ex63a : Datum :=
  { id := "iatridou2000_ex63a"
    source := ⟨"iatridou-2000", "(63a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I knew this were chocolate, I would eat it."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("cf_type", "presCF"), ("aktionsart", "individual-level stative")] }

def ex63b : Datum :=
  { id := "iatridou2000_ex63b"
    source := ⟨"iatridou-2000", "(63b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I were tall, I would be able to reach the ceiling."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("cf_type", "presCF"), ("aktionsart", "individual-level stative")] }

def ex64a : Datum :=
  { id := "iatridou2000_ex64a"
    source := ⟨"iatridou-2000", "(64a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he were drunk at next week's meeting, the boss would be really angry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("cf_type", "flv"), ("aktionsart", "stage-level stative")] }

def ex64b : Datum :=
  { id := "iatridou2000_ex64b"
    source := ⟨"iatridou-2000", "(64b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he were drunk, he would be louder."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("cf_type", "presCF"), ("aktionsart", "stage-level stative")] }

def ex65 : Datum :=
  { id := "iatridou2000_ex65"
    source := ⟨"iatridou-2000", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he takes the syrup, ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("tense", "present"), ("aktionsart", "telic"), ("evaluation", "future")] }

def ex66 : Datum :=
  { id := "iatridou2000_ex66"
    source := ⟨"iatridou-2000", "(66)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he is tall, ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("tense", "present"), ("aktionsart", "individual-level stative"), ("evaluation", "now")] }

def ex67a : Datum :=
  { id := "iatridou2000_ex67a"
    source := ⟨"iatridou-2000", "(67a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he is drunk next week, ..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("tense", "present"), ("aktionsart", "stage-level stative"), ("evaluation", "future")] }

def ex67b : Datum :=
  { id := "iatridou2000_ex67b"
    source := ⟨"iatridou-2000", "(67b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he is drunk, we should not let him drive."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("tense", "present"), ("aktionsart", "stage-level stative"), ("evaluation", "now")] }

def ex68a : Datum :=
  { id := "iatridou2000_ex68a"
    source := ⟨"iatridou-2000", "(68a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't know if he will come, but if he came, he would have a great time."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("cf_type", "flv"), ("speaker", "agnostic about the antecedent")] }

def ex69b : Datum :=
  { id := "iatridou2000_ex69b"
    source := ⟨"iatridou-2000", "(69b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He's not rich. Too bad, because if he were rich, he would be popular with that crowd."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4"), ("cf_type", "presCF"), ("speaker", "believes the antecedent false")] }

def ex74 : Datum :=
  { id := "iatridou2000_ex74"
    source := ⟨"iatridou-2000", "(74)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An ton aγapuse avrio, θa imun poli eftiχ₁ismeni."
    glossedTokens := [("An", "if"), ("ton", "him"), ("aγapuse", "love.IPFV.PST"), ("avrio", "tomorrow"), ("θa", "FUT"), ("imun", "was"), ("poli", "very"), ("eftiχ₁ismeni", "happy")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['t', 'o', 'n'], ['h', 'i', 'm'], [⟨['t', 'o', 'n'], ['h', 'i', 'm'], none⟩]⟩, ⟨['a', 'γ', 'a', 'p', 'u', 's', 'e'], ['l', 'o', 'v', 'e', '.', 'I', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['a', 'γ', 'a', 'p', 'u', 's', 'e'], ['l', 'o', 'v', 'e', '.', 'I', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['i', 'm', 'u', 'n'], ['w', 'a', 's'], [⟨['i', 'm', 'u', 'n'], ['w', 'a', 's'], none⟩]⟩, ⟨['p', 'o', 'l', 'i'], ['v', 'e', 'r', 'y'], [⟨['p', 'o', 'l', 'i'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['e', 'f', 't', 'i', 'χ', '₁', 'i', 's', 'm', 'e', 'n', 'i'], ['h', 'a', 'p', 'p', 'y'], [⟨['e', 'f', 't', 'i', 'χ', '₁', 'i', 's', 'm', 'e', 'n', 'i'], ['h', 'a', 'p', 'p', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("impf", "yes"), ("reading", "stage-level stative, not inchoative")] }

def ex75 : Datum :=
  { id := "iatridou2000_ex75"
    source := ⟨"iatridou-2000", "(75)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An ton aγapuse, θa itan poli eftiχ₁ismeni."
    glossedTokens := [("An", "if"), ("ton", "him"), ("aγapuse", "love.IPFV.PST"), ("θa", "FUT"), ("itan", "was"), ("poli", "very"), ("eftiχ₁ismeni", "happy")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['t', 'o', 'n'], ['h', 'i', 'm'], [⟨['t', 'o', 'n'], ['h', 'i', 'm'], none⟩]⟩, ⟨['a', 'γ', 'a', 'p', 'u', 's', 'e'], ['l', 'o', 'v', 'e', '.', 'I', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['a', 'γ', 'a', 'p', 'u', 's', 'e'], ['l', 'o', 'v', 'e', '.', 'I', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['i', 't', 'a', 'n'], ['w', 'a', 's'], [⟨['i', 't', 'a', 'n'], ['w', 'a', 's'], none⟩]⟩, ⟨['p', 'o', 'l', 'i'], ['v', 'e', 'r', 'y'], [⟨['p', 'o', 'l', 'i'], ['v', 'e', 'r', 'y'], none⟩]⟩, ⟨['e', 'f', 't', 'i', 'χ', '₁', 'i', 's', 'm', 'e', 'n', 'i'], ['h', 'a', 'p', 'p', 'y'], [⟨['e', 'f', 't', 'i', 'χ', '₁', 'i', 's', 'm', 'e', 'n', 'i'], ['h', 'a', 'p', 'p', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("cf_type", "presCF"), ("impf", "yes")] }

def ex79 : Datum :=
  { id := "iatridou2000_ex79"
    source := ⟨"iatridou-2000", "(79)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An avrio kata tin δiarkia tis teletis δiavazes tin efimeriδa, θa se apelian."
    glossedTokens := [("An", "if"), ("avrio", "tomorrow"), ("kata", "during"), ("tin", ""), ("δiarkia", ""), ("tis", "the"), ("teletis", "ceremony"), ("δiavazes", "read.IPFV.PST"), ("tin", "the"), ("efimeriδa", "newspaper"), ("θa", "FUT"), ("se", "you"), ("apelian", "fire.PST.IPFV")]
    glossedWords := [⟨['A', 'n'], ['i', 'f'], [⟨['A', 'n'], ['i', 'f'], none⟩]⟩, ⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['a', 'v', 'r', 'i', 'o'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩, ⟨['k', 'a', 't', 'a'], ['d', 'u', 'r', 'i', 'n', 'g'], [⟨['k', 'a', 't', 'a'], ['d', 'u', 'r', 'i', 'n', 'g'], none⟩]⟩, ⟨['t', 'i', 'n'], [], [⟨['t', 'i', 'n'], [], none⟩]⟩, ⟨['δ', 'i', 'a', 'r', 'k', 'i', 'a'], [], [⟨['δ', 'i', 'a', 'r', 'k', 'i', 'a'], [], none⟩]⟩, ⟨['t', 'i', 's'], ['t', 'h', 'e'], [⟨['t', 'i', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['t', 'e', 'l', 'e', 't', 'i', 's'], ['c', 'e', 'r', 'e', 'm', 'o', 'n', 'y'], [⟨['t', 'e', 'l', 'e', 't', 'i', 's'], ['c', 'e', 'r', 'e', 'm', 'o', 'n', 'y'], none⟩]⟩, ⟨['δ', 'i', 'a', 'v', 'a', 'z', 'e', 's'], ['r', 'e', 'a', 'd', '.', 'I', 'P', 'F', 'V', '.', 'P', 'S', 'T'], [⟨['δ', 'i', 'a', 'v', 'a', 'z', 'e', 's'], ['r', 'e', 'a', 'd', '.', 'I', 'P', 'F', 'V', '.', 'P', 'S', 'T'], none⟩]⟩, ⟨['t', 'i', 'n'], ['t', 'h', 'e'], [⟨['t', 'i', 'n'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 'f', 'i', 'm', 'e', 'r', 'i', 'δ', 'a'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r'], [⟨['e', 'f', 'i', 'm', 'e', 'r', 'i', 'δ', 'a'], ['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r'], none⟩]⟩, ⟨['θ', 'a'], ['F', 'U', 'T'], [⟨['θ', 'a'], ['F', 'U', 'T'], none⟩]⟩, ⟨['s', 'e'], ['y', 'o', 'u'], [⟨['s', 'e'], ['y', 'o', 'u'], none⟩]⟩, ⟨['a', 'p', 'e', 'l', 'i', 'a', 'n'], ['f', 'i', 'r', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], [⟨['a', 'p', 'e', 'l', 'i', 'a', 'n'], ['f', 'i', 'r', 'e', '.', 'P', 'S', 'T', '.', 'I', 'P', 'F', 'V'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5"), ("cf_type", "flv"), ("impf", "yes"), ("reading", "ongoing")] }

def ex97a : Datum :=
  { id := "iatridou2000_ex97a"
    source := ⟨"iatridou-2000", "(97a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Dudo que Maria esté enferma."
    glossedTokens := [("Dudo", "I doubt"), ("que", "that"), ("Maria", "Maria"), ("esté", "be.PRS.SBJV"), ("enferma", "sick")]
    glossedWords := [⟨['D', 'u', 'd', 'o'], ['I', ' ', 'd', 'o', 'u', 'b', 't'], [⟨['D', 'u', 'd', 'o'], ['I', ' ', 'd', 'o', 'u', 'b', 't'], none⟩]⟩, ⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], [⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], [⟨['M', 'a', 'r', 'i', 'a'], ['M', 'a', 'r', 'i', 'a'], none⟩]⟩, ⟨['e', 's', 't', 'é'], ['b', 'e', '.', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V'], [⟨['e', 's', 't', 'é'], ['b', 'e', '.', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V'], none⟩]⟩, ⟨['e', 'n', 'f', 'e', 'r', 'm', 'a'], ['s', 'i', 'c', 'k'], [⟨['e', 'n', 'f', 'e', 'r', 'm', 'a'], ['s', 'i', 'c', 'k'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Dudo que Maria estuviera enferma.", .acceptable), ("Dudo que Maria está enferma.", .ungrammatical), ("Dudo que Maria estaba enferma.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "6.1"), ("mood", "dubitative subjunctive"), ("paradigm", "past and present subjunctive")] }

def ex98 : Datum :=
  { id := "iatridou2000_ex98"
    source := ⟨"iatridou-2000", "(98)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je doute que Marie ait un parapluie rouge."
    glossedTokens := [("Je", "I"), ("doute", "doubt"), ("que", "that"), ("Marie", "Marie"), ("ait", "have.PRS.SBJV"), ("un", "an"), ("parapluie", "umbrella"), ("rouge", "red")]
    glossedWords := [⟨['J', 'e'], ['I'], [⟨['J', 'e'], ['I'], none⟩]⟩, ⟨['d', 'o', 'u', 't', 'e'], ['d', 'o', 'u', 'b', 't'], [⟨['d', 'o', 'u', 't', 'e'], ['d', 'o', 'u', 'b', 't'], none⟩]⟩, ⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], [⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['a', 'i', 't'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V'], [⟨['a', 'i', 't'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', 'S', 'B', 'J', 'V'], none⟩]⟩, ⟨['u', 'n'], ['a', 'n'], [⟨['u', 'n'], ['a', 'n'], none⟩]⟩, ⟨['p', 'a', 'r', 'a', 'p', 'l', 'u', 'i', 'e'], ['u', 'm', 'b', 'r', 'e', 'l', 'l', 'a'], [⟨['p', 'a', 'r', 'a', 'p', 'l', 'u', 'i', 'e'], ['u', 'm', 'b', 'r', 'e', 'l', 'l', 'a'], none⟩]⟩, ⟨['r', 'o', 'u', 'g', 'e'], ['r', 'e', 'd'], [⟨['r', 'o', 'u', 'g', 'e'], ['r', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "A: Marie avait un parapluie rouge."
    judgment := .acceptable
    contrasts := [("Je doute que Marie a un parapluie rouge.", .ungrammatical), ("Je doute que Marie avait un parapluie rouge.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "6.1"), ("mood", "dubitative subjunctive"), ("paradigm", "nonpast subjunctive only")] }

def ex99 : Datum :=
  { id := "iatridou2000_ex99"
    source := ⟨"iatridou-2000", "(99)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si Marie avait un parapluie rouge, ..."
    glossedTokens := [("Si", "if"), ("Marie", "Marie"), ("avait", "have.PST.IND"), ("un", "an"), ("parapluie", "umbrella"), ("rouge", "red")]
    glossedWords := [⟨['S', 'i'], ['i', 'f'], [⟨['S', 'i'], ['i', 'f'], none⟩]⟩, ⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], [⟨['M', 'a', 'r', 'i', 'e'], ['M', 'a', 'r', 'i', 'e'], none⟩]⟩, ⟨['a', 'v', 'a', 'i', 't'], ['h', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'I', 'N', 'D'], [⟨['a', 'v', 'a', 'i', 't'], ['h', 'a', 'v', 'e', '.', 'P', 'S', 'T', '.', 'I', 'N', 'D'], none⟩]⟩, ⟨['u', 'n'], ['a', 'n'], [⟨['u', 'n'], ['a', 'n'], none⟩]⟩, ⟨['p', 'a', 'r', 'a', 'p', 'l', 'u', 'i', 'e'], ['u', 'm', 'b', 'r', 'e', 'l', 'l', 'a'], [⟨['p', 'a', 'r', 'a', 'p', 'l', 'u', 'i', 'e'], ['u', 'm', 'b', 'r', 'e', 'l', 'l', 'a'], none⟩]⟩, ⟨['r', 'o', 'u', 'g', 'e'], ['r', 'e', 'd'], [⟨['r', 'o', 'u', 'g', 'e'], ['r', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := [("Si Marie ait un parapluie rouge, ...", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "6.1"), ("mood", "past indicative"), ("paradigm", "nonpast subjunctive only")] }

def all : List Datum := [ex1a, ex1b, ex2a, ex2b, en_flv, en_presCF, en_pastCF, gr_flv, gr_pastCF, fr_flv, fr_presCF, fr_pastCF, ex7, ex10a, ex10b, ex11, ex13b, ex20, ex21b, ex21c, ex47a, ex47b, ex47d, ex48a, ex48b, ex53, ex54, ex59, ex60a, ex60b, ex62b, ex63a, ex63b, ex64a, ex64b, ex65, ex66, ex67a, ex67b, ex68a, ex69b, ex74, ex75, ex79, ex97a, ex98, ex99]

/-- The time at which the conditional is evaluated. -/
inductive Evaluation where
  /-- future: the future -/
  | future
  /-- now: the present -/
  | now
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `evaluation`. -/
def evaluation (e : Datum) : Option Evaluation :=
  e.parse? "evaluation" [("future", .future), ("now", .now)]

/-- The aspectual class of the predicate. -/
inductive Aktionsart where
  /-- telic: telic -/
  | telic
  /-- activity: an activity -/
  | activity
  /-- individual-level stative: an individual-level stative -/
  | individualLevelStative
  /-- stage-level stative: a stage-level stative -/
  | stageLevelStative
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `aktionsart`. -/
def aktionsart (e : Datum) : Option Aktionsart :=
  e.parse? "aktionsart" [("telic", .telic), ("activity", .activity),
    ("individual-level stative", .individualLevelStative),
    ("stage-level stative", .stageLevelStative)]

end Iatridou2000.Examples
