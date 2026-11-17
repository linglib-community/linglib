module

public import Linglib.Data.Examples.Schema

/-!
# `LoGuercio2025` — typed example data

Auto-generated from `Linglib/Data/Examples/LoGuercio2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LoGuercio2025.Examples`.
-/

@[expose] public section

namespace LoGuercio2025.Examples

def outOfBlue_epithet : Datum :=
  { id := "loguercio2025_outOfBlue_epithet"
    source := ⟨"lo-guercio-2025", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived late."
    glossedTokens := []
    context := "Out of the blue, no prior mention of any epithet construction."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "epithet"), ("licensingMechanism", "outOfBlue")] }

def priorMention_epithet : Datum :=
  { id := "loguercio2025_priorMention_epithet"
    source := ⟨"lo-guercio-2025", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived first, then that bastard Pedro arrived."
    glossedTokens := []
    context := "Single conjoined utterance; the ACI target is the first conjunct's bare `John`."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "John (first conjunct)"), ("expressionType", "epithet"), ("licensingMechanism", "priorMention")] }

def subconstituent_epithet : Datum :=
  { id := "loguercio2025_subconstituent_epithet"
    source := ⟨"lo-guercio-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John met with that bastard Pedro."
    glossedTokens := []
    context := "Single sentence; the epithet construction occurs as a subconstituent making the alternative for the matrix `John` available."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "John (matrix subject)"), ("expressionType", "epithet"), ("licensingMechanism", "subconstituent")] }

def outOfBlue_honorific : Datum :=
  { id := "loguercio2025_outOfBlue_honorific"
    source := ⟨"lo-guercio-2025", "(20a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Diego entró."
    glossedTokens := [("Diego", "Diego"), ("entró", "entered")]
    glossedWords := [⟨['D', 'i', 'e', 'g', 'o'], ['D', 'i', 'e', 'g', 'o'], [⟨['D', 'i', 'e', 'g', 'o'], ['D', 'i', 'e', 'g', 'o'], none⟩]⟩, ⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd'], [⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Out-of-the-blue Spanish utterance; no prior contextual relevance of *don/doña*."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "honorific"), ("licensingMechanism", "outOfBlue"), ("language", "Spanish")] }

def contrastive_honorific : Datum :=
  { id := "loguercio2025_contrastive_honorific"
    source := ⟨"lo-guercio-2025", "(23a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Primero entró Donato. Después entró Don Pedro."
    glossedTokens := [("Primero", "first"), ("entró", "entered"), ("Donato", "Donato"), ("Después", "afterwards"), ("entró", "entered"), ("Don", "HON.M"), ("Pedro", "Pedro")]
    glossedWords := [⟨['P', 'r', 'i', 'm', 'e', 'r', 'o'], ['f', 'i', 'r', 's', 't'], [⟨['P', 'r', 'i', 'm', 'e', 'r', 'o'], ['f', 'i', 'r', 's', 't'], none⟩]⟩, ⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd'], [⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['D', 'o', 'n', 'a', 't', 'o'], ['D', 'o', 'n', 'a', 't', 'o'], [⟨['D', 'o', 'n', 'a', 't', 'o'], ['D', 'o', 'n', 'a', 't', 'o'], none⟩]⟩, ⟨['D', 'e', 's', 'p', 'u', 'é', 's'], ['a', 'f', 't', 'e', 'r', 'w', 'a', 'r', 'd', 's'], [⟨['D', 'e', 's', 'p', 'u', 'é', 's'], ['a', 'f', 't', 'e', 'r', 'w', 'a', 'r', 'd', 's'], none⟩]⟩, ⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd'], [⟨['e', 'n', 't', 'r', 'ó'], ['e', 'n', 't', 'e', 'r', 'e', 'd'], none⟩]⟩, ⟨['D', 'o', 'n'], ['H', 'O', 'N', '.', 'M'], [⟨['D', 'o', 'n'], ['H', 'O', 'N', '.', 'M'], none⟩]⟩, ⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], [⟨['P', 'e', 'd', 'r', 'o'], ['P', 'e', 'd', 'r', 'o'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Two-segment discourse; the second segment uses honorific *Don* while the first uses bare name *Donato*."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Donato (first segment)"), ("expressionType", "honorific"), ("licensingMechanism", "priorMention"), ("language", "Spanish")] }

def outOfBlue_appositive : Datum :=
  { id := "loguercio2025_outOfBlue_appositive"
    source := ⟨"lo-guercio-2025", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Diego recommended an aspirin."
    glossedTokens := []
    context := "Out-of-the-blue; no prior appositive construction in discourse."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "appositive"), ("licensingMechanism", "outOfBlue")] }

def priorMention_appositive : Datum :=
  { id := "loguercio2025_priorMention_appositive"
    source := ⟨"lo-guercio-2025", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
    glossedTokens := []
    context := "Two-segment discourse; the second segment's `, a doctor,` appositive makes the same-shape appositive a contextually-relevant alternative for `Diego`."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Diego (first segment)"), ("expressionType", "appositive"), ("licensingMechanism", "priorMention")] }

def outOfBlue_suppAdverb : Datum :=
  { id := "loguercio2025_outOfBlue_suppAdverb"
    source := ⟨"lo-guercio-2025", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament."
    glossedTokens := []
    context := "Out-of-the-blue assertion with no supplementary-adverb construction in discourse."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "supplementaryAdverb"), ("licensingMechanism", "outOfBlue")] }

def priorMention_suppAdverb : Datum :=
  { id := "loguercio2025_priorMention_suppAdverb"
    source := ⟨"lo-guercio-2025", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament and luckily, Pedro signed up for the tournament."
    glossedTokens := []
    context := "Conjoined utterance; the second conjunct's `luckily,` makes the parallel adverb-modified variant available for the first conjunct."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan-signup proposition (first conjunct)"), ("expressionType", "supplementaryAdverb"), ("licensingMechanism", "priorMention")] }

def priorMention_emotiveMarker : Datum :=
  { id := "loguercio2025_priorMention_emotiveMarker"
    source := ⟨"lo-guercio-2025", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament, and Alas/Wow!, Pedro signed up for the tournament as well."
    glossedTokens := []
    context := "Conjoined utterance; second conjunct's emotive marker `Alas/Wow!` parallels the first conjunct."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan-signup proposition (first conjunct)"), ("expressionType", "emotiveMarker"), ("licensingMechanism", "priorMention")] }

def registerBlocking : Datum :=
  { id := "loguercio2025_registerBlocking"
    source := ⟨"lo-guercio-2025", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That bastard John is late."
    glossedTokens := []
    context := "Both *bastard* and *motherfucker* are lexical items in the substitution source, with *motherfucker* CI-stronger; the prediction would be an ACI ¬(speaker believes John is a motherfucker)."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "epithet"), ("licensingMechanism", "register"), ("registerContrast", "bastard~motherfucker")] }

def disjunction_independent_of_assertion : Datum :=
  { id := "loguercio2025_disjunction_independent_of_assertion"
    source := ⟨"lo-guercio-2025", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan called María or that bastard Pedro."
    glossedTokens := []
    context := "Test of independence-of-assertion: the CI-stronger conjunctive variant has different at-issue content from the disjunctive utterance, yet the ACI still arises."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "María"), ("expressionType", "epithet"), ("aciProperty", "independentOfAssertion")] }

def DE_aci_survives : Datum :=
  { id := "loguercio2025_DE_aci_survives"
    source := ⟨"lo-guercio-2025", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that Juan or that bastard Pedro passed the exam."
    glossedTokens := []
    context := "Downward-entailing embedding under `doubt`; tests whether DE blocks ACI computation."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan"), ("expressionType", "epithet"), ("aciProperty", "unaffectedByDE")] }

def cancellation : Datum :=
  { id := "loguercio2025_cancellation"
    source := ⟨"lo-guercio-2025", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan arrived first. Then that bastard Pedro arrived. By the way, Juan is also a bastard."
    glossedTokens := []
    context := "Tests cancellability of the ACI ¬(speaker believes Juan is a bastard) triggered by the prior-mention configuration."
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("aciStatus", "cancelled"), ("aciProperty", "cancellable")] }

def all : List Datum := [outOfBlue_epithet, priorMention_epithet, subconstituent_epithet, outOfBlue_honorific, contrastive_honorific, outOfBlue_appositive, priorMention_appositive, outOfBlue_suppAdverb, priorMention_suppAdverb, priorMention_emotiveMarker, registerBlocking, disjunction_independent_of_assertion, DE_aci_survives, cancellation]

end LoGuercio2025.Examples
