module

public import Linglib.Data.Examples.Schema

/-!
# `Collins2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Collins2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Collins2005.Examples`.
-/

@[expose] public section

namespace Collins2005.Examples

def ex9a : Datum :=
  { id := "collins2005_ex9a"
    source := ⟨"collins-2005", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was by John written."
    glossedTokens := []
    context := "The passive with the external argument in Spec,vP and no movement of the participle phrase."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "inSitu"), ("verb", "written"), ("agent", "John"), ("patient", "the book")] }

def ex9b : Datum :=
  { id := "collins2005_ex9b"
    source := ⟨"collins-2005", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was written by John."
    glossedTokens := []
    context := "The passive derived by PartP movement to Spec,VoiceP, (22) and (30)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "partP"), ("verb", "written"), ("agent", "John"), ("patient", "the book")] }

def ex10a : Datum :=
  { id := "collins2005_ex10a"
    source := ⟨"collins-2005", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given to any student by no professor."
    glossedTokens := []
    context := "Barss and Lasnik c-command test: a negative quantifier in the by-phrase and a negative polarity item in a preceding PP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "npi"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "false"), ("verb", "given"), ("agent", "no professor"), ("patient", "the book"), ("pp", "to any student")] }

def ex10b : Datum :=
  { id := "collins2005_ex10b"
    source := ⟨"collins-2005", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given to the other by each professor."
    glossedTokens := []
    context := "Barss and Lasnik c-command test: each in the by-phrase and the other in a preceding PP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "other"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "false"), ("verb", "given"), ("agent", "each professor"), ("patient", "the book"), ("pp", "to the other")] }

def ex10c : Datum :=
  { id := "collins2005_ex10c"
    source := ⟨"collins-2005", "(10c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given by no professor to any student."
    glossedTokens := []
    context := "The PP follows the by-phrase: it evacuated PartP before the remnant fronted, (58), and the external argument c-commands it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "npi"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "true"), ("verb", "given"), ("agent", "no professor"), ("patient", "the book"), ("pp", "to any student")] }

def ex10d : Datum :=
  { id := "collins2005_ex10d"
    source := ⟨"collins-2005", "(10d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A book was given by each professor to the other."
    glossedTokens := []
    context := "The PP follows the by-phrase, evacuated before the remnant PartP fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "other"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "true"), ("verb", "given"), ("agent", "each professor"), ("patient", "a book"), ("pp", "to the other")] }

def ex15a : Datum :=
  { id := "collins2005_ex15a"
    source := ⟨"collins-2005", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The argument was summed up by the coach."
    glossedTokens := []
    context := "A particle verb passivized: the particle precedes the external argument."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "partP"), ("verb", "summed"), ("agent", "the coach"), ("patient", "the argument"), ("particle", "up")] }

def ex15b : Datum :=
  { id := "collins2005_ex15b"
    source := ⟨"collins-2005", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The argument was summed by the coach up."
    glossedTokens := []
    context := "The order head movement of the verb to Voice would derive, stranding the particle after the external argument."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "headMovement"), ("verb", "summed"), ("agent", "the coach"), ("patient", "the argument"), ("particle", "up")] }

def ex18a : Datum :=
  { id := "collins2005_ex18a"
    source := ⟨"collins-2005", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was spoken to by Mary."
    glossedTokens := []
    context := "A pseudo-passive: the stranded preposition precedes the external argument."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "partP"), ("verb", "spoken"), ("agent", "Mary"), ("patient", "John"), ("particle", "to")] }

def ex18b : Datum :=
  { id := "collins2005_ex18b"
    source := ⟨"collins-2005", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was spoken by Mary to."
    glossedTokens := []
    context := "The order head movement of the verb to Voice would derive, stranding the preposition after the external argument."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "headMovement"), ("verb", "spoken"), ("agent", "Mary"), ("patient", "John"), ("particle", "to")] }

def ex23a : Datum :=
  { id := "collins2005_ex23a"
    source := ⟨"collins-2005", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has seen the book."
    glossedTokens := []
    context := "Active perfect: the participle is c-selected by have, and there is no VoiceP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "participle"), ("auxiliary", "have"), ("voiceP", "false")] }

def ex23b : Datum :=
  { id := "collins2005_ex23b"
    source := ⟨"collins-2005", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book has seen by Mary."
    glossedTokens := []
    context := "Passive with have: the participle in Spec,VoiceP is already licensed by Voice and cannot also be checked by have."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "participle"), ("auxiliary", "have"), ("voiceP", "true")] }

def ex23c : Datum :=
  { id := "collins2005_ex23c"
    source := ⟨"collins-2005", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was seen by Mary."
    glossedTokens := []
    context := "Passive with be, which imposes no requirement on its complement; Voice licenses the participle."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "participle"), ("auxiliary", "be"), ("voiceP", "true")] }

def ex23d : Datum :=
  { id := "collins2005_ex23d"
    source := ⟨"collins-2005", "(23d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was seen the book."
    glossedTokens := []
    context := "Active with be and no VoiceP: nothing licenses the participle."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "participle"), ("auxiliary", "be"), ("voiceP", "false")] }

def ex27a : Datum :=
  { id := "collins2005_ex27a"
    source := ⟨"collins-2005", "(27a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A book written by John is on the table."
    glossedTokens := []
    context := "A passive participle modifying a noun: VoiceP present, no auxiliary."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "participle"), ("auxiliary", "none"), ("voiceP", "true")] }

def ex27b : Datum :=
  { id := "collins2005_ex27b"
    source := ⟨"collins-2005", "(27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man written a book just came in."
    glossedTokens := []
    context := "A past participle modifying a noun: neither a Voice head nor have."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "participle"), ("auxiliary", "none"), ("voiceP", "false")] }

def ex29 : Datum :=
  { id := "collins2005_ex29"
    source := ⟨"collins-2005", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was written by the book."
    glossedTokens := []
    context := "The internal argument in the by-phrase and the external argument raised to Spec,IP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "byComplement"), ("complement", "DP")] }

def ex56c : Datum :=
  { id := "collins2005_ex56c"
    source := ⟨"collins-2005", "(56c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given to Mary by John."
    glossedTokens := []
    context := "The PP pied-piped inside PartP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "partP"), ("evacuated", "false"), ("verb", "given"), ("agent", "John"), ("patient", "the book"), ("pp", "to Mary")] }

def ex56d : Datum :=
  { id := "collins2005_ex56d"
    source := ⟨"collins-2005", "(56d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given by John to Mary."
    glossedTokens := []
    context := "The PP evacuated to Spec,XP before the remnant PartP fronted, (58)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "passive"), ("analysis", "partP"), ("evacuated", "true"), ("verb", "given"), ("agent", "John"), ("patient", "the book"), ("pp", "to Mary")] }

def ex60a : Datum :=
  { id := "collins2005_ex60a"
    source := ⟨"collins-2005", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A gift was given by every student to his professor."
    glossedTokens := []
    context := "A quantifier in the by-phrase binding a pronoun in a PP that follows it, evacuated before the remnant PartP fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "variable"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "true"), ("verb", "given"), ("agent", "every student"), ("patient", "a gift"), ("pp", "to his professor")] }

def ex72a : Datum :=
  { id := "collins2005_ex72a"
    source := ⟨"collins-2005", "(72a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The magazines were sent to herself by Mary."
    glossedTokens := []
    context := "Principle A with the reflexive inside the fronted PartP: binding needs reconstruction, (73)."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "reflexive"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "false"), ("verb", "sent"), ("agent", "Mary"), ("patient", "the magazines"), ("pp", "to herself")] }

def ex74a : Datum :=
  { id := "collins2005_ex74a"
    source := ⟨"collins-2005", "(74a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The magazines were sent by Mary to herself."
    glossedTokens := []
    context := "Principle A with the reflexive in an evacuated PP: the external argument c-commands it without reconstruction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "reflexive"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "true"), ("verb", "sent"), ("agent", "Mary"), ("patient", "the magazines"), ("pp", "to herself")] }

def ex75 : Datum :=
  { id := "collins2005_ex75"
    source := ⟨"collins-2005", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Money was given to his mother by every boy."
    glossedTokens := []
    context := "A quantifier in the by-phrase binding a pronoun inside the fronted PartP: licensed once PartP reconstructs, without a Weak Crossover violation (§9.1)."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "variable"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "false"), ("verb", "given"), ("agent", "every boy"), ("patient", "money"), ("pp", "to his mother")] }

def ex76a : Datum :=
  { id := "collins2005_ex76a"
    source := ⟨"collins-2005", "(76a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The magazines were sent to Mary's mother by her yesterday."
    glossedTokens := []
    context := "Principle C with the name inside the fronted PartP and a coindexed pronoun in the by-phrase."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "name"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "false"), ("verb", "sent"), ("agent", "her"), ("patient", "the magazines"), ("pp", "to Mary's mother"), ("felicity", "infelicitous")] }

def ex80a : Datum :=
  { id := "collins2005_ex80a"
    source := ⟨"collins-2005", "(80a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The magazines were sent to her by Mary."
    glossedTokens := []
    context := "Principle B: the pronoun, coindexed with the external argument, is c-commanded by it when the external argument Merges, (84)."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "pronoun"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "false"), ("verb", "sent"), ("agent", "Mary"), ("patient", "the magazines"), ("pp", "to her")] }

def ex85a : Datum :=
  { id := "collins2005_ex85a"
    source := ⟨"collins-2005", "(85a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given to him by John's mother."
    glossedTokens := []
    context := "Principle C: the pronoun inside the fronted PartP does not c-command the name in the by-phrase."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "name"), ("antecedent", "pp"), ("dependent", "external"), ("evacuated", "false"), ("verb", "given"), ("agent", "John's mother"), ("patient", "the book"), ("pp", "to him")] }

def ex85b : Datum :=
  { id := "collins2005_ex85b"
    source := ⟨"collins-2005", "(85b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book was given by him to John's mother."
    glossedTokens := []
    context := "Principle C: the pronoun in the by-phrase c-commands the name in the evacuated PP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "name"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "true"), ("verb", "given"), ("agent", "him"), ("patient", "the book"), ("pp", "to John's mother")] }

def ex91a : Datum :=
  { id := "collins2005_ex91a"
    source := ⟨"collins-2005", "(91a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Books were given by the students to each other."
    glossedTokens := []
    context := "A reciprocal in a PP that follows the by-phrase, evacuated before the remnant PartP fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "reciprocal"), ("antecedent", "external"), ("dependent", "pp"), ("evacuated", "true"), ("verb", "given"), ("agent", "the students"), ("patient", "books"), ("pp", "to each other")] }

def ex91b : Datum :=
  { id := "collins2005_ex91b"
    source := ⟨"collins-2005", "(91b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Books were given to the students by each other."
    glossedTokens := []
    context := "A reciprocal in the by-phrase with its antecedent in a PP inside the fronted PartP, which does not c-command the external argument."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "licensing"), ("dependency", "reciprocal"), ("antecedent", "pp"), ("dependent", "external"), ("evacuated", "false"), ("verb", "given"), ("agent", "each other"), ("patient", "books"), ("pp", "to the students")] }

def all : List Datum := [ex9a, ex9b, ex10a, ex10b, ex10c, ex10d, ex15a, ex15b, ex18a, ex18b, ex23a, ex23b, ex23c, ex23d, ex27a, ex27b, ex29, ex56c, ex56d, ex60a, ex72a, ex74a, ex75, ex76a, ex80a, ex85a, ex85b, ex91a, ex91b]

end Collins2005.Examples
