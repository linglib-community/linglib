module

public import Linglib.Data.StructureDataset.Schema

/-!
# `Dixon1982`: language samples

Auto-generated from `Linglib/Data/StructureDataset/Dixon1982.json` by
`scripts/gen_structure_dataset.py`. Do not edit by hand; edit the JSON and re-run the generator.
Declarations live in `namespace Dixon1982.StructureDataset`.
-/

@[expose] public section

namespace Dixon1982.StructureDataset

open Data.StructureDataset

/-- part of speech: The part of speech of the items of a semantic type in a language, in the abbreviations of Table 2 (p. 35). -/
inductive PartOfSpeech where
  /-- `A`: adjective -/
  | adjective
  /-- `N`: noun -/
  | noun
  /-- `V`: verb -/
  | verb
  /-- `ADVERB`: adverb -/
  | adverb
  /-- `PART`: particle -/
  | particle
  /-- `Nᵛ`: verbalised noun, a verb compounding a noun with *hu* 'do' or a few other verbs (Hua, p. 41) -/
  | verbalisedNoun
  /-- `N-A`: a noun that can also modify as an adjective (Telugu, p. 42) -/
  | nounAdjective
  /-- `Ad[+N]`: an adjunctive that modifies only nouns (Sango, p. 39) -/
  | adjunctiveN
  /-- `Ad[+V]`: an adjunctive that modifies only verbs (Sango, p. 39) -/
  | adjunctiveV
  /-- `Ad[+N,+V,S]`: an adjunctive that modifies nouns or verbs or is a substantive (Sango, p. 39) -/
  | adjunctiveNVS
  /-- `Ad[+N,S]`: an adjunctive that modifies nouns or is a substantive (Sango, p. 39) -/
  | adjunctiveNS
  /-- `A/V`: an adjective for the unmarked member of an antonym pair and a verb for the marked (pp. 51-52) -/
  | adjectiveVerb
  /-- `N/V`: a noun for the unmarked member of an antonym pair and a verb for the marked (pp. 51-52) -/
  | nounVerb
  /-- `A/ADVERB`: an adjective for one member of an antonym pair and an adverb for the other (Luganda, p. 48) -/
  | adjectiveAdverb
  /-- `N/ADVERB`: a noun for the unmarked member of an antonym pair and an adverb for the marked (Hausa, p. 52) -/
  | nounAdverb
  deriving DecidableEq, Repr

/-- A row of a sample: a language with its codes for each parameter. -/
structure Row where
  /-- The language. -/
  language : Language
  /-- The codes for SPEED. -/
  speed : List (Coded PartOfSpeech)
  /-- The codes for DIMENSION. -/
  dimension : List (Coded PartOfSpeech)
  /-- The codes for PHYSICAL PROPERTY. -/
  physicalProperty : List (Coded PartOfSpeech)
  /-- The codes for COLOUR. -/
  color : List (Coded PartOfSpeech)
  /-- The codes for HUMAN PROPENSITY. -/
  humanPropensity : List (Coded PartOfSpeech)
  /-- The codes for VALUE. -/
  value : List (Coded PartOfSpeech)
  /-- The codes for AGE. -/
  age : List (Coded PartOfSpeech)
  deriving DecidableEq, Repr

def swahili : Language :=
  { id := "swahili", name := "Swahili", glottocode := some "swah1253" }

def luganda : Language :=
  { id := "luganda", name := "Luganda", glottocode := some "gand1255" }

def bemba : Language :=
  { id := "bemba", name := "Bemba", glottocode := some "bemb1257" }

def japanese : Language :=
  { id := "japanese", name := "Japanese", glottocode := some "nucl1643" }

def sango : Language :=
  { id := "sango", name := "Sango", glottocode := some "sang1328" }

def hausa : Language :=
  { id := "hausa", name := "Hausa", glottocode := some "haus1257" }

def acooli : Language :=
  { id := "acooli", name := "Acooli", glottocode := some "acol1236" }

def hua : Language :=
  { id := "hua", name := "Hua", glottocode := some "huaa1250" }

def alamblak : Language :=
  { id := "alamblak", name := "Alamblak", glottocode := some "alam1246" }

def telugu : Language :=
  { id := "telugu", name := "Telugu", glottocode := some "telu1262" }

def kiriwinian : Language :=
  { id := "kiriwinian", name := "Kiriwinian", glottocode := some "kili1267" }

def tzotzil : Language :=
  { id := "tzotzil", name := "Tzotzil", glottocode := some "tzot1259" }

def chinook : Language :=
  { id := "chinook", name := "Chinook", glottocode := some "wasc1239" }

def yurok : Language :=
  { id := "yurok", name := "Yurok", glottocode := some "yuro1248" }

def samoan : Language :=
  { id := "samoan", name := "Samoan", glottocode := some "samo1305" }

def english : Language :=
  { id := "english", name := "English", glottocode := some "stan1293" }

def dyirbal : Language :=
  { id := "dyirbal", name := "Dyirbal", glottocode := some "dyir1250" }

/-- The part-of-speech membership of the seven types, from the basic part of speech of the roots expressing three dozen representative concepts in each language (§1.4.1). The rows of Table 2, in the order of the source (dixon-1982, Table 2, p. 35). -/
def table2 : List Row := [
  { language := swahili,
    speed := [⟨.adjective, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := luganda,
    speed := [⟨.adjectiveAdverb, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.noun, false, false, true⟩, ⟨.verb, false, false, true⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := bemba,
    speed := [⟨.adverb, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.verb, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    color := [⟨.verb, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := japanese,
    speed := [⟨.adjective, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.verb, false, false, true⟩, ⟨.noun, false, false, true⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := sango,
    speed := [⟨.adjunctiveV, false, false, false⟩],
    dimension := [⟨.adjunctiveNVS, false, false, false⟩, ⟨.verb, false, false, false⟩],
    physicalProperty := [⟨.verb, false, false, false⟩, ⟨.noun, false, false, true⟩],
    color := [⟨.adjunctiveN, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.adjunctiveNS, false, false, true⟩],
    value := [⟨.adjunctiveNVS, false, false, false⟩],
    age := [⟨.adjunctiveN, false, false, false⟩] },
  { language := hausa,
    speed := [⟨.nounAdverb, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩, ⟨.nounVerb, false, false, false⟩],
    physicalProperty := [⟨.verb, false, false, false⟩, ⟨.noun, false, false, false⟩, ⟨.nounVerb, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩],
    value := [⟨.noun, false, false, false⟩, ⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := acooli,
    speed := [⟨.adverb, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.verb, false, false, false⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := hua,
    speed := [⟨.verbalisedNoun, false, false, false⟩],
    dimension := [⟨.verbalisedNoun, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    physicalProperty := [⟨.verbalisedNoun, false, false, false⟩, ⟨.adjective, false, false, true⟩, ⟨.verb, false, false, true⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.verbalisedNoun, false, false, false⟩, ⟨.adjective, false, false, true⟩, ⟨.verb, false, false, true⟩],
    value := [⟨.verbalisedNoun, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := alamblak,
    speed := [⟨.adverb, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.verb, false, false, false⟩, ⟨.adjectiveVerb, false, false, false⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.verb, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := telugu,
    speed := [⟨.nounAdjective, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩, ⟨.nounAdjective, false, false, false⟩, ⟨.adjective, false, false, true⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.adjective, false, false, false⟩, ⟨.nounAdjective, false, false, false⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := kiriwinian,
    speed := [⟨.adverb, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩, ⟨.adjective, false, false, false⟩, ⟨.verb, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.adjective, false, false, false⟩],
    color := [⟨.noun, false, false, false⟩],
    humanPropensity := [⟨.verb, false, false, false⟩, ⟨.noun, false, false, true⟩, ⟨.adjective, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := tzotzil,
    speed := [⟨.adjective, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩, ⟨.verb, false, false, true⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.verb, false, false, true⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.adjective, false, false, true⟩, ⟨.verb, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := chinook,
    speed := [⟨.particle, false, false, false⟩],
    dimension := [⟨.noun, false, false, false⟩],
    physicalProperty := [⟨.particle, false, false, false⟩, ⟨.noun, false, false, true⟩, ⟨.verb, false, false, true⟩],
    color := [⟨.particle, false, false, false⟩],
    humanPropensity := [⟨.noun, false, false, false⟩, ⟨.verb, false, false, true⟩, ⟨.particle, false, false, true⟩],
    value := [⟨.noun, false, false, false⟩],
    age := [⟨.verb, false, false, false⟩] },
  { language := yurok,
    speed := [⟨.verb, false, false, false⟩],
    dimension := [⟨.verb, false, false, false⟩],
    physicalProperty := [⟨.verb, false, false, false⟩],
    color := [⟨.verb, false, false, false⟩],
    humanPropensity := [⟨.verb, false, false, false⟩],
    value := [⟨.verb, false, false, false⟩],
    age := [⟨.verb, false, false, false⟩] },
  { language := samoan,
    speed := [⟨.verb, false, false, false⟩],
    dimension := [⟨.verb, false, false, false⟩],
    physicalProperty := [⟨.verb, false, false, false⟩],
    color := [⟨.verb, false, false, false⟩],
    humanPropensity := [⟨.verb, false, false, false⟩, ⟨.noun, false, false, true⟩],
    value := [⟨.verb, false, false, false⟩],
    age := [⟨.verb, false, false, false⟩] },
  { language := english,
    speed := [⟨.adjective, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩, ⟨.verb, false, false, true⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.adjective, false, false, false⟩, ⟨.noun, false, false, true⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] },
  { language := dyirbal,
    speed := [⟨.adjective, false, false, false⟩],
    dimension := [⟨.adjective, false, false, false⟩],
    physicalProperty := [⟨.adjective, false, false, false⟩],
    color := [⟨.adjective, false, false, false⟩],
    humanPropensity := [⟨.adjective, false, false, false⟩],
    value := [⟨.adjective, false, false, false⟩],
    age := [⟨.adjective, false, false, false⟩] }]

end Dixon1982.StructureDataset
