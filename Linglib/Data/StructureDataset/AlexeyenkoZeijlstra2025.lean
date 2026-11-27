module

public import Linglib.Data.StructureDataset.Schema

/-!
# `AlexeyenkoZeijlstra2025`: language samples

Auto-generated from `Linglib/Data/StructureDataset/AlexeyenkoZeijlstra2025.json` by
`scripts/gen_structure_dataset.py`. Do not edit by hand; edit the JSON and re-run the generator.
Declarations live in `namespace AlexeyenkoZeijlstra2025.StructureDataset`.
-/

@[expose] public section

namespace AlexeyenkoZeijlstra2025.StructureDataset

open CLDF.StructureDataset

/-- adjective order: The side of the noun on which the attributive adjective stands, the two blocks of Table 3. -/
inductive AdjectiveOrder where
  /-- `A–N`: The adjective precedes the noun. -/
  | adjectiveNoun
  /-- `N–A`: The adjective follows the noun. -/
  | nounAdjective
  deriving DecidableEq, Repr

/-- XP-intervention: Whether a dependent of the adjective may stand between the adjective and the noun, the two halves of Table 3. -/
inductive Intervention where
  /-- `XP-intervention possible`: A dependent may separate the adjective from the noun. -/
  | possible
  /-- `XP-intervention impossible`: No dependent may separate the adjective from the noun. -/
  | impossible
  deriving DecidableEq, Repr

/-- A row of a sample: a language with its codes for each parameter. -/
structure Row where
  /-- The language. -/
  language : Language
  /-- The codes for adjective order. -/
  adjectiveOrder : List (Coded AdjectiveOrder)
  /-- The codes for XP-intervention. -/
  intervention : List (Coded Intervention)
  deriving DecidableEq, Repr

def abkhaz : Language :=
  { id := "abkhaz", name := "Abkhaz", glottocode := some "abkh1244" }

def bulgarian : Language :=
  { id := "bulgarian", name := "Bulgarian", glottocode := some "bulg1262" }

def polish : Language :=
  { id := "polish", name := "Polish", glottocode := some "poli1260" }

def russian : Language :=
  { id := "russian", name := "Russian", glottocode := some "russ1263" }

def latin : Language :=
  { id := "latin", name := "Latin", glottocode := some "lati1261" }

def lithuanian : Language :=
  { id := "lithuanian", name := "Lithuanian", glottocode := some "lith1251" }

def mandarin : Language :=
  { id := "mandarin", name := "Mandarin", glottocode := some "mand1415" }

def modern_greek : Language :=
  { id := "modern_greek", name := "Modern Greek", glottocode := some "mode1248" }

def statimcets : Language :=
  { id := "statimcets", name := "St'át'imcets", glottocode := some "lill1248" }

def tagalog : Language :=
  { id := "tagalog", name := "Tagalog", glottocode := some "taga1270" }

def armenian : Language :=
  { id := "armenian", name := "Armenian", glottocode := some "nucl1235" }

def dutch : Language :=
  { id := "dutch", name := "Dutch", glottocode := some "dutc1256" }

def english : Language :=
  { id := "english", name := "English", glottocode := some "stan1293" }

def german : Language :=
  { id := "german", name := "German", glottocode := some "stan1295" }

def icelandic : Language :=
  { id := "icelandic", name := "Icelandic", glottocode := some "icel1247" }

def estonian : Language :=
  { id := "estonian", name := "Estonian", glottocode := some "esto1258" }

def finnish : Language :=
  { id := "finnish", name := "Finnish", glottocode := some "finn1318" }

def hungarian : Language :=
  { id := "hungarian", name := "Hungarian", glottocode := some "hung1274" }

def french : Language :=
  { id := "french", name := "French", glottocode := some "stan1290" }

def italian : Language :=
  { id := "italian", name := "Italian", glottocode := some "ital1282" }

def portuguese : Language :=
  { id := "portuguese", name := "Portuguese", glottocode := some "port1283" }

def romanian : Language :=
  { id := "romanian", name := "Romanian", glottocode := some "roma1327" }

def spanish : Language :=
  { id := "spanish", name := "Spanish", glottocode := some "stan1288" }

def georgian : Language :=
  { id := "georgian", name := "Georgian", glottocode := some "nucl1302" }

def serbo_croatian : Language :=
  { id := "serbo_croatian", name := "Serbo-Croatian", glottocode := some "sout1528" }

def atong : Language :=
  { id := "atong", name := "Atong", glottocode := some "aton1241" }

def farsi : Language :=
  { id := "farsi", name := "Farsi", glottocode := some "west2369" }

def kalaallisut : Language :=
  { id := "kalaallisut", name := "Kalaallisut", glottocode := some "kala1399" }

def basque : Language :=
  { id := "basque", name := "Basque", glottocode := some "basq1248" }

def chacobo : Language :=
  { id := "chacobo", name := "Chácobo", glottocode := some "chac1251" }

def eastern_oromo : Language :=
  { id := "eastern_oromo", name := "Eastern Oromo", glottocode := some "east2652" }

/-- The sample of languages investigated for the (reverse) HFF effects. The rows of Table 3, in the order of the source (alexeyenko-zeijlstra-2025, Table 3, p. 17). -/
def table3 : List Row := [
  { language := abkhaz,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := bulgarian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := polish,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := russian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := latin,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := lithuanian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := mandarin,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := modern_greek,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := statimcets,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := tagalog,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := armenian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := dutch,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := english,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := german,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := icelandic,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := estonian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := finnish,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := hungarian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := french,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := italian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := portuguese,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := romanian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := spanish,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := georgian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := serbo_croatian,
    adjectiveOrder := [⟨.adjectiveNoun, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := atong,
    adjectiveOrder := [⟨.nounAdjective, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := farsi,
    adjectiveOrder := [⟨.nounAdjective, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := kalaallisut,
    adjectiveOrder := [⟨.nounAdjective, false, false, false⟩],
    intervention := [⟨.possible, false, false, false⟩] },
  { language := basque,
    adjectiveOrder := [⟨.nounAdjective, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := chacobo,
    adjectiveOrder := [⟨.nounAdjective, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] },
  { language := eastern_oromo,
    adjectiveOrder := [⟨.nounAdjective, false, false, false⟩],
    intervention := [⟨.impossible, false, false, false⟩] }]

end AlexeyenkoZeijlstra2025.StructureDataset
