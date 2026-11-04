module

public import Linglib.Data.Statistics.Schema
public import Linglib.Data.StructureDataset.Schema

/-!
# `Haspelmath2001`: language samples

Auto-generated from `Linglib/Data/StructureDataset/Haspelmath2001.json` by
`scripts/gen_structure_dataset.py`. Do not edit by hand; edit the JSON and re-run the generator.
Declarations live in `namespace Haspelmath2001.StructureDataset`.
-/

@[expose] public section

namespace Haspelmath2001.StructureDataset

open CLDF.StructureDataset

/-- branch: The genealogical groups the criteria of section 1 reason with, by the textbook classification; the chapter names most of them on p. 1493. -/
inductive Branch where
  /-- `Romance`: Romance -/
  | romance
  /-- `Germanic`: Germanic -/
  | germanic
  /-- `Slavic`: Slavic -/
  | slavic
  /-- `Baltic`: Baltic -/
  | baltic
  /-- `Greek`: Greek -/
  | greek
  /-- `Albanian`: Albanian -/
  | albanian
  /-- `western Uralic`: western Uralic -/
  | westernUralic
  /-- `Celtic`: Celtic -/
  | celtic
  /-- `Basque`: Basque -/
  | basque
  /-- `Turkic`: Turkic -/
  | turkic
  /-- `eastern Uralic`: eastern Uralic -/
  | easternUralic
  /-- `Kartvelian`: Kartvelian -/
  | kartvelian
  /-- `Nakh-Daghestanian`: Nakh-Daghestanian -/
  | nakhDaghestanian
  /-- `Abkhaz-Adyghean`: Abkhaz-Adyghean -/
  | abkhazAdyghean
  /-- `Afro-Asiatic`: Afro-Asiatic -/
  | afroAsiatic
  /-- `Armenian`: Armenian -/
  | armenian
  /-- `Latin`: Latin -/
  | latin
  /-- `Iranian`: Iranian -/
  | iranian
  /-- `Indic`: Indic -/
  | indic
  deriving DecidableEq, Repr

/-- definite and indefinite articles: The legend of Map 107.1, p. 1494. -/
inductive Articles where
  /-- `definite and indefinite article present`: Inside the solid line. -/
  | both
  /-- `only definite article present`: Between the solid and the dashed line. -/
  | definiteOnly
  /-- `no line`: Outside both lines. -/
  | neither
  deriving DecidableEq, Repr

/-- relative clauses: The legend of Map 107.2, p. 1494. -/
inductive RelativeClause where
  /-- `relative clause with introducing relative pronoun`: Inside the solid line. -/
  | relativePronoun
  /-- `only particle relative clause`: Inside the dotted line. -/
  | particleOnly
  /-- `no line`: Outside both lines. -/
  | other
  deriving DecidableEq, Repr

/-- have-perfect: Map 107.3, p. 1495. -/
inductive HavePerfect where
  /-- `have-perfect`: Inside the line. -/
  | havePerfect
  /-- `no line`: Outside the line. -/
  | other
  deriving DecidableEq, Repr

/-- experiencers: Map 107.4, p. 1496. -/
inductive Experiencer where
  /-- `predominant generalization`: Inside the line. -/
  | generalizing
  /-- `predominant inversion`: Outside the line. -/
  | inverting
  deriving DecidableEq, Repr

/-- participial passive: Map 107.5, p. 1496. -/
inductive ParticipialPassive where
  /-- `participial passive`: Inside the line. -/
  | participial
  /-- `no line`: Outside the line. -/
  | other
  deriving DecidableEq, Repr

/-- anticausative pairs: The legend of Map 107.6, p. 1497. -/
inductive Anticausative where
  /-- `70-100 % anticausatives`: Inside the solid line. -/
  | high
  /-- `50-70 % anticausatives`: Inside the dashed line. -/
  | mid
  /-- `no line`: Outside both lines. -/
  | low
  deriving DecidableEq, Repr

/-- external possessors: Map 107.7, p. 1498. -/
inductive ExternalPossessor where
  /-- `dative external possessor`: Inside the line. -/
  | dative
  /-- `no line`: Outside the line. -/
  | other
  deriving DecidableEq, Repr

/-- negative indefinites: Map 107.8, p. 1498. -/
inductive NegativeIndefinite where
  /-- `V + NI`: Inside a line: no verbal negation with a negative indefinite. -/
  | withoutVerbalNegation
  /-- `NV + NI`: Outside the lines. -/
  | withVerbalNegation
  deriving DecidableEq, Repr

/-- comparatives: The legend of Map 107.9, p. 1499. -/
inductive ComparativeType where
  /-- `particle comparative`: Inside the solid line. -/
  | particle
  /-- `locative comparative`: Inside a dotted line. -/
  | locative
  deriving DecidableEq, Repr

/-- equatives: Map 107.10, p. 1500. -/
inductive Equative where
  /-- `relative-based equative`: Inside the line. -/
  | relativeBased
  /-- `no line`: Outside the line. -/
  | other
  deriving DecidableEq, Repr

/-- subject agreement: The legend of Map 107.11, p. 1500. -/
inductive SubjectAgreement where
  /-- `languages with strict subject agreement`: Inside a solid line. -/
  | strict
  /-- `languages with obligatory subject pronouns, lacking verb agreement`: Inside a dotted line. -/
  | obligatoryPronouns
  /-- `no line`: Outside the lines. -/
  | other
  deriving DecidableEq, Repr

/-- intensifiers and reflexives: Map 107.12, p. 1501. -/
inductive IntensifierReflexive where
  /-- `intensifier-reflexive differentiation`: Inside the line. -/
  | differentiated
  /-- `no line`: Outside the line. -/
  | other
  deriving DecidableEq, Repr

/-- A row of a sample: a language with its codes for each parameter. -/
structure Row where
  /-- The language. -/
  language : Language
  /-- The codes for branch. -/
  branch : List (Coded Branch)
  /-- The codes for definite and indefinite articles. -/
  articles : List (Coded Articles)
  /-- The codes for relative clauses. -/
  relativeClause : List (Coded RelativeClause)
  /-- The codes for have-perfect. -/
  havePerfect : List (Coded HavePerfect)
  /-- The codes for experiencers. -/
  experiencer : List (Coded Experiencer)
  /-- The codes for participial passive. -/
  participialPassive : List (Coded ParticipialPassive)
  /-- The codes for anticausative pairs. -/
  anticausative : List (Coded Anticausative)
  /-- The codes for external possessors. -/
  externalPossessor : List (Coded ExternalPossessor)
  /-- The codes for negative indefinites. -/
  negativeIndefinite : List (Coded NegativeIndefinite)
  /-- The codes for comparatives. -/
  comparativeType : List (Coded ComparativeType)
  /-- The codes for equatives. -/
  equative : List (Coded Equative)
  /-- The codes for subject agreement. -/
  subjectAgreement : List (Coded SubjectAgreement)
  /-- The codes for intensifiers and reflexives. -/
  intensifierReflexive : List (Coded IntensifierReflexive)
  /-- The codes for experiencer ratio. -/
  experiencerRatio : List (Coded Data.Statistics.Decimal)
  /-- The codes for anticausative percentage. -/
  anticausativePercent : List (Coded Data.Statistics.Decimal)
  /-- The codes for printed score. -/
  printedScore : List (Coded Data.Statistics.Decimal)
  deriving DecidableEq, Repr

def albanian : Language :=
  { id := "albanian", name := "Albanian", glottocode := some "alba1267" }

def armenian : Language :=
  { id := "armenian", name := "Armenian", glottocode := some "arme1241" }

def basque : Language :=
  { id := "basque", name := "Basque", glottocode := some "basq1248" }

def breton : Language :=
  { id := "breton", name := "Breton", glottocode := some "bret1244" }

def bulgarian : Language :=
  { id := "bulgarian", name := "Bulgarian", glottocode := some "bulg1262" }

def czech : Language :=
  { id := "czech", name := "Czech", glottocode := some "czec1258" }

def dutch : Language :=
  { id := "dutch", name := "Dutch", glottocode := some "dutc1256" }

def english : Language :=
  { id := "english", name := "English", glottocode := some "stan1293" }

def estonian : Language :=
  { id := "estonian", name := "Estonian", glottocode := some "esto1258" }

def finnish : Language :=
  { id := "finnish", name := "Finnish", glottocode := some "finn1318" }

def french : Language :=
  { id := "french", name := "French", glottocode := some "stan1290" }

def gaelic : Language :=
  { id := "gaelic", name := "Scots Gaelic", glottocode := some "scot1245" }

def georgian : Language :=
  { id := "georgian", name := "Georgian", glottocode := some "nucl1302" }

def german : Language :=
  { id := "german", name := "German", glottocode := some "stan1295" }

def greek : Language :=
  { id := "greek", name := "Greek", glottocode := some "mode1248" }

def hungarian : Language :=
  { id := "hungarian", name := "Hungarian", glottocode := some "hung1274" }

def icelandic : Language :=
  { id := "icelandic", name := "Icelandic", glottocode := some "icel1247" }

def irish : Language :=
  { id := "irish", name := "Irish", glottocode := some "iris1253" }

def italian : Language :=
  { id := "italian", name := "Italian", glottocode := some "ital1282" }

def komi : Language :=
  { id := "komi", name := "Komi", glottocode := some "komi1267" }

def latin : Language :=
  { id := "latin", name := "Latin", glottocode := some "lati1261" }

def latvian : Language :=
  { id := "latvian", name := "Latvian", glottocode := some "latv1249" }

def laz : Language :=
  { id := "laz", name := "Laz", glottocode := some "lazz1240" }

def lezgian : Language :=
  { id := "lezgian", name := "Lezgian", glottocode := some "lezg1247" }

def lithuanian : Language :=
  { id := "lithuanian", name := "Lithuanian", glottocode := some "lith1251" }

def maltese : Language :=
  { id := "maltese", name := "Maltese", glottocode := some "malt1254" }

def mari : Language :=
  { id := "mari", name := "Mari", glottocode := some "mari1278" }

def mordvin : Language :=
  { id := "mordvin", name := "Mordvin", glottocode := some "mord1256" }

def nenets : Language :=
  { id := "nenets", name := "Nenets", glottocode := some "nene1251" }

def norwegian : Language :=
  { id := "norwegian", name := "Norwegian", glottocode := some "norw1258" }

def polish : Language :=
  { id := "polish", name := "Polish", glottocode := some "poli1260" }

def portuguese : Language :=
  { id := "portuguese", name := "Portuguese", glottocode := some "port1283" }

def romanian : Language :=
  { id := "romanian", name := "Romanian", glottocode := some "roma1327" }

def russian : Language :=
  { id := "russian", name := "Russian", glottocode := some "russ1263" }

def saami : Language :=
  { id := "saami", name := "Saami", glottocode := some "saam1281" }

def sardinian : Language :=
  { id := "sardinian", name := "Sardinian", glottocode := none }

def serbo_croatian : Language :=
  { id := "serbo_croatian", name := "Serbian/Croatian", glottocode := some "sout1528" }

def slovene : Language :=
  { id := "slovene", name := "Slovene", glottocode := some "slov1268" }

def spanish : Language :=
  { id := "spanish", name := "Spanish", glottocode := some "stan1288" }

def swedish : Language :=
  { id := "swedish", name := "Swedish", glottocode := some "swed1254" }

def tatar : Language :=
  { id := "tatar", name := "Tatar", glottocode := some "tata1255" }

def turkish : Language :=
  { id := "turkish", name := "Turkish", glottocode := some "nucl1301" }

def ubykh : Language :=
  { id := "ubykh", name := "Ubykh", glottocode := some "ubyk1235" }

def udmurt : Language :=
  { id := "udmurt", name := "Udmurt", glottocode := some "udmu1245" }

def ukrainian : Language :=
  { id := "ukrainian", name := "Ukrainian", glottocode := some "ukra1253" }

def welsh : Language :=
  { id := "welsh", name := "Welsh", glottocode := some "wels1247" }

def iranian : Language :=
  { id := "iranian", name := "Iranian", glottocode := some "iran1269" }

def indic : Language :=
  { id := "indic", name := "Indic", glottocode := some "indo1321" }

def persian : Language :=
  { id := "persian", name := "Persian", glottocode := some "west2369" }

def kurdish : Language :=
  { id := "kurdish", name := "Kurdish", glottocode := some "kurd1259" }

def baluchi : Language :=
  { id := "baluchi", name := "Baluchi", glottocode := some "balo1260" }

def hindi_urdu : Language :=
  { id := "hindi_urdu", name := "Hindi/Urdu", glottocode := some "hind1270" }

def maithili : Language :=
  { id := "maithili", name := "Maithili", glottocode := some "mait1250" }

def punjabi : Language :=
  { id := "punjabi", name := "Punjabi", glottocode := some "panj1256" }

/-- The languages of the name maps and the side of each line they lie on. The rows of Maps 107.1-107.13, in the order of the source (haspelmath-2001, Maps 107.1-107.13, pp. 1494-1505). -/
def maps : List Row := [
  { language := albanian,
    branch := [⟨.albanian, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨102, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨8, 0⟩, false, false, false⟩] },
  { language := armenian,
    branch := [⟨.armenian, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [⟨.mid, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [⟨⟨65, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨1, 0⟩, false, false, false⟩] },
  { language := basque,
    branch := [⟨.basque, false, false, false⟩],
    articles := [⟨.definiteOnly, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨010, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨2, 0⟩, false, false, false⟩] },
  { language := breton,
    branch := [⟨.celtic, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.particleOnly, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.locative, false, false, false⟩],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨024, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨2, 0⟩, false, false, false⟩] },
  { language := bulgarian,
    branch := [⟨.slavic, false, false, false⟩],
    articles := [⟨.definiteOnly, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨048, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := czech,
    branch := [⟨.slavic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨076, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨6, 0⟩, false, false, false⟩] },
  { language := dutch,
    branch := [⟨.germanic, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.strict, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨064, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨8, 0⟩, false, false, false⟩] },
  { language := english,
    branch := [⟨.germanic, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.high, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.strict, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨00, 1⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨100, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨7, 0⟩, false, false, false⟩] },
  { language := estonian,
    branch := [⟨.westernUralic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨083, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [] },
  { language := finnish,
    branch := [⟨.westernUralic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [⟨.low, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨087, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨47, 0⟩, false, false, false⟩],
    printedScore := [] },
  { language := french,
    branch := [⟨.romance, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.high, false, false, false⟩],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.strict, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨012, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨91, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨9, 0⟩, false, false, false⟩] },
  { language := gaelic,
    branch := [⟨.celtic, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := georgian,
    branch := [⟨.kartvelian, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [⟨.mid, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨308, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨67, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨1, 0⟩, false, false, false⟩] },
  { language := german,
    branch := [⟨.germanic, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.high, false, false, false⟩],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.strict, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨074, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨100, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨9, 0⟩, false, false, false⟩] },
  { language := greek,
    branch := [⟨.greek, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.high, false, false, false⟩],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨027, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨100, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨7, 0⟩, false, false, false⟩] },
  { language := hungarian,
    branch := [⟨.westernUralic, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.low, false, false, false⟩],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨022, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨44, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := icelandic,
    branch := [⟨.germanic, false, false, false⟩],
    articles := [⟨.definiteOnly, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.strict, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨229, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨6, 0⟩, false, false, false⟩] },
  { language := irish,
    branch := [⟨.celtic, false, false, false⟩],
    articles := [⟨.definiteOnly, false, false, false⟩],
    relativeClause := [⟨.particleOnly, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨221, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [] },
  { language := italian,
    branch := [⟨.romance, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨048, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨8, 0⟩, false, false, false⟩] },
  { language := komi,
    branch := [⟨.easternUralic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := latin,
    branch := [⟨.latin, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := latvian,
    branch := [⟨.baltic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨164, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := laz,
    branch := [⟨.kartvelian, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [⟨.locative, false, false, false⟩],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := lezgian,
    branch := [⟨.nakhDaghestanian, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [⟨.low, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.obligatoryPronouns, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨50, 1⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨40, 0⟩, false, false, false⟩],
    printedScore := [] },
  { language := lithuanian,
    branch := [⟨.baltic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.high, false, false, false⟩],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨083, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨74, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := maltese,
    branch := [⟨.afroAsiatic, false, false, false⟩],
    articles := [⟨.definiteOnly, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨069, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨2, 0⟩, false, false, false⟩] },
  { language := mari,
    branch := [⟨.easternUralic, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [⟨⟨079, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [] },
  { language := mordvin,
    branch := [⟨.easternUralic, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [⟨⟨116, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [] },
  { language := nenets,
    branch := [⟨.easternUralic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.locative, false, false, false⟩],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := norwegian,
    branch := [⟨.germanic, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.obligatoryPronouns, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨012, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨6, 0⟩, false, false, false⟩] },
  { language := polish,
    branch := [⟨.slavic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨088, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := portuguese,
    branch := [⟨.romance, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨014, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨8, 0⟩, false, false, false⟩] },
  { language := romanian,
    branch := [⟨.romance, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.high, false, false, false⟩],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨225, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨96, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨7, 0⟩, false, false, false⟩] },
  { language := russian,
    branch := [⟨.slavic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [⟨.high, false, false, false⟩],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.particle, false, false, false⟩],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.strict, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨211, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨100, 0⟩, false, false, false⟩],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := saami,
    branch := [⟨.easternUralic, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [⟨⟨081, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [] },
  { language := sardinian,
    branch := [⟨.romance, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [⟨⟨8, 0⟩, false, false, false⟩] },
  { language := serbo_croatian,
    branch := [⟨.slavic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨075, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := slovene,
    branch := [⟨.slavic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := spanish,
    branch := [⟨.romance, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨043, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨8, 0⟩, false, false, false⟩] },
  { language := swedish,
    branch := [⟨.germanic, false, false, false⟩],
    articles := [⟨.both, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.havePerfect, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withoutVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.obligatoryPronouns, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [⟨⟨012, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨6, 0⟩, false, false, false⟩] },
  { language := tatar,
    branch := [⟨.turkic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := turkish,
    branch := [⟨.turkic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.generalizing, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [⟨.low, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [⟨.locative, false, false, false⟩],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨046, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨34, 0⟩, false, false, false⟩],
    printedScore := [] },
  { language := ubykh,
    branch := [⟨.abkhazAdyghean, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [⟨.locative, false, false, false⟩],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := udmurt,
    branch := [⟨.easternUralic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [⟨.low, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨109, 2⟩, false, false, false⟩],
    anticausativePercent := [⟨⟨46, 0⟩, false, false, false⟩],
    printedScore := [] },
  { language := ukrainian,
    branch := [⟨.slavic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.relativePronoun, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.dative, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [⟨.other, false, false, false⟩],
    intensifierReflexive := [⟨.differentiated, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [⟨⟨5, 0⟩, false, false, false⟩] },
  { language := welsh,
    branch := [⟨.celtic, false, false, false⟩],
    articles := [⟨.definiteOnly, false, false, false⟩],
    relativeClause := [⟨.particleOnly, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [⟨.other, false, false, false⟩],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [⟨.strict, false, false, false⟩],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [⟨⟨092, 2⟩, false, false, false⟩],
    anticausativePercent := [],
    printedScore := [⟨⟨1, 0⟩, false, false, false⟩] }]

/-- What the prose of section 2 reports of the eastern Indo-European languages, which the maps do not cover but for Armenian. The rows of section 2, in the order of the source (haspelmath-2001, section 2, pp. 1494-1501). -/
def prose : List Row := [
  { language := iranian,
    branch := [⟨.iranian, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := indic,
    branch := [⟨.indic, false, false, false⟩],
    articles := [⟨.neither, false, false, false⟩],
    relativeClause := [⟨.other, false, false, false⟩],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [⟨.inverting, false, false, false⟩],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [⟨.withVerbalNegation, false, false, false⟩],
    comparativeType := [],
    equative := [⟨.other, false, false, false⟩],
    subjectAgreement := [],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := persian,
    branch := [⟨.iranian, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := kurdish,
    branch := [⟨.iranian, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := baluchi,
    branch := [⟨.iranian, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := hindi_urdu,
    branch := [⟨.indic, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [⟨.other, false, false, false⟩],
    experiencer := [],
    participialPassive := [],
    anticausative := [⟨.low, false, false, false⟩],
    externalPossessor := [⟨.other, false, false, false⟩],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [⟨.other, false, false, false⟩],
    experiencerRatio := [],
    anticausativePercent := [⟨⟨35, 0⟩, false, false, false⟩],
    printedScore := [] },
  { language := maithili,
    branch := [⟨.indic, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [⟨.participial, false, false, false⟩],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] },
  { language := punjabi,
    branch := [⟨.indic, false, false, false⟩],
    articles := [],
    relativeClause := [],
    havePerfect := [],
    experiencer := [],
    participialPassive := [],
    anticausative := [],
    externalPossessor := [],
    negativeIndefinite := [],
    comparativeType := [],
    equative := [⟨.relativeBased, false, false, false⟩],
    subjectAgreement := [],
    intensifierReflexive := [],
    experiencerRatio := [],
    anticausativePercent := [],
    printedScore := [] }]

end Haspelmath2001.StructureDataset
