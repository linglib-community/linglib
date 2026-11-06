module

public import Linglib.Data.Examples.Schema

/-!
# `Haspelmath2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Haspelmath2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Haspelmath2001.Examples`.
-/

@[expose] public section

namespace Haspelmath2001.Examples

def articles_en : Datum :=
  { id := "haspelmath2001_articles_en"
    source := ⟨"haspelmath-2001", "§2.1"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "the book / a book"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "articles"), ("value", "sae")] }

def relpro_en : Datum :=
  { id := "haspelmath2001_relpro_en"
    source := ⟨"haspelmath-2001", "§2.2"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "the suspicious woman whom I described"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativePronouns"), ("value", "sae")] }

def relparticle_en : Datum :=
  { id := "haspelmath2001_relparticle_en"
    source := ⟨"haspelmath-2001", "§2.2"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "the radio that I bought"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativePronouns"), ("value", "particle")] }

def haveperf_en : Datum :=
  { id := "haspelmath2001_haveperf_en"
    source := ⟨"haspelmath-2001", "§2.3"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "I have written"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "havePerfect"), ("value", "sae")] }

def haveperf_sv : Datum :=
  { id := "haspelmath2001_haveperf_sv"
    source := ⟨"haspelmath-2001", "§2.3"⟩
    reportedIn := none
    method := some .description
    language := "swed1254"
    primaryText := "jag har skrivit"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "havePerfect"), ("value", "sae")] }

def haveperf_es : Datum :=
  { id := "haspelmath2001_haveperf_es"
    source := ⟨"haspelmath-2001", "§2.3"⟩
    reportedIn := none
    method := some .description
    language := "stan1288"
    primaryText := "he escrito"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "havePerfect"), ("value", "sae")] }

def perf_fi : Datum :=
  { id := "haspelmath2001_perf_fi"
    source := ⟨"haspelmath-2001", "§2.3"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "ole-n saa-nut"
    glossedTokens := [("ole-n", "be-1SG"), ("saa-nut", "receive-PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "havePerfect"), ("value", "participialCopula")] }

def perf_cy : Datum :=
  { id := "haspelmath2001_perf_cy"
    source := ⟨"haspelmath-2001", "§2.3"⟩
    reportedIn := none
    method := some .description
    language := "wels1247"
    primaryText := "wedi"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "havePerfect"), ("value", "prepositional")] }

def nomexp_en : Datum :=
  { id := "haspelmath2001_nomexp_en"
    source := ⟨"haspelmath-2001", "§2.4"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "I like it"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "nominativeExperiencers"), ("value", "generalizing")] }

def invexp_en : Datum :=
  { id := "haspelmath2001_invexp_en"
    source := ⟨"haspelmath-2001", "§2.4"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "It pleases me"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "nominativeExperiencers"), ("value", "inverting")] }

def getpass_cy : Datum :=
  { id := "haspelmath2001_getpass_cy"
    source := ⟨"haspelmath-2001", "§2.5"⟩
    reportedIn := none
    method := some .description
    language := "wels1247"
    primaryText := "Terry got his hitting by a snowball"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "participialPassive"), ("value", "getPassive")] }

def caus_mn : Datum :=
  { id := "haspelmath2001_caus_mn"
    source := ⟨"haspelmath-2001", "§2.6"⟩
    reportedIn := none
    method := some .description
    language := "halh1238"
    primaryText := "xajl-uul-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "anticausativeProminence"), ("value", "causative")] }

def anticaus_ru : Datum :=
  { id := "haspelmath2001_anticaus_ru"
    source := ⟨"haspelmath-2001", "§2.6"⟩
    reportedIn := none
    method := some .description
    language := "russ1263"
    primaryText := "izmenit'-sja"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "anticausativeProminence"), ("value", "anticausative")] }

def datposs_de : Datum :=
  { id := "haspelmath2001_datposs_de"
    source := ⟨"haspelmath-2001", "§2.7"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "Die Mutter wäscht dem Kind die Haare."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "dativeExternalPossessors"), ("value", "dative")] }

def locposs_sv : Datum :=
  { id := "haspelmath2001_locposs_sv"
    source := ⟨"haspelmath-2001", "§2.7"⟩
    reportedIn := none
    method := some .description
    language := "swed1254"
    primaryText := "Någon bröt armen på honom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "dativeExternalPossessors"), ("value", "locative")] }

def vni_de : Datum :=
  { id := "haspelmath2001_vni_de"
    source := ⟨"haspelmath-2001", "§2.8"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "Niemand kommt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "negativeIndefinitesWithoutVerbalNegation"), ("value", "sae")] }

def nvni_el : Datum :=
  { id := "haspelmath2001_nvni_el"
    source := ⟨"haspelmath-2001", "§2.8"⟩
    reportedIn := none
    method := some .description
    language := "mode1248"
    primaryText := "Kanénas dhen érxete."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "negativeIndefinitesWithoutVerbalNegation"), ("value", "negatedVerb")] }

def mixed_it_pre : Datum :=
  { id := "haspelmath2001_mixed_it_pre"
    source := ⟨"haspelmath-2001", "§2.8"⟩
    reportedIn := none
    method := some .description
    language := "ital1282"
    primaryText := "Nessuno viene."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "negativeIndefinitesWithoutVerbalNegation"), ("value", "mixed")] }

def mixed_it_post : Datum :=
  { id := "haspelmath2001_mixed_it_post"
    source := ⟨"haspelmath-2001", "§2.8"⟩
    reportedIn := none
    method := some .description
    language := "ital1282"
    primaryText := "Non ho visto nessuno."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "negativeIndefinitesWithoutVerbalNegation"), ("value", "mixed")] }

def equative_ca : Datum :=
  { id := "haspelmath2001_equative_ca"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "stan1289"
    primaryText := "tan Z com X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_pt : Datum :=
  { id := "haspelmath2001_equative_pt"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "port1283"
    primaryText := "tão Z como X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_de : Datum :=
  { id := "haspelmath2001_equative_de"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "so Z wie X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_ru : Datum :=
  { id := "haspelmath2001_equative_ru"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "russ1263"
    primaryText := "tak(oj) že Z kak X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_hu : Datum :=
  { id := "haspelmath2001_equative_hu"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "hung1274"
    primaryText := "olyan Z mint X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_fi : Datum :=
  { id := "haspelmath2001_equative_fi"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "finn1318"
    primaryText := "niin Z kuin X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_ka : Datum :=
  { id := "haspelmath2001_equative_ka"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "nucl1302"
    primaryText := "isetive Z rogorc X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_bg : Datum :=
  { id := "haspelmath2001_equative_bg"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "bulg1262"
    primaryText := "xubava kato tebe"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "sae")] }

def equative_ga : Datum :=
  { id := "haspelmath2001_equative_ga"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "iris1253"
    primaryText := "chomh Z le X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "special")] }

def equative_sv : Datum :=
  { id := "haspelmath2001_equative_sv"
    source := ⟨"haspelmath-2001", "§2.10"⟩
    reportedIn := none
    method := some .description
    language := "swed1254"
    primaryText := "lika Z som X"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "relativeBasedEquative"), ("value", "equally")] }

def agr_bg : Datum :=
  { id := "haspelmath2001_agr_bg"
    source := ⟨"haspelmath-2001", "§2.11"⟩
    reportedIn := none
    method := some .description
    language := "bulg1262"
    primaryText := "vie rabotite / rabotite"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "strictAgreement"), ("value", "referential")] }

def agr_de : Datum :=
  { id := "haspelmath2001_agr_de"
    source := ⟨"haspelmath-2001", "§2.11"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "ihr arbeit-et"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "strictAgreement"), ("value", "sae")] }

def nopro_sv : Datum :=
  { id := "haspelmath2001_nopro_sv"
    source := ⟨"haspelmath-2001", "§2.11"⟩
    reportedIn := none
    method := some .description
    language := "swed1254"
    primaryText := "jag biter / du biter / han biter"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "strictAgreement"), ("value", "obligatoryPronouns")] }

def intref_de : Datum :=
  { id := "haspelmath2001_intref_de"
    source := ⟨"haspelmath-2001", "§2.12"⟩
    reportedIn := none
    method := some .description
    language := "stan1295"
    primaryText := "sich / selbst"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "intensifierReflexiveDifferentiation"), ("value", "sae")] }

def intref_ru : Datum :=
  { id := "haspelmath2001_intref_ru"
    source := ⟨"haspelmath-2001", "§2.12"⟩
    reportedIn := none
    method := some .description
    language := "russ1263"
    primaryText := "sebja / sam"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "intensifierReflexiveDifferentiation"), ("value", "sae")] }

def intref_it : Datum :=
  { id := "haspelmath2001_intref_it"
    source := ⟨"haspelmath-2001", "§2.12"⟩
    reportedIn := none
    method := some .description
    language := "ital1282"
    primaryText := "si / stesso"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "intensifierReflexiveDifferentiation"), ("value", "sae")] }

def intref_el : Datum :=
  { id := "haspelmath2001_intref_el"
    source := ⟨"haspelmath-2001", "§2.12"⟩
    reportedIn := none
    method := some .description
    language := "mode1248"
    primaryText := "eaftó / ídhjos"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "intensifierReflexiveDifferentiation"), ("value", "sae")] }

def intref_fa : Datum :=
  { id := "haspelmath2001_intref_fa"
    source := ⟨"haspelmath-2001", "§2.12"⟩
    reportedIn := none
    method := some .description
    language := "west2369"
    primaryText := "Hušang xodaš-rā did"
    glossedTokens := [("Hušang", "Hushang"), ("xodaš-rā", "self-ACC"), ("did", "saw")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "intensifierReflexiveDifferentiation"), ("value", "undifferentiated")] }

def comparative_ja : Datum :=
  { id := "haspelmath2001_comparative_ja"
    source := ⟨"haspelmath-2001", "§3.2"⟩
    reportedIn := none
    method := some .description
    language := "nucl1643"
    primaryText := "inu-ga neko yori ookii"
    glossedTokens := [("inu-ga", "dog-SUBJ"), ("neko", "cat"), ("yori", "from"), ("ookii", "big")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "comparativeMarking"), ("value", "standardMarkerOnly")] }

def with_en : Datum :=
  { id := "haspelmath2001_with_en"
    source := ⟨"haspelmath-2001", "§3.4"⟩
    reportedIn := none
    method := some .description
    language := "stan1293"
    primaryText := "with her husband / with the hammer"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "comitativeInstrumentalSyncretism"), ("value", "sae")] }

def negcoord_nl : Datum :=
  { id := "haspelmath2001_negcoord_nl"
    source := ⟨"haspelmath-2001", "§3.6"⟩
    reportedIn := none
    method := some .description
    language := "dutc1256"
    primaryText := "noch A noch B"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("feature", "negativeCoordination"), ("value", "sae")] }

def all : List Datum := [articles_en, relpro_en, relparticle_en, haveperf_en, haveperf_sv, haveperf_es, perf_fi, perf_cy, nomexp_en, invexp_en, getpass_cy, caus_mn, anticaus_ru, datposs_de, locposs_sv, vni_de, nvni_el, mixed_it_pre, mixed_it_post, equative_ca, equative_pt, equative_de, equative_ru, equative_hu, equative_fi, equative_ka, equative_bg, equative_ga, equative_sv, agr_bg, agr_de, nopro_sv, intref_de, intref_ru, intref_it, intref_el, intref_fa, comparative_ja, with_en, negcoord_nl]

end Haspelmath2001.Examples
