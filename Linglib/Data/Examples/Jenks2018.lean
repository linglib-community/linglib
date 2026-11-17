module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Jenks2018` — typed example data

Auto-generated from `Linglib/Data/Examples/Jenks2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jenks2018.Examples`.
-/

@[expose] public section

namespace Jenks2018.Examples

def ex_10a : Datum :=
  { id := "jenks2018_10a"
    source := ⟨"chen-2004", "p. 1165"⟩
    reportedIn := some ⟨"jenks-2018", "(10a)"⟩
    language := "mand1415"
    primaryText := "Yueliang sheng shang lai le."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("position", "subject"), ("form", "bare")] }

def ex_10b_bare : Datum :=
  { id := "jenks2018_10b_bare"
    source := ⟨"jenks-2018", "(10b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Taiwan (de) zongtong hen shengqi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("position", "subject"), ("form", "bare")] }

def ex_10b_dem : Datum :=
  { id := "jenks2018_10b_dem"
    source := ⟨"jenks-2018", "(10b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na/Zhe ge Taiwan (de) zongtong hen shengqi."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("position", "subject"), ("form", "demonstrative")] }

def ex_11a : Datum :=
  { id := "jenks2018_11a"
    source := ⟨"cheng-sybesma-1999", ""⟩
    reportedIn := some ⟨"jenks-2018", "(11a)"⟩
    language := "mand1415"
    primaryText := "Hufei he-wan-le tang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "immediateSituation"), ("position", "object"), ("form", "bare")] }

def ex_11b : Datum :=
  { id := "jenks2018_11b"
    source := ⟨"cheng-sybesma-1999", "p. 510"⟩
    reportedIn := some ⟨"jenks-2018", "(11b)"⟩
    language := "mand1415"
    primaryText := "Gou yao guo malu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "immediateSituation"), ("position", "subject"), ("form", "bare")] }

def ex_14a : Datum :=
  { id := "jenks2018_14a"
    source := ⟨"jenks-2018", "(14a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Chezi bei jingcha lanjie le yinwei mei you tiezhi zai paizhao shang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "partWholeBridging"), ("position", "object"), ("form", "bare")] }

def ex_14b_bare : Datum :=
  { id := "jenks2018_14b_bare"
    source := ⟨"jenks-2018", "(14b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Paul renwei na shou shi hen youmei, jishi ta bu renshi shiren."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "producerBridging"), ("position", "object"), ("form", "bare")] }

def ex_14b_dem : Datum :=
  { id := "jenks2018_14b_dem"
    source := ⟨"jenks-2018", "(14b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Paul renwei na shou shi hen youmei, jishi ta bu renshi na wei shiren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "producerBridging"), ("position", "object"), ("form", "demonstrative")] }

def ex_15b_bare : Datum :=
  { id := "jenks2018_15b_bare"
    source := ⟨"jenks-2018", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo zuotian yudao nansheng."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "object"), ("form", "bare")] }

def ex_15b_dem : Datum :=
  { id := "jenks2018_15b_dem"
    source := ⟨"jenks-2018", "(15b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo zuotian yudao na ge nansheng."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "object"), ("form", "demonstrative")] }

def ex_15c_bare : Datum :=
  { id := "jenks2018_15c_bare"
    source := ⟨"jenks-2018", "(15c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo dai gei nansheng yi ge liwu."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "indirectObject"), ("form", "bare")] }

def ex_15c_dem : Datum :=
  { id := "jenks2018_15c_dem"
    source := ⟨"jenks-2018", "(15c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo dai gei na ge nansheng yi ge liwu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "indirectObject"), ("form", "demonstrative")] }

def ex_15d_bare : Datum :=
  { id := "jenks2018_15d_bare"
    source := ⟨"jenks-2018", "(15d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Nansheng kanqilai you er-shi sui zuoyou."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "subject"), ("form", "bare"), ("topic", "continuing")] }

def ex_15d_dem : Datum :=
  { id := "jenks2018_15d_dem"
    source := ⟨"jenks-2018", "(15d)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na ge nansheng kanqilai you er-shi sui zuoyou."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "subject"), ("form", "demonstrative"), ("topic", "continuing")] }

def ex_15e_bare : Datum :=
  { id := "jenks2018_15e_bare"
    source := ⟨"jenks-2018", "(15e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo bu renwei nansheng hen youqu."
    glossedTokens := []
    context := ""
    judgment := .marginal
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("form", "bare"), ("topic", "continuing")] }

def ex_15e_dem : Datum :=
  { id := "jenks2018_15e_dem"
    source := ⟨"jenks-2018", "(15e)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Wo bu renwei na ge nansheng hen youqu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("form", "demonstrative"), ("topic", "continuing")] }

def ex_16b : Datum :=
  { id := "jenks2018_16b"
    source := ⟨"jenks-2018", "(16b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Jingcha huaiyi na ge nuren nashihou shou le shang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("form", "demonstrative")] }

def ex_16c : Datum :=
  { id := "jenks2018_16c"
    source := ⟨"jenks-2018", "(16c)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Jingcha huaiyi nuren nashihou shou le shang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := [("definite", .unacceptable)]
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("form", "bare")] }

def ex_18b : Datum :=
  { id := "jenks2018_18b"
    source := ⟨"cheng-huang-1996", "p. 130, (22d)"⟩
    reportedIn := some ⟨"jenks-2018", "(18b)"⟩
    language := "mand1415"
    primaryText := "Ni jiao shei jinlai, wo dou jian na ge ren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object"), ("form", "demonstrative")] }

def ex_19 : Datum :=
  { id := "jenks2018_19"
    source := ⟨"jenks-2018", "(19)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ni jiao shei jinlai, wo dou jian ren."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object"), ("form", "bare")] }

def ex_20_bare : Datum :=
  { id := "jenks2018_20_bare"
    source := ⟨"jenks-2018", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge [you yi zhi shuiniu de] nongfu dou hui da shuiniu."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object"), ("form", "bare")] }

def ex_20_dem : Datum :=
  { id := "jenks2018_20_dem"
    source := ⟨"jenks-2018", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge [you yi zhi shuiniu de] nongfu dou hui da na zhi shuiniu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("position", "object"), ("form", "demonstrative")] }

def ex_28_bare : Datum :=
  { id := "jenks2018_28_bare"
    source := ⟨"jenks-2018", "(28)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Obama mei dao yi ge chengshi ta dou gen shizhang ji anmi an."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("environment", "largerSituation"), ("position", "object"), ("form", "bare")] }

def ex_28_dem : Datum :=
  { id := "jenks2018_28_dem"
    source := ⟨"jenks-2018", "(28)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Obama mei dao yi ge chengshi ta dou gen zhe wei shizhang ji anmi an."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "4.3"), ("environment", "largerSituation"), ("position", "object"), ("form", "demonstrative")] }

def ex_49_bare : Datum :=
  { id := "jenks2018_49_bare"
    source := ⟨"jenks-2018", "(49)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge mai le fangzi de ren dou xuyao xiuli wuding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("environment", "partWholeBridging"), ("position", "object"), ("form", "bare")] }

def ex_49_dem : Datum :=
  { id := "jenks2018_49_dem"
    source := ⟨"jenks-2018", "(49)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mei ge mai le fangzi de ren dou xuyao xiuli na ge wuding."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("environment", "partWholeBridging"), ("position", "object"), ("form", "demonstrative")] }

def ex_51B_bare : Datum :=
  { id := "jenks2018_51B_bare"
    source := ⟨"jenks-2018", "(51B)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Mao sha le (ta)."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "subject"), ("form", "bare"), ("topic", "nontopic")] }

def ex_51B_dem : Datum :=
  { id := "jenks2018_51B_dem"
    source := ⟨"jenks-2018", "(51B)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na zhi mao sha le (ta)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "subject"), ("form", "demonstrative"), ("topic", "nontopic")] }

def ex_51Bp_bare : Datum :=
  { id := "jenks2018_51Bp_bare"
    source := ⟨"jenks-2018", "(51B′)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ta bei mao sha le."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "object"), ("form", "bare"), ("topic", "nontopic")] }

def ex_51Bp_dem : Datum :=
  { id := "jenks2018_51Bp_dem"
    source := ⟨"jenks-2018", "(51B′)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Ta bei na zhi mao sha le."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "object"), ("form", "demonstrative"), ("topic", "nontopic")] }

def ex_52b_bare : Datum :=
  { id := "jenks2018_52b_bare"
    source := ⟨"jenks-2018", "(52b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Nansheng, wo hen bu xihuan."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "leftDislocated"), ("form", "bare"), ("topic", "new")] }

def ex_52b_dem : Datum :=
  { id := "jenks2018_52b_dem"
    source := ⟨"jenks-2018", "(52b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Na ge nansheng, wo hen bu xihuan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "leftDislocated"), ("form", "demonstrative"), ("topic", "new")] }

def ex_53 : Datum :=
  { id := "jenks2018_53"
    source := ⟨"jenks-2018", "(53)"⟩
    reportedIn := none
    method := some .elicitation
    language := "mand1415"
    primaryText := "Nansheng ne, wo hen bu xihuan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("position", "leftDislocated"), ("form", "bare"), ("topic", "continuing")] }

def ex_54a : Datum :=
  { id := "jenks2018_54a"
    source := ⟨"jenks-2018", "(54a)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Lou5baan2 haa6zau3 lei5 gim2caa4 gung1zok3."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_54b : Datum :=
  { id := "jenks2018_54b"
    source := ⟨"jenks-2018", "(54b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Zung2tung2 gam1maan5 baat3 dim2 soeng5 din6si6."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("position", "subject")] }

def ex_55b_clf : Datum :=
  { id := "jenks2018_55b_clf"
    source := ⟨"jenks-2018", "(55b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Keoi5 m4 jing6wai4 go3 zing3zi6gaa1 hou2 jau5ceoi3."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("form", "classifier")] }

def ex_55b_dem : Datum :=
  { id := "jenks2018_55b_dem"
    source := ⟨"jenks-2018", "(55b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Keoi5 m4 jing6wai4 go2 go3 zing3zi6gaa1 hou2 jau5ceoi3."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "anaphoric"), ("position", "embeddedSubject"), ("form", "demonstrative")] }

def ex_56 : Datum :=
  { id := "jenks2018_56"
    source := ⟨"jenks-2018", "(56)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Mui5 go3 jau5 jat1 zek3 maa5 ge3 nung4fu1 daa2 zek3 maa5."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "donkey"), ("position", "object"), ("form", "classifier")] }

def ex_59 : Datum :=
  { id := "jenks2018_59"
    source := ⟨"jenks-2018", "(59)"⟩
    reportedIn := none
    method := some .elicitation
    language := "cant1236"
    primaryText := "Hai2 Ou3baa1maa2 heoi3 gwo3 ge3 mui5 jat1 go3 sing4si5, keoi5 dou1 tung4 go3 si5zoeng2 gin3 gwo3 min6."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("position", "object"), ("form", "classifier")] }

def all : List Datum := [ex_10a, ex_10b_bare, ex_10b_dem, ex_11a, ex_11b, ex_14a, ex_14b_bare, ex_14b_dem, ex_15b_bare, ex_15b_dem, ex_15c_bare, ex_15c_dem, ex_15d_bare, ex_15d_dem, ex_15e_bare, ex_15e_dem, ex_16b, ex_16c, ex_18b, ex_19, ex_20_bare, ex_20_dem, ex_28_bare, ex_28_dem, ex_49_bare, ex_49_dem, ex_51B_bare, ex_51B_dem, ex_51Bp_bare, ex_51Bp_dem, ex_52b_bare, ex_52b_dem, ex_53, ex_54a, ex_54b, ex_55b_clf, ex_55b_dem, ex_56, ex_59]

/-- The definite environments the paper tests. -/
inductive Environment where
  /-- largerSituation: a larger-situation definite, unique by world knowledge -/
  | largerSituation
  /-- immediateSituation: an immediate-situation definite, unique in the utterance context -/
  | immediateSituation
  /-- partWholeBridging: a definite bridged to an antecedent that contains its referent -/
  | partWholeBridging
  /-- producerBridging: a definite bridged to the product of its referent -/
  | producerBridging
  /-- anaphoric: a definite anaphoric to an antecedent in a narrative sequence -/
  | anaphoric
  /-- donkey: a definite covarying with an indefinite that does not c-command it -/
  | donkey
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `environment`. -/
def environment (e : Datum) : Option Environment :=
  e.parse? "environment" [("largerSituation", .largerSituation), ("immediateSituation", .immediateSituation),
    ("partWholeBridging", .partWholeBridging), ("producerBridging", .producerBridging),
    ("anaphoric", .anaphoric), ("donkey", .donkey)]

/-- The form of the definite noun phrase under test. -/
inductive Form where
  /-- bare: a bare noun -/
  | bare
  /-- demonstrative: a demonstrative with a classifier and a noun, [Dem-Clf-N] -/
  | demonstrative
  /-- classifier: a classifier and a noun, [Clf-N] -/
  | classifier
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `form`. -/
def form (e : Datum) : Option Form :=
  e.parse? "form" [("bare", .bare), ("demonstrative", .demonstrative), ("classifier", .classifier)]

/-- The discourse status the paper assigns the definite, where it assigns one. -/
inductive Topic where
  /-- continuing: a continuing topic, a contrastive one included -/
  | continuing
  /-- new: a new topic, as under left-dislocation -/
  | new
  /-- nontopic: a noun phrase outside the topic situation of the question under discussion -/
  | nontopic
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `topic`. -/
def topic (e : Datum) : Option Topic :=
  e.parse? "topic" [("continuing", .continuing), ("new", .new), ("nontopic", .nontopic)]

/-- The reading of the noun phrase under test that the paper judges apart from the sentence. -/
inductive Reading where
  /-- definite: the noun phrase refers back to the antecedent -/
  | definite
  deriving DecidableEq, Repr, Fintype

/-- The name the rows give the reading. -/
def Reading.label : Reading → String
  | .definite => "definite"

/-- The judgment a row records for the reading, if it records one. -/
def reading (e : Datum) (r : Reading) : Option Judgment :=
  e.readings.lookup r.label

end Jenks2018.Examples
