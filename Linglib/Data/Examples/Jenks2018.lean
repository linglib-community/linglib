module

public import Linglib.Data.Examples.Schema

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
    source := ⟨"jenks-2018", "(10a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Yueliang sheng shang lai le."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("topic", "none"), ("position", "subject"), ("bare", "ok")] }

def ex_10b : Datum :=
  { id := "jenks2018_10b"
    source := ⟨"jenks-2018", "(10b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "(#Na/#Zhe ge) Taiwan (de) zongtong hen shengqi."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "largerSituation"), ("topic", "none"), ("position", "subject"), ("bare", "ok"), ("marked", "bad")] }

def ex_11a : Datum :=
  { id := "jenks2018_11a"
    source := ⟨"jenks-2018", "(11a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Hufei he-wan-le tang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "immediateSituation"), ("topic", "none"), ("position", "object"), ("bare", "ok")] }

def ex_11b : Datum :=
  { id := "jenks2018_11b"
    source := ⟨"jenks-2018", "(11b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Gou yao guo malu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "immediateSituation"), ("topic", "none"), ("position", "subject"), ("bare", "ok")] }

def ex_14a : Datum :=
  { id := "jenks2018_14a"
    source := ⟨"jenks-2018", "(14a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Chezi bei jingcha lanjie le yinwei mei you tiezhi zai paizhao shang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "partWholeBridging"), ("topic", "none"), ("position", "object"), ("bare", "ok")] }

def ex_14b : Datum :=
  { id := "jenks2018_14b"
    source := ⟨"jenks-2018", "(14b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Paul renwei na shou shi hen youmei, jishi ta bu renshi #(na wei) shiren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.1"), ("environment", "producerBridging"), ("topic", "none"), ("position", "object"), ("bare", "bad"), ("marked", "ok")] }

def ex_15b : Datum :=
  { id := "jenks2018_15b"
    source := ⟨"jenks-2018", "(15b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wo zuotian yudao #(na ge) nansheng."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("topic", "none"), ("position", "object"), ("bare", "bad"), ("marked", "ok")] }

def ex_15c : Datum :=
  { id := "jenks2018_15c"
    source := ⟨"jenks-2018", "(15c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wo dai gei #(na ge) nansheng yi ge liwu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("topic", "none"), ("position", "indirectObject"), ("bare", "bad"), ("marked", "ok")] }

def ex_15d : Datum :=
  { id := "jenks2018_15d"
    source := ⟨"jenks-2018", "(15d)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "(Na ge) nansheng kanqilai you er-shi sui zuoyou."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("topic", "continuing"), ("position", "subject"), ("bare", "ok"), ("marked", "ok")] }

def ex_15e : Datum :=
  { id := "jenks2018_15e"
    source := ⟨"jenks-2018", "(15e)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Wo bu renwei ?(na ge) nansheng hen youqu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("topic", "continuing"), ("position", "embeddedSubject"), ("bare", "ok"), ("marked", "ok")] }

def ex_16b : Datum :=
  { id := "jenks2018_16b"
    source := ⟨"jenks-2018", "(16b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Jingcha huaiyi na ge nuren nashihou shou le shang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("topic", "none"), ("position", "embeddedSubject"), ("marked", "ok")] }

def ex_16c : Datum :=
  { id := "jenks2018_16c"
    source := ⟨"jenks-2018", "(16c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Jingcha huaiyi nuren nashihou shou le shang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.2"), ("environment", "anaphoric"), ("topic", "none"), ("position", "embeddedSubject"), ("bare", "bad")] }

def ex_18b : Datum :=
  { id := "jenks2018_18b"
    source := ⟨"jenks-2018", "(18b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni jiao shei jinlai, wo dou jian na ge ren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("topic", "none"), ("position", "object"), ("marked", "ok")] }

def ex_19 : Datum :=
  { id := "jenks2018_19"
    source := ⟨"jenks-2018", "(19)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni jiao shei jinlai, wo dou jian ren."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("topic", "none"), ("position", "object"), ("bare", "bad")] }

def ex_20 : Datum :=
  { id := "jenks2018_20"
    source := ⟨"jenks-2018", "(20)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Mei ge [you yi zhi shuiniu de] nongfu dou hui da #(na zhi) shuiniu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "3.3"), ("environment", "donkey"), ("topic", "none"), ("position", "object"), ("bare", "bad"), ("marked", "ok")] }

def ex_49 : Datum :=
  { id := "jenks2018_49"
    source := ⟨"jenks-2018", "(49)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Mei ge mai le fangzi de ren dou xuyao xiuli (#na ge) wuding."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("environment", "partWholeBridging"), ("topic", "none"), ("position", "object"), ("bare", "ok"), ("marked", "bad")] }

def ex_51B : Datum :=
  { id := "jenks2018_51B"
    source := ⟨"jenks-2018", "(51B)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "#(Na zhi) mao sha le (ta)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("topic", "new"), ("position", "subject"), ("bare", "bad"), ("marked", "ok")] }

def ex_51Bp : Datum :=
  { id := "jenks2018_51Bp"
    source := ⟨"jenks-2018", "(51B′)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ta bei #(na zhi) mao sha le."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("topic", "none"), ("position", "object"), ("bare", "bad"), ("marked", "ok")] }

def ex_52b : Datum :=
  { id := "jenks2018_52b"
    source := ⟨"jenks-2018", "(52b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "#(Na ge) nansheng, wo hen bu xihuan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("topic", "new"), ("position", "leftDislocated"), ("bare", "bad"), ("marked", "ok")] }

def ex_53 : Datum :=
  { id := "jenks2018_53"
    source := ⟨"jenks-2018", "(53)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Nansheng ne, wo hen bu xihuan."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.3"), ("environment", "anaphoric"), ("topic", "continuing"), ("position", "leftDislocated"), ("bare", "ok")] }

def ex_54a : Datum :=
  { id := "jenks2018_54a"
    source := ⟨"jenks-2018", "(54a)"⟩
    reportedIn := none
    language := "cant1236"
    primaryText := "Lou5baan2 haa6zau3 lei5 gim2caa4 gung1zok3."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("topic", "none"), ("position", "subject"), ("marked", "ok")] }

def ex_54b : Datum :=
  { id := "jenks2018_54b"
    source := ⟨"jenks-2018", "(54b)"⟩
    reportedIn := none
    language := "cant1236"
    primaryText := "Zung2tung2 gam1maan5 baat3 dim2 soeng5 din6si6."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "largerSituation"), ("topic", "none"), ("position", "subject"), ("marked", "ok")] }

def ex_55b : Datum :=
  { id := "jenks2018_55b"
    source := ⟨"jenks-2018", "(55b)"⟩
    reportedIn := none
    language := "cant1236"
    primaryText := "Keoi5 m4 jing6wai4 (#go2) go3 zing3zi6gaa1 hou2 jau5ceoi3."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "anaphoric"), ("topic", "none"), ("position", "embeddedSubject"), ("marked", "ok")] }

def ex_56 : Datum :=
  { id := "jenks2018_56"
    source := ⟨"jenks-2018", "(56)"⟩
    reportedIn := none
    language := "cant1236"
    primaryText := "Mui5 go3 jau5 jat1 zek3 maa5 ge3 nung4fu1 daa2 zek3 maa5."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("environment", "donkey"), ("topic", "none"), ("position", "object"), ("marked", "ok")] }

def all : List Datum := [ex_10a, ex_10b, ex_11a, ex_11b, ex_14a, ex_14b, ex_15b, ex_15c, ex_15d, ex_15e, ex_16b, ex_16c, ex_18b, ex_19, ex_20, ex_49, ex_51B, ex_51Bp, ex_52b, ex_53, ex_54a, ex_54b, ex_55b, ex_56]

end Jenks2018.Examples
