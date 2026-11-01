module

public import Linglib.Data.Examples.Schema

/-!
# `Rett2020b` — typed example data

Auto-generated from `Linglib/Data/Examples/Rett2020b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rett2020b.Examples`.
-/

@[expose] public section

namespace Rett2020b.Examples

def ex_50a : Datum :=
  { id := "rett2020b_50a"
    source := ⟨"rett-2020b", "(50a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is as tall as Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive")] }

def ex_50b : Datum :=
  { id := "rett2020b_50b"
    source := ⟨"rett-2020b", "(50b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is tall like Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly")] }

def ex_50c : Datum :=
  { id := "rett2020b_50c"
    source := ⟨"rett-2020b", "(50c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is tall; Bill is tall (too)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "conjoined")] }

def ex_50d : Datum :=
  { id := "rett2020b_50d"
    source := ⟨"rett-2020b", "(50d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane equals Bill in height."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateMain")] }

def ex_51a : Datum :=
  { id := "rett2020b_51a"
    source := ⟨"rett-2020b", "(51a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is as tall as Bill, in fact she's taller."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "weak")] }

def ex_51b : Datum :=
  { id := "rett2020b_51b"
    source := ⟨"rett-2020b", "(51b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is tall like Bill, in fact she's taller."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly"), ("diagnostic", "weak")] }

def ex_51c : Datum :=
  { id := "rett2020b_51c"
    source := ⟨"rett-2020b", "(51c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is tall; Bill is tall (too). In fact she's taller."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "conjoined"), ("diagnostic", "weak")] }

def ex_51d : Datum :=
  { id := "rett2020b_51d"
    source := ⟨"rett-2020b", "(51d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane equals Bill in height, in fact she's taller."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateMain"), ("diagnostic", "weak")] }

def ex_53a : Datum :=
  { id := "rett2020b_53a"
    source := ⟨"rett-2020b", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is as tall as Bill, but she's short."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "evaluativity")] }

def ex_53b : Datum :=
  { id := "rett2020b_53b"
    source := ⟨"rett-2020b", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is tall like Bill, but she's short."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly"), ("diagnostic", "evaluativity")] }

def ex_53c : Datum :=
  { id := "rett2020b_53c"
    source := ⟨"rett-2020b", "(53c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is tall; Bill is tall (too), but she is short."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "conjoined"), ("diagnostic", "evaluativity")] }

def ex_53d : Datum :=
  { id := "rett2020b_53d"
    source := ⟨"rett-2020b", "(53d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane equals Bill in height, but she's short."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateMain"), ("diagnostic", "evaluativity")] }

def ex_54a : Datum :=
  { id := "rett2020b_54a"
    source := ⟨"rett-2020b", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is twice as tall as Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "factor")] }

def ex_54b : Datum :=
  { id := "rett2020b_54b"
    source := ⟨"rett-2020b", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is twice tall like Bill."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly"), ("diagnostic", "factor")] }

def ex_54c : Datum :=
  { id := "rett2020b_54c"
    source := ⟨"rett-2020b", "(54c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane is twice tall; Bill is tall (too)."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "conjoined"), ("diagnostic", "factor")] }

def ex_54d : Datum :=
  { id := "rett2020b_54d"
    source := ⟨"rett-2020b", "(54d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane twice equals Bill in height."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateMain"), ("diagnostic", "factor")] }

def ex_55 : Datum :=
  { id := "rett2020b_55"
    source := ⟨"rett-2020b", "(55)"⟩
    reportedIn := none
    method := some .elicitation
    language := "swed1254"
    primaryText := "Thomas är lika lång som Christoffer; han är faktiskt längre."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateAdverbial"), ("diagnostic", "weak")] }

def ex_56 : Datum :=
  { id := "rett2020b_56"
    source := ⟨"rett-2020b", "(56)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan is even lang als Piet. Hij is zelfs langer."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateAdverbial"), ("diagnostic", "weak")] }

def ex_58 : Datum :=
  { id := "rett2020b_58"
    source := ⟨"rett-2020b", "(58)"⟩
    reportedIn := none
    language := "croa1245"
    primaryText := "Ivan je visok kao Petar."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly")] }

def ex_59 : Datum :=
  { id := "rett2020b_59"
    source := ⟨"rett-2020b", "(59)"⟩
    reportedIn := none
    language := "croa1245"
    primaryText := "Ivan je dvostruko visok kao Petar."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly"), ("diagnostic", "factor")] }

def ex_61 : Datum :=
  { id := "rett2020b_61"
    source := ⟨"rett-2020b", "(61)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni è alto come Marco."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly")] }

def ex_62 : Datum :=
  { id := "rett2020b_62"
    source := ⟨"rett-2020b", "(62)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni è due volte alto come Marco."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly"), ("diagnostic", "factor")] }

def ex_63 : Datum :=
  { id := "rett2020b_63"
    source := ⟨"rett-2020b", "(63)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan is zo lang als Piet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive")] }

def ex_64 : Datum :=
  { id := "rett2020b_64"
    source := ⟨"rett-2020b", "(64)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan is twee keer zo lang als Piet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "factor")] }

def ex_65 : Datum :=
  { id := "rett2020b_65"
    source := ⟨"rett-2020b", "(65)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan is zo lang als Piet, en hij is heel klein."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "evaluativity")] }

def ex_66 : Datum :=
  { id := "rett2020b_66"
    source := ⟨"rett-2020b", "(66)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan is zo lang als Piet. Hij is zelfs langer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "weak")] }

def ex_67 : Datum :=
  { id := "rett2020b_67"
    source := ⟨"rett-2020b", "(67)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Thomas är dubbelt så lång som Christoffer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "factor")] }

def ex_68 : Datum :=
  { id := "rett2020b_68"
    source := ⟨"rett-2020b", "(68)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Thomas är så lång som Christoffer, men båda är korta."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "evaluativity")] }

def ex_69 : Datum :=
  { id := "rett2020b_69"
    source := ⟨"rett-2020b", "(69)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Thomas är så lång som Christoffer, han är till och med högre."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive"), ("diagnostic", "weak")] }

def ex_70 : Datum :=
  { id := "rett2020b_70"
    source := ⟨"rett-2020b", "(70)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni è tanto alto quanto Pietro, ma è basso."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative"), ("diagnostic", "evaluativity")] }

def ex_71 : Datum :=
  { id := "rett2020b_71"
    source := ⟨"rett-2020b", "(71)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "G è tanto alto quanto P. Infatti, è più alto."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative"), ("diagnostic", "weak")] }

def ex_72 : Datum :=
  { id := "rett2020b_72"
    source := ⟨"rett-2020b", "(72)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni è due volte tanto alto quanto Pietro."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative"), ("diagnostic", "factor")] }

def ex_73 : Datum :=
  { id := "rett2020b_73"
    source := ⟨"rett-2020b", "(73)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan es tan alto como Pedro, pero Pedro es bajito."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative"), ("diagnostic", "evaluativity")] }

def ex_74 : Datum :=
  { id := "rett2020b_74"
    source := ⟨"rett-2020b", "(74)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan es tan alto como Pedro. De hecho, él es más alto."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative"), ("diagnostic", "weak")] }

def ex_75 : Datum :=
  { id := "rett2020b_75"
    source := ⟨"rett-2020b", "(75)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Juan es dos veces tan alto como Pedro."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative"), ("diagnostic", "factor")] }

def ex_26 : Datum :=
  { id := "rett2020b_26"
    source := ⟨"rett-2020b", "(26)"⟩
    reportedIn := none
    language := "alba1267"
    primaryText := "Ime motër ëstë e bukur si ti."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly")] }

def ex_27 : Datum :=
  { id := "rett2020b_27"
    source := ⟨"rett-2020b", "(27)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Sestra mi e xubava kato tebe."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly")] }

def ex_28 : Datum :=
  { id := "rett2020b_28"
    source := ⟨"rett-2020b", "(28)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I adhelfí mu ine ómorfi san (kj) eséna."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly")] }

def ex_29 : Datum :=
  { id := "rett2020b_29"
    source := ⟨"rett-2020b", "(29)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mia sorella è carina come te."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "smOnly")] }

def ex_30 : Datum :=
  { id := "rett2020b_30"
    source := ⟨"rett-2020b", "(30)"⟩
    reportedIn := none
    language := "port1283"
    primaryText := "A minha irmã é tão bonita quanto você."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative")] }

def ex_31 : Datum :=
  { id := "rett2020b_31"
    source := ⟨"rett-2020b", "(31)"⟩
    reportedIn := none
    language := "panj1256"
    primaryText := "Ó ónna caŋgaa ai jínnaa ó daa pràà."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive")] }

def ex_34 : Datum :=
  { id := "rett2020b_34"
    source := ⟨"rett-2020b", "(34)"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "M-toto wa-ngu ni hodari sawa na wa-ko."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateMain")] }

def ex_37 : Datum :=
  { id := "rett2020b_37"
    source := ⟨"rett-2020b", "(37)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Tā gēn nǐ yíyàng gāo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateAdverbial")] }

def ex_39 : Datum :=
  { id := "rett2020b_39"
    source := ⟨"rett-2020b", "(39)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Systir mín er jafn stór og ég."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "predicateAdverbial")] }

def ex_47 : Datum :=
  { id := "rett2020b_47"
    source := ⟨"rett-2020b", "(47)"⟩
    reportedIn := none
    language := "wels1247"
    primaryText := "Mae e cyn ddued â'r frân."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "dedicated")] }

def ex_92 : Datum :=
  { id := "rett2020b_92"
    source := ⟨"rett-2020b", "(92)"⟩
    reportedIn := none
    language := "stan1289"
    primaryText := "La meva germana és tan bonica com tu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative")] }

def ex_93 : Datum :=
  { id := "rett2020b_93"
    source := ⟨"rett-2020b", "(93)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Suomalaiset eivät anna kättä niin paljon kuin keskieurooppalaiset."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "sufficientive")] }

def ex_95 : Datum :=
  { id := "rett2020b_95"
    source := ⟨"rett-2020b", "(95)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I adjelfí mu ine tóso ómorfi óso kj esí."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative")] }

def ex_97 : Datum :=
  { id := "rett2020b_97"
    source := ⟨"rett-2020b", "(97)"⟩
    reportedIn := none
    language := "lith1251"
    primaryText := "Šiandien taip šalta kaip vakar."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative")] }

def ex_100 : Datum :=
  { id := "rett2020b_100"
    source := ⟨"rett-2020b", "(100)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Moja sestra je tako čedna kot ti."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "demonstrative")] }

def all : List Datum := [ex_50a, ex_50b, ex_50c, ex_50d, ex_51a, ex_51b, ex_51c, ex_51d, ex_53a, ex_53b, ex_53c, ex_53d, ex_54a, ex_54b, ex_54c, ex_54d, ex_55, ex_56, ex_58, ex_59, ex_61, ex_62, ex_63, ex_64, ex_65, ex_66, ex_67, ex_68, ex_69, ex_70, ex_71, ex_72, ex_73, ex_74, ex_75, ex_26, ex_27, ex_28, ex_29, ex_30, ex_31, ex_34, ex_37, ex_39, ex_47, ex_92, ex_93, ex_95, ex_97, ex_100]

end Rett2020b.Examples
