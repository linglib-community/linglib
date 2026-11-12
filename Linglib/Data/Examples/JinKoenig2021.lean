module

public import Linglib.Data.Examples.Schema

/-!
# `JinKoenig2021` — typed example data

Auto-generated from `Linglib/Data/Examples/JinKoenig2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace JinKoenig2021.Examples`.
-/

@[expose] public section

namespace JinKoenig2021.Examples

def jk2021_1 : Datum :=
  { id := "jk2021_1"
    source := ⟨"jin-koenig-2021", "(1)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai peur qu'il ne pleuve demain."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("concept", "fear"), ("negator", "ne"), ("negator_kind", "dedicated")] }

def jk2021_3 : Datum :=
  { id := "jk2021_3"
    source := ⟨"jin-koenig-2021", "(3)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je souhaite qu'il ne pleuve demain."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")] }

def jk2021_4 : Datum :=
  { id := "jk2021_4"
    source := ⟨"jin-koenig-2021", "(4)"⟩
    reportedIn := none
    method := some .corpus
    language := "mand1415"
    primaryText := "9 míng wǎngyǒu mángzhe quànshuō, què wàng-le méi bàojǐng."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("concept", "forget"), ("negator", "méi"), ("negator_kind", "standard")] }

def jk2021_14 : Datum :=
  { id := "jk2021_14"
    source := ⟨"jin-koenig-2021", "(14)"⟩
    reportedIn := none
    method := some .corpus
    language := "mand1415"
    primaryText := "wǒ yě tǐng pà tā bié xiǎngbùkāi, zuò shǎ shì."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.1"), ("concept", "fear"), ("negator", "bié"), ("negator_kind", "imperative")] }

def jk2021_15 : Datum :=
  { id := "jk2021_15"
    source := ⟨"jin-koenig-2021", "(15)"⟩
    reportedIn := none
    method := some .corpus
    language := "mand1415"
    primaryText := "wǒ zěnyàng nénggòu bìmiǎn bú zài zuò yí gè piànzi?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.1"), ("concept", "avoid"), ("negator", "bù"), ("negator_kind", "standard")] }

def jk2021_16 : Datum :=
  { id := "jk2021_16"
    source := ⟨"jin-koenig-2021", "(16)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1290"
    primaryText := "Je regrette qu'il ne faille souvent attendre des années avant que l'histoire ne juge les tyrans."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.2"), ("concept", "regret"), ("negator", "ne"), ("negator_kind", "dedicated"), ("entrenched", "low")] }

def jk2021_17 : Datum :=
  { id := "jk2021_17"
    source := ⟨"jin-koenig-2021", "(17)"⟩
    reportedIn := none
    method := some .corpus
    language := "mand1415"
    primaryText := "...gèng hòuhuǐ zìjǐ bùgāi tīng Lǔ Sù de zhǔzhāng..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.2"), ("concept", "regret"), ("negator", "bùgāi"), ("negator_kind", "deontic")] }

def jk2021_18 : Datum :=
  { id := "jk2021_18"
    source := ⟨"jin-koenig-2021", "(18)"⟩
    reportedIn := none
    method := some .corpus
    language := "mand1415"
    primaryText := "dàjiā dōu àn'àn-de bàoyuàn Kèmíng bùgāi bǎ nà gè nǚrén gǎnzǒu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.2"), ("concept", "complain"), ("negator", "bùgāi"), ("negator_kind", "deontic")] }

def jk2021_19 : Datum :=
  { id := "jk2021_19"
    source := ⟨"jin-koenig-2021", "(19)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Niez-vous qu'il... ne soit un grand artiste?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.3"), ("concept", "deny"), ("negator", "ne"), ("negator_kind", "dedicated")] }

def jk2021_20 : Datum :=
  { id := "jk2021_20"
    source := ⟨"jin-koenig-2021", "(20)"⟩
    reportedIn := none
    method := some .elicitation
    language := "zarm1239"
    primaryText := "a tugu ey se kang a sinda sida."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.3"), ("concept", "hide"), ("negator", "sinda"), ("negator_kind", "copular")] }

def jk2021_21 : Datum :=
  { id := "jk2021_21"
    source := ⟨"jin-koenig-2021", "(21)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1290"
    primaryText := "Cet officier a oublié de ne pas tenir compte des avertissements que ses supérieurs lui avait notifiés en son temps."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.4"), ("concept", "forget"), ("negator", "ne pas"), ("negator_kind", "standard"), ("entrenched", "low")] }

def jk2021_22 : Datum :=
  { id := "jk2021_22"
    source := ⟨"jin-koenig-2021", "(22)"⟩
    reportedIn := none
    method := some .elicitation
    language := "zarm1239"
    primaryText := "a batu a mana graduate manang."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.4"), ("concept", "delay"), ("negator", "mana"), ("negator_kind", "standard")] }

def jk2021_23 : Datum :=
  { id := "jk2021_23"
    source := ⟨"jin-koenig-2021", "(23)"⟩
    reportedIn := none
    method := some .elicitation
    language := "gulf1241"
    primaryText := "ta-kallam-na maʕaa-h tˤawaal il-lail, wallah b-il-guwah maa waafag."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.1.4"), ("concept", "barely"), ("negator", "maa"), ("negator_kind", "standard")] }

def jk2021_24 : Datum :=
  { id := "jk2021_24"
    source := ⟨"jin-koenig-2021", "(24)"⟩
    reportedIn := none
    method := some .elicitation
    language := "gulf1241"
    primaryText := "gabl maa atzawaʒ ʕisht maʕa ahl-ii."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("concept", "before"), ("negator", "maa"), ("negator_kind", "standard")] }

def jk2021_25 : Datum :=
  { id := "jk2021_25"
    source := ⟨"jin-koenig-2021", "(25)"⟩
    reportedIn := none
    method := some .elicitation
    language := "zarm1239"
    primaryText := "ey si batu a ma si ka."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("concept", "cannotWait"), ("negator", "si"), ("negator_kind", "standard")] }

def jk2021_26 : Datum :=
  { id := "jk2021_26"
    source := ⟨"jin-koenig-2021", "(26)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1290"
    primaryText := "...les produits laitiers n'entraînent pas à asthme et ne déclenchent pas rarement des symptômes d'asthme..."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.2"), ("concept", "rarely"), ("negator", "ne pas"), ("negator_kind", "standard")] }

def jk2021_27 : Datum :=
  { id := "jk2021_27"
    source := ⟨"jin-koenig-2021", "(27)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il ne dépend que de moi qu'il n'obtienne satisfaction."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.3.3"), ("concept", "onlyDependsOn"), ("negator", "ne"), ("negator_kind", "dedicated")] }

def jk2021_28 : Datum :=
  { id := "jk2021_28"
    source := ⟨"jin-koenig-2021", "(28)"⟩
    reportedIn := none
    method := some .description
    language := "stan1290"
    primaryText := "La question se posa sur mes lèvres autrement que je ne l'aurais voulu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.4"), ("concept", "differentThan"), ("negator", "ne"), ("negator_kind", "dedicated")] }

def jk2021_29 : Datum :=
  { id := "jk2021_29"
    source := ⟨"jin-koenig-2021", "(29)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "I consumed all I could at my friends' wedding recently. The food was simply delicious! I was sad that I was too full to not be able to eat more!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6.4"), ("concept", "tooTo"), ("negator", "not"), ("negator_kind", "standard")] }

def all : List Datum := [jk2021_1, jk2021_3, jk2021_4, jk2021_14, jk2021_15, jk2021_16, jk2021_17, jk2021_18, jk2021_19, jk2021_20, jk2021_21, jk2021_22, jk2021_23, jk2021_24, jk2021_25, jk2021_26, jk2021_27, jk2021_28, jk2021_29]

end JinKoenig2021.Examples
