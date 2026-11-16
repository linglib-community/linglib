module

public import Linglib.Data.Examples.Schema

/-!
# `DeBelderVanCraenenbroeck2015` — typed example data

Auto-generated from `Linglib/Data/Examples/DeBelderVanCraenenbroeck2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DeBelderVanCraenenbroeck2015.Examples`.
-/

@[expose] public section

namespace DeBelderVanCraenenbroeck2015.Examples

def ex_2 : Datum :=
  { id := "debeldervancraenenbroeck2015_2"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(2)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik heb het waarom van de zaak nooit begrepen."
    glossedTokens := [("Ik", "I"), ("heb", "have"), ("het", "the"), ("waarom", "why"), ("van", "of"), ("de", "the"), ("zaak", "case"), ("nooit", "never"), ("begrepen.", "understood")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'e', 'b']], [['h', 'a', 'v', 'e']]⟩, ⟨[['h', 'e', 't']], [['t', 'h', 'e']]⟩, ⟨[['w', 'a', 'a', 'r', 'o', 'm']], [['w', 'h', 'y']]⟩, ⟨[['v', 'a', 'n']], [['o', 'f']]⟩, ⟨[['d', 'e']], [['t', 'h', 'e']]⟩, ⟨[['z', 'a', 'a', 'k']], [['c', 'a', 's', 'e']]⟩, ⟨[['n', 'o', 'o', 'i', 't']], [['n', 'e', 'v', 'e', 'r']]⟩, ⟨[['b', 'e', 'g', 'r', 'e', 'p', 'e', 'n']], [['u', 'n', 'd', 'e', 'r', 's', 't', 'o', 'o', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "waarom"), ("class", "wh"), ("structure", "nominal")] }

def ex_3 : Datum :=
  { id := "debeldervancraenenbroeck2015_3"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(3)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "In een krantenartikel komt het wat/hoe/wie/waar altijd voor het waarom."
    glossedTokens := [("In", "in"), ("een", "a"), ("krantenartikel", "newspaper.article"), ("komt", "comes"), ("het", "the"), ("wat/hoe/wie/waar", "what/how/who/where"), ("altijd", "always"), ("voor", "before"), ("het", "the"), ("waarom.", "why")]
    glossedWords := [⟨[['I', 'n']], [['i', 'n']]⟩, ⟨[['e', 'e', 'n']], [['a']]⟩, ⟨[['k', 'r', 'a', 'n', 't', 'e', 'n', 'a', 'r', 't', 'i', 'k', 'e', 'l']], [['n', 'e', 'w', 's', 'p', 'a', 'p', 'e', 'r', '.', 'a', 'r', 't', 'i', 'c', 'l', 'e']]⟩, ⟨[['k', 'o', 'm', 't']], [['c', 'o', 'm', 'e', 's']]⟩, ⟨[['h', 'e', 't']], [['t', 'h', 'e']]⟩, ⟨[['w', 'a', 't', '/', 'h', 'o', 'e', '/', 'w', 'i', 'e', '/', 'w', 'a', 'a', 'r']], [['w', 'h', 'a', 't', '/', 'h', 'o', 'w', '/', 'w', 'h', 'o', '/', 'w', 'h', 'e', 'r', 'e']]⟩, ⟨[['a', 'l', 't', 'i', 'j', 'd']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['v', 'o', 'o', 'r']], [['b', 'e', 'f', 'o', 'r', 'e']]⟩, ⟨[['h', 'e', 't']], [['t', 'h', 'e']]⟩, ⟨[['w', 'a', 'a', 'r', 'o', 'm']], [['w', 'h', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "wat/hoe/wie/waar"), ("class", "wh"), ("structure", "nominal")] }

def ex_4 : Datum :=
  { id := "debeldervancraenenbroeck2015_4"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(4)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De studenten jij-en onderling."
    glossedTokens := [("De", "the"), ("studenten", "students"), ("jij-en", "you-INFINITIVE"), ("onderling.", "among.one.another")]
    glossedWords := [⟨[['D', 'e']], [['t', 'h', 'e']]⟩, ⟨[['s', 't', 'u', 'd', 'e', 'n', 't', 'e', 'n']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩, ⟨[['j', 'i', 'j'], ['e', 'n']], [['y', 'o', 'u'], ['I', 'N', 'F', 'I', 'N', 'I', 'T', 'I', 'V', 'E']]⟩, ⟨[['o', 'n', 'd', 'e', 'r', 'l', 'i', 'n', 'g']], [['a', 'm', 'o', 'n', 'g', '.', 'o', 'n', 'e', '.', 'a', 'n', 'o', 't', 'h', 'e', 'r']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "jij"), ("class", "pronoun"), ("structure", "verbal")] }

def ex_5 : Datum :=
  { id := "debeldervancraenenbroeck2015_5"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(5)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Martha is mijn tweede ik."
    glossedTokens := [("Martha", "Martha"), ("is", "is"), ("mijn", "my"), ("tweede", "second"), ("ik.", "I")]
    glossedWords := [⟨[['M', 'a', 'r', 't', 'h', 'a']], [['M', 'a', 'r', 't', 'h', 'a']]⟩, ⟨[['i', 's']], [['i', 's']]⟩, ⟨[['m', 'i', 'j', 'n']], [['m', 'y']]⟩, ⟨[['t', 'w', 'e', 'e', 'd', 'e']], [['s', 'e', 'c', 'o', 'n', 'd']]⟩, ⟨[['i', 'k']], [['I']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "ik"), ("class", "pronoun"), ("structure", "nominal")] }

def ex_6 : Datum :=
  { id := "debeldervancraenenbroeck2015_6"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(6)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Niets te maar-en!"
    glossedTokens := [("Niets", "nothing"), ("te", "to"), ("maar-en!", "but-INFINITIVE")]
    glossedWords := [⟨[['N', 'i', 'e', 't', 's']], [['n', 'o', 't', 'h', 'i', 'n', 'g']]⟩, ⟨[['t', 'e']], [['t', 'o']]⟩, ⟨[['m', 'a', 'a', 'r'], ['e', 'n']], [['b', 'u', 't'], ['I', 'N', 'F', 'I', 'N', 'I', 'T', 'I', 'V', 'E']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "maar"), ("class", "conjunction"), ("structure", "verbal")] }

def ex_7 : Datum :=
  { id := "debeldervancraenenbroeck2015_7"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(7)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Paard is een het-woord."
    glossedTokens := [("Paard", "horse"), ("is", "is"), ("een", "a"), ("het-woord.", "the.NEUTER.DEFINITE-word")]
    glossedWords := [⟨[['P', 'a', 'a', 'r', 'd']], [['h', 'o', 'r', 's', 'e']]⟩, ⟨[['i', 's']], [['i', 's']]⟩, ⟨[['e', 'e', 'n']], [['a']]⟩, ⟨[['h', 'e', 't'], ['w', 'o', 'o', 'r', 'd']], [['t', 'h', 'e', '.', 'N', 'E', 'U', 'T', 'E', 'R', '.', 'D', 'E', 'F', 'I', 'N', 'I', 'T', 'E'], ['w', 'o', 'r', 'd']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "het"), ("class", "article"), ("structure", "compound")] }

def ex_8a : Datum :=
  { id := "debeldervancraenenbroeck2015_8a"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(8a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het getik van de klok"
    glossedTokens := [("het", "the"), ("getik", "GE-tick"), ("van", "of"), ("de", "the"), ("klok", "clock")]
    glossedWords := [⟨[['h', 'e', 't']], [['t', 'h', 'e']]⟩, ⟨[['g', 'e', 't', 'i', 'k']], [['G', 'E'], ['t', 'i', 'c', 'k']]⟩, ⟨[['v', 'a', 'n']], [['o', 'f']]⟩, ⟨[['d', 'e']], [['t', 'h', 'e']]⟩, ⟨[['k', 'l', 'o', 'k']], [['c', 'l', 'o', 'c', 'k']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "tik"), ("class", "lexical"), ("structure", "geNominal")] }

def ex_8b : Datum :=
  { id := "debeldervancraenenbroeck2015_8b"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(8b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het gefluit van de vogels"
    glossedTokens := [("het", "the"), ("gefluit", "GE-whistle"), ("van", "of"), ("de", "the"), ("vogels", "birds")]
    glossedWords := [⟨[['h', 'e', 't']], [['t', 'h', 'e']]⟩, ⟨[['g', 'e', 'f', 'l', 'u', 'i', 't']], [['G', 'E'], ['w', 'h', 'i', 's', 't', 'l', 'e']]⟩, ⟨[['v', 'a', 'n']], [['o', 'f']]⟩, ⟨[['d', 'e']], [['t', 'h', 'e']]⟩, ⟨[['v', 'o', 'g', 'e', 'l', 's']], [['b', 'i', 'r', 'd', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "fluit"), ("class", "lexical"), ("structure", "geNominal")] }

def ex_9a : Datum :=
  { id := "debeldervancraenenbroeck2015_9a"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-maar niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-maar", "GE-but"), ("niet.", "not")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'o', 'e', 'f']], [['n', 'e', 'e', 'd']]⟩, ⟨[['a', 'l']], [['a', 'l', 'l']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e'], ['m', 'a', 'a', 'r']], [['G', 'E'], ['b', 'u', 't']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "maar"), ("class", "conjunction"), ("structure", "geNominal")] }

def ex_9b : Datum :=
  { id := "debeldervancraenenbroeck2015_9b"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-alhoewel niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-alhoewel", "GE-although"), ("niet.", "not")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'o', 'e', 'f']], [['n', 'e', 'e', 'd']]⟩, ⟨[['a', 'l']], [['a', 'l', 'l']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e'], ['a', 'l', 'h', 'o', 'e', 'w', 'e', 'l']], [['G', 'E'], ['a', 'l', 't', 'h', 'o', 'u', 'g', 'h']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "alhoewel"), ("class", "conjunction"), ("structure", "geNominal")] }

def ex_9c : Datum :=
  { id := "debeldervancraenenbroeck2015_9c"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-of niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-of", "GE-or"), ("niet.", "not")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'o', 'e', 'f']], [['n', 'e', 'e', 'd']]⟩, ⟨[['a', 'l']], [['a', 'l', 'l']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e'], ['o', 'f']], [['G', 'E'], ['o', 'r']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "of"), ("class", "conjunction"), ("structure", "geNominal")] }

def ex_9d : Datum :=
  { id := "debeldervancraenenbroeck2015_9d"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-hé niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-hé", "GE-PARTICLE"), ("niet.", "not")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'o', 'e', 'f']], [['n', 'e', 'e', 'd']]⟩, ⟨[['a', 'l']], [['a', 'l', 'l']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e'], ['h', 'é']], [['G', 'E'], ['P', 'A', 'R', 'T', 'I', 'C', 'L', 'E']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "hé"), ("class", "particle"), ("structure", "geNominal")] }

def ex_9e : Datum :=
  { id := "debeldervancraenenbroeck2015_9e"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9e)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-waarom niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-waarom", "GE-why"), ("niet.", "not")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'o', 'e', 'f']], [['n', 'e', 'e', 'd']]⟩, ⟨[['a', 'l']], [['a', 'l', 'l']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e'], ['w', 'a', 'a', 'r', 'o', 'm']], [['G', 'E'], ['w', 'h', 'y']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "waarom"), ("class", "wh"), ("structure", "geNominal")] }

def ex_9f : Datum :=
  { id := "debeldervancraenenbroeck2015_9f"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9f)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-nooit niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-nooit", "GE-never"), ("niet.", "not")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'o', 'e', 'f']], [['n', 'e', 'e', 'd']]⟩, ⟨[['a', 'l']], [['a', 'l', 'l']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e'], ['n', 'o', 'o', 'i', 't']], [['G', 'E'], ['n', 'e', 'v', 'e', 'r']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "nooit"), ("class", "adverb"), ("structure", "geNominal")] }

def ex_9g : Datum :=
  { id := "debeldervancraenenbroeck2015_9g"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(9g)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik hoef al dat ge-ik niet."
    glossedTokens := [("Ik", "I"), ("hoef", "need"), ("al", "all"), ("dat", "that"), ("ge-ik", "GE-I"), ("niet.", "not")]
    glossedWords := [⟨[['I', 'k']], [['I']]⟩, ⟨[['h', 'o', 'e', 'f']], [['n', 'e', 'e', 'd']]⟩, ⟨[['a', 'l']], [['a', 'l', 'l']]⟩, ⟨[['d', 'a', 't']], [['t', 'h', 'a', 't']]⟩, ⟨[['g', 'e'], ['i', 'k']], [['G', 'E'], ['I']]⟩, ⟨[['n', 'i', 'e', 't']], [['n', 'o', 't']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "rootPosition"), ("item", "ik"), ("class", "pronoun"), ("structure", "geNominal")] }

def ex_10 : Datum :=
  { id := "debeldervancraenenbroeck2015_10"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(10)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Mijn tweede ik is ongelukkig."
    glossedTokens := [("Mijn", "my"), ("tweede", "second"), ("ik", "I"), ("is", "is"), ("ongelukkig.", "unhappy")]
    glossedWords := [⟨[['M', 'i', 'j', 'n']], [['m', 'y']]⟩, ⟨[['t', 'w', 'e', 'e', 'd', 'e']], [['s', 'e', 'c', 'o', 'n', 'd']]⟩, ⟨[['i', 'k']], [['I']]⟩, ⟨[['i', 's']], [['i', 's']]⟩, ⟨[['o', 'n', 'g', 'e', 'l', 'u', 'k', 'k', 'i', 'g']], [['u', 'n', 'h', 'a', 'p', 'p', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Mijn tweede ik ben ongelukkig.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "agreement"), ("item", "ik"), ("class", "pronoun"), ("copula", "is")] }

def ex_11 : Datum :=
  { id := "debeldervancraenenbroeck2015_11"
    source := ⟨"de-belder-van-craenenbroeck-2015", "(11)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Niets te maar-en je hebt veel werk!"
    glossedTokens := [("Niets", "nothing"), ("te", "to"), ("maar-en", "but-INFINITIVE"), ("je", "you"), ("hebt", "have"), ("veel", "much"), ("werk!", "work")]
    glossedWords := [⟨[['N', 'i', 'e', 't', 's']], [['n', 'o', 't', 'h', 'i', 'n', 'g']]⟩, ⟨[['t', 'e']], [['t', 'o']]⟩, ⟨[['m', 'a', 'a', 'r'], ['e', 'n']], [['b', 'u', 't'], ['I', 'N', 'F', 'I', 'N', 'I', 'T', 'I', 'V', 'E']]⟩, ⟨[['j', 'e']], [['y', 'o', 'u']]⟩, ⟨[['h', 'e', 'b', 't']], [['h', 'a', 'v', 'e']]⟩, ⟨[['v', 'e', 'e', 'l']], [['m', 'u', 'c', 'h']]⟩, ⟨[['w', 'e', 'r', 'k']], [['w', 'o', 'r', 'k']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.4.4"), ("construction", "selection"), ("item", "maar"), ("class", "conjunction")] }

def all : List Datum := [ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8a, ex_8b, ex_9a, ex_9b, ex_9c, ex_9d, ex_9e, ex_9f, ex_9g, ex_10, ex_11]

end DeBelderVanCraenenbroeck2015.Examples
