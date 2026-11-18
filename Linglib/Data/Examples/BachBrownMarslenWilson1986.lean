module

public import Linglib.Data.Examples.Schema

/-!
# `BachBrownMarslenWilson1986` — typed example data

Auto-generated from `Linglib/Data/Examples/BachBrownMarslenWilson1986.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BachBrownMarslenWilson1986.Examples`.
-/

@[expose] public section

namespace BachBrownMarslenWilson1986.Examples

def ex_1 : Datum :=
  { id := "bachbrownmarslenwilson1986_1"
    source := ⟨"bach-brown-marslen-wilson-1986", "(1)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De mannen hebben Hans de paarden leren voeren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "crossed"), ("verb_cluster_size", "2")] }

def ex_2 : Datum :=
  { id := "bachbrownmarslenwilson1986_2"
    source := ⟨"bach-brown-marslen-wilson-1986", "(2)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Männer haben Hans die Pferde füttern lehren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "nested"), ("verb_cluster_size", "2")] }

def ex_3 : Datum :=
  { id := "bachbrownmarslenwilson1986_3"
    source := ⟨"bach-brown-marslen-wilson-1986", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The men taught Hans to feed the horses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "right-branching"), ("verb_cluster_size", "2")] }

def ex_4 : Datum :=
  { id := "bachbrownmarslenwilson1986_4"
    source := ⟨"bach-brown-marslen-wilson-1986", "(4)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jeanine heeft de mannen Hans de paarden helpen leren voeren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "crossed"), ("verb_cluster_size", "3")] }

def ex_5 : Datum :=
  { id := "bachbrownmarslenwilson1986_5"
    source := ⟨"bach-brown-marslen-wilson-1986", "(5)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Johanna hat die Männer Hans die Pferde füttern lehren helfen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "nested"), ("verb_cluster_size", "3")] }

def ex_6 : Datum :=
  { id := "bachbrownmarslenwilson1986_6"
    source := ⟨"bach-brown-marslen-wilson-1986", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Joanna helped the men teach Hans to feed the horses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "right-branching"), ("verb_cluster_size", "3")] }

def ex_7 : Datum :=
  { id := "bachbrownmarslenwilson1986_7"
    source := ⟨"bach-brown-marslen-wilson-1986", "(7)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Karel heeft Jeanine de mannen Hans de paarden zien helpen leren voeren."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "crossed"), ("verb_cluster_size", "4")] }

def ex_8 : Datum :=
  { id := "bachbrownmarslenwilson1986_8"
    source := ⟨"bach-brown-marslen-wilson-1986", "(8)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Karl hat Johanna die Männer Hans die Pferde füttern lehren helfen sehen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "nested"), ("verb_cluster_size", "4")] }

def ex_9 : Datum :=
  { id := "bachbrownmarslenwilson1986_9"
    source := ⟨"bach-brown-marslen-wilson-1986", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Charles saw Joanna help the men teach Hans to feed the horses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "right-branching"), ("verb_cluster_size", "4")] }

def level1_nl : Datum :=
  { id := "bachbrownmarslenwilson1986_level1_nl"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 1 (Dutch)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De lerares heeft de knikkers opgeruimd."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "1")] }

def level1_de : Datum :=
  { id := "bachbrownmarslenwilson1986_level1_de"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 1 (German)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Lehrerin hat die Murmeln aufgeräumt."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "1")] }

def level2_nl : Datum :=
  { id := "bachbrownmarslenwilson1986_level2_nl"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 2 (Dutch)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jantje heeft de lerares de knikkers helpen opruimen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "2"), ("dependency", "crossed")] }

def level2_de : Datum :=
  { id := "bachbrownmarslenwilson1986_level2_de"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 2 (German)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wolfgang hat der Lehrerin die Murmeln aufräumen helfen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "2"), ("dependency", "nested")] }

def level3_nl : Datum :=
  { id := "bachbrownmarslenwilson1986_level3_nl"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 3 (Dutch)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Aad heeft Jantje de lerares de knikkers laten helpen opruimen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "3"), ("dependency", "crossed")] }

def level3_de : Datum :=
  { id := "bachbrownmarslenwilson1986_level3_de"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 3 (German)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Arnim hat Wolfgang der Lehrerin die Murmeln aufräumen helfen lassen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "3"), ("dependency", "nested")] }

def level4_nl : Datum :=
  { id := "bachbrownmarslenwilson1986_level4_nl"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 4 (Dutch)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ingrid heeft Lotte de bewoners de blinde het eten horen leren helpen koken."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "4"), ("dependency", "crossed")] }

def level4_de : Datum :=
  { id := "bachbrownmarslenwilson1986_level4_de"
    source := ⟨"bach-brown-marslen-wilson-1986", "Level 4 (German)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ingrid hat Lotte die Bewohner dem Blinden das Essen kochen helfen lehren hören."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "test"), ("embedding_level", "4"), ("dependency", "nested")] }

def para2_nl : Datum :=
  { id := "bachbrownmarslenwilson1986_para2_nl"
    source := ⟨"bach-brown-marslen-wilson-1986", "Paraphrase Level 2 (Dutch)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jantje heeft de lerares geholpen om de knikkers op te ruimen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "paraphrase"), ("embedding_level", "2"), ("dependency", "right-branching")] }

def para2_de : Datum :=
  { id := "bachbrownmarslenwilson1986_para2_de"
    source := ⟨"bach-brown-marslen-wilson-1986", "Paraphrase Level 2 (German)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wolfgang hat der Lehrerin geholfen, die Murmeln aufzuräumen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "paraphrase"), ("embedding_level", "2"), ("dependency", "right-branching")] }

def para3_de : Datum :=
  { id := "bachbrownmarslenwilson1986_para3_de"
    source := ⟨"bach-brown-marslen-wilson-1986", "Paraphrase Level 3 (German)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Arnim hat Wolfgang dazu gebracht, der Lehrerin beim Aufräumen der Murmeln zu helfen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "paraphrase"), ("embedding_level", "3"), ("dependency", "right-branching")] }

def ex_10 : Datum :=
  { id := "bachbrownmarslenwilson1986_10"
    source := ⟨"bach-brown-marslen-wilson-1986", "(10)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Henk heeft de kinderen Anneke de koeien laten zien melken."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "crossed"), ("verb_cluster_size", "3")] }

def ex_11 : Datum :=
  { id := "bachbrownmarslenwilson1986_11"
    source := ⟨"bach-brown-marslen-wilson-1986", "(11)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans hat die Kinder Anna die Kühe melken sehen lassen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "nested"), ("verb_cluster_size", "3")] }

def ex_13 : Datum :=
  { id := "bachbrownmarslenwilson1986_13"
    source := ⟨"bach-brown-marslen-wilson-1986", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which sonatas are these violins easy to play on?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "crossed"), ("construction", "long-distance filler-gap")] }

def ex_14 : Datum :=
  { id := "bachbrownmarslenwilson1986_14"
    source := ⟨"bach-brown-marslen-wilson-1986", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which violins are these sonatas easy to play on?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("dependency", "nested"), ("construction", "long-distance filler-gap")] }

def filler1_de : Datum :=
  { id := "bachbrownmarslenwilson1986_filler1_de"
    source := ⟨"bach-brown-marslen-wilson-1986", "Filler Level 1 (German)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Ball wurde durch das Fenster geworfen."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("sentence_type", "filler"), ("embedding_level", "1")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, level1_nl, level1_de, level2_nl, level2_de, level3_nl, level3_de, level4_nl, level4_de, para2_nl, para2_de, para3_de, ex_10, ex_11, ex_13, ex_14, filler1_de]

end BachBrownMarslenWilson1986.Examples
