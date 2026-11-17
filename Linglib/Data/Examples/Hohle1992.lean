module

public import Linglib.Data.Examples.Schema

/-!
# `Hohle1992` — typed example data

Auto-generated from `Linglib/Data/Examples/Hohle1992.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hohle1992.Examples`.
-/

@[expose] public section

namespace Hohle1992.Examples

def ex1b : Datum :=
  { id := "hohle1992_ex1b"
    source := ⟨"hohle-1992", "(1b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(das stimmt) Karl schreibt ein DREHbuch"
    glossedTokens := []
    context := "ich habe Hanna gefragt, was Karl grade macht, und sie hat die alberne Behauptung aufgestellt, daß er ein DREHbuch schreibt"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "content"), ("accent", "object")] }

def ex2b : Datum :=
  { id := "hohle1992_ex2b"
    source := ⟨"hohle-1992", "(2b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(das stimmt) Karl SCHREIBT ein Drehbuch"
    glossedTokens := []
    context := "ich habe Hanna gefragt, was Karl grade macht, und sie hat die alberne Behauptung aufgestellt, daß er ein DREHbuch schreibt"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "second")] }

def ex4a : Datum :=
  { id := "hohle1992_ex4a"
    source := ⟨"hohle-1992", "(4a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(nein) Karl HAT nicht gelogen"
    glossedTokens := []
    context := "Karl hat BESTIMMT nicht gelogen"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "second"), ("verbContent", "temporal auxiliary")] }

def ex5a : Datum :=
  { id := "hohle1992_ex5a"
    source := ⟨"hohle-1992", "(5a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(doch) ich HÖRE mal auf"
    glossedTokens := []
    context := "hörst du denn NIE auf?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "second"), ("verbContent", "particle verb")] }

def ex6a : Datum :=
  { id := "hohle1992_ex6a"
    source := ⟨"hohle-1992", "(6a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(aber ja) sie MACHT ihm den Garaus"
    glossedTokens := []
    context := "ich kann mir nicht vorstellen, daß sie ihn wirklich umbringen will"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "second"), ("verbContent", "idiom")] }

def ex7a : Datum :=
  { id := "hohle1992_ex7a"
    source := ⟨"hohle-1992", "(7a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "HÖRT sie denn damit auf?"
    glossedTokens := []
    context := "ich habe Hanna gebeten, damit AUFzuhören"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("clauseType", "polar interrogative")] }

def ex8a : Datum :=
  { id := "hohle1992_ex8a"
    source := ⟨"hohle-1992", "(8a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "HAT er den Hund denn getreten?"
    glossedTokens := []
    context := "es heißt, daß Karl den HUND getreten hat"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("clauseType", "polar interrogative")] }

def ex9a : Datum :=
  { id := "hohle1992_ex9a"
    source := ⟨"hohle-1992", "(9a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(und?) LESEN Sie ihm die Leviten?"
    glossedTokens := []
    context := "ich habe Karl gedroht, daß ich ihm die LEVITEN lesen werde"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("clauseType", "polar interrogative")] }

def ex10a : Datum :=
  { id := "hohle1992_ex10a"
    source := ⟨"hohle-1992", "(10a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "wann HÖRT sie denn damit auf?"
    glossedTokens := []
    context := "ich habe Hanna gebeten, damit AUFzuhören"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("clauseType", "wh-interrogative")] }

def ex11a : Datum :=
  { id := "hohle1992_ex11a"
    source := ⟨"hohle-1992", "(11a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "wer HAT den Hund denn getreten?"
    glossedTokens := []
    context := "ich habe den Hund nicht getreten, und Karl hat es auch nicht getan"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("clauseType", "wh-interrogative")] }

def ex12a : Datum :=
  { id := "hohle1992_ex12a"
    source := ⟨"hohle-1992", "(12a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "warum NIMMT er denn nicht teil?"
    glossedTokens := []
    context := "daß Karl nicht teilnimmt, hat nichts mit seiner Kurzsichtigkeit zu tun"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "1"), ("focus", "verum"), ("accent", "finite verb"), ("clauseType", "wh-interrogative"), ("negation", "in background")] }

def ex45a : Datum :=
  { id := "hohle1992_ex45a"
    source := ⟨"hohle-1992", "(45a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "wenn Hanna meint, Karl schreibt ein DREHBUCH, (dann sollte sie sich schon mal um einen Produzenten kümmern)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("focus", "content"), ("embedded", "verb-second")] }

def ex45b : Datum :=
  { id := "hohle1992_ex45b"
    source := ⟨"hohle-1992", "(45b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "wenn Hanna meint, Karl SCHREIBT ein Drehbuch, (dann …)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("focus", "verum"), ("accent", "finite verb"), ("embedded", "verb-second")] }

def ex47a : Datum :=
  { id := "hohle1992_ex47a"
    source := ⟨"hohle-1992", "(47a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "daß Karl behauptet, sie HÖRT damit auf, wundert mich überhaupt nicht"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("focus", "verum"), ("accent", "finite verb"), ("embedded", "verb-second")] }

def ex47b : Datum :=
  { id := "hohle1992_ex47b"
    source := ⟨"hohle-1992", "(47b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jemand, der denkt, sie LIEST uns die Leviten, kann sie nicht sehr gut kennen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.1"), ("focus", "verum"), ("accent", "finite verb"), ("embedded", "verb-second")] }

def ex48a : Datum :=
  { id := "hohle1992_ex48a"
    source := ⟨"hohle-1992", "(48a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ich bin sicher, DAß sie mal in Rom war (aber ob das KÜRZLICH war, weiß ich nicht)"
    glossedTokens := []
    context := "weißt du, ob Hanna kürzlich in ROM war?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("focus", "verum"), ("accent", "complementizer"), ("verumType", "C")] }

def ex48b : Datum :=
  { id := "hohle1992_ex48b"
    source := ⟨"hohle-1992", "(48b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ich weiß nicht, OB sie in Rom war (aber WENN das der Fall ist, muß es vor kurzer ZEIT gewesen sein)"
    glossedTokens := []
    context := "weißt du, ob Hanna kürzlich in ROM war?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("focus", "verum"), ("accent", "complementizer"), ("verumType", "C")] }

def ex50a : Datum :=
  { id := "hohle1992_ex50a"
    source := ⟨"hohle-1992", "(50a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(ja) ich denke, er HÖRT damit auf"
    glossedTokens := []
    context := "vielleicht hört Karl damit AUF"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("focus", "verum"), ("accent", "finite verb"), ("verumType", "F")] }

def ex50b : Datum :=
  { id := "hohle1992_ex50b"
    source := ⟨"hohle-1992", "(50b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(ja) ich denke, DAß er damit aufhört"
    glossedTokens := []
    context := "vielleicht hört Karl damit AUF"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("focus", "verum"), ("accent", "complementizer"), ("verumType", "C")] }

def ex51a : Datum :=
  { id := "hohle1992_ex51a"
    source := ⟨"hohle-1992", "(51a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber Hanna meint, DAß er gelogen hat"
    glossedTokens := []
    context := "Karl hat BESTIMMT nicht gelogen"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("focus", "verum"), ("accent", "complementizer"), ("verumType", "C")] }

def ex51b : Datum :=
  { id := "hohle1992_ex51b"
    source := ⟨"hohle-1992", "(51b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber Hanna meint, er HAT gelogen"
    glossedTokens := []
    context := "Karl hat BESTIMMT nicht gelogen"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("focus", "verum"), ("accent", "finite verb"), ("verumType", "F")] }

def ex52a : Datum :=
  { id := "hohle1992_ex52a"
    source := ⟨"hohle-1992", "(52a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ich bin sicher, sie WAR mal in Rom (aber ob das KÜRZLICH war, weiß ich nicht)"
    glossedTokens := []
    context := "weißt du, ob Hanna kürzlich in ROM war?"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "5.2"), ("focus", "verum"), ("accent", "finite verb"), ("verumType", "F")] }

def ex55a : Datum :=
  { id := "hohle1992_ex55a"
    source := ⟨"hohle-1992", "(55a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber Hanna denkt, er HÖRT ihr nicht zu"
    glossedTokens := []
    context := "ich hoffe, daß Karl ihr ZUhört"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("focus", "verum"), ("accent", "finite verb"), ("verumType", "F"), ("negation", "in focus"), ("scoping", "negation over VERUM")] }

def ex55b : Datum :=
  { id := "hohle1992_ex55b"
    source := ⟨"hohle-1992", "(55b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber Hanna denkt, DAß er ihr nicht zuhört"
    glossedTokens := []
    context := "ich hoffe, daß Karl ihr ZUhört"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("focus", "verum"), ("accent", "complementizer"), ("verumType", "C"), ("negation", "in background"), ("scoping", "VERUM over negation")] }

def ex57a : Datum :=
  { id := "hohle1992_ex57a"
    source := ⟨"hohle-1992", "(57a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber Karl HAT kein Drehbuch geschrieben"
    glossedTokens := []
    context := "es heißt, daß Karl ein DREHBUCH geschrieben hat"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("focus", "verum"), ("accent", "finite verb"), ("verumType", "F"), ("negation", "in focus"), ("scoping", "negation over VERUM")] }

def ex58a : Datum :=
  { id := "hohle1992_ex58a"
    source := ⟨"hohle-1992", "(58a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(aber nein) sie MACHT mir nicht den Garaus"
    glossedTokens := []
    context := "Hanna macht dir bestimmt den GARAUS"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("focus", "verum"), ("accent", "finite verb"), ("verumType", "F"), ("negation", "in focus"), ("scoping", "negation over VERUM")] }

def ex59a : Datum :=
  { id := "hohle1992_ex59a"
    source := ⟨"hohle-1992", "(59a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(wieso lächerlich?) HÖRT sie denn nicht damit auf?"
    glossedTokens := []
    context := "Karl hat die lächerliche Behauptung aufgestellt, daß sie damit AUFhört"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.1"), ("focus", "verum"), ("accent", "finite verb"), ("verumType", "F"), ("negation", "in focus"), ("scoping", "negation over VERUM"), ("clauseType", "polar interrogative")] }

def ex62a : Datum :=
  { id := "hohle1992_ex62a"
    source := ⟨"hohle-1992", "(62a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber Hanna denkt, er hört ihr NICHT zu"
    glossedTokens := []
    context := "ich hoffe, daß Karl ihr ZUhört"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.2"), ("focus", "negation"), ("accent", "negation particle")] }

def ex64a : Datum :=
  { id := "hohle1992_ex64a"
    source := ⟨"hohle-1992", "(64a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(ja) er HÖRT ihr zu"
    glossedTokens := []
    context := "ich hoffe, er hört ihr ZU"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("focus", "verum"), ("accent", "finite verb")] }

def ex64b : Datum :=
  { id := "hohle1992_ex64b"
    source := ⟨"hohle-1992", "(64b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(nein) er hört ihr NICHT zu"
    glossedTokens := []
    context := "ich hoffe, er hört ihr ZU"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("focus", "negation"), ("accent", "negation particle")] }

def ex64c : Datum :=
  { id := "hohle1992_ex64c"
    source := ⟨"hohle-1992", "(64c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(nein) er HÖRT ihr nicht zu"
    glossedTokens := []
    context := "ich hoffe, er hört ihr ZU"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "6.3"), ("focus", "verum"), ("accent", "finite verb"), ("negation", "in focus")] }

def ex68a : Datum :=
  { id := "hohle1992_ex68a"
    source := ⟨"hohle-1992", "(68a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ich hoffe, sie HÖRT damit auf"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "second")] }

def ex68b : Datum :=
  { id := "hohle1992_ex68b"
    source := ⟨"hohle-1992", "(68b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ich hoffe, daß sie damit aufHÖRT"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "none"), ("accent", "finite verb"), ("verbPosition", "final")] }

def ex68c : Datum :=
  { id := "hohle1992_ex68c"
    source := ⟨"hohle-1992", "(68c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ich hoffe, daß sie damit AUFhört"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "content"), ("accent", "verb particle"), ("verbPosition", "final")] }

def ex70a : Datum :=
  { id := "hohle1992_ex70a"
    source := ⟨"hohle-1992", "(70a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hanna fürchtet, er LIEST ihr die Leviten"
    glossedTokens := []
    context := "ich kann mir nicht vorstellen, daß er Hanna die LEVITEN liest"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "second")] }

def ex70b : Datum :=
  { id := "hohle1992_ex70b"
    source := ⟨"hohle-1992", "(70b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hanna fürchtet, daß er ihr die Leviten LIEST"
    glossedTokens := []
    context := "ich kann mir nicht vorstellen, daß er Hanna die LEVITEN liest"
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "none"), ("accent", "finite verb"), ("verbPosition", "final")] }

def ex71a : Datum :=
  { id := "hohle1992_ex71a"
    source := ⟨"hohle-1992", "(71a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Karl meint, sie IST in Rom"
    glossedTokens := []
    context := "ich möchte wissen, ob sie in ROM ist"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "verum"), ("accent", "copula"), ("verbPosition", "second")] }

def ex71b : Datum :=
  { id := "hohle1992_ex71b"
    source := ⟨"hohle-1992", "(71b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Karl meint, daß sie in Rom IST"
    glossedTokens := []
    context := "ich möchte wissen, ob sie in ROM ist"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "verum"), ("accent", "copula"), ("verbPosition", "final")] }

def ex72a : Datum :=
  { id := "hohle1992_ex72a"
    source := ⟨"hohle-1992", "(72a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hanna meint, er SCHREIBT ein Drehbuch"
    glossedTokens := []
    context := "ich möchte wissen, ob Karl ein DREHBUCH schreibt"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "second")] }

def ex72b : Datum :=
  { id := "hohle1992_ex72b"
    source := ⟨"hohle-1992", "(72b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hanna meint, daß er ein Drehbuch SCHREIBT"
    glossedTokens := []
    context := "ich möchte wissen, ob Karl ein DREHBUCH schreibt"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "7"), ("focus", "verum"), ("accent", "finite verb"), ("verbPosition", "final")] }

def ex77a : Datum :=
  { id := "hohle1992_ex77a"
    source := ⟨"hohle-1992", "(77a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber jeder, der WO das Buch gelesen hat, ist davon begeistert"
    glossedTokens := []
    context := "ich kenne nur wenige Leute, die (wo) dieses Buch gelesen haben"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.1"), ("focus", "verum"), ("accent", "relative particle"), ("verumType", "C"), ("variety", "dialect with relative particle")] }

def ex78a : Datum :=
  { id := "hohle1992_ex78a"
    source := ⟨"hohle-1992", "(78a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jetzt möchte ich wissen, mit wem DAß du getanzt hast"
    glossedTokens := []
    context := "du hast mir erzählt, mit wem (daß) du NICHT getanzt hast"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.1"), ("focus", "verum"), ("accent", "complementizer"), ("verumType", "C"), ("variety", "dialect with interrogative particle")] }

def ex79a : Datum :=
  { id := "hohle1992_ex79a"
    source := ⟨"hohle-1992", "(79a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jetzt möchte ich wissen, wen DAß du reingelegt hast"
    glossedTokens := []
    context := "du hast mir erzählt, wen (daß) du NICHT reingelegt hast"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.1"), ("focus", "verum"), ("accent", "complementizer"), ("verumType", "C"), ("variety", "dialect with interrogative particle")] }

def ex80a : Datum :=
  { id := "hohle1992_ex80a"
    source := ⟨"hohle-1992", "(80a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jeder, DER wo das Buch gelesen hat, ist davon begeistert"
    glossedTokens := []
    context := "ich kenne nur wenige Leute, die (wo) dieses Buch gelesen haben"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.1"), ("focus", "none"), ("accent", "relative pronoun"), ("variety", "dialect with relative particle")] }

def ex81 : Datum :=
  { id := "hohle1992_ex81"
    source := ⟨"hohle-1992", "(81)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "WER hat den Hund (denn) getreten?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.1"), ("focus", "none"), ("accent", "interrogative pronoun"), ("verbPosition", "second")] }

def ex82a : Datum :=
  { id := "hohle1992_ex82a"
    source := ⟨"hohle-1992", "(82a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber jeder, DER das Buch gelesen hat, ist davon begeistert"
    glossedTokens := []
    context := "ich kenne nur wenige Leute, die dieses Buch gelesen haben"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.2"), ("focus", "verum"), ("accent", "relative pronoun"), ("verumType", "RW")] }

def ex83a : Datum :=
  { id := "hohle1992_ex83a"
    source := ⟨"hohle-1992", "(83a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jetzt möchte ich wissen, WEN du reingelegt hast"
    glossedTokens := []
    context := "du hast mir erzählt, wen du NICHT reingelegt hast"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.2"), ("focus", "verum"), ("accent", "interrogative pronoun"), ("verumType", "RW")] }

def ex84a : Datum :=
  { id := "hohle1992_ex84a"
    source := ⟨"hohle-1992", "(84a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber die paar Leute, mit DENEN sie getanzt hat, sind völlig hingerissen"
    glossedTokens := []
    context := "Hanna tanzt nur ganz selten"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.2"), ("focus", "verum"), ("accent", "relative phrase"), ("verumType", "RW")] }

def ex85a : Datum :=
  { id := "hohle1992_ex85a"
    source := ⟨"hohle-1992", "(85a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jetzt möchte ich wissen, mit WEM du getanzt hast"
    glossedTokens := []
    context := "du hast mir erzählt, mit wem du NICHT getanzt hast"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.2"), ("focus", "verum"), ("accent", "interrogative phrase"), ("verumType", "RW")] }

def ex86a : Datum :=
  { id := "hohle1992_ex86a"
    source := ⟨"hohle-1992", "(86a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aber ein Autor, DESSEN Werk ich gelesen habe, ist Chr. Morgenstern"
    glossedTokens := []
    context := "ich habe von den meisten Schriftstellern so gut wie nichts gelesen"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.2"), ("focus", "verum"), ("accent", "relative phrase"), ("verumType", "RW")] }

def ex87a : Datum :=
  { id := "hohle1992_ex87a"
    source := ⟨"hohle-1992", "(87a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "nun sag doch mal, WESSEN Aufsatz du gelesen hast"
    glossedTokens := []
    context := "du hast also weder Karls noch Hannas Aufsatz gelesen"
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("section", "9.2"), ("focus", "verum"), ("accent", "interrogative phrase"), ("verumType", "RW")] }

def all : List Datum := [ex1b, ex2b, ex4a, ex5a, ex6a, ex7a, ex8a, ex9a, ex10a, ex11a, ex12a, ex45a, ex45b, ex47a, ex47b, ex48a, ex48b, ex50a, ex50b, ex51a, ex51b, ex52a, ex55a, ex55b, ex57a, ex58a, ex59a, ex62a, ex64a, ex64b, ex64c, ex68a, ex68b, ex68c, ex70a, ex70b, ex71a, ex71b, ex72a, ex72b, ex77a, ex78a, ex79a, ex80a, ex81, ex82a, ex83a, ex84a, ex85a, ex86a, ex87a]

end Hohle1992.Examples
