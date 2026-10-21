module

public import Linglib.Data.Examples.Schema

/-!
# `Schwarz2009` — typed example data

Auto-generated from `Linglib/Data/Examples/Schwarz2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schwarz2009.Examples`.
-/

@[expose] public section

namespace Schwarz2009.Examples

def ex25_weak : Datum :=
  { id := "schwarz2009_ex25_weak"
    source := ⟨"schwarz-2009", "(25)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "In der New Yorker Bibliothek gibt es ein Buch über Topinambur. Neulich war ich dort und habe im Buch nach einer Antwort auf die Frage gesucht, ob man Topinambur grillen kann."
    glossedTokens := [("In", "In"), ("der", "the"), ("New", "New"), ("Yorker", "York"), ("Bibliothek", "library"), ("gibt", "exists"), ("es", "EXPL"), ("ein", "a"), ("Buch", "book"), ("über", "about"), ("Topinambur", "topinambur"), ("Neulich", "Recently"), ("war", "was"), ("ich", "I"), ("dort", "there"), ("und", "and"), ("habe", "have"), ("im", "in-the.WEAK"), ("Buch", "book"), ("nach", "for"), ("einer", "an"), ("Antwort", "answer"), ("auf", "to"), ("die", "the"), ("Frage", "question"), ("gesucht", "searched"), ("ob", "whether"), ("man", "one"), ("Topinambur", "topinambur"), ("grillen", "grill"), ("kann", "can")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex25_strong : Datum :=
  { id := "schwarz2009_ex25_strong"
    source := ⟨"schwarz-2009", "(25)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "In der New Yorker Bibliothek gibt es ein Buch über Topinambur. Neulich war ich dort und habe in dem Buch nach einer Antwort auf die Frage gesucht, ob man Topinambur grillen kann."
    glossedTokens := [("In", "In"), ("der", "the"), ("New", "New"), ("Yorker", "York"), ("Bibliothek", "library"), ("gibt", "exists"), ("es", "EXPL"), ("ein", "a"), ("Buch", "book"), ("über", "about"), ("Topinambur", "topinambur"), ("Neulich", "Recently"), ("war", "was"), ("ich", "I"), ("dort", "there"), ("und", "and"), ("habe", "have"), ("in", "in"), ("dem", "the.STRONG"), ("Buch", "book"), ("nach", "for"), ("einer", "an"), ("Antwort", "answer"), ("auf", "to"), ("die", "the"), ("Frage", "question"), ("gesucht", "searched"), ("ob", "whether"), ("man", "one"), ("Topinambur", "topinambur"), ("grillen", "grill"), ("kann", "can")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex26_weak : Datum :=
  { id := "schwarz2009_ex26_weak"
    source := ⟨"schwarz-2009", "(26)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bei der Gutshausbesichtigung hat mich eines der Zimmer besonders beeindruckt. Angeblich hat Goethe im Jahr 1810 eine Nacht im Zimmer verbracht."
    glossedTokens := [("Bei", "During"), ("der", "the"), ("Gutshausbesichtigung", "mansion tour"), ("hat", "has"), ("mich", "me"), ("eines", "one"), ("der", "the.GEN"), ("Zimmer", "rooms"), ("besonders", "especially"), ("beeindruckt", "impressed"), ("Angeblich", "Supposedly"), ("hat", "has"), ("Goethe", "Goethe"), ("im", "in-the.WEAK"), ("Jahr", "year"), ("1810", "1810"), ("eine", "a"), ("Nacht", "night"), ("im", "in-the.WEAK"), ("Zimmer", "room"), ("verbracht", "spent")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex26_strong : Datum :=
  { id := "schwarz2009_ex26_strong"
    source := ⟨"schwarz-2009", "(26)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Bei der Gutshausbesichtigung hat mich eines der Zimmer besonders beeindruckt. Angeblich hat Goethe im Jahr 1810 eine Nacht in dem Zimmer verbracht."
    glossedTokens := [("Bei", "During"), ("der", "the"), ("Gutshausbesichtigung", "mansion tour"), ("hat", "has"), ("mich", "me"), ("eines", "one"), ("der", "the.GEN"), ("Zimmer", "rooms"), ("besonders", "especially"), ("beeindruckt", "impressed"), ("Angeblich", "Supposedly"), ("hat", "has"), ("Goethe", "Goethe"), ("im", "in-the.WEAK"), ("Jahr", "year"), ("1810", "1810"), ("eine", "a"), ("Nacht", "night"), ("in", "in"), ("dem", "the.STRONG"), ("Zimmer", "room"), ("verbracht", "spent")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex28_weak : Datum :=
  { id := "schwarz2009_ex28_weak"
    source := ⟨"schwarz-2009", "(28)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Maria hat einen Ornithologen ins Seminar eingeladen. Ich halte vom Mann nicht sehr viel."
    glossedTokens := [("Maria", "Maria"), ("hat", "has"), ("einen", "an"), ("Ornithologen", "ornithologist"), ("ins", "to-the"), ("Seminar", "seminar"), ("eingeladen", "invited"), ("Ich", "I"), ("halte", "hold"), ("vom", "of-the.WEAK"), ("Mann", "man"), ("nicht", "not"), ("sehr", "very"), ("viel", "much")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex28_strong : Datum :=
  { id := "schwarz2009_ex28_strong"
    source := ⟨"schwarz-2009", "(28)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Maria hat einen Ornithologen ins Seminar eingeladen. Ich halte von dem Mann nicht sehr viel."
    glossedTokens := [("Maria", "Maria"), ("hat", "has"), ("einen", "an"), ("Ornithologen", "ornithologist"), ("ins", "to-the"), ("Seminar", "seminar"), ("eingeladen", "invited"), ("Ich", "I"), ("halte", "hold"), ("von", "of"), ("dem", "the.STRONG"), ("Mann", "man"), ("nicht", "not"), ("sehr", "very"), ("viel", "much")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex29_weak : Datum :=
  { id := "schwarz2009_ex29_weak"
    source := ⟨"schwarz-2009", "(29)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans hat schon wieder angerufen. Ich will vom Idioten nichts mehr hören."
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("schon", "already"), ("wieder", "again"), ("angerufen", "called"), ("Ich", "I"), ("will", "want"), ("vom", "of-the.WEAK"), ("Idioten", "idiot"), ("nichts", "not"), ("mehr", "more"), ("hören", "hear")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex29_strong : Datum :=
  { id := "schwarz2009_ex29_strong"
    source := ⟨"schwarz-2009", "(29)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans hat schon wieder angerufen. Ich will von dem Idioten nichts mehr hören."
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("schon", "already"), ("wieder", "again"), ("angerufen", "called"), ("Ich", "I"), ("will", "want"), ("von", "of"), ("dem", "the.STRONG"), ("Idioten", "idiot"), ("nichts", "not"), ("mehr", "more"), ("hören", "hear")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes")] }

def ex31_weak : Datum :=
  { id := "schwarz2009_ex31_weak"
    source := ⟨"schwarz-2009", "(31)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jedes Mal, wenn ein Ornithologe im Seminar einen Vortrag hält, wollen die Studenten vom Mann wissen, ob Vogelgesang grammatischen Regeln folgt."
    glossedTokens := [("Jedes", "Every"), ("Mal", "time"), ("wenn", "when"), ("ein", "an"), ("Ornithologe", "ornithologist"), ("im", "in-the.WEAK"), ("Seminar", "seminar"), ("einen", "a"), ("Vortrag", "lecture"), ("hält", "holds"), ("wollen", "want"), ("die", "the"), ("Studenten", "students"), ("vom", "of-the.WEAK"), ("Mann", "man"), ("wissen", "know"), ("ob", "whether"), ("Vogelgesang", "bird singing"), ("grammatischen", "grammatical"), ("Regeln", "rules"), ("folgt", "follows")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes"), ("covarying", "yes")] }

def ex31_strong : Datum :=
  { id := "schwarz2009_ex31_strong"
    source := ⟨"schwarz-2009", "(31)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jedes Mal, wenn ein Ornithologe im Seminar einen Vortrag hält, wollen die Studenten von dem Mann wissen, ob Vogelgesang grammatischen Regeln folgt."
    glossedTokens := [("Jedes", "Every"), ("Mal", "time"), ("wenn", "when"), ("ein", "an"), ("Ornithologe", "ornithologist"), ("im", "in-the.WEAK"), ("Seminar", "seminar"), ("einen", "a"), ("Vortrag", "lecture"), ("hält", "holds"), ("wollen", "want"), ("die", "the"), ("Studenten", "students"), ("von", "of"), ("dem", "the.STRONG"), ("Mann", "man"), ("wissen", "know"), ("ob", "whether"), ("Vogelgesang", "bird singing"), ("grammatischen", "grammatical"), ("Regeln", "rules"), ("folgt", "follows")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "anaphoric"), ("unique", "no"), ("antecedent", "yes"), ("covarying", "yes")] }

def ex40_weak : Datum :=
  { id := "schwarz2009_ex40_weak"
    source := ⟨"schwarz-2009", "(40)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Buch, das du suchst, steht im Glasschrank."
    glossedTokens := [("Das", "the"), ("Buch", "book"), ("das", "that"), ("du", "you"), ("suchst", "look for"), ("steht", "stands"), ("im", "in-the.WEAK"), ("Glasschrank", "glass-cabinet")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "immediateSituation"), ("unique", "yes"), ("antecedent", "no")] }

def ex40_strong : Datum :=
  { id := "schwarz2009_ex40_strong"
    source := ⟨"schwarz-2009", "(40)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Buch, das du suchst, steht in dem Glasschrank."
    glossedTokens := [("Das", "the"), ("Buch", "book"), ("das", "that"), ("du", "you"), ("suchst", "look for"), ("steht", "stands"), ("in", "in"), ("dem", "the.STRONG"), ("Glasschrank", "glass-cabinet")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "immediateSituation"), ("unique", "yes"), ("antecedent", "no")] }

def ex41_weak : Datum :=
  { id := "schwarz2009_ex41_weak"
    source := ⟨"schwarz-2009", "(41)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Einbrecher ist zum Glück vom Hund verjagt worden."
    glossedTokens := [("Der", "the"), ("Einbrecher", "burglar"), ("ist", "is"), ("zum Glück", "luckily"), ("vom", "by-the.WEAK"), ("Hund", "dog"), ("verjagt", "chase away"), ("worden", "been")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "largerSituation"), ("unique", "yes"), ("antecedent", "no")] }

def ex41_strong : Datum :=
  { id := "schwarz2009_ex41_strong"
    source := ⟨"schwarz-2009", "(41)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Einbrecher ist zum Glück von dem Hund verjagt worden."
    glossedTokens := [("Der", "the"), ("Einbrecher", "burglar"), ("ist", "is"), ("zum Glück", "luckily"), ("von", "by"), ("dem", "the.STRONG"), ("Hund", "dog"), ("verjagt", "chase away"), ("worden", "been")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "largerSituation"), ("unique", "yes"), ("antecedent", "no")] }

def ex42_weak : Datum :=
  { id := "schwarz2009_ex42_weak"
    source := ⟨"schwarz-2009", "(42)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Empfang wurde vom Bürgermeister eröffnet."
    glossedTokens := [("Der", "The"), ("Empfang", "reception"), ("wurde", "was"), ("vom", "by-the.WEAK"), ("Bürgermeister", "mayor"), ("eröffnet", "opened")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "largerSituation"), ("unique", "yes"), ("antecedent", "no")] }

def ex42_strong : Datum :=
  { id := "schwarz2009_ex42_strong"
    source := ⟨"schwarz-2009", "(42)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Empfang wurde von dem Bürgermeister eröffnet."
    glossedTokens := [("Der", "The"), ("Empfang", "reception"), ("wurde", "was"), ("von", "by"), ("dem", "the.STRONG"), ("Bürgermeister", "mayor"), ("eröffnet", "opened")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "largerSituation"), ("unique", "yes"), ("antecedent", "no")] }

def ex46a_weak : Datum :=
  { id := "schwarz2009_ex46a_weak"
    source := ⟨"schwarz-2009", "(46a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "In der Kabinettsitzung heute wird ein neuer Vorschlag vom Kanzler erwartet."
    glossedTokens := [("In", "In"), ("der", "the"), ("Kabinettsitzung", "cabinet meeting"), ("heute", "today"), ("wird", "is"), ("ein", "a"), ("neuer", "new"), ("Vorschlag", "proposal"), ("vom", "by-the.A"), ("Kanzler", "chancellor"), ("erwartet", "expected")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "largerSituation"), ("unique", "yes"), ("antecedent", "no")] }

def ex46b_weak : Datum :=
  { id := "schwarz2009_ex46b_weak"
    source := ⟨"schwarz-2009", "(46b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "In der Kabinettsitzung heute wird ein neuer Vorschlag vom Minister erwartet."
    glossedTokens := [("In", "In"), ("der", "the"), ("Kabinettsitzung", "cabinet meeting"), ("heute", "today"), ("wird", "is"), ("ein", "a"), ("neuer", "new"), ("Vorschlag", "proposal"), ("vom", "by-the.A"), ("Minister", "minister"), ("erwartet", "expected")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "largerSituation"), ("unique", "no"), ("antecedent", "no")] }

def ex48_weak : Datum :=
  { id := "schwarz2009_ex48_weak"
    source := ⟨"schwarz-2009", "(48)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jedes Mal, wenn eine Runde vorbei ist, werden die Karten vom Gewinner neu gemischt und verteilt."
    glossedTokens := [("Jedes", "Every"), ("Mal", "time"), ("wenn", "when"), ("eine", "a"), ("Runde", "round"), ("vorbei", "over"), ("ist", "is"), ("werden", "are"), ("die", "the"), ("Karten", "cards"), ("vom", "by-the.WEAK"), ("Gewinner", "winner"), ("neu", "newly"), ("gemischt", "shuffled"), ("und", "and"), ("verteilt", "dealt")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("unique", "yes"), ("antecedent", "no"), ("covarying", "yes")] }

def ex58_weak : Datum :=
  { id := "schwarz2009_ex58_weak"
    source := ⟨"schwarz-2009", "(58)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Kühlschrank war so groß, dass der Kürbis problemlos im Gemüsefach untergebracht werden konnte."
    glossedTokens := [("Der", "The"), ("Kühlschrank", "fridge"), ("war", "was"), ("so", "so"), ("groß", "big"), ("dass", "that"), ("der", "the"), ("Kürbis", "pumpkin"), ("problemlos", "without a problem"), ("im", "in-the.WEAK"), ("Gemüsefach", "crisper"), ("untergebracht", "stowed"), ("werden", "be"), ("konnte", "could")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "partWholeBridging"), ("relation", "part"), ("antecedent", "relatum")] }

def ex58_strong : Datum :=
  { id := "schwarz2009_ex58_strong"
    source := ⟨"schwarz-2009", "(58)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Kühlschrank war so groß, dass der Kürbis problemlos in dem Gemüsefach untergebracht werden konnte."
    glossedTokens := [("Der", "The"), ("Kühlschrank", "fridge"), ("war", "was"), ("so", "so"), ("groß", "big"), ("dass", "that"), ("der", "the"), ("Kürbis", "pumpkin"), ("problemlos", "without a problem"), ("in", "in"), ("dem", "the.STRONG"), ("Gemüsefach", "crisper"), ("untergebracht", "stowed"), ("werden", "be"), ("konnte", "could")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "partWholeBridging"), ("relation", "part"), ("antecedent", "relatum")] }

def ex59_weak : Datum :=
  { id := "schwarz2009_ex59_weak"
    source := ⟨"schwarz-2009", "(59)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Theaterstück missfiel dem Kritiker so sehr, dass er in seiner Besprechung kein gutes Haar am Autor ließ."
    glossedTokens := [("Das", "The"), ("Theaterstück", "play"), ("missfiel", "displeased"), ("dem", "the"), ("Kritiker", "critic"), ("so", "so"), ("sehr", "much"), ("dass", "that"), ("er", "he"), ("in", "in"), ("seiner", "his"), ("Besprechung", "review"), ("kein", "no"), ("gutes", "good"), ("Haar", "hair"), ("am", "on-the.WEAK"), ("Autor", "author"), ("ließ", "left")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "producerBridging"), ("relation", "nonPart"), ("antecedent", "relatum")] }

def ex59_strong : Datum :=
  { id := "schwarz2009_ex59_strong"
    source := ⟨"schwarz-2009", "(59)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Theaterstück missfiel dem Kritiker so sehr, dass er in seiner Besprechung kein gutes Haar an dem Autor ließ."
    glossedTokens := [("Das", "The"), ("Theaterstück", "play"), ("missfiel", "displeased"), ("dem", "the"), ("Kritiker", "critic"), ("so", "so"), ("sehr", "much"), ("dass", "that"), ("er", "he"), ("in", "in"), ("seiner", "his"), ("Besprechung", "review"), ("kein", "no"), ("gutes", "good"), ("Haar", "hair"), ("an", "on"), ("dem", "the.STRONG"), ("Autor", "author"), ("ließ", "left")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "producerBridging"), ("relation", "nonPart"), ("antecedent", "relatum")] }

def ex62_weak : Datum :=
  { id := "schwarz2009_ex62_weak"
    source := ⟨"schwarz-2009", "(62)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jeder, der einen Roman gekauft hat, hatte schon einmal eine Kurzgeschichte vom Autor gelesen."
    glossedTokens := [("Jeder", "Everyone"), ("der", "that"), ("einen", "a"), ("Roman", "novel"), ("gekauft", "bought"), ("hat", "has"), ("hatte", "had"), ("schon", "already"), ("einmal", "once"), ("eine", "a"), ("Kurzgeschichte", "short story"), ("vom", "by-the.WEAK"), ("Autor", "author"), ("gelesen", "read")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "producerBridging"), ("relation", "nonPart"), ("antecedent", "relatum"), ("covarying", "yes")] }

def ex62_strong : Datum :=
  { id := "schwarz2009_ex62_strong"
    source := ⟨"schwarz-2009", "(62)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jeder, der einen Roman gekauft hat, hatte schon einmal eine Kurzgeschichte von dem Autor gelesen."
    glossedTokens := [("Jeder", "Everyone"), ("der", "that"), ("einen", "a"), ("Roman", "novel"), ("gekauft", "bought"), ("hat", "has"), ("hatte", "had"), ("schon", "already"), ("einmal", "once"), ("eine", "a"), ("Kurzgeschichte", "short story"), ("von", "by"), ("dem", "the.STRONG"), ("Autor", "author"), ("gelesen", "read")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "producerBridging"), ("relation", "nonPart"), ("antecedent", "relatum"), ("covarying", "yes")] }

def ex63_weak : Datum :=
  { id := "schwarz2009_ex63_weak"
    source := ⟨"schwarz-2009", "(63)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Jeder Student, der ein Auto parkte, brachte einen Parkschein am Rückspiegel an."
    glossedTokens := [("Jeder", "Every"), ("Student", "student"), ("der", "that"), ("ein", "a"), ("Auto", "car"), ("parkte", "parked"), ("brachte", "attached"), ("einen", "a"), ("Parkschein", "parking-pass"), ("am", "on-the.WEAK"), ("Rückspiegel", "rear view mirror"), ("an", "PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "partWholeBridging"), ("relation", "part"), ("antecedent", "relatum"), ("covarying", "yes")] }

def ex231_weak : Datum :=
  { id := "schwarz2009_ex231_weak"
    source := ⟨"schwarz-2009", "(231)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "An jedem Bahnhof, in den unser Zug einfuhr, wurde mir ein Brief vom Bürgermeister überreicht."
    glossedTokens := [("An", "At"), ("jedem", "every"), ("Bahnhof", "train station"), ("in", "in"), ("den", "which"), ("unser", "our"), ("Zug", "train"), ("einfuhr", "entered into"), ("wurde", "was"), ("mir", "I"), ("ein", "a"), ("Brief", "letter"), ("vom", "from-the.WEAK"), ("Bürgermeister", "mayor"), ("überreicht", "handed")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "largerSituation"), ("relation", "part"), ("antecedent", "other"), ("covarying", "yes")] }

def ex231_strong : Datum :=
  { id := "schwarz2009_ex231_strong"
    source := ⟨"schwarz-2009", "(231)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "An jedem Bahnhof, in den unser Zug einfuhr, wurde mir ein Brief von dem Bürgermeister überreicht."
    glossedTokens := [("An", "At"), ("jedem", "every"), ("Bahnhof", "train station"), ("in", "in"), ("den", "which"), ("unser", "our"), ("Zug", "train"), ("einfuhr", "entered into"), ("wurde", "was"), ("mir", "I"), ("ein", "a"), ("Brief", "letter"), ("von", "from"), ("dem", "the.STRONG"), ("Bürgermeister", "mayor"), ("überreicht", "handed")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "largerSituation"), ("relation", "part"), ("antecedent", "other"), ("covarying", "yes")] }

def ex275_weak : Datum :=
  { id := "schwarz2009_ex275_weak"
    source := ⟨"schwarz-2009", "(275)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans entdeckte in der Bibliothek einen Roman über den Hudson. Dabei fiel ihm ein, dass er vor langer Zeit einmal einen Vortrag vom Autor besucht hatte."
    glossedTokens := [("Hans", "Hans"), ("entdeckte", "discovered"), ("in", "in"), ("der", "the"), ("Bibliothek", "library"), ("einen", "a"), ("Roman", "novel"), ("über", "about"), ("den", "the"), ("Hudson", "Hudson"), ("Dabei", "In the process"), ("fiel", "remembered"), ("ihm", "he.DAT"), ("ein", "PART"), ("dass", "that"), ("er", "he"), ("vor langer Zeit", "a long time ago"), ("einmal", "once"), ("einen", "a"), ("Vortrag", "lecture"), ("vom", "by-the.WEAK"), ("Autor", "author"), ("besucht", "attended"), ("hatte", "had")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "weak"), ("use", "producerBridging"), ("relation", "nonPart"), ("antecedent", "relatum")] }

def ex275_strong : Datum :=
  { id := "schwarz2009_ex275_strong"
    source := ⟨"schwarz-2009", "(275)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans entdeckte in der Bibliothek einen Roman über den Hudson. Dabei fiel ihm ein, dass er vor langer Zeit einmal einen Vortrag von dem Autor besucht hatte."
    glossedTokens := [("Hans", "Hans"), ("entdeckte", "discovered"), ("in", "in"), ("der", "the"), ("Bibliothek", "library"), ("einen", "a"), ("Roman", "novel"), ("über", "about"), ("den", "the"), ("Hudson", "Hudson"), ("Dabei", "In the process"), ("fiel", "remembered"), ("ihm", "he.DAT"), ("ein", "PART"), ("dass", "that"), ("er", "he"), ("vor langer Zeit", "a long time ago"), ("einmal", "once"), ("einen", "a"), ("Vortrag", "lecture"), ("von", "by"), ("dem", "the.STRONG"), ("Autor", "author"), ("besucht", "attended"), ("hatte", "had")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "producerBridging"), ("relation", "nonPart"), ("antecedent", "relatum")] }

def all : List Datum := [ex25_weak, ex25_strong, ex26_weak, ex26_strong, ex28_weak, ex28_strong, ex29_weak, ex29_strong, ex31_weak, ex31_strong, ex40_weak, ex40_strong, ex41_weak, ex41_strong, ex42_weak, ex42_strong, ex46a_weak, ex46b_weak, ex48_weak, ex58_weak, ex58_strong, ex59_weak, ex59_strong, ex62_weak, ex62_strong, ex63_weak, ex231_weak, ex231_strong, ex275_weak, ex275_strong]

end Schwarz2009.Examples
