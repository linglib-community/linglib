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
    glossedWords := [⟨[['I', 'n']], [['I', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['N', 'e', 'w']], [['N', 'e', 'w']]⟩, ⟨[['Y', 'o', 'r', 'k', 'e', 'r']], [['Y', 'o', 'r', 'k']]⟩, ⟨[['B', 'i', 'b', 'l', 'i', 'o', 't', 'h', 'e', 'k']], [['l', 'i', 'b', 'r', 'a', 'r', 'y']]⟩, ⟨[['g', 'i', 'b', 't']], [['e', 'x', 'i', 's', 't', 's']]⟩, ⟨[['e', 's']], [['E', 'X', 'P', 'L']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'u', 'c', 'h']], [['b', 'o', 'o', 'k']]⟩, ⟨[['ü', 'b', 'e', 'r']], [['a', 'b', 'o', 'u', 't']]⟩, ⟨[['T', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']], [['t', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']]⟩, ⟨[['N', 'e', 'u', 'l', 'i', 'c', 'h']], [['R', 'e', 'c', 'e', 'n', 't', 'l', 'y']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['i', 'c', 'h']], [['I']]⟩, ⟨[['d', 'o', 'r', 't']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['u', 'n', 'd']], [['a', 'n', 'd']]⟩, ⟨[['h', 'a', 'b', 'e']], [['h', 'a', 'v', 'e']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['B', 'u', 'c', 'h']], [['b', 'o', 'o', 'k']]⟩, ⟨[['n', 'a', 'c', 'h']], [['f', 'o', 'r']]⟩, ⟨[['e', 'i', 'n', 'e', 'r']], [['a', 'n']]⟩, ⟨[['A', 'n', 't', 'w', 'o', 'r', 't']], [['a', 'n', 's', 'w', 'e', 'r']]⟩, ⟨[['a', 'u', 'f']], [['t', 'o']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['F', 'r', 'a', 'g', 'e']], [['q', 'u', 'e', 's', 't', 'i', 'o', 'n']]⟩, ⟨[['g', 'e', 's', 'u', 'c', 'h', 't']], [['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd']]⟩, ⟨[['o', 'b']], [['w', 'h', 'e', 't', 'h', 'e', 'r']]⟩, ⟨[['m', 'a', 'n']], [['o', 'n', 'e']]⟩, ⟨[['T', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']], [['t', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']]⟩, ⟨[['g', 'r', 'i', 'l', 'l', 'e', 'n']], [['g', 'r', 'i', 'l', 'l']]⟩, ⟨[['k', 'a', 'n', 'n']], [['c', 'a', 'n']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['I', 'n']], [['I', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['N', 'e', 'w']], [['N', 'e', 'w']]⟩, ⟨[['Y', 'o', 'r', 'k', 'e', 'r']], [['Y', 'o', 'r', 'k']]⟩, ⟨[['B', 'i', 'b', 'l', 'i', 'o', 't', 'h', 'e', 'k']], [['l', 'i', 'b', 'r', 'a', 'r', 'y']]⟩, ⟨[['g', 'i', 'b', 't']], [['e', 'x', 'i', 's', 't', 's']]⟩, ⟨[['e', 's']], [['E', 'X', 'P', 'L']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'u', 'c', 'h']], [['b', 'o', 'o', 'k']]⟩, ⟨[['ü', 'b', 'e', 'r']], [['a', 'b', 'o', 'u', 't']]⟩, ⟨[['T', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']], [['t', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']]⟩, ⟨[['N', 'e', 'u', 'l', 'i', 'c', 'h']], [['R', 'e', 'c', 'e', 'n', 't', 'l', 'y']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['i', 'c', 'h']], [['I']]⟩, ⟨[['d', 'o', 'r', 't']], [['t', 'h', 'e', 'r', 'e']]⟩, ⟨[['u', 'n', 'd']], [['a', 'n', 'd']]⟩, ⟨[['h', 'a', 'b', 'e']], [['h', 'a', 'v', 'e']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['B', 'u', 'c', 'h']], [['b', 'o', 'o', 'k']]⟩, ⟨[['n', 'a', 'c', 'h']], [['f', 'o', 'r']]⟩, ⟨[['e', 'i', 'n', 'e', 'r']], [['a', 'n']]⟩, ⟨[['A', 'n', 't', 'w', 'o', 'r', 't']], [['a', 'n', 's', 'w', 'e', 'r']]⟩, ⟨[['a', 'u', 'f']], [['t', 'o']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['F', 'r', 'a', 'g', 'e']], [['q', 'u', 'e', 's', 't', 'i', 'o', 'n']]⟩, ⟨[['g', 'e', 's', 'u', 'c', 'h', 't']], [['s', 'e', 'a', 'r', 'c', 'h', 'e', 'd']]⟩, ⟨[['o', 'b']], [['w', 'h', 'e', 't', 'h', 'e', 'r']]⟩, ⟨[['m', 'a', 'n']], [['o', 'n', 'e']]⟩, ⟨[['T', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']], [['t', 'o', 'p', 'i', 'n', 'a', 'm', 'b', 'u', 'r']]⟩, ⟨[['g', 'r', 'i', 'l', 'l', 'e', 'n']], [['g', 'r', 'i', 'l', 'l']]⟩, ⟨[['k', 'a', 'n', 'n']], [['c', 'a', 'n']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['B', 'e', 'i']], [['D', 'u', 'r', 'i', 'n', 'g']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['G', 'u', 't', 's', 'h', 'a', 'u', 's', 'b', 'e', 's', 'i', 'c', 'h', 't', 'i', 'g', 'u', 'n', 'g']], [['m', 'a', 'n', 's', 'i', 'o', 'n', ' ', 't', 'o', 'u', 'r']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['m', 'i', 'c', 'h']], [['m', 'e']]⟩, ⟨[['e', 'i', 'n', 'e', 's']], [['o', 'n', 'e']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e', '.', 'G', 'E', 'N']]⟩, ⟨[['Z', 'i', 'm', 'm', 'e', 'r']], [['r', 'o', 'o', 'm', 's']]⟩, ⟨[['b', 'e', 's', 'o', 'n', 'd', 'e', 'r', 's']], [['e', 's', 'p', 'e', 'c', 'i', 'a', 'l', 'l', 'y']]⟩, ⟨[['b', 'e', 'e', 'i', 'n', 'd', 'r', 'u', 'c', 'k', 't']], [['i', 'm', 'p', 'r', 'e', 's', 's', 'e', 'd']]⟩, ⟨[['A', 'n', 'g', 'e', 'b', 'l', 'i', 'c', 'h']], [['S', 'u', 'p', 'p', 'o', 's', 'e', 'd', 'l', 'y']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['G', 'o', 'e', 't', 'h', 'e']], [['G', 'o', 'e', 't', 'h', 'e']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['J', 'a', 'h', 'r']], [['y', 'e', 'a', 'r']]⟩, ⟨[['1', '8', '1', '0']], [['1', '8', '1', '0']]⟩, ⟨[['e', 'i', 'n', 'e']], [['a']]⟩, ⟨[['N', 'a', 'c', 'h', 't']], [['n', 'i', 'g', 'h', 't']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['Z', 'i', 'm', 'm', 'e', 'r']], [['r', 'o', 'o', 'm']]⟩, ⟨[['v', 'e', 'r', 'b', 'r', 'a', 'c', 'h', 't']], [['s', 'p', 'e', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['B', 'e', 'i']], [['D', 'u', 'r', 'i', 'n', 'g']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['G', 'u', 't', 's', 'h', 'a', 'u', 's', 'b', 'e', 's', 'i', 'c', 'h', 't', 'i', 'g', 'u', 'n', 'g']], [['m', 'a', 'n', 's', 'i', 'o', 'n', ' ', 't', 'o', 'u', 'r']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['m', 'i', 'c', 'h']], [['m', 'e']]⟩, ⟨[['e', 'i', 'n', 'e', 's']], [['o', 'n', 'e']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e', '.', 'G', 'E', 'N']]⟩, ⟨[['Z', 'i', 'm', 'm', 'e', 'r']], [['r', 'o', 'o', 'm', 's']]⟩, ⟨[['b', 'e', 's', 'o', 'n', 'd', 'e', 'r', 's']], [['e', 's', 'p', 'e', 'c', 'i', 'a', 'l', 'l', 'y']]⟩, ⟨[['b', 'e', 'e', 'i', 'n', 'd', 'r', 'u', 'c', 'k', 't']], [['i', 'm', 'p', 'r', 'e', 's', 's', 'e', 'd']]⟩, ⟨[['A', 'n', 'g', 'e', 'b', 'l', 'i', 'c', 'h']], [['S', 'u', 'p', 'p', 'o', 's', 'e', 'd', 'l', 'y']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['G', 'o', 'e', 't', 'h', 'e']], [['G', 'o', 'e', 't', 'h', 'e']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['J', 'a', 'h', 'r']], [['y', 'e', 'a', 'r']]⟩, ⟨[['1', '8', '1', '0']], [['1', '8', '1', '0']]⟩, ⟨[['e', 'i', 'n', 'e']], [['a']]⟩, ⟨[['N', 'a', 'c', 'h', 't']], [['n', 'i', 'g', 'h', 't']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['Z', 'i', 'm', 'm', 'e', 'r']], [['r', 'o', 'o', 'm']]⟩, ⟨[['v', 'e', 'r', 'b', 'r', 'a', 'c', 'h', 't']], [['s', 'p', 'e', 'n', 't']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a', 'n']]⟩, ⟨[['O', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'e', 'n']], [['o', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'i', 's', 't']]⟩, ⟨[['i', 'n', 's']], [['t', 'o'], ['t', 'h', 'e']]⟩, ⟨[['S', 'e', 'm', 'i', 'n', 'a', 'r']], [['s', 'e', 'm', 'i', 'n', 'a', 'r']]⟩, ⟨[['e', 'i', 'n', 'g', 'e', 'l', 'a', 'd', 'e', 'n']], [['i', 'n', 'v', 'i', 't', 'e', 'd']]⟩, ⟨[['I', 'c', 'h']], [['I']]⟩, ⟨[['h', 'a', 'l', 't', 'e']], [['h', 'o', 'l', 'd']]⟩, ⟨[['v', 'o', 'm']], [['o', 'f'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['M', 'a', 'n', 'n']], [['m', 'a', 'n']]⟩, ⟨[['n', 'i', 'c', 'h', 't']], [['n', 'o', 't']]⟩, ⟨[['s', 'e', 'h', 'r']], [['v', 'e', 'r', 'y']]⟩, ⟨[['v', 'i', 'e', 'l']], [['m', 'u', 'c', 'h']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['M', 'a', 'r', 'i', 'a']], [['M', 'a', 'r', 'i', 'a']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a', 'n']]⟩, ⟨[['O', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'e', 'n']], [['o', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'i', 's', 't']]⟩, ⟨[['i', 'n', 's']], [['t', 'o'], ['t', 'h', 'e']]⟩, ⟨[['S', 'e', 'm', 'i', 'n', 'a', 'r']], [['s', 'e', 'm', 'i', 'n', 'a', 'r']]⟩, ⟨[['e', 'i', 'n', 'g', 'e', 'l', 'a', 'd', 'e', 'n']], [['i', 'n', 'v', 'i', 't', 'e', 'd']]⟩, ⟨[['I', 'c', 'h']], [['I']]⟩, ⟨[['h', 'a', 'l', 't', 'e']], [['h', 'o', 'l', 'd']]⟩, ⟨[['v', 'o', 'n']], [['o', 'f']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['M', 'a', 'n', 'n']], [['m', 'a', 'n']]⟩, ⟨[['n', 'i', 'c', 'h', 't']], [['n', 'o', 't']]⟩, ⟨[['s', 'e', 'h', 'r']], [['v', 'e', 'r', 'y']]⟩, ⟨[['v', 'i', 'e', 'l']], [['m', 'u', 'c', 'h']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['H', 'a', 'n', 's']], [['H', 'a', 'n', 's']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['s', 'c', 'h', 'o', 'n']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['w', 'i', 'e', 'd', 'e', 'r']], [['a', 'g', 'a', 'i', 'n']]⟩, ⟨[['a', 'n', 'g', 'e', 'r', 'u', 'f', 'e', 'n']], [['c', 'a', 'l', 'l', 'e', 'd']]⟩, ⟨[['I', 'c', 'h']], [['I']]⟩, ⟨[['w', 'i', 'l', 'l']], [['w', 'a', 'n', 't']]⟩, ⟨[['v', 'o', 'm']], [['o', 'f'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['I', 'd', 'i', 'o', 't', 'e', 'n']], [['i', 'd', 'i', 'o', 't']]⟩, ⟨[['n', 'i', 'c', 'h', 't', 's']], [['n', 'o', 't']]⟩, ⟨[['m', 'e', 'h', 'r']], [['m', 'o', 'r', 'e']]⟩, ⟨[['h', 'ö', 'r', 'e', 'n']], [['h', 'e', 'a', 'r']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['H', 'a', 'n', 's']], [['H', 'a', 'n', 's']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['s', 'c', 'h', 'o', 'n']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['w', 'i', 'e', 'd', 'e', 'r']], [['a', 'g', 'a', 'i', 'n']]⟩, ⟨[['a', 'n', 'g', 'e', 'r', 'u', 'f', 'e', 'n']], [['c', 'a', 'l', 'l', 'e', 'd']]⟩, ⟨[['I', 'c', 'h']], [['I']]⟩, ⟨[['w', 'i', 'l', 'l']], [['w', 'a', 'n', 't']]⟩, ⟨[['v', 'o', 'n']], [['o', 'f']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['I', 'd', 'i', 'o', 't', 'e', 'n']], [['i', 'd', 'i', 'o', 't']]⟩, ⟨[['n', 'i', 'c', 'h', 't', 's']], [['n', 'o', 't']]⟩, ⟨[['m', 'e', 'h', 'r']], [['m', 'o', 'r', 'e']]⟩, ⟨[['h', 'ö', 'r', 'e', 'n']], [['h', 'e', 'a', 'r']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['J', 'e', 'd', 'e', 's']], [['E', 'v', 'e', 'r', 'y']]⟩, ⟨[['M', 'a', 'l']], [['t', 'i', 'm', 'e']]⟩, ⟨[['w', 'e', 'n', 'n']], [['w', 'h', 'e', 'n']]⟩, ⟨[['e', 'i', 'n']], [['a', 'n']]⟩, ⟨[['O', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'e']], [['o', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'i', 's', 't']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['S', 'e', 'm', 'i', 'n', 'a', 'r']], [['s', 'e', 'm', 'i', 'n', 'a', 'r']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['V', 'o', 'r', 't', 'r', 'a', 'g']], [['l', 'e', 'c', 't', 'u', 'r', 'e']]⟩, ⟨[['h', 'ä', 'l', 't']], [['h', 'o', 'l', 'd', 's']]⟩, ⟨[['w', 'o', 'l', 'l', 'e', 'n']], [['w', 'a', 'n', 't']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['S', 't', 'u', 'd', 'e', 'n', 't', 'e', 'n']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩, ⟨[['v', 'o', 'm']], [['o', 'f'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['M', 'a', 'n', 'n']], [['m', 'a', 'n']]⟩, ⟨[['w', 'i', 's', 's', 'e', 'n']], [['k', 'n', 'o', 'w']]⟩, ⟨[['o', 'b']], [['w', 'h', 'e', 't', 'h', 'e', 'r']]⟩, ⟨[['V', 'o', 'g', 'e', 'l', 'g', 'e', 's', 'a', 'n', 'g']], [['b', 'i', 'r', 'd', ' ', 's', 'i', 'n', 'g', 'i', 'n', 'g']]⟩, ⟨[['g', 'r', 'a', 'm', 'm', 'a', 't', 'i', 's', 'c', 'h', 'e', 'n']], [['g', 'r', 'a', 'm', 'm', 'a', 't', 'i', 'c', 'a', 'l']]⟩, ⟨[['R', 'e', 'g', 'e', 'l', 'n']], [['r', 'u', 'l', 'e', 's']]⟩, ⟨[['f', 'o', 'l', 'g', 't']], [['f', 'o', 'l', 'l', 'o', 'w', 's']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['J', 'e', 'd', 'e', 's']], [['E', 'v', 'e', 'r', 'y']]⟩, ⟨[['M', 'a', 'l']], [['t', 'i', 'm', 'e']]⟩, ⟨[['w', 'e', 'n', 'n']], [['w', 'h', 'e', 'n']]⟩, ⟨[['e', 'i', 'n']], [['a', 'n']]⟩, ⟨[['O', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'e']], [['o', 'r', 'n', 'i', 't', 'h', 'o', 'l', 'o', 'g', 'i', 's', 't']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['S', 'e', 'm', 'i', 'n', 'a', 'r']], [['s', 'e', 'm', 'i', 'n', 'a', 'r']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['V', 'o', 'r', 't', 'r', 'a', 'g']], [['l', 'e', 'c', 't', 'u', 'r', 'e']]⟩, ⟨[['h', 'ä', 'l', 't']], [['h', 'o', 'l', 'd', 's']]⟩, ⟨[['w', 'o', 'l', 'l', 'e', 'n']], [['w', 'a', 'n', 't']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['S', 't', 'u', 'd', 'e', 'n', 't', 'e', 'n']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩, ⟨[['v', 'o', 'n']], [['o', 'f']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['M', 'a', 'n', 'n']], [['m', 'a', 'n']]⟩, ⟨[['w', 'i', 's', 's', 'e', 'n']], [['k', 'n', 'o', 'w']]⟩, ⟨[['o', 'b']], [['w', 'h', 'e', 't', 'h', 'e', 'r']]⟩, ⟨[['V', 'o', 'g', 'e', 'l', 'g', 'e', 's', 'a', 'n', 'g']], [['b', 'i', 'r', 'd', ' ', 's', 'i', 'n', 'g', 'i', 'n', 'g']]⟩, ⟨[['g', 'r', 'a', 'm', 'm', 'a', 't', 'i', 's', 'c', 'h', 'e', 'n']], [['g', 'r', 'a', 'm', 'm', 'a', 't', 'i', 'c', 'a', 'l']]⟩, ⟨[['R', 'e', 'g', 'e', 'l', 'n']], [['r', 'u', 'l', 'e', 's']]⟩, ⟨[['f', 'o', 'l', 'g', 't']], [['f', 'o', 'l', 'l', 'o', 'w', 's']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['B', 'u', 'c', 'h']], [['b', 'o', 'o', 'k']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['d', 'u']], [['y', 'o', 'u']]⟩, ⟨[['s', 'u', 'c', 'h', 's', 't']], [['l', 'o', 'o', 'k', ' ', 'f', 'o', 'r']]⟩, ⟨[['s', 't', 'e', 'h', 't']], [['s', 't', 'a', 'n', 'd', 's']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['G', 'l', 'a', 's', 's', 'c', 'h', 'r', 'a', 'n', 'k']], [['g', 'l', 'a', 's', 's'], ['c', 'a', 'b', 'i', 'n', 'e', 't']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['B', 'u', 'c', 'h']], [['b', 'o', 'o', 'k']]⟩, ⟨[['d', 'a', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['d', 'u']], [['y', 'o', 'u']]⟩, ⟨[['s', 'u', 'c', 'h', 's', 't']], [['l', 'o', 'o', 'k', ' ', 'f', 'o', 'r']]⟩, ⟨[['s', 't', 'e', 'h', 't']], [['s', 't', 'a', 'n', 'd', 's']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['G', 'l', 'a', 's', 's', 'c', 'h', 'r', 'a', 'n', 'k']], [['g', 'l', 'a', 's', 's'], ['c', 'a', 'b', 'i', 'n', 'e', 't']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['E', 'i', 'n', 'b', 'r', 'e', 'c', 'h', 'e', 'r']], [['b', 'u', 'r', 'g', 'l', 'a', 'r']]⟩, ⟨[['i', 's', 't']], [['i', 's']]⟩, ⟨[['z', 'u', 'm', ' ', 'G', 'l', 'ü', 'c', 'k']], [['l', 'u', 'c', 'k', 'i', 'l', 'y']]⟩, ⟨[['v', 'o', 'm']], [['b', 'y'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['H', 'u', 'n', 'd']], [['d', 'o', 'g']]⟩, ⟨[['v', 'e', 'r', 'j', 'a', 'g', 't']], [['c', 'h', 'a', 's', 'e', ' ', 'a', 'w', 'a', 'y']]⟩, ⟨[['w', 'o', 'r', 'd', 'e', 'n']], [['b', 'e', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['E', 'i', 'n', 'b', 'r', 'e', 'c', 'h', 'e', 'r']], [['b', 'u', 'r', 'g', 'l', 'a', 'r']]⟩, ⟨[['i', 's', 't']], [['i', 's']]⟩, ⟨[['z', 'u', 'm', ' ', 'G', 'l', 'ü', 'c', 'k']], [['l', 'u', 'c', 'k', 'i', 'l', 'y']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['H', 'u', 'n', 'd']], [['d', 'o', 'g']]⟩, ⟨[['v', 'e', 'r', 'j', 'a', 'g', 't']], [['c', 'h', 'a', 's', 'e', ' ', 'a', 'w', 'a', 'y']]⟩, ⟨[['w', 'o', 'r', 'd', 'e', 'n']], [['b', 'e', 'e', 'n']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'e', 'r']], [['T', 'h', 'e']]⟩, ⟨[['E', 'm', 'p', 'f', 'a', 'n', 'g']], [['r', 'e', 'c', 'e', 'p', 't', 'i', 'o', 'n']]⟩, ⟨[['w', 'u', 'r', 'd', 'e']], [['w', 'a', 's']]⟩, ⟨[['v', 'o', 'm']], [['b', 'y'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['B', 'ü', 'r', 'g', 'e', 'r', 'm', 'e', 'i', 's', 't', 'e', 'r']], [['m', 'a', 'y', 'o', 'r']]⟩, ⟨[['e', 'r', 'ö', 'f', 'f', 'n', 'e', 't']], [['o', 'p', 'e', 'n', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'e', 'r']], [['T', 'h', 'e']]⟩, ⟨[['E', 'm', 'p', 'f', 'a', 'n', 'g']], [['r', 'e', 'c', 'e', 'p', 't', 'i', 'o', 'n']]⟩, ⟨[['w', 'u', 'r', 'd', 'e']], [['w', 'a', 's']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['B', 'ü', 'r', 'g', 'e', 'r', 'm', 'e', 'i', 's', 't', 'e', 'r']], [['m', 'a', 'y', 'o', 'r']]⟩, ⟨[['e', 'r', 'ö', 'f', 'f', 'n', 'e', 't']], [['o', 'p', 'e', 'n', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['I', 'n']], [['I', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['K', 'a', 'b', 'i', 'n', 'e', 't', 't', 's', 'i', 't', 'z', 'u', 'n', 'g']], [['c', 'a', 'b', 'i', 'n', 'e', 't', ' ', 'm', 'e', 'e', 't', 'i', 'n', 'g']]⟩, ⟨[['h', 'e', 'u', 't', 'e']], [['t', 'o', 'd', 'a', 'y']]⟩, ⟨[['w', 'i', 'r', 'd']], [['i', 's']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['n', 'e', 'u', 'e', 'r']], [['n', 'e', 'w']]⟩, ⟨[['V', 'o', 'r', 's', 'c', 'h', 'l', 'a', 'g']], [['p', 'r', 'o', 'p', 'o', 's', 'a', 'l']]⟩, ⟨[['v', 'o', 'm']], [['b', 'y'], ['t', 'h', 'e', '.', 'A']]⟩, ⟨[['K', 'a', 'n', 'z', 'l', 'e', 'r']], [['c', 'h', 'a', 'n', 'c', 'e', 'l', 'l', 'o', 'r']]⟩, ⟨[['e', 'r', 'w', 'a', 'r', 't', 'e', 't']], [['e', 'x', 'p', 'e', 'c', 't', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['I', 'n']], [['I', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['K', 'a', 'b', 'i', 'n', 'e', 't', 't', 's', 'i', 't', 'z', 'u', 'n', 'g']], [['c', 'a', 'b', 'i', 'n', 'e', 't', ' ', 'm', 'e', 'e', 't', 'i', 'n', 'g']]⟩, ⟨[['h', 'e', 'u', 't', 'e']], [['t', 'o', 'd', 'a', 'y']]⟩, ⟨[['w', 'i', 'r', 'd']], [['i', 's']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['n', 'e', 'u', 'e', 'r']], [['n', 'e', 'w']]⟩, ⟨[['V', 'o', 'r', 's', 'c', 'h', 'l', 'a', 'g']], [['p', 'r', 'o', 'p', 'o', 's', 'a', 'l']]⟩, ⟨[['v', 'o', 'm']], [['b', 'y'], ['t', 'h', 'e', '.', 'A']]⟩, ⟨[['M', 'i', 'n', 'i', 's', 't', 'e', 'r']], [['m', 'i', 'n', 'i', 's', 't', 'e', 'r']]⟩, ⟨[['e', 'r', 'w', 'a', 'r', 't', 'e', 't']], [['e', 'x', 'p', 'e', 'c', 't', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['J', 'e', 'd', 'e', 's']], [['E', 'v', 'e', 'r', 'y']]⟩, ⟨[['M', 'a', 'l']], [['t', 'i', 'm', 'e']]⟩, ⟨[['w', 'e', 'n', 'n']], [['w', 'h', 'e', 'n']]⟩, ⟨[['e', 'i', 'n', 'e']], [['a']]⟩, ⟨[['R', 'u', 'n', 'd', 'e']], [['r', 'o', 'u', 'n', 'd']]⟩, ⟨[['v', 'o', 'r', 'b', 'e', 'i']], [['o', 'v', 'e', 'r']]⟩, ⟨[['i', 's', 't']], [['i', 's']]⟩, ⟨[['w', 'e', 'r', 'd', 'e', 'n']], [['a', 'r', 'e']]⟩, ⟨[['d', 'i', 'e']], [['t', 'h', 'e']]⟩, ⟨[['K', 'a', 'r', 't', 'e', 'n']], [['c', 'a', 'r', 'd', 's']]⟩, ⟨[['v', 'o', 'm']], [['b', 'y'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['G', 'e', 'w', 'i', 'n', 'n', 'e', 'r']], [['w', 'i', 'n', 'n', 'e', 'r']]⟩, ⟨[['n', 'e', 'u']], [['n', 'e', 'w', 'l', 'y']]⟩, ⟨[['g', 'e', 'm', 'i', 's', 'c', 'h', 't']], [['s', 'h', 'u', 'f', 'f', 'l', 'e', 'd']]⟩, ⟨[['u', 'n', 'd']], [['a', 'n', 'd']]⟩, ⟨[['v', 'e', 'r', 't', 'e', 'i', 'l', 't']], [['d', 'e', 'a', 'l', 't']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'e', 'r']], [['T', 'h', 'e']]⟩, ⟨[['K', 'ü', 'h', 'l', 's', 'c', 'h', 'r', 'a', 'n', 'k']], [['f', 'r', 'i', 'd', 'g', 'e']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o']], [['s', 'o']]⟩, ⟨[['g', 'r', 'o', 'ß']], [['b', 'i', 'g']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['K', 'ü', 'r', 'b', 'i', 's']], [['p', 'u', 'm', 'p', 'k', 'i', 'n']]⟩, ⟨[['p', 'r', 'o', 'b', 'l', 'e', 'm', 'l', 'o', 's']], [['w', 'i', 't', 'h', 'o', 'u', 't', ' ', 'a', ' ', 'p', 'r', 'o', 'b', 'l', 'e', 'm']]⟩, ⟨[['i', 'm']], [['i', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['G', 'e', 'm', 'ü', 's', 'e', 'f', 'a', 'c', 'h']], [['c', 'r', 'i', 's', 'p', 'e', 'r']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 'g', 'e', 'b', 'r', 'a', 'c', 'h', 't']], [['s', 't', 'o', 'w', 'e', 'd']]⟩, ⟨[['w', 'e', 'r', 'd', 'e', 'n']], [['b', 'e']]⟩, ⟨[['k', 'o', 'n', 'n', 't', 'e']], [['c', 'o', 'u', 'l', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'e', 'r']], [['T', 'h', 'e']]⟩, ⟨[['K', 'ü', 'h', 'l', 's', 'c', 'h', 'r', 'a', 'n', 'k']], [['f', 'r', 'i', 'd', 'g', 'e']]⟩, ⟨[['w', 'a', 'r']], [['w', 'a', 's']]⟩, ⟨[['s', 'o']], [['s', 'o']]⟩, ⟨[['g', 'r', 'o', 'ß']], [['b', 'i', 'g']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['K', 'ü', 'r', 'b', 'i', 's']], [['p', 'u', 'm', 'p', 'k', 'i', 'n']]⟩, ⟨[['p', 'r', 'o', 'b', 'l', 'e', 'm', 'l', 'o', 's']], [['w', 'i', 't', 'h', 'o', 'u', 't', ' ', 'a', ' ', 'p', 'r', 'o', 'b', 'l', 'e', 'm']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['G', 'e', 'm', 'ü', 's', 'e', 'f', 'a', 'c', 'h']], [['c', 'r', 'i', 's', 'p', 'e', 'r']]⟩, ⟨[['u', 'n', 't', 'e', 'r', 'g', 'e', 'b', 'r', 'a', 'c', 'h', 't']], [['s', 't', 'o', 'w', 'e', 'd']]⟩, ⟨[['w', 'e', 'r', 'd', 'e', 'n']], [['b', 'e']]⟩, ⟨[['k', 'o', 'n', 'n', 't', 'e']], [['c', 'o', 'u', 'l', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'a', 's']], [['T', 'h', 'e']]⟩, ⟨[['T', 'h', 'e', 'a', 't', 'e', 'r', 's', 't', 'ü', 'c', 'k']], [['p', 'l', 'a', 'y']]⟩, ⟨[['m', 'i', 's', 's', 'f', 'i', 'e', 'l']], [['d', 'i', 's', 'p', 'l', 'e', 'a', 's', 'e', 'd']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['K', 'r', 'i', 't', 'i', 'k', 'e', 'r']], [['c', 'r', 'i', 't', 'i', 'c']]⟩, ⟨[['s', 'o']], [['s', 'o']]⟩, ⟨[['s', 'e', 'h', 'r']], [['m', 'u', 'c', 'h']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['e', 'r']], [['h', 'e']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['s', 'e', 'i', 'n', 'e', 'r']], [['h', 'i', 's']]⟩, ⟨[['B', 'e', 's', 'p', 'r', 'e', 'c', 'h', 'u', 'n', 'g']], [['r', 'e', 'v', 'i', 'e', 'w']]⟩, ⟨[['k', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['g', 'u', 't', 'e', 's']], [['g', 'o', 'o', 'd']]⟩, ⟨[['H', 'a', 'a', 'r']], [['h', 'a', 'i', 'r']]⟩, ⟨[['a', 'm']], [['o', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['A', 'u', 't', 'o', 'r']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['l', 'i', 'e', 'ß']], [['l', 'e', 'f', 't']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['D', 'a', 's']], [['T', 'h', 'e']]⟩, ⟨[['T', 'h', 'e', 'a', 't', 'e', 'r', 's', 't', 'ü', 'c', 'k']], [['p', 'l', 'a', 'y']]⟩, ⟨[['m', 'i', 's', 's', 'f', 'i', 'e', 'l']], [['d', 'i', 's', 'p', 'l', 'e', 'a', 's', 'e', 'd']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e']]⟩, ⟨[['K', 'r', 'i', 't', 'i', 'k', 'e', 'r']], [['c', 'r', 'i', 't', 'i', 'c']]⟩, ⟨[['s', 'o']], [['s', 'o']]⟩, ⟨[['s', 'e', 'h', 'r']], [['m', 'u', 'c', 'h']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['e', 'r']], [['h', 'e']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['s', 'e', 'i', 'n', 'e', 'r']], [['h', 'i', 's']]⟩, ⟨[['B', 'e', 's', 'p', 'r', 'e', 'c', 'h', 'u', 'n', 'g']], [['r', 'e', 'v', 'i', 'e', 'w']]⟩, ⟨[['k', 'e', 'i', 'n']], [['n', 'o']]⟩, ⟨[['g', 'u', 't', 'e', 's']], [['g', 'o', 'o', 'd']]⟩, ⟨[['H', 'a', 'a', 'r']], [['h', 'a', 'i', 'r']]⟩, ⟨[['a', 'n']], [['o', 'n']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['A', 'u', 't', 'o', 'r']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['l', 'i', 'e', 'ß']], [['l', 'e', 'f', 't']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['J', 'e', 'd', 'e', 'r']], [['E', 'v', 'e', 'r', 'y', 'o', 'n', 'e']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'a', 't']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['R', 'o', 'm', 'a', 'n']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['g', 'e', 'k', 'a', 'u', 'f', 't']], [['b', 'o', 'u', 'g', 'h', 't']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['h', 'a', 't', 't', 'e']], [['h', 'a', 'd']]⟩, ⟨[['s', 'c', 'h', 'o', 'n']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['e', 'i', 'n', 'm', 'a', 'l']], [['o', 'n', 'c', 'e']]⟩, ⟨[['e', 'i', 'n', 'e']], [['a']]⟩, ⟨[['K', 'u', 'r', 'z', 'g', 'e', 's', 'c', 'h', 'i', 'c', 'h', 't', 'e']], [['s', 'h', 'o', 'r', 't', ' ', 's', 't', 'o', 'r', 'y']]⟩, ⟨[['v', 'o', 'm']], [['b', 'y'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['A', 'u', 't', 'o', 'r']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['g', 'e', 'l', 'e', 's', 'e', 'n']], [['r', 'e', 'a', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['J', 'e', 'd', 'e', 'r']], [['E', 'v', 'e', 'r', 'y', 'o', 'n', 'e']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'a', 't']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['R', 'o', 'm', 'a', 'n']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['g', 'e', 'k', 'a', 'u', 'f', 't']], [['b', 'o', 'u', 'g', 'h', 't']]⟩, ⟨[['h', 'a', 't']], [['h', 'a', 's']]⟩, ⟨[['h', 'a', 't', 't', 'e']], [['h', 'a', 'd']]⟩, ⟨[['s', 'c', 'h', 'o', 'n']], [['a', 'l', 'r', 'e', 'a', 'd', 'y']]⟩, ⟨[['e', 'i', 'n', 'm', 'a', 'l']], [['o', 'n', 'c', 'e']]⟩, ⟨[['e', 'i', 'n', 'e']], [['a']]⟩, ⟨[['K', 'u', 'r', 'z', 'g', 'e', 's', 'c', 'h', 'i', 'c', 'h', 't', 'e']], [['s', 'h', 'o', 'r', 't', ' ', 's', 't', 'o', 'r', 'y']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['A', 'u', 't', 'o', 'r']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['g', 'e', 'l', 'e', 's', 'e', 'n']], [['r', 'e', 'a', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['J', 'e', 'd', 'e', 'r']], [['E', 'v', 'e', 'r', 'y']]⟩, ⟨[['S', 't', 'u', 'd', 'e', 'n', 't']], [['s', 't', 'u', 'd', 'e', 'n', 't']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'a', 't']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['A', 'u', 't', 'o']], [['c', 'a', 'r']]⟩, ⟨[['p', 'a', 'r', 'k', 't', 'e']], [['p', 'a', 'r', 'k', 'e', 'd']]⟩, ⟨[['b', 'r', 'a', 'c', 'h', 't', 'e']], [['a', 't', 't', 'a', 'c', 'h', 'e', 'd']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['P', 'a', 'r', 'k', 's', 'c', 'h', 'e', 'i', 'n']], [['p', 'a', 'r', 'k', 'i', 'n', 'g'], ['p', 'a', 's', 's']]⟩, ⟨[['a', 'm']], [['o', 'n'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['R', 'ü', 'c', 'k', 's', 'p', 'i', 'e', 'g', 'e', 'l']], [['r', 'e', 'a', 'r', ' ', 'v', 'i', 'e', 'w', ' ', 'm', 'i', 'r', 'r', 'o', 'r']]⟩, ⟨[['a', 'n']], [['P', 'A', 'R', 'T']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['A', 'n']], [['A', 't']]⟩, ⟨[['j', 'e', 'd', 'e', 'm']], [['e', 'v', 'e', 'r', 'y']]⟩, ⟨[['B', 'a', 'h', 'n', 'h', 'o', 'f']], [['t', 'r', 'a', 'i', 'n', ' ', 's', 't', 'a', 't', 'i', 'o', 'n']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'i', 'c', 'h']]⟩, ⟨[['u', 'n', 's', 'e', 'r']], [['o', 'u', 'r']]⟩, ⟨[['Z', 'u', 'g']], [['t', 'r', 'a', 'i', 'n']]⟩, ⟨[['e', 'i', 'n', 'f', 'u', 'h', 'r']], [['e', 'n', 't', 'e', 'r', 'e', 'd', ' ', 'i', 'n', 't', 'o']]⟩, ⟨[['w', 'u', 'r', 'd', 'e']], [['w', 'a', 's']]⟩, ⟨[['m', 'i', 'r']], [['I']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'r', 'i', 'e', 'f']], [['l', 'e', 't', 't', 'e', 'r']]⟩, ⟨[['v', 'o', 'm']], [['f', 'r', 'o', 'm'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['B', 'ü', 'r', 'g', 'e', 'r', 'm', 'e', 'i', 's', 't', 'e', 'r']], [['m', 'a', 'y', 'o', 'r']]⟩, ⟨[['ü', 'b', 'e', 'r', 'r', 'e', 'i', 'c', 'h', 't']], [['h', 'a', 'n', 'd', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['A', 'n']], [['A', 't']]⟩, ⟨[['j', 'e', 'd', 'e', 'm']], [['e', 'v', 'e', 'r', 'y']]⟩, ⟨[['B', 'a', 'h', 'n', 'h', 'o', 'f']], [['t', 'r', 'a', 'i', 'n', ' ', 's', 't', 'a', 't', 'i', 'o', 'n']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'n']], [['w', 'h', 'i', 'c', 'h']]⟩, ⟨[['u', 'n', 's', 'e', 'r']], [['o', 'u', 'r']]⟩, ⟨[['Z', 'u', 'g']], [['t', 'r', 'a', 'i', 'n']]⟩, ⟨[['e', 'i', 'n', 'f', 'u', 'h', 'r']], [['e', 'n', 't', 'e', 'r', 'e', 'd', ' ', 'i', 'n', 't', 'o']]⟩, ⟨[['w', 'u', 'r', 'd', 'e']], [['w', 'a', 's']]⟩, ⟨[['m', 'i', 'r']], [['I']]⟩, ⟨[['e', 'i', 'n']], [['a']]⟩, ⟨[['B', 'r', 'i', 'e', 'f']], [['l', 'e', 't', 't', 'e', 'r']]⟩, ⟨[['v', 'o', 'n']], [['f', 'r', 'o', 'm']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['B', 'ü', 'r', 'g', 'e', 'r', 'm', 'e', 'i', 's', 't', 'e', 'r']], [['m', 'a', 'y', 'o', 'r']]⟩, ⟨[['ü', 'b', 'e', 'r', 'r', 'e', 'i', 'c', 'h', 't']], [['h', 'a', 'n', 'd', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['H', 'a', 'n', 's']], [['H', 'a', 'n', 's']]⟩, ⟨[['e', 'n', 't', 'd', 'e', 'c', 'k', 't', 'e']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r', 'e', 'd']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['B', 'i', 'b', 'l', 'i', 'o', 't', 'h', 'e', 'k']], [['l', 'i', 'b', 'r', 'a', 'r', 'y']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['R', 'o', 'm', 'a', 'n']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['ü', 'b', 'e', 'r']], [['a', 'b', 'o', 'u', 't']]⟩, ⟨[['d', 'e', 'n']], [['t', 'h', 'e']]⟩, ⟨[['H', 'u', 'd', 's', 'o', 'n']], [['H', 'u', 'd', 's', 'o', 'n']]⟩, ⟨[['D', 'a', 'b', 'e', 'i']], [['I', 'n', ' ', 't', 'h', 'e', ' ', 'p', 'r', 'o', 'c', 'e', 's', 's']]⟩, ⟨[['f', 'i', 'e', 'l']], [['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', 'e', 'd']]⟩, ⟨[['i', 'h', 'm']], [['h', 'e', '.', 'D', 'A', 'T']]⟩, ⟨[['e', 'i', 'n']], [['P', 'A', 'R', 'T']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['e', 'r']], [['h', 'e']]⟩, ⟨[['v', 'o', 'r', ' ', 'l', 'a', 'n', 'g', 'e', 'r', ' ', 'Z', 'e', 'i', 't']], [['a', ' ', 'l', 'o', 'n', 'g', ' ', 't', 'i', 'm', 'e', ' ', 'a', 'g', 'o']]⟩, ⟨[['e', 'i', 'n', 'm', 'a', 'l']], [['o', 'n', 'c', 'e']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['V', 'o', 'r', 't', 'r', 'a', 'g']], [['l', 'e', 'c', 't', 'u', 'r', 'e']]⟩, ⟨[['v', 'o', 'm']], [['b', 'y'], ['t', 'h', 'e', '.', 'W', 'E', 'A', 'K']]⟩, ⟨[['A', 'u', 't', 'o', 'r']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['b', 'e', 's', 'u', 'c', 'h', 't']], [['a', 't', 't', 'e', 'n', 'd', 'e', 'd']]⟩, ⟨[['h', 'a', 't', 't', 'e']], [['h', 'a', 'd']]⟩]
    lgrConformance := some .wordAligned
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
    glossedWords := [⟨[['H', 'a', 'n', 's']], [['H', 'a', 'n', 's']]⟩, ⟨[['e', 'n', 't', 'd', 'e', 'c', 'k', 't', 'e']], [['d', 'i', 's', 'c', 'o', 'v', 'e', 'r', 'e', 'd']]⟩, ⟨[['i', 'n']], [['i', 'n']]⟩, ⟨[['d', 'e', 'r']], [['t', 'h', 'e']]⟩, ⟨[['B', 'i', 'b', 'l', 'i', 'o', 't', 'h', 'e', 'k']], [['l', 'i', 'b', 'r', 'a', 'r', 'y']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['R', 'o', 'm', 'a', 'n']], [['n', 'o', 'v', 'e', 'l']]⟩, ⟨[['ü', 'b', 'e', 'r']], [['a', 'b', 'o', 'u', 't']]⟩, ⟨[['d', 'e', 'n']], [['t', 'h', 'e']]⟩, ⟨[['H', 'u', 'd', 's', 'o', 'n']], [['H', 'u', 'd', 's', 'o', 'n']]⟩, ⟨[['D', 'a', 'b', 'e', 'i']], [['I', 'n', ' ', 't', 'h', 'e', ' ', 'p', 'r', 'o', 'c', 'e', 's', 's']]⟩, ⟨[['f', 'i', 'e', 'l']], [['r', 'e', 'm', 'e', 'm', 'b', 'e', 'r', 'e', 'd']]⟩, ⟨[['i', 'h', 'm']], [['h', 'e', '.', 'D', 'A', 'T']]⟩, ⟨[['e', 'i', 'n']], [['P', 'A', 'R', 'T']]⟩, ⟨[['d', 'a', 's', 's']], [['t', 'h', 'a', 't']]⟩, ⟨[['e', 'r']], [['h', 'e']]⟩, ⟨[['v', 'o', 'r', ' ', 'l', 'a', 'n', 'g', 'e', 'r', ' ', 'Z', 'e', 'i', 't']], [['a', ' ', 'l', 'o', 'n', 'g', ' ', 't', 'i', 'm', 'e', ' ', 'a', 'g', 'o']]⟩, ⟨[['e', 'i', 'n', 'm', 'a', 'l']], [['o', 'n', 'c', 'e']]⟩, ⟨[['e', 'i', 'n', 'e', 'n']], [['a']]⟩, ⟨[['V', 'o', 'r', 't', 'r', 'a', 'g']], [['l', 'e', 'c', 't', 'u', 'r', 'e']]⟩, ⟨[['v', 'o', 'n']], [['b', 'y']]⟩, ⟨[['d', 'e', 'm']], [['t', 'h', 'e', '.', 'S', 'T', 'R', 'O', 'N', 'G']]⟩, ⟨[['A', 'u', 't', 'o', 'r']], [['a', 'u', 't', 'h', 'o', 'r']]⟩, ⟨[['b', 'e', 's', 'u', 'c', 'h', 't']], [['a', 't', 't', 'e', 'n', 'd', 'e', 'd']]⟩, ⟨[['h', 'a', 't', 't', 'e']], [['h', 'a', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("article", "strong"), ("use", "producerBridging"), ("relation", "nonPart"), ("antecedent", "relatum")] }

def all : List Datum := [ex25_weak, ex25_strong, ex26_weak, ex26_strong, ex28_weak, ex28_strong, ex29_weak, ex29_strong, ex31_weak, ex31_strong, ex40_weak, ex40_strong, ex41_weak, ex41_strong, ex42_weak, ex42_strong, ex46a_weak, ex46b_weak, ex48_weak, ex58_weak, ex58_strong, ex59_weak, ex59_strong, ex62_weak, ex62_strong, ex63_weak, ex231_weak, ex231_strong, ex275_weak, ex275_strong]

end Schwarz2009.Examples
