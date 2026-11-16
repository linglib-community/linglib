module

public import Linglib.Data.Examples.Schema

/-!
# `WechslerZlatic2000` — typed example data

Auto-generated from `Linglib/Data/Examples/WechslerZlatic2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WechslerZlatic2000.Examples`.
-/

@[expose] public section

namespace WechslerZlatic2000.Examples

def ex_1 : Datum :=
  { id := "wechslerzlatic2000_1"
    source := ⟨"wechsler-zlatic-2000", "(6)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova stara knjiga stalno pada. Molim vas, podignite je."
    glossedTokens := [("Ova", "this-NOM.F.SG"), ("stara", "old-NOM.F.SG"), ("knjiga", "book(F)-NOM.SG"), ("stalno", "always"), ("pada", "fall-3SG"), ("Molim", "please"), ("vas", "you"), ("podignite", "pick.2PL"), ("je", "it.F.SG")]
    glossedWords := [⟨[['O', 'v', 'a']], [['t', 'h', 'i', 's'], ['N', 'O', 'M', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['s', 't', 'a', 'r', 'a']], [['o', 'l', 'd'], ['N', 'O', 'M', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['k', 'n', 'j', 'i', 'g', 'a']], [['b', 'o', 'o', 'k', '(', 'F', ')'], ['N', 'O', 'M', '.', 'S', 'G']]⟩, ⟨[['s', 't', 'a', 'l', 'n', 'o']], [['a', 'l', 'w', 'a', 'y', 's']]⟩, ⟨[['p', 'a', 'd', 'a']], [['f', 'a', 'l', 'l'], ['3', 'S', 'G']]⟩, ⟨[['M', 'o', 'l', 'i', 'm']], [['p', 'l', 'e', 'a', 's', 'e']]⟩, ⟨[['v', 'a', 's']], [['y', 'o', 'u']]⟩, ⟨[['p', 'o', 'd', 'i', 'g', 'n', 'i', 't', 'e']], [['p', 'i', 'c', 'k', '.', '2', 'P', 'L']]⟩, ⟨[['j', 'e']], [['i', 't', '.', 'F', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "determiner adjective"), ("index", "verb pronoun")] }

def ex_2 : Datum :=
  { id := "wechslerzlatic2000_2"
    source := ⟨"wechsler-zlatic-2000", "(11a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ovo malo devojče je ušlo. Ono je htelo da telefonira."
    glossedTokens := [("Ovo", "this.NT.SG"), ("malo", "little.NT.SG"), ("devojče", "girl.(NT).SG"), ("je", "AUX.3SG"), ("ušlo", "entered.NT.SG"), ("Ono", "it.NT.SG"), ("je", "AUX.SG"), ("htelo", "wanted.NT.SG"), ("da", "that"), ("telefonira", "telephone.3SG")]
    glossedWords := [⟨[['O', 'v', 'o']], [['t', 'h', 'i', 's', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['m', 'a', 'l', 'o']], [['l', 'i', 't', 't', 'l', 'e', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['d', 'e', 'v', 'o', 'j', 'č', 'e']], [['g', 'i', 'r', 'l', '.', '(', 'N', 'T', ')', '.', 'S', 'G']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', '3', 'S', 'G']]⟩, ⟨[['u', 'š', 'l', 'o']], [['e', 'n', 't', 'e', 'r', 'e', 'd', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['O', 'n', 'o']], [['i', 't', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', 'S', 'G']]⟩, ⟨[['h', 't', 'e', 'l', 'o']], [['w', 'a', 'n', 't', 'e', 'd', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['d', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['t', 'e', 'l', 'e', 'f', 'o', 'n', 'i', 'r', 'a']], [['t', 'e', 'l', 'e', 'p', 'h', 'o', 'n', 'e', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "neuter singular"), ("agreement", "index")] }

def ex_3 : Datum :=
  { id := "wechslerzlatic2000_3"
    source := ⟨"wechsler-zlatic-2000", "(11b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ovo malo devojče je ušlo. Ona je htela da telefonira."
    glossedTokens := [("Ovo", "this.NT.SG"), ("malo", "little.NT.SG"), ("devojče", "girl.(NT).SG"), ("je", "AUX.3SG"), ("ušlo", "entered.NT.SG"), ("Ona", "she.F.SG"), ("je", "AUX.SG"), ("htela", "wanted.F.SG"), ("da", "that"), ("telefonira", "telephone.3SG")]
    glossedWords := [⟨[['O', 'v', 'o']], [['t', 'h', 'i', 's', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['m', 'a', 'l', 'o']], [['l', 'i', 't', 't', 'l', 'e', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['d', 'e', 'v', 'o', 'j', 'č', 'e']], [['g', 'i', 'r', 'l', '.', '(', 'N', 'T', ')', '.', 'S', 'G']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', '3', 'S', 'G']]⟩, ⟨[['u', 'š', 'l', 'o']], [['e', 'n', 't', 'e', 'r', 'e', 'd', '.', 'N', 'T', '.', 'S', 'G']]⟩, ⟨[['O', 'n', 'a']], [['s', 'h', 'e', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', 'S', 'G']]⟩, ⟨[['h', 't', 'e', 'l', 'a']], [['w', 'a', 'n', 't', 'e', 'd', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['t', 'e', 'l', 'e', 'f', 'o', 'n', 'i', 'r', 'a']], [['t', 'e', 'l', 'e', 'p', 'h', 'o', 'n', 'e', '.', '3', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "feminine singular"), ("agreement", "pragmatic")] }

def ex_4 : Datum :=
  { id := "wechslerzlatic2000_4"
    source := ⟨"wechsler-zlatic-2000", "(12)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ova stara knjiga"
    glossedTokens := [("ova", "this-NOM.F.SG"), ("stara", "old-NOM.F.SG"), ("knjiga", "book(F)-NOM.SG")]
    glossedWords := [⟨[['o', 'v', 'a']], [['t', 'h', 'i', 's'], ['N', 'O', 'M', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['s', 't', 'a', 'r', 'a']], [['o', 'l', 'd'], ['N', 'O', 'M', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['k', 'n', 'j', 'i', 'g', 'a']], [['b', 'o', 'o', 'k', '(', 'F', ')'], ['N', 'O', 'M', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agreement", "concord")] }

def ex_5 : Datum :=
  { id := "wechslerzlatic2000_5"
    source := ⟨"wechsler-zlatic-2000", "(13)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova stara knjiga je pala."
    glossedTokens := [("Ova", "this-F.SG"), ("stara", "old-F.SG"), ("knjiga", "book(F)-NOM.SG"), ("je", "AUX.3SG"), ("pala", "fall-PPRT-F.SG")]
    glossedWords := [⟨[['O', 'v', 'a']], [['t', 'h', 'i', 's'], ['F', '.', 'S', 'G']]⟩, ⟨[['s', 't', 'a', 'r', 'a']], [['o', 'l', 'd'], ['F', '.', 'S', 'G']]⟩, ⟨[['k', 'n', 'j', 'i', 'g', 'a']], [['b', 'o', 'o', 'k', '(', 'F', ')'], ['N', 'O', 'M', '.', 'S', 'G']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'a', 'l', 'a']], [['f', 'a', 'l', 'l'], ['P', 'P', 'R', 'T'], ['F', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("target", "participle")] }

def ex_6 : Datum :=
  { id := "wechslerzlatic2000_6"
    source := ⟨"wechsler-zlatic-2000", "(19a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Taj stari sudija je dobro sudio. On ..."
    glossedTokens := [("Taj", "that.M"), ("stari", "old.M"), ("sudija", "judge"), ("je", "AUX"), ("dobro", "well"), ("sudio", "judged.M"), ("On", "3M.SG")]
    glossedWords := [⟨[['T', 'a', 'j']], [['t', 'h', 'a', 't', '.', 'M']]⟩, ⟨[['s', 't', 'a', 'r', 'i']], [['o', 'l', 'd', '.', 'M']]⟩, ⟨[['s', 'u', 'd', 'i', 'j', 'a']], [['j', 'u', 'd', 'g', 'e']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X']]⟩, ⟨[['d', 'o', 'b', 'r', 'o']], [['w', 'e', 'l', 'l']]⟩, ⟨[['s', 'u', 'd', 'i', 'o']], [['j', 'u', 'd', 'g', 'e', 'd', '.', 'M']]⟩, ⟨[['O', 'n']], [['3', 'M', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "sudija"), ("sex", "male"), ("gender", "masculine")] }

def ex_7 : Datum :=
  { id := "wechslerzlatic2000_7"
    source := ⟨"wechsler-zlatic-2000", "(19b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta stara sudija je dobro sudila. Ona ..."
    glossedTokens := [("Ta", "that.F"), ("stara", "old.F"), ("sudija", "judge"), ("je", "AUX"), ("dobro", "well"), ("sudila", "judged.F"), ("Ona", "3F.SG")]
    glossedWords := [⟨[['T', 'a']], [['t', 'h', 'a', 't', '.', 'F']]⟩, ⟨[['s', 't', 'a', 'r', 'a']], [['o', 'l', 'd', '.', 'F']]⟩, ⟨[['s', 'u', 'd', 'i', 'j', 'a']], [['j', 'u', 'd', 'g', 'e']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X']]⟩, ⟨[['d', 'o', 'b', 'r', 'o']], [['w', 'e', 'l', 'l']]⟩, ⟨[['s', 'u', 'd', 'i', 'l', 'a']], [['j', 'u', 'd', 'g', 'e', 'd', '.', 'F']]⟩, ⟨[['O', 'n', 'a']], [['3', 'F', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "sudija"), ("sex", "female"), ("gender", "feminine")] }

def ex_8 : Datum :=
  { id := "wechslerzlatic2000_8"
    source := ⟨"wechsler-zlatic-2000", "(21a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "taj kit"
    glossedTokens := [("taj", "that.M"), ("kit", "whale")]
    glossedWords := [⟨[['t', 'a', 'j']], [['t', 'h', 'a', 't', '.', 'M']]⟩, ⟨[['k', 'i', 't']], [['w', 'h', 'a', 'l', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "kit"), ("sex", "unspecified")] }

def ex_9 : Datum :=
  { id := "wechslerzlatic2000_9"
    source := ⟨"wechsler-zlatic-2000", "(21b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Kit je podojio svoje mladunče."
    glossedTokens := [("Kit", "whale"), ("je", "AUX.SG"), ("podojio", "nursed.3.M.SG"), ("svoje", "self"), ("mladunče", "offspring")]
    glossedWords := [⟨[['K', 'i', 't']], [['w', 'h', 'a', 'l', 'e']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', 'S', 'G']]⟩, ⟨[['p', 'o', 'd', 'o', 'j', 'i', 'o']], [['n', 'u', 'r', 's', 'e', 'd', '.', '3', '.', 'M', '.', 'S', 'G']]⟩, ⟨[['s', 'v', 'o', 'j', 'e']], [['s', 'e', 'l', 'f']]⟩, ⟨[['m', 'l', 'a', 'd', 'u', 'n', 'č', 'e']], [['o', 'f', 'f', 's', 'p', 'r', 'i', 'n', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "kit"), ("gender", "masculine")] }

def ex_10 : Datum :=
  { id := "wechslerzlatic2000_10"
    source := ⟨"wechsler-zlatic-2000", "(23a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova telad je pasla."
    glossedTokens := [("Ova", "this.F.SG"), ("telad", "calves"), ("je", "AUX.3SG"), ("pasla", "grazed.F.SG")]
    glossedWords := [⟨[['O', 'v', 'a']], [['t', 'h', 'i', 's', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['t', 'e', 'l', 'a', 'd']], [['c', 'a', 'l', 'v', 'e', 's']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', '3', 'S', 'G']]⟩, ⟨[['p', 'a', 's', 'l', 'a']], [['g', 'r', 'a', 'z', 'e', 'd', '.', 'F', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ova telad su pasla.", .acceptable)]
    readings := []
    paperFeatures := [("noun", "telad"), ("predicate", "nondistributive")] }

def ex_11 : Datum :=
  { id := "wechslerzlatic2000_11"
    source := ⟨"wechsler-zlatic-2000", "(23b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ova telad imaju po dva roga."
    glossedTokens := [("Ova", "this.NT.PL"), ("telad", "calves"), ("imaju", "have.PL"), ("po", "each"), ("dva", "two"), ("roga", "horns")]
    glossedWords := [⟨[['O', 'v', 'a']], [['t', 'h', 'i', 's', '.', 'N', 'T', '.', 'P', 'L']]⟩, ⟨[['t', 'e', 'l', 'a', 'd']], [['c', 'a', 'l', 'v', 'e', 's']]⟩, ⟨[['i', 'm', 'a', 'j', 'u']], [['h', 'a', 'v', 'e', '.', 'P', 'L']]⟩, ⟨[['p', 'o']], [['e', 'a', 'c', 'h']]⟩, ⟨[['d', 'v', 'a']], [['t', 'w', 'o']]⟩, ⟨[['r', 'o', 'g', 'a']], [['h', 'o', 'r', 'n', 's']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ova telad ima po dva roga.", .ungrammatical), ("Ova telad ima po dva roga.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "telad"), ("predicate", "distributive")] }

def ex_12 : Datum :=
  { id := "wechslerzlatic2000_12"
    source := ⟨"wechsler-zlatic-2000", "(28)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Vratio mi je ovaj ludi Steva violinu koju sam mu pozajmio."
    glossedTokens := [("Vratio", "returned.1SG"), ("mi", "me"), ("je", "AUX.3SG"), ("ovaj", "this.NOM.M.SG"), ("ludi", "crazy.NOM.M.SG"), ("Steva", "Steve.NOM"), ("violinu", "violin-ACC"), ("koju", "which"), ("sam", "AUX.1SG"), ("mu", "3DAT.M.SG"), ("pozajmio", "loaned")]
    glossedWords := [⟨[['V', 'r', 'a', 't', 'i', 'o']], [['r', 'e', 't', 'u', 'r', 'n', 'e', 'd', '.', '1', 'S', 'G']]⟩, ⟨[['m', 'i']], [['m', 'e']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X', '.', '3', 'S', 'G']]⟩, ⟨[['o', 'v', 'a', 'j']], [['t', 'h', 'i', 's', '.', 'N', 'O', 'M', '.', 'M', '.', 'S', 'G']]⟩, ⟨[['l', 'u', 'd', 'i']], [['c', 'r', 'a', 'z', 'y', '.', 'N', 'O', 'M', '.', 'M', '.', 'S', 'G']]⟩, ⟨[['S', 't', 'e', 'v', 'a']], [['S', 't', 'e', 'v', 'e', '.', 'N', 'O', 'M']]⟩, ⟨[['v', 'i', 'o', 'l', 'i', 'n', 'u']], [['v', 'i', 'o', 'l', 'i', 'n'], ['A', 'C', 'C']]⟩, ⟨[['k', 'o', 'j', 'u']], [['w', 'h', 'i', 'c', 'h']]⟩, ⟨[['s', 'a', 'm']], [['A', 'U', 'X', '.', '1', 'S', 'G']]⟩, ⟨[['m', 'u']], [['3', 'D', 'A', 'T', '.', 'M', '.', 'S', 'G']]⟩, ⟨[['p', 'o', 'z', 'a', 'j', 'm', 'i', 'o']], [['l', 'o', 'a', 'n', 'e', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "Steva"), ("declension", "II"), ("gender", "masculine")] }

def ex_13 : Datum :=
  { id := "wechslerzlatic2000_13"
    source := ⟨"wechsler-zlatic-2000", "(30a)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta mušterija je došla."
    glossedTokens := [("Ta", "that.F"), ("mušterija", "customer"), ("je", "AUX"), ("došla", "came.F")]
    glossedWords := [⟨[['T', 'a']], [['t', 'h', 'a', 't', '.', 'F']]⟩, ⟨[['m', 'u', 'š', 't', 'e', 'r', 'i', 'j', 'a']], [['c', 'u', 's', 't', 'o', 'm', 'e', 'r']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X']]⟩, ⟨[['d', 'o', 'š', 'l', 'a']], [['c', 'a', 'm', 'e', '.', 'F']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mušterija"), ("sex", "unspecified")] }

def ex_14 : Datum :=
  { id := "wechslerzlatic2000_14"
    source := ⟨"wechsler-zlatic-2000", "(30b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Taj mušterija je došao."
    glossedTokens := [("Taj", "that.M"), ("mušterija", "customer"), ("je", "AUX"), ("došao", "came.M")]
    glossedWords := [⟨[['T', 'a', 'j']], [['t', 'h', 'a', 't', '.', 'M']]⟩, ⟨[['m', 'u', 'š', 't', 'e', 'r', 'i', 'j', 'a']], [['c', 'u', 's', 't', 'o', 'm', 'e', 'r']]⟩, ⟨[['j', 'e']], [['A', 'U', 'X']]⟩, ⟨[['d', 'o', 'š', 'a', 'o']], [['c', 'a', 'm', 'e', '.', 'M']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mušterija"), ("sex", "male")] }

def ex_15 : Datum :=
  { id := "wechslerzlatic2000_15"
    source := ⟨"wechsler-zlatic-2000", "(33)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Te sudije su došle."
    glossedTokens := [("Te", "those.F.PL"), ("sudije", "judge(F).PL"), ("su", "AUX.3PL"), ("došle", "came.F.PL")]
    glossedWords := [⟨[['T', 'e']], [['t', 'h', 'o', 's', 'e', '.', 'F', '.', 'P', 'L']]⟩, ⟨[['s', 'u', 'd', 'i', 'j', 'e']], [['j', 'u', 'd', 'g', 'e', '(', 'F', ')', '.', 'P', 'L']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', '3', 'P', 'L']]⟩, ⟨[['d', 'o', 'š', 'l', 'e']], [['c', 'a', 'm', 'e', '.', 'F', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "sudije"), ("number", "plural")] }

def ex_16 : Datum :=
  { id := "wechslerzlatic2000_16"
    source := ⟨"wechsler-zlatic-2000", "(34)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ove naočare su nove. One ..."
    glossedTokens := [("Ove", "this.PL"), ("naočare", "glasses"), ("su", "be.3PL"), ("nove", "new.PL"), ("One", "3PL")]
    glossedWords := [⟨[['O', 'v', 'e']], [['t', 'h', 'i', 's', '.', 'P', 'L']]⟩, ⟨[['n', 'a', 'o', 'č', 'a', 'r', 'e']], [['g', 'l', 'a', 's', 's', 'e', 's']]⟩, ⟨[['s', 'u']], [['b', 'e', '.', '3', 'P', 'L']]⟩, ⟨[['n', 'o', 'v', 'e']], [['n', 'e', 'w', '.', 'P', 'L']]⟩, ⟨[['O', 'n', 'e']], [['3', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "naočare"), ("type", "plurale tantum")] }

def ex_17 : Datum :=
  { id := "wechslerzlatic2000_17"
    source := ⟨"wechsler-zlatic-2000", "(36)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Sreo sam braću. Ona su došla."
    glossedTokens := [("Sreo", "met.1SG"), ("sam", "AUX"), ("braću", "brothers.ACC"), ("Ona", "they.N.PL"), ("su", "AUX.3.PL"), ("došla", "came.N.PL")]
    glossedWords := [⟨[['S', 'r', 'e', 'o']], [['m', 'e', 't', '.', '1', 'S', 'G']]⟩, ⟨[['s', 'a', 'm']], [['A', 'U', 'X']]⟩, ⟨[['b', 'r', 'a', 'ć', 'u']], [['b', 'r', 'o', 't', 'h', 'e', 'r', 's', '.', 'A', 'C', 'C']]⟩, ⟨[['O', 'n', 'a']], [['t', 'h', 'e', 'y', '.', 'N', '.', 'P', 'L']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', '3', '.', 'P', 'L']]⟩, ⟨[['d', 'o', 'š', 'l', 'a']], [['c', 'a', 'm', 'e', '.', 'N', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "braća"), ("pronoun", "neuter plural")] }

def ex_18 : Datum :=
  { id := "wechslerzlatic2000_18"
    source := ⟨"wechsler-zlatic-2000", "(37)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ovu dobru braću"
    glossedTokens := [("ovu", "this-ACC.F.SG"), ("dobru", "good-ACC.F.SG"), ("braću", "brothers-ACC")]
    glossedWords := [⟨[['o', 'v', 'u']], [['t', 'h', 'i', 's'], ['A', 'C', 'C', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'o', 'b', 'r', 'u']], [['g', 'o', 'o', 'd'], ['A', 'C', 'C', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['b', 'r', 'a', 'ć', 'u']], [['b', 'r', 'o', 't', 'h', 'e', 'r', 's'], ['A', 'C', 'C']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "braća"), ("concord", "feminine singular")] }

def ex_19 : Datum :=
  { id := "wechslerzlatic2000_19"
    source := ⟨"wechsler-zlatic-2000", "(38)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ovom dobrom braćom"
    glossedTokens := [("ovom", "this-INS.F.SG"), ("dobrom", "good-INS.F.SG"), ("braćom", "brothers-INS")]
    glossedWords := [⟨[['o', 'v', 'o', 'm']], [['t', 'h', 'i', 's'], ['I', 'N', 'S', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'o', 'b', 'r', 'o', 'm']], [['g', 'o', 'o', 'd'], ['I', 'N', 'S', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['b', 'r', 'a', 'ć', 'o', 'm']], [['b', 'r', 'o', 't', 'h', 'e', 'r', 's'], ['I', 'N', 'S']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "braća"), ("concord", "feminine singular")] }

def ex_20 : Datum :=
  { id := "wechslerzlatic2000_20"
    source := ⟨"wechsler-zlatic-2000", "(40)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Sreo sam gospodu. Oni su bili jako ljubazni."
    glossedTokens := [("Sreo", "met.1SG"), ("sam", "AUX"), ("gospodu", "gentlemen.ACC"), ("Oni", "they.M.PL"), ("su", "AUX.PL"), ("bili", "were.M.PL"), ("jako", "very"), ("ljubazni", "kind.M.PL")]
    glossedWords := [⟨[['S', 'r', 'e', 'o']], [['m', 'e', 't', '.', '1', 'S', 'G']]⟩, ⟨[['s', 'a', 'm']], [['A', 'U', 'X']]⟩, ⟨[['g', 'o', 's', 'p', 'o', 'd', 'u']], [['g', 'e', 'n', 't', 'l', 'e', 'm', 'e', 'n', '.', 'A', 'C', 'C']]⟩, ⟨[['O', 'n', 'i']], [['t', 'h', 'e', 'y', '.', 'M', '.', 'P', 'L']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', 'P', 'L']]⟩, ⟨[['b', 'i', 'l', 'i']], [['w', 'e', 'r', 'e', '.', 'M', '.', 'P', 'L']]⟩, ⟨[['j', 'a', 'k', 'o']], [['v', 'e', 'r', 'y']]⟩, ⟨[['l', 'j', 'u', 'b', 'a', 'z', 'n', 'i']], [['k', 'i', 'n', 'd', '.', 'M', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Sreo sam gospodu. Ona su bila jako ljubazna.", .ungrammatical), ("Sreo sam gospodu. Ona su bila jako ljubazna.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "gospoda"), ("pronoun", "masculine plural")] }

def ex_21 : Datum :=
  { id := "wechslerzlatic2000_21"
    source := ⟨"wechsler-zlatic-2000", "(41)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Posmatrali smo ovu dobru decu. Ona su spavala."
    glossedTokens := [("Posmatrali", "watched.1.PL"), ("smo", "AUX"), ("ovu", "this.F.SG"), ("dobru", "good.F.SG"), ("decu", "children.F.SG"), ("Ona", "they.N.PL"), ("su", "AUX.3PL"), ("spavala", "slept.NT.PL")]
    glossedWords := [⟨[['P', 'o', 's', 'm', 'a', 't', 'r', 'a', 'l', 'i']], [['w', 'a', 't', 'c', 'h', 'e', 'd', '.', '1', '.', 'P', 'L']]⟩, ⟨[['s', 'm', 'o']], [['A', 'U', 'X']]⟩, ⟨[['o', 'v', 'u']], [['t', 'h', 'i', 's', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'o', 'b', 'r', 'u']], [['g', 'o', 'o', 'd', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'e', 'c', 'u']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['O', 'n', 'a']], [['t', 'h', 'e', 'y', '.', 'N', '.', 'P', 'L']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', '3', 'P', 'L']]⟩, ⟨[['s', 'p', 'a', 'v', 'a', 'l', 'a']], [['s', 'l', 'e', 'p', 't', '.', 'N', 'T', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("concord", "feminine singular"), ("index", "neuter plural")] }

def ex_22 : Datum :=
  { id := "wechslerzlatic2000_22"
    source := ⟨"wechsler-zlatic-2000", "(42)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Deca su spavala. Mi smo ih videli."
    glossedTokens := [("Deca", "children"), ("su", "AUX.3PL"), ("spavala", "slept.NT.PL"), ("Mi", "we"), ("smo", "AUX.PL"), ("ih", "them.ACC.PL"), ("videli", "saw")]
    glossedWords := [⟨[['D', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', '3', 'P', 'L']]⟩, ⟨[['s', 'p', 'a', 'v', 'a', 'l', 'a']], [['s', 'l', 'e', 'p', 't', '.', 'N', 'T', '.', 'P', 'L']]⟩, ⟨[['M', 'i']], [['w', 'e']]⟩, ⟨[['s', 'm', 'o']], [['A', 'U', 'X', '.', 'P', 'L']]⟩, ⟨[['i', 'h']], [['t', 'h', 'e', 'm', '.', 'A', 'C', 'C', '.', 'P', 'L']]⟩, ⟨[['v', 'i', 'd', 'e', 'l', 'i']], [['s', 'a', 'w']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("index", "neuter plural")] }

def ex_23 : Datum :=
  { id := "wechslerzlatic2000_23"
    source := ⟨"wechsler-zlatic-2000", "(43)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta dobra deca su došla."
    glossedTokens := [("Ta", "that.F.SG"), ("dobra", "good.F.SG"), ("deca", "children(F.SG)"), ("su", "AUX.3PL"), ("došla", "come-PPRT.N.PL")]
    glossedWords := [⟨[['T', 'a']], [['t', 'h', 'a', 't', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'o', 'b', 'r', 'a']], [['g', 'o', 'o', 'd', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '(', 'F', '.', 'S', 'G', ')']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', '3', 'P', 'L']]⟩, ⟨[['d', 'o', 'š', 'l', 'a']], [['c', 'o', 'm', 'e'], ['P', 'P', 'R', 'T', '.', 'N', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "participle")] }

def ex_24 : Datum :=
  { id := "wechslerzlatic2000_24"
    source := ⟨"wechsler-zlatic-2000", "(44)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta dobra deca dolaze."
    glossedTokens := [("Ta", "that.F.SG"), ("dobra", "good.F.SG"), ("deca", "children(F.SG)"), ("dolaze", "come.3.PL")]
    glossedWords := [⟨[['T', 'a']], [['t', 'h', 'a', 't', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'o', 'b', 'r', 'a']], [['g', 'o', 'o', 'd', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '(', 'F', '.', 'S', 'G', ')']]⟩, ⟨[['d', 'o', 'l', 'a', 'z', 'e']], [['c', 'o', 'm', 'e', '.', '3', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "finite verb")] }

def ex_25 : Datum :=
  { id := "wechslerzlatic2000_25"
    source := ⟨"wechsler-zlatic-2000", "(50)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ja smatram decu gladnom."
    glossedTokens := [("Ja", "I"), ("smatram", "consider"), ("decu", "children.ACC(F.SG[N.PL])"), ("gladnom", "hungry.INST.FEM.SG")]
    glossedWords := [⟨[['J', 'a']], [['I']]⟩, ⟨[['s', 'm', 'a', 't', 'r', 'a', 'm']], [['c', 'o', 'n', 's', 'i', 'd', 'e', 'r']]⟩, ⟨[['d', 'e', 'c', 'u']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '.', 'A', 'C', 'C', '(', 'F', '.', 'S', 'G', '[', 'N', '.', 'P', 'L', ']', ')']]⟩, ⟨[['g', 'l', 'a', 'd', 'n', 'o', 'm']], [['h', 'u', 'n', 'g', 'r', 'y', '.', 'I', 'N', 'S', 'T', '.', 'F', 'E', 'M', '.', 'S', 'G']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ja smatram decu gladnim.", .ungrammatical), ("Ja smatram decu gladnim.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "secondary predicate")] }

def ex_26 : Datum :=
  { id := "wechslerzlatic2000_26"
    source := ⟨"wechsler-zlatic-2000", "(51)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jelena i deca su došli."
    glossedTokens := [("Jelena", "Yelena(F.SG[F.SG])"), ("i", "and"), ("deca", "children(F.SG[N.PL])"), ("su", "AUX.3.PL"), ("došli", "came.M.PL")]
    glossedWords := [⟨[['J', 'e', 'l', 'e', 'n', 'a']], [['Y', 'e', 'l', 'e', 'n', 'a', '(', 'F', '.', 'S', 'G', '[', 'F', '.', 'S', 'G', ']', ')']]⟩, ⟨[['i']], [['a', 'n', 'd']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '(', 'F', '.', 'S', 'G', '[', 'N', '.', 'P', 'L', ']', ')']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', '3', '.', 'P', 'L']]⟩, ⟨[['d', 'o', 'š', 'l', 'i']], [['c', 'a', 'm', 'e', '.', 'M', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jelena i deca su došle.", .ungrammatical), ("Jelena i deca su došle.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "coordination")] }

def ex_27 : Datum :=
  { id := "wechslerzlatic2000_27"
    source := ⟨"wechsler-zlatic-2000", "(52)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Jelena i deca su gladni."
    glossedTokens := [("Jelena", "Yelena(F.SG[F.SG])"), ("i", "and"), ("deca", "children(F.SG[N.PL])"), ("su", "AUX.3.PL"), ("gladni", "hungry.M.PL")]
    glossedWords := [⟨[['J', 'e', 'l', 'e', 'n', 'a']], [['Y', 'e', 'l', 'e', 'n', 'a', '(', 'F', '.', 'S', 'G', '[', 'F', '.', 'S', 'G', ']', ')']]⟩, ⟨[['i']], [['a', 'n', 'd']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '(', 'F', '.', 'S', 'G', '[', 'N', '.', 'P', 'L', ']', ')']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', '3', '.', 'P', 'L']]⟩, ⟨[['g', 'l', 'a', 'd', 'n', 'i']], [['h', 'u', 'n', 'g', 'r', 'y', '.', 'M', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Jelena i deca su gladne.", .ungrammatical), ("Jelena i deca su gladne.", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "coordination")] }

def ex_28 : Datum :=
  { id := "wechslerzlatic2000_28"
    source := ⟨"wechsler-zlatic-2000", "(53)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "Ta deca i ta čudovišta su se lepo igrala."
    glossedTokens := [("Ta", "that"), ("deca", "children(F.SG[N.PL])"), ("i", "and"), ("ta", "those"), ("čudovišta", "monsters(N.PL[N.PL])"), ("su", "AUX"), ("se", "REFL"), ("lepo", "well"), ("igrala", "played.N.PL")]
    glossedWords := [⟨[['T', 'a']], [['t', 'h', 'a', 't']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n', '(', 'F', '.', 'S', 'G', '[', 'N', '.', 'P', 'L', ']', ')']]⟩, ⟨[['i']], [['a', 'n', 'd']]⟩, ⟨[['t', 'a']], [['t', 'h', 'o', 's', 'e']]⟩, ⟨[['č', 'u', 'd', 'o', 'v', 'i', 'š', 't', 'a']], [['m', 'o', 'n', 's', 't', 'e', 'r', 's', '(', 'N', '.', 'P', 'L', '[', 'N', '.', 'P', 'L', ']', ')']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X']]⟩, ⟨[['s', 'e']], [['R', 'E', 'F', 'L']]⟩, ⟨[['l', 'e', 'p', 'o']], [['w', 'e', 'l', 'l']]⟩, ⟨[['i', 'g', 'r', 'a', 'l', 'a']], [['p', 'l', 'a', 'y', 'e', 'd', '.', 'N', '.', 'P', 'L']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Ta deca i ta čudovišta su se lepo igrali.", .marginal), ("Ta deca i ta čudovišta su se lepo igrali.", .marginal)]
    readings := []
    paperFeatures := [("noun", "deca"), ("target", "coordination")] }

def ex_29 : Datum :=
  { id := "wechslerzlatic2000_29"
    source := ⟨"wechsler-zlatic-2000", "(54)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "deca koja su tada bila"
    glossedTokens := [("deca", "children"), ("koja", "who.N.PL"), ("su", "AUX.PL"), ("tada", "then"), ("bila", "were")]
    glossedWords := [⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['k', 'o', 'j', 'a']], [['w', 'h', 'o', '.', 'N', '.', 'P', 'L']]⟩, ⟨[['s', 'u']], [['A', 'U', 'X', '.', 'P', 'L']]⟩, ⟨[['t', 'a', 'd', 'a']], [['t', 'h', 'e', 'n']]⟩, ⟨[['b', 'i', 'l', 'a']], [['w', 'e', 'r', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("deca koja je tada bila", .ungrammatical), ("deca koja je tada bila", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "nominative")] }

def ex_30 : Datum :=
  { id := "wechslerzlatic2000_30"
    source := ⟨"wechsler-zlatic-2000", "(55)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "deca koju sam video"
    glossedTokens := [("deca", "children"), ("koju", "who.ACC.F.SG"), ("sam", "AUX.1.SG"), ("video", "saw")]
    glossedWords := [⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['k', 'o', 'j', 'u']], [['w', 'h', 'o', '.', 'A', 'C', 'C', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['s', 'a', 'm']], [['A', 'U', 'X', '.', '1', '.', 'S', 'G']]⟩, ⟨[['v', 'i', 'd', 'e', 'o']], [['s', 'a', 'w']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "accusative")] }

def ex_31 : Datum :=
  { id := "wechslerzlatic2000_31"
    source := ⟨"wechsler-zlatic-2000", "(56)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "deca koje se svi plaše"
    glossedTokens := [("deca", "children"), ("koje", "who.GEN.F.SG"), ("se", "REFL"), ("svi", "all"), ("plaše", "fear")]
    glossedWords := [⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['k', 'o', 'j', 'e']], [['w', 'h', 'o', '.', 'G', 'E', 'N', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['s', 'e']], [['R', 'E', 'F', 'L']]⟩, ⟨[['s', 'v', 'i']], [['a', 'l', 'l']]⟩, ⟨[['p', 'l', 'a', 'š', 'e']], [['f', 'e', 'a', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("deca kojih se svi plaše", .acceptable), ("deca kojih se svi plaše", .acceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "genitive")] }

def ex_32 : Datum :=
  { id := "wechslerzlatic2000_32"
    source := ⟨"wechsler-zlatic-2000", "(59)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "moja deca, što ih nije briga nizašta"
    glossedTokens := [("moja", "my"), ("deca", "children"), ("što", "that"), ("ih", "3.ACC.PL"), ("nije", "NEG.AUX"), ("briga", "care"), ("nizašta", "nothing")]
    glossedWords := [⟨[['m', 'o', 'j', 'a']], [['m', 'y']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['š', 't', 'o']], [['t', 'h', 'a', 't']]⟩, ⟨[['i', 'h']], [['3', '.', 'A', 'C', 'C', '.', 'P', 'L']]⟩, ⟨[['n', 'i', 'j', 'e']], [['N', 'E', 'G', '.', 'A', 'U', 'X']]⟩, ⟨[['b', 'r', 'i', 'g', 'a']], [['c', 'a', 'r', 'e']]⟩, ⟨[['n', 'i', 'z', 'a', 'š', 't', 'a']], [['n', 'o', 't', 'h', 'i', 'n', 'g']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("moja deca, što je nije briga nizašta", .ungrammatical), ("moja deca, što je nije briga nizašta", .unacceptable)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "što")] }

def ex_33 : Datum :=
  { id := "wechslerzlatic2000_33"
    source := ⟨"wechsler-zlatic-2000", "(61b)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "moja deca, što ih se svi plaše"
    glossedTokens := [("moja", "my"), ("deca", "children"), ("što", "that"), ("ih", "3.GEN.PL"), ("se", "REFL"), ("svi", "all"), ("plaše", "fear")]
    glossedWords := [⟨[['m', 'o', 'j', 'a']], [['m', 'y']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['š', 't', 'o']], [['t', 'h', 'a', 't']]⟩, ⟨[['i', 'h']], [['3', '.', 'G', 'E', 'N', '.', 'P', 'L']]⟩, ⟨[['s', 'e']], [['R', 'E', 'F', 'L']]⟩, ⟨[['s', 'v', 'i']], [['a', 'l', 'l']]⟩, ⟨[['p', 'l', 'a', 'š', 'e']], [['f', 'e', 'a', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("moja deca, što je se svi plaše", .ungrammatical)]
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "što")] }

def ex_34 : Datum :=
  { id := "wechslerzlatic2000_34"
    source := ⟨"wechsler-zlatic-2000", "(64)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Su Majestad suprema está contento. Él ..."
    glossedTokens := [("Su", "his"), ("Majestad", "majesty"), ("suprema", "supreme.F"), ("está", "is"), ("contento", "happy.M"), ("Él", "he")]
    glossedWords := [⟨[['S', 'u']], [['h', 'i', 's']]⟩, ⟨[['M', 'a', 'j', 'e', 's', 't', 'a', 'd']], [['m', 'a', 'j', 'e', 's', 't', 'y']]⟩, ⟨[['s', 'u', 'p', 'r', 'e', 'm', 'a']], [['s', 'u', 'p', 'r', 'e', 'm', 'e', '.', 'F']]⟩, ⟨[['e', 's', 't', 'á']], [['i', 's']]⟩, ⟨[['c', 'o', 'n', 't', 'e', 'n', 't', 'o']], [['h', 'a', 'p', 'p', 'y', '.', 'M']]⟩, ⟨[['É', 'l']], [['h', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "Majestad"), ("concord", "feminine"), ("index", "masculine")] }

def ex_35 : Datum :=
  { id := "wechslerzlatic2000_35"
    source := ⟨"wechsler-zlatic-2000", "(62)"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "moja deca, što je se svi plaše"
    glossedTokens := [("moja", "my"), ("deca", "children"), ("što", "that"), ("je", "3.GEN.F.SG"), ("se", "REFL"), ("svi", "all"), ("plaše", "fear")]
    glossedWords := [⟨[['m', 'o', 'j', 'a']], [['m', 'y']]⟩, ⟨[['d', 'e', 'c', 'a']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['š', 't', 'o']], [['t', 'h', 'a', 't']]⟩, ⟨[['j', 'e']], [['3', '.', 'G', 'E', 'N', '.', 'F', '.', 'S', 'G']]⟩, ⟨[['s', 'e']], [['R', 'E', 'F', 'L']]⟩, ⟨[['s', 'v', 'i']], [['a', 'l', 'l']]⟩, ⟨[['p', 'l', 'a', 'š', 'e']], [['f', 'e', 'a', 'r']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "deca"), ("relative", "što"), ("resumptive", "singular")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_26, ex_27, ex_28, ex_29, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35]

end WechslerZlatic2000.Examples
