module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `FuscoSgrizzi2026` — typed example data

Auto-generated from `Linglib/Data/Examples/FuscoSgrizzi2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FuscoSgrizzi2026.Examples`.
-/

@[expose] public section

namespace FuscoSgrizzi2026.Examples

def ex4a : Datum :=
  { id := "fuscosgrizzi2026_ex4a"
    source := ⟨"fusco-sgrizzi-2026", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    glossedWords := [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['d', 'i'], ['d', 'i'], [⟨['d', 'i'], ['d', 'i'], none⟩]⟩, ⟨['a', 'v', 'e', 'r', 'e'], ['h', 'a', 'v', 'e', '-', 'I', 'N', 'F'], []⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['f', 'i', 'g', 'l', 'i', 'o', '.'], ['c', 'h', 'i', 'l', 'd'], [⟨['f', 'i', 'g', 'l', 'i', 'o'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "belief"), ("grammatical", "yes")] }

def ex4b : Datum :=
  { id := "fuscosgrizzi2026_ex4b"
    source := ⟨"fusco-sgrizzi-2026", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a avere un figlio."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    glossedWords := [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['a'], ['a'], [⟨['a'], ['a'], none⟩]⟩, ⟨['a', 'v', 'e', 'r', 'e'], ['h', 'a', 'v', 'e', '-', 'I', 'N', 'F'], []⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['f', 'i', 'g', 'l', 'i', 'o', '.'], ['c', 'h', 'i', 'l', 'd'], [⟨['f', 'i', 'g', 'l', 'i', 'o'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "intention"), ("grammatical", "yes")] }

def ex4a_control : Datum :=
  { id := "fuscosgrizzi2026_ex4a_control"
    source := ⟨"fusco-sgrizzi-2026", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    glossedWords := [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['d', 'i'], ['d', 'i'], [⟨['d', 'i'], ['d', 'i'], none⟩]⟩, ⟨['a', 'v', 'e', 'r', 'e'], ['h', 'a', 'v', 'e', '-', 'I', 'N', 'F'], []⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['f', 'i', 'g', 'l', 'i', 'o', '.'], ['c', 'h', 'i', 'l', 'd'], [⟨['f', 'i', 'g', 'l', 'i', 'o'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "subjectControl"), ("grammatical", "yes")] }

def ex11a : Datum :=
  { id := "fuscosgrizzi2026_ex11a"
    source := ⟨"fusco-sgrizzi-2026", "(11a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio, ma non è vero."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio,", "child"), ("ma", "but"), ("non", "not"), ("è", "be-PRS.3SG"), ("vero.", "true")]
    glossedWords := [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['d', 'i'], ['d', 'i'], [⟨['d', 'i'], ['d', 'i'], none⟩]⟩, ⟨['a', 'v', 'e', 'r', 'e'], ['h', 'a', 'v', 'e', '-', 'I', 'N', 'F'], []⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['f', 'i', 'g', 'l', 'i', 'o', ','], ['c', 'h', 'i', 'l', 'd'], [⟨['f', 'i', 'g', 'l', 'i', 'o'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['m', 'a'], ['b', 'u', 't'], [⟨['m', 'a'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'o', 'n'], ['n', 'o', 't'], [⟨['n', 'o', 'n'], ['n', 'o', 't'], none⟩]⟩, ⟨['è'], ['b', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['v', 'e', 'r', 'o', '.'], ['t', 'r', 'u', 'e'], [⟨['v', 'e', 'r', 'o'], ['t', 'r', 'u', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "truthAssessable"), ("grammatical", "yes")] }

def ex11b : Datum :=
  { id := "fuscosgrizzi2026_ex11b"
    source := ⟨"fusco-sgrizzi-2026", "(11b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni ad avere un figlio, ma non è vero."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("ad", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio,", "child"), ("ma", "but"), ("non", "not"), ("è", "be-PRS.3SG"), ("vero.", "true")]
    glossedWords := [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['a', 'd'], ['a'], [⟨['a', 'd'], ['a'], none⟩]⟩, ⟨['a', 'v', 'e', 'r', 'e'], ['h', 'a', 'v', 'e', '-', 'I', 'N', 'F'], []⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['f', 'i', 'g', 'l', 'i', 'o', ','], ['c', 'h', 'i', 'l', 'd'], [⟨['f', 'i', 'g', 'l', 'i', 'o'], ['c', 'h', 'i', 'l', 'd'], none⟩]⟩, ⟨['m', 'a'], ['b', 'u', 't'], [⟨['m', 'a'], ['b', 'u', 't'], none⟩]⟩, ⟨['n', 'o', 'n'], ['n', 'o', 't'], [⟨['n', 'o', 'n'], ['n', 'o', 't'], none⟩]⟩, ⟨['è'], ['b', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['v', 'e', 'r', 'o', '.'], ['t', 'r', 'u', 'e'], [⟨['v', 'e', 'r', 'o'], ['t', 'r', 'u', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .unacceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "truthAssessable"), ("grammatical", "no")] }

def ex12 : Datum :=
  { id := "fuscosgrizzi2026_ex12"
    source := ⟨"fusco-sgrizzi-2026", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La conduttrice ha convinto l'ospite ad essere intervistato."
    glossedTokens := [("La", "the"), ("conduttrice", "conductor"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("l'ospite", "the.guest"), ("ad", "to"), ("essere", "be-INF"), ("intervistato.", "interviewed-PST.PRT.M")]
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'o', 'n', 'd', 'u', 't', 't', 'r', 'i', 'c', 'e'], ['c', 'o', 'n', 'd', 'u', 'c', 't', 'o', 'r'], [⟨['c', 'o', 'n', 'd', 'u', 't', 't', 'r', 'i', 'c', 'e'], ['c', 'o', 'n', 'd', 'u', 'c', 't', 'o', 'r'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['l', '\'', 'o', 's', 'p', 'i', 't', 'e'], ['t', 'h', 'e', '.', 'g', 'u', 'e', 's', 't'], [⟨['l', '\'', 'o', 's', 'p', 'i', 't', 'e'], ['t', 'h', 'e', '.', 'g', 'u', 'e', 's', 't'], none⟩]⟩, ⟨['a', 'd'], ['t', 'o'], [⟨['a', 'd'], ['t', 'o'], none⟩]⟩, ⟨['e', 's', 's', 'e', 'r', 'e'], ['b', 'e', '-', 'I', 'N', 'F'], []⟩, ⟨['i', 'n', 't', 'e', 'r', 'v', 'i', 's', 't', 'a', 't', 'o', '.'], ['i', 'n', 't', 'e', 'r', 'v', 'i', 'e', 'w', 'e', 'd', '-', 'P', 'S', 'T', '.', 'P', 'R', 'T', '.', 'M'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "passive"), ("grammatical", "yes")] }

def ex13 : Datum :=
  { id := "fuscosgrizzi2026_ex13"
    source := ⟨"fusco-sgrizzi-2026", "(13)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a cominciare a lavorare."
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("cominciare", "begin-INF"), ("a", "to"), ("lavorare.", "work-INF")]
    glossedWords := [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], [⟨['M', 'a', 'r', 'c', 'o'], ['M', 'a', 'r', 'c', 'o'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['a'], ['a'], [⟨['a'], ['a'], none⟩]⟩, ⟨['c', 'o', 'm', 'i', 'n', 'c', 'i', 'a', 'r', 'e'], ['b', 'e', 'g', 'i', 'n', '-', 'I', 'N', 'F'], []⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['l', 'a', 'v', 'o', 'r', 'a', 'r', 'e', '.'], ['w', 'o', 'r', 'k', '-', 'I', 'N', 'F'], []⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "aspectual"), ("grammatical", "yes")] }

def ex14 : Datum :=
  { id := "fuscosgrizzi2026_ex14"
    source := ⟨"fusco-sgrizzi-2026", "(14)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "L'operaio lo prova a costruire."
    glossedTokens := [("L'operaio", "the-worker"), ("lo", "it"), ("prova", "try-PRS.3SG"), ("a", "to"), ("costruire.", "build")]
    glossedWords := [⟨['L', '\'', 'o', 'p', 'e', 'r', 'a', 'i', 'o'], ['t', 'h', 'e', '-', 'w', 'o', 'r', 'k', 'e', 'r'], []⟩, ⟨['l', 'o'], ['i', 't'], [⟨['l', 'o'], ['i', 't'], none⟩]⟩, ⟨['p', 'r', 'o', 'v', 'a'], ['t', 'r', 'y', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['c', 'o', 's', 't', 'r', 'u', 'i', 'r', 'e', '.'], ['b', 'u', 'i', 'l', 'd'], [⟨['c', 'o', 's', 't', 'r', 'u', 'i', 'r', 'e'], ['b', 'u', 'i', 'l', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "vP"), ("diagnostic", "cliticClimbing"), ("grammatical", "yes")] }

def ex15 : Datum :=
  { id := "fuscosgrizzi2026_ex15"
    source := ⟨"fusco-sgrizzi-2026", "(15)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni lo pensa a costruire domani."
    glossedTokens := [("Gianni", "Gianni"), ("lo", "it"), ("pensa", "think-PRS.3SG"), ("a", "to"), ("costruire", "build"), ("domani.", "tomorrow")]
    glossedWords := [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['l', 'o'], ['i', 't'], [⟨['l', 'o'], ['i', 't'], none⟩]⟩, ⟨['p', 'e', 'n', 's', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['c', 'o', 's', 't', 'r', 'u', 'i', 'r', 'e'], ['b', 'u', 'i', 'l', 'd'], [⟨['c', 'o', 's', 't', 'r', 'u', 'i', 'r', 'e'], ['b', 'u', 'i', 'l', 'd'], none⟩]⟩, ⟨['d', 'o', 'm', 'a', 'n', 'i', '.'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], [⟨['d', 'o', 'm', 'a', 'n', 'i'], ['t', 'o', 'm', 'o', 'r', 'r', 'o', 'w'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "cliticClimbing"), ("grammatical", "no")] }

def ex16 : Datum :=
  { id := "fuscosgrizzi2026_ex16"
    source := ⟨"fusco-sgrizzi-2026", "(16)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni mi ha convinto a non salutare più il capo."
    glossedTokens := [("Gianni", "Gianni"), ("mi", "me.CL"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("a", "to"), ("non", "not"), ("salutare", "greet-INF"), ("più", "anymore"), ("il", "the"), ("capo.", "boss")]
    glossedWords := [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['m', 'i'], ['m', 'e', '.', 'C', 'L'], [⟨['m', 'i'], ['m', 'e', '.', 'C', 'L'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['n', 'o', 'n'], ['n', 'o', 't'], [⟨['n', 'o', 'n'], ['n', 'o', 't'], none⟩]⟩, ⟨['s', 'a', 'l', 'u', 't', 'a', 'r', 'e'], ['g', 'r', 'e', 'e', 't', '-', 'I', 'N', 'F'], []⟩, ⟨['p', 'i', 'ù'], ['a', 'n', 'y', 'm', 'o', 'r', 'e'], [⟨['p', 'i', 'ù'], ['a', 'n', 'y', 'm', 'o', 'r', 'e'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'p', 'o', '.'], ['b', 'o', 's', 's'], [⟨['c', 'a', 'p', 'o'], ['b', 'o', 's', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "negation"), ("grammatical", "yes")] }

def ex17 : Datum :=
  { id := "fuscosgrizzi2026_ex17"
    source := ⟨"fusco-sgrizzi-2026", "(17)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri Gianni mi ha convinto a comprare una macchina nuova il mese prossimo."
    glossedTokens := [("Ieri", "yesterday"), ("Gianni", "Gianni"), ("mi", "me.CL"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("a", "to"), ("comprare", "buy-INF"), ("una", "a"), ("macchina", "car"), ("nuova", "new"), ("il", "the"), ("mese", "month"), ("prossimo.", "next")]
    glossedWords := [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['m', 'i'], ['m', 'e', '.', 'C', 'L'], [⟨['m', 'i'], ['m', 'e', '.', 'C', 'L'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['c', 'o', 'n', 'v', 'i', 'n', 't', 'o'], ['c', 'o', 'n', 'v', 'i', 'n', 'c', 'e', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['c', 'o', 'm', 'p', 'r', 'a', 'r', 'e'], ['b', 'u', 'y', '-', 'I', 'N', 'F'], []⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'a', 'c', 'c', 'h', 'i', 'n', 'a'], ['c', 'a', 'r'], [⟨['m', 'a', 'c', 'c', 'h', 'i', 'n', 'a'], ['c', 'a', 'r'], none⟩]⟩, ⟨['n', 'u', 'o', 'v', 'a'], ['n', 'e', 'w'], [⟨['n', 'u', 'o', 'v', 'a'], ['n', 'e', 'w'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'e', 's', 'e'], ['m', 'o', 'n', 't', 'h'], [⟨['m', 'e', 's', 'e'], ['m', 'o', 'n', 't', 'h'], none⟩]⟩, ⟨['p', 'r', 'o', 's', 's', 'i', 'm', 'o', '.'], ['n', 'e', 'x', 't'], [⟨['p', 'r', 'o', 's', 's', 'i', 'm', 'o'], ['n', 'e', 'x', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "independentTime"), ("grammatical", "yes")] }

def ex18 : Datum :=
  { id := "fuscosgrizzi2026_ex18"
    source := ⟨"fusco-sgrizzi-2026", "(18)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri Gianni ha provato a riparare la macchina il mese prossimo."
    glossedTokens := [("Ieri", "yesterday"), ("Gianni", "Gianni"), ("ha", "have-PRS.3SG"), ("provato", "try-PST.PTCP"), ("a", "to"), ("riparare", "repair"), ("la", "the"), ("macchina", "car"), ("il", "the"), ("mese", "month"), ("prossimo.", "next")]
    glossedWords := [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], [⟨['G', 'i', 'a', 'n', 'n', 'i'], ['G', 'i', 'a', 'n', 'n', 'i'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '-', 'P', 'R', 'S', '.', '3', 'S', 'G'], []⟩, ⟨['p', 'r', 'o', 'v', 'a', 't', 'o'], ['t', 'r', 'y', '-', 'P', 'S', 'T', '.', 'P', 'T', 'C', 'P'], []⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['r', 'i', 'p', 'a', 'r', 'a', 'r', 'e'], ['r', 'e', 'p', 'a', 'i', 'r'], [⟨['r', 'i', 'p', 'a', 'r', 'a', 'r', 'e'], ['r', 'e', 'p', 'a', 'i', 'r'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'a', 'c', 'c', 'h', 'i', 'n', 'a'], ['c', 'a', 'r'], [⟨['m', 'a', 'c', 'c', 'h', 'i', 'n', 'a'], ['c', 'a', 'r'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['m', 'e', 's', 'e'], ['m', 'o', 'n', 't', 'h'], [⟨['m', 'e', 's', 'e'], ['m', 'o', 'n', 't', 'h'], none⟩]⟩, ⟨['p', 'r', 'o', 's', 's', 'i', 'm', 'o', '.'], ['n', 'e', 'x', 't'], [⟨['p', 'r', 'o', 's', 's', 'i', 'm', 'o'], ['n', 'e', 'x', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    contrasts := []
    readings := []
    paperFeatures := [("size", "vP"), ("diagnostic", "independentTime"), ("grammatical", "no")] }

def all : List Datum := [ex4a, ex4b, ex4a_control, ex11a, ex11b, ex12, ex13, ex14, ex15, ex16, ex17, ex18]

/-- A property of an infinitival complement the paper tests. -/
inductive Diagnostic where
  /-- belief: belief -/
  | belief
  /-- intention: intention -/
  | intention
  /-- truthAssessable: truthAssessable -/
  | truthAssessable
  /-- subjectControl: subjectControl -/
  | subjectControl
  /-- passive: passive -/
  | passive
  /-- aspectual: aspectual -/
  | aspectual
  /-- negation: negation -/
  | negation
  /-- independentTime: independentTime -/
  | independentTime
  /-- cliticClimbing: cliticClimbing -/
  | cliticClimbing
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `diagnostic`. -/
def diagnostic (e : Datum) : Option Diagnostic :=
  e.parse? "diagnostic" [("belief", .belief), ("intention", .intention), ("truthAssessable", .truthAssessable),
    ("subjectControl", .subjectControl), ("passive", .passive), ("aspectual", .aspectual),
    ("negation", .negation), ("independentTime", .independentTime),
    ("cliticClimbing", .cliticClimbing)]

end FuscoSgrizzi2026.Examples
