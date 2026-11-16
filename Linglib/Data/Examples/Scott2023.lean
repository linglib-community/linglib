module

public import Linglib.Data.Examples.Schema

/-!
# `Scott2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Scott2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Scott2023.Examples`.
-/

@[expose] public section

namespace Scott2023.Examples

def ex_78a : Datum :=
  { id := "scott2023_78a"
    source := ⟨"scott-2023", "ch. 4, (78a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma qo b'et *qo=y."
    glossedTokens := [("Ma", "PROX"), ("qo", "B1PL"), ("b'et", "walk"), ("qo=y", "1PL=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['q', 'o'], ['B', '1', 'P', 'L'], [⟨['q', 'o'], ['B', '1', 'P', 'L'], none⟩]⟩, ⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', 'o', '=', 'y'], ['1', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'o'], ['1', 'P', 'L'], none⟩, ⟨['y'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_78b : Datum :=
  { id := "scott2023_78b"
    source := ⟨"scott-2023", "ch. 4, (78b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' q-tz'ib'-an *qo=y."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("q-tz'ib'-an", "A1PL-write-DS"), ("qo=y", "1PL=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], [⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], none⟩]⟩, ⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], [⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], none⟩]⟩, ⟨['q', '-', 't', 'z', '\'', 'i', 'b', '\'', '-', 'a', 'n'], ['A', '1', 'P', 'L', '-', 'w', 'r', 'i', 't', 'e', '-', 'D', 'S'], [⟨['q'], ['A', '1', 'P', 'L'], none⟩, ⟨['t', 'z', '\'', 'i', 'b', '\''], ['w', 'r', 'i', 't', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['q', 'o', '=', 'y'], ['1', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'o'], ['1', 'P', 'L'], none⟩, ⟨['y'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_78c : Datum :=
  { id := "scott2023_78c"
    source := ⟨"scott-2023", "ch. 4, (78c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "q-lan *qo=y"
    glossedTokens := [("q-lan", "A1PL-wool.thread"), ("qo=y", "1PL=DISAGR")]
    glossedWords := [⟨['q', '-', 'l', 'a', 'n'], ['A', '1', 'P', 'L', '-', 'w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], [⟨['q'], ['A', '1', 'P', 'L'], none⟩, ⟨['l', 'a', 'n'], ['w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], some '-'⟩]⟩, ⟨['q', 'o', '=', 'y'], ['1', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'o'], ['1', 'P', 'L'], none⟩, ⟨['y'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_79 : Datum :=
  { id := "scott2023_79"
    source := ⟨"scott-2023", "ch. 4, (79)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qo'=y."
    glossedTokens := [("B'et", "walk"), ("qo'=y", "1PL=DISAGR")]
    glossedWords := [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', 'o', '\'', '=', 'y'], ['1', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'o', '\''], ['1', 'P', 'L'], none⟩, ⟨['y'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_68b : Datum :=
  { id := "scott2023_68b"
    source := ⟨"scott-2023", "ch. 4, (68b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "O qo tan=i."
    glossedTokens := [("O", "PFV"), ("qo", "B1PL"), ("tan", "sleep"), ("=i", "=DISAGR")]
    glossedWords := [⟨['O'], ['P', 'F', 'V'], [⟨['O'], ['P', 'F', 'V'], none⟩]⟩, ⟨['q', 'o'], ['B', '1', 'P', 'L'], [⟨['q', 'o'], ['B', '1', 'P', 'L'], none⟩]⟩, ⟨['t', 'a', 'n'], ['s', 'l', 'e', 'e', 'p'], [⟨['t', 'a', 'n'], ['s', 'l', 'e', 'e', 'p'], none⟩]⟩, ⟨['=', 'i'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1plExcl"), ("morphemes", "=i")] }

def ex_85a : Datum :=
  { id := "scott2023_85a"
    source := ⟨"scott-2023", "ch. 4, (85a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chin b'et *qin=i."
    glossedTokens := [("Ma", "PROX"), ("chin", "B1SG"), ("b'et", "walk"), ("qin=i", "1SG=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['c', 'h', 'i', 'n'], ['B', '1', 'S', 'G'], [⟨['c', 'h', 'i', 'n'], ['B', '1', 'S', 'G'], none⟩]⟩, ⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', 'i', 'n', '=', 'i'], ['1', 'S', 'G', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_85b : Datum :=
  { id := "scott2023_85b"
    source := ⟨"scott-2023", "ch. 4, (85b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' n-tz'ib'-an *qin=i."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("n-tz'ib'-an", "A1SG-write-DS"), ("qin=i", "1SG=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], [⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], none⟩]⟩, ⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], [⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], none⟩]⟩, ⟨['n', '-', 't', 'z', '\'', 'i', 'b', '\'', '-', 'a', 'n'], ['A', '1', 'S', 'G', '-', 'w', 'r', 'i', 't', 'e', '-', 'D', 'S'], [⟨['n'], ['A', '1', 'S', 'G'], none⟩, ⟨['t', 'z', '\'', 'i', 'b', '\''], ['w', 'r', 'i', 't', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['q', 'i', 'n', '=', 'i'], ['1', 'S', 'G', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_85c : Datum :=
  { id := "scott2023_85c"
    source := ⟨"scott-2023", "ch. 4, (85c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "n-lan *qin=i"
    glossedTokens := [("n-lan", "A1SG-wool.thread"), ("qin=i", "1SG=DISAGR")]
    glossedWords := [⟨['n', '-', 'l', 'a', 'n'], ['A', '1', 'S', 'G', '-', 'w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], [⟨['n'], ['A', '1', 'S', 'G'], none⟩, ⟨['l', 'a', 'n'], ['w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], some '-'⟩]⟩, ⟨['q', 'i', 'n', '=', 'i'], ['1', 'S', 'G', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_62 : Datum :=
  { id := "scott2023_62"
    source := ⟨"scott-2023", "ch. 3, (62)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chin b'et=i."
    glossedTokens := [("Ma", "PROX"), ("chin", "B1SG"), ("b'et", "walk"), ("=i", "=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['c', 'h', 'i', 'n'], ['B', '1', 'S', 'G'], [⟨['c', 'h', 'i', 'n'], ['B', '1', 'S', 'G'], none⟩]⟩, ⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['=', 'i'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1sg"), ("morphemes", "=i")] }

def ex_86a : Datum :=
  { id := "scott2023_86a"
    source := ⟨"scott-2023", "ch. 4, (86a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'et q=i."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'et", "walk"), ("q=i", "2PL=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], [⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], none⟩]⟩, ⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', '=', 'i'], ['2', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q'], ['2', 'P', 'L'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_86b : Datum :=
  { id := "scott2023_86b"
    source := ⟨"scott-2023", "ch. 4, (86b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' ky-tz'ib'-an q=i."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("ky-tz'ib'-an", "A2/3PL-write-DS"), ("q=i", "2PL=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], [⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], none⟩]⟩, ⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], [⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], none⟩]⟩, ⟨['k', 'y', '-', 't', 'z', '\'', 'i', 'b', '\'', '-', 'a', 'n'], ['A', '2', '/', '3', 'P', 'L', '-', 'w', 'r', 'i', 't', 'e', '-', 'D', 'S'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['t', 'z', '\'', 'i', 'b', '\''], ['w', 'r', 'i', 't', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['q', '=', 'i'], ['2', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q'], ['2', 'P', 'L'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_86c : Datum :=
  { id := "scott2023_86c"
    source := ⟨"scott-2023", "ch. 4, (86c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-lan q=i"
    glossedTokens := [("ky-lan", "A2/3PL-wool.thread"), ("q=i", "2PL=DISAGR")]
    glossedWords := [⟨['k', 'y', '-', 'l', 'a', 'n'], ['A', '2', '/', '3', 'P', 'L', '-', 'w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['l', 'a', 'n'], ['w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], some '-'⟩]⟩, ⟨['q', '=', 'i'], ['2', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q'], ['2', 'P', 'L'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_87a : Datum :=
  { id := "scott2023_87a"
    source := ⟨"scott-2023", "ch. 4, (87a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'et qa."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'et", "walk"), ("qa", "PL")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], [⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], none⟩]⟩, ⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['b', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', 'a'], ['P', 'L'], [⟨['q', 'a'], ['P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_87b : Datum :=
  { id := "scott2023_87b"
    source := ⟨"scott-2023", "ch. 4, (87b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' ky-tz'ib'-an qa."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("ky-tz'ib'-an", "A2/3PL-write-DS"), ("qa", "PL")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], [⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], none⟩]⟩, ⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], [⟨['k', 'u', 'b', '\''], ['D', 'I', 'R', ':', 'd', 'o', 'w', 'n'], none⟩]⟩, ⟨['k', 'y', '-', 't', 'z', '\'', 'i', 'b', '\'', '-', 'a', 'n'], ['A', '2', '/', '3', 'P', 'L', '-', 'w', 'r', 'i', 't', 'e', '-', 'D', 'S'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['t', 'z', '\'', 'i', 'b', '\''], ['w', 'r', 'i', 't', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['q', 'a'], ['P', 'L'], [⟨['q', 'a'], ['P', 'L'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_87c : Datum :=
  { id := "scott2023_87c"
    source := ⟨"scott-2023", "ch. 4, (87c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-lan qa"
    glossedTokens := [("ky-lan", "A2/3PL-wool.thread"), ("qa", "PL")]
    glossedWords := [⟨['k', 'y', '-', 'l', 'a', 'n'], ['A', '2', '/', '3', 'P', 'L', '-', 'w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['l', 'a', 'n'], ['w', 'o', 'o', 'l', '.', 't', 'h', 'r', 'e', 'a', 'd'], some '-'⟩]⟩, ⟨['q', 'a'], ['P', 'L'], [⟨['q', 'a'], ['P', 'L'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_88b : Datum :=
  { id := "scott2023_88b"
    source := ⟨"scott-2023", "ch. 4, (88b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qin=i."
    glossedTokens := [("B'et", "walk"), ("qin=i", "1SG=DISAGR")]
    glossedWords := [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', 'i', 'n', '=', 'i'], ['1', 'S', 'G', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_88c : Datum :=
  { id := "scott2023_88c"
    source := ⟨"scott-2023", "ch. 4, (88c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et q=i."
    glossedTokens := [("B'et", "walk"), ("q=i", "2PL=DISAGR")]
    glossedWords := [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', '=', 'i'], ['2', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q'], ['2', 'P', 'L'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_88d : Datum :=
  { id := "scott2023_88d"
    source := ⟨"scott-2023", "ch. 4, (88d)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qa."
    glossedTokens := [("B'et", "walk"), ("qa", "PL")]
    glossedWords := [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], [⟨['B', '\'', 'e', 't'], ['w', 'a', 'l', 'k'], none⟩]⟩, ⟨['q', 'a'], ['P', 'L'], [⟨['q', 'a'], ['P', 'L'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_69a : Datum :=
  { id := "scott2023_69a"
    source := ⟨"scott-2023", "ch. 4, (69a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma tz'=ok ky-ke'y-an qa qin=i."
    glossedTokens := [("Ma", "PROX"), ("tz'=ok", "B2/3SG=DIR:in"), ("ky-ke'y-an", "A2/3PL-see-DS"), ("qa", "PL"), ("qin=i", "1SG=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['t', 'z', '\'', '=', 'o', 'k'], ['B', '2', '/', '3', 'S', 'G', '=', 'D', 'I', 'R', ':', 'i', 'n'], [⟨['t', 'z', '\''], ['B', '2', '/', '3', 'S', 'G'], none⟩, ⟨['o', 'k'], ['D', 'I', 'R', ':', 'i', 'n'], some '='⟩]⟩, ⟨['k', 'y', '-', 'k', 'e', '\'', 'y', '-', 'a', 'n'], ['A', '2', '/', '3', 'P', 'L', '-', 's', 'e', 'e', '-', 'D', 'S'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['k', 'e', '\'', 'y'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['q', 'a'], ['P', 'L'], [⟨['q', 'a'], ['P', 'L'], none⟩]⟩, ⟨['q', 'i', 'n', '=', 'i'], ['1', 'S', 'G', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "object"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_89a : Datum :=
  { id := "scott2023_89a"
    source := ⟨"scott-2023", "ch. 4, (89a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-ja q=i"
    glossedTokens := [("ky-ja", "A2/3PL-house"), ("q=i", "2PL=DISAGR")]
    glossedWords := [⟨['k', 'y', '-', 'j', 'a'], ['A', '2', '/', '3', 'P', 'L', '-', 'h', 'o', 'u', 's', 'e'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['j', 'a'], ['h', 'o', 'u', 's', 'e'], some '-'⟩]⟩, ⟨['q', '=', 'i'], ['2', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q'], ['2', 'P', 'L'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_89b : Datum :=
  { id := "scott2023_89b"
    source := ⟨"scott-2023", "ch. 4, (89b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-ja=y"
    glossedTokens := [("ky-ja", "A2/3PL-house"), ("=y", "=DISAGR")]
    glossedWords := [⟨['k', 'y', '-', 'j', 'a'], ['A', '2', '/', '3', 'P', 'L', '-', 'h', 'o', 'u', 's', 'e'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['j', 'a'], ['h', 'o', 'u', 's', 'e'], some '-'⟩]⟩, ⟨['=', 'y'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['y'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "=i"), ("optionalReduction", "yes")] }

def ex_90b : Datum :=
  { id := "scott2023_90b"
    source := ⟨"scott-2023", "ch. 4, (90b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ tzaj ky-q'ama-'n=i w-i=y."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("tzaj", "DIR:come"), ("ky-q'ama-'n", "A2/3PL-tell-DS"), ("=i", "=DISAGR"), ("w-i=y", "A1SG-RN:dat=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], [⟨['∅'], ['B', '2', '/', '3', 'S', 'G'], none⟩]⟩, ⟨['t', 'z', 'a', 'j'], ['D', 'I', 'R', ':', 'c', 'o', 'm', 'e'], [⟨['t', 'z', 'a', 'j'], ['D', 'I', 'R', ':', 'c', 'o', 'm', 'e'], none⟩]⟩, ⟨['k', 'y', '-', 'q', '\'', 'a', 'm', 'a', '-', '\'', 'n'], ['A', '2', '/', '3', 'P', 'L', '-', 't', 'e', 'l', 'l', '-', 'D', 'S'], [⟨['k', 'y'], ['A', '2', '/', '3', 'P', 'L'], none⟩, ⟨['q', '\'', 'a', 'm', 'a'], ['t', 'e', 'l', 'l'], some '-'⟩, ⟨['\'', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['=', 'i'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩, ⟨['w', '-', 'i', '=', 'y'], ['A', '1', 'S', 'G', '-', 'R', 'N', ':', 'd', 'a', 't', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['w'], ['A', '1', 'S', 'G'], none⟩, ⟨['i'], ['R', 'N', ':', 'd', 'a', 't'], some '-'⟩, ⟨['y'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "2pl"), ("morphemes", "=i"), ("optionalReduction", "yes")] }

def ex_91a : Datum :=
  { id := "scott2023_91a"
    source := ⟨"scott-2023", "ch. 4, (91a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'ix-an q=i."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'ix-an", "dance-DS"), ("q=i", "2PL=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], [⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], none⟩]⟩, ⟨['b', '\'', 'i', 'x', '-', 'a', 'n'], ['d', 'a', 'n', 'c', 'e', '-', 'D', 'S'], [⟨['b', '\'', 'i', 'x'], ['d', 'a', 'n', 'c', 'e'], none⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['q', '=', 'i'], ['2', 'P', 'L', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q'], ['2', 'P', 'L'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_91b : Datum :=
  { id := "scott2023_91b"
    source := ⟨"scott-2023", "ch. 4, (91b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'ix-n=i."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'ix-n", "dance-DS"), ("=i", "=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], [⟨['c', 'h', 'i'], ['B', '2', '/', '3', 'P', 'L'], none⟩]⟩, ⟨['b', '\'', 'i', 'x', '-', 'n'], ['d', 'a', 'n', 'c', 'e', '-', 'D', 'S'], [⟨['b', '\'', 'i', 'x'], ['d', 'a', 'n', 'c', 'e'], none⟩, ⟨['n'], ['D', 'S'], some '-'⟩]⟩, ⟨['=', 'i'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "=i")] }

def ex_57 : Datum :=
  { id := "scott2023_57"
    source := ⟨"scott-2023", "ch. 3, (57)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chn=ok t-ke'y-an Mintz."
    glossedTokens := [("Ma", "PROX"), ("chn=ok", "B1SG=DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("Mintz", "Mintz")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['c', 'h', 'n', '=', 'o', 'k'], ['B', '1', 'S', 'G', '=', 'D', 'I', 'R', ':', 'i', 'n'], [⟨['c', 'h', 'n'], ['B', '1', 'S', 'G'], none⟩, ⟨['o', 'k'], ['D', 'I', 'R', ':', 'i', 'n'], some '='⟩]⟩, ⟨['t', '-', 'k', 'e', '\'', 'y', '-', 'a', 'n'], ['A', '2', '/', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['k', 'e', '\'', 'y'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['M', 'i', 'n', 't', 'z'], ['M', 'i', 'n', 't', 'z'], [⟨['M', 'i', 'n', 't', 'z'], ['M', 'i', 'n', 't', 'z'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "agreeingObject"), ("cell", "1sg"), ("setB", "chin")] }

def ex_59 : Datum :=
  { id := "scott2023_59"
    source := ⟨"scott-2023", "ch. 3, (59)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma tz'=ok t-ke'y-an Mintz qin=i."
    glossedTokens := [("Ma", "PROX"), ("tz'=ok", "B2/3SG=DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("Mintz", "Mintz"), ("qin=i", "1SG=DISAGR")]
    glossedWords := [⟨['M', 'a'], ['P', 'R', 'O', 'X'], [⟨['M', 'a'], ['P', 'R', 'O', 'X'], none⟩]⟩, ⟨['t', 'z', '\'', '=', 'o', 'k'], ['B', '2', '/', '3', 'S', 'G', '=', 'D', 'I', 'R', ':', 'i', 'n'], [⟨['t', 'z', '\''], ['B', '2', '/', '3', 'S', 'G'], none⟩, ⟨['o', 'k'], ['D', 'I', 'R', ':', 'i', 'n'], some '='⟩]⟩, ⟨['t', '-', 'k', 'e', '\'', 'y', '-', 'a', 'n'], ['A', '2', '/', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['k', 'e', '\'', 'y'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['M', 'i', 'n', 't', 'z'], ['M', 'i', 'n', 't', 'z'], [⟨['M', 'i', 'n', 't', 'z'], ['M', 'i', 'n', 't', 'z'], none⟩]⟩, ⟨['q', 'i', 'n', '=', 'i'], ['1', 'S', 'G', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "defaultObject"), ("cell", "1sg"), ("setB", "tz'")] }

def ex_73 : Datum :=
  { id := "scott2023_73"
    source := ⟨"scott-2023", "ch. 3, (73)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Taj w-ul=i …"
    glossedTokens := [("Taj", "when"), ("w-ul", "A1SG-arrive"), ("=i", "=DISAGR")]
    glossedWords := [⟨['T', 'a', 'j'], ['w', 'h', 'e', 'n'], [⟨['T', 'a', 'j'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['w', '-', 'u', 'l'], ['A', '1', 'S', 'G', '-', 'a', 'r', 'r', 'i', 'v', 'e'], [⟨['w'], ['A', '1', 'S', 'G'], none⟩, ⟨['u', 'l'], ['a', 'r', 'r', 'i', 'v', 'e'], some '-'⟩]⟩, ⟨['=', 'i'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extendedErgative"), ("position", "S"), ("cell", "1sg"), ("setA", "w")] }

def ex_77a : Datum :=
  { id := "scott2023_77a"
    source := ⟨"scott-2023", "ch. 3, (77a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Taj t-ok t-ke'y-an=i qin=i …"
    glossedTokens := [("Taj", "when"), ("t-ok", "A2/3SG-DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("=i", "=DISAGR"), ("qin=i", "1SG=DISAGR")]
    glossedWords := [⟨['T', 'a', 'j'], ['w', 'h', 'e', 'n'], [⟨['T', 'a', 'j'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['t', '-', 'o', 'k'], ['A', '2', '/', '3', 'S', 'G', '-', 'D', 'I', 'R', ':', 'i', 'n'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['o', 'k'], ['D', 'I', 'R', ':', 'i', 'n'], some '-'⟩]⟩, ⟨['t', '-', 'k', 'e', '\'', 'y', '-', 'a', 'n'], ['A', '2', '/', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['k', 'e', '\'', 'y'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['=', 'i'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩, ⟨['q', 'i', 'n', '=', 'i'], ['1', 'S', 'G', '=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['q', 'i', 'n'], ['1', 'S', 'G'], none⟩, ⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "object"), ("cell", "1sg"), ("setA", "t")] }

def ex_77b : Datum :=
  { id := "scott2023_77b"
    source := ⟨"scott-2023", "ch. 3, (77b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Taj w-ok t-ke'y-an=i …"
    glossedTokens := [("Taj", "when"), ("w-ok", "A1SG-DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("=i", "=DISAGR")]
    glossedWords := [⟨['T', 'a', 'j'], ['w', 'h', 'e', 'n'], [⟨['T', 'a', 'j'], ['w', 'h', 'e', 'n'], none⟩]⟩, ⟨['w', '-', 'o', 'k'], ['A', '1', 'S', 'G', '-', 'D', 'I', 'R', ':', 'i', 'n'], [⟨['w'], ['A', '1', 'S', 'G'], none⟩, ⟨['o', 'k'], ['D', 'I', 'R', ':', 'i', 'n'], some '-'⟩]⟩, ⟨['t', '-', 'k', 'e', '\'', 'y', '-', 'a', 'n'], ['A', '2', '/', '3', 'S', 'G', '-', 's', 'e', 'e', '-', 'D', 'S'], [⟨['t'], ['A', '2', '/', '3', 'S', 'G'], none⟩, ⟨['k', 'e', '\'', 'y'], ['s', 'e', 'e'], some '-'⟩, ⟨['a', 'n'], ['D', 'S'], some '-'⟩]⟩, ⟨['=', 'i'], ['=', 'D', 'I', 'S', 'A', 'G', 'R'], [⟨['i'], ['D', 'I', 'S', 'A', 'G', 'R'], some '='⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "object"), ("cell", "1sg"), ("setA", "w")] }

def all : List Datum := [ex_78a, ex_78b, ex_78c, ex_79, ex_68b, ex_85a, ex_85b, ex_85c, ex_62, ex_86a, ex_86b, ex_86c, ex_87a, ex_87b, ex_87c, ex_88b, ex_88c, ex_88d, ex_69a, ex_89a, ex_89b, ex_90b, ex_91a, ex_91b, ex_57, ex_59, ex_73, ex_77a, ex_77b]

end Scott2023.Examples
