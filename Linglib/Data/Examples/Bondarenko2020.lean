module

public import Linglib.Data.Examples.Schema

/-!
# `Bondarenko2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Bondarenko2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bondarenko2020.Examples`.
-/

@[expose] public section

namespace Bondarenko2020.Examples

def ex_1a : Datum :=
  { id := "bondarenko2020_1a"
    source := ⟨"bondarenko-2020", "(1a)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi zagaha ɘdj-ɘ: gɘžɘ han-a:"
    glossedTokens := [("Dugar", "Dugar"), ("mi:sgɘi", "cat.NOM"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("gɘžɘ", "COMP"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['D', 'u', 'g', 'a', 'r']], [['D', 'u', 'g', 'a', 'r']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't', '.', 'N', 'O', 'M']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ']], [['e', 'a', 't'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ɘ', 'ž', 'ɘ']], [['C', 'O', 'M', 'P']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := [("Dugar mi:sgɘi zagaha ɘdi-xɘ gɘžɘ han-a:", .acceptable)]
    readings := []
    paperFeatures := [("complement", "CP"), ("translation", "think")] }

def ex_1b : Datum :=
  { id := "bondarenko2020_1b"
    source := ⟨"bondarenko-2020", "(1b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi zagaha ɘdj-ɘ: gɘžɘ han-a: xarin mi:sgɘi zagaha ɘdj-ɘ:-güi"
    glossedTokens := [("Dugar", "Dugar"), ("mi:sgɘi", "cat.NOM"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("gɘžɘ", "COMP"), ("han-a:", "think-PST"), ("xarin", "but"), ("mi:sgɘi", "cat"), ("zagaha", "fish"), ("ɘdj-ɘ:-güi", "eat-PST-NEG")]
    glossedWords := [⟨[['D', 'u', 'g', 'a', 'r']], [['D', 'u', 'g', 'a', 'r']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't', '.', 'N', 'O', 'M']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ']], [['e', 'a', 't'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ɘ', 'ž', 'ɘ']], [['C', 'O', 'M', 'P']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ'], ['g', 'ü', 'i']], [['e', 'a', 't'], ['P', 'S', 'T'], ['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The fish was missing. Dugar was wrong about who ate it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "CP"), ("test", "denial")] }

def ex_2a : Datum :=
  { id := "bondarenko2020_2a"
    source := ⟨"bondarenko-2020", "(2a)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ:ʃ-i:jɘ-n’ han-a:"
    glossedTokens := [("Dugar", "Dugar.NOM"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:ʃ-i:jɘ-n’", "eat-PART-ACC-3"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['D', 'u', 'g', 'a', 'r']], [['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i'], ['n']], [['c', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ'], ['n', '’']], [['e', 'a', 't'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C'], ['3']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("translation", "remember")] }

def ex_2b : Datum :=
  { id := "bondarenko2020_2b"
    source := ⟨"bondarenko-2020", "(2b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ:ʃ-i:jɘ-n’ han-a: xarin mi:sgɘi zagaha ɘdj-ɘ:-güi"
    glossedTokens := [("Dugar", "Dugar"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:ʃ-i:jɘ-n’", "eat-PART-ACC-3"), ("han-a:", "think-PST"), ("xarin", "but"), ("mi:sgɘi", "cat"), ("zagaha", "fish"), ("ɘdj-ɘ:-güi", "eat-PST-NEG")]
    glossedWords := [⟨[['D', 'u', 'g', 'a', 'r']], [['D', 'u', 'g', 'a', 'r']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i'], ['n']], [['c', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ'], ['n', '’']], [['e', 'a', 't'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C'], ['3']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ'], ['g', 'ü', 'i']], [['e', 'a', 't'], ['P', 'S', 'T'], ['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The fish was missing. Dugar is wrong about who ate it."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("test", "denial")] }

def ex_3a : Datum :=
  { id := "bondarenko2020_3a"
    source := ⟨"bondarenko-2020", "(3a)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Bi Badma tɘrgɘ ɘmdɘl-ɘ: gü gɘžɘ mɘdɘ-nɘ-güi-b xarin Sajana Badm-i:n tɘrgɘ ɘmdɘl-ɘ:ʃ-i:jɘ han-a:"
    glossedTokens := [("Bi", "1SG.NOM"), ("Badma", "Badma.NOM"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:", "break-PST"), ("gü", "Q"), ("gɘžɘ", "COMP"), ("mɘdɘ-nɘ-güi-b", "know-PRS-NEG-1SG"), ("xarin", "but"), ("Sajana", "Sajana.NOM"), ("Badm-i:n", "Badma-GEN"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:ʃ-i:jɘ", "break-PART-ACC"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['B', 'i']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ']], [['b', 'r', 'e', 'a', 'k'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ü']], [['Q']]⟩, ⟨[['g', 'ɘ', 'ž', 'ɘ']], [['C', 'O', 'M', 'P']]⟩, ⟨[['m', 'ɘ', 'd', 'ɘ'], ['n', 'ɘ'], ['g', 'ü', 'i'], ['b']], [['k', 'n', 'o', 'w'], ['P', 'R', 'S'], ['N', 'E', 'G'], ['1', 'S', 'G']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['S', 'a', 'j', 'a', 'n', 'a']], [['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm'], ['i', 'n']], [['B', 'a', 'd', 'm', 'a'], ['G', 'E', 'N']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ']], [['b', 'r', 'e', 'a', 'k'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker is ignorant about the issue, but wants to report Sajana's opinion/memory."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("test", "ignorance")] }

def ex_3b : Datum :=
  { id := "bondarenko2020_3b"
    source := ⟨"bondarenko-2020", "(3b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Bi Badma tɘrgɘ ɘmdɘl-ɘ: gü gɘžɘ mɘdɘ-nɘ-güi-b xarin Sajana Badma tɘrgɘ ɘmdɘl-ɘ: gɘžɘ han-a:"
    glossedTokens := [("Bi", "1SG.NOM"), ("Badma", "Badma.NOM"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:", "break-PST"), ("gü", "Q"), ("gɘžɘ", "COMP"), ("mɘdɘ-nɘ-güi-b", "know-PRS-NEG-1SG"), ("xarin", "but"), ("Sajana", "Sajana.NOM"), ("Badma", "Badma.NOM"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:", "break-PST"), ("gɘžɘ", "COMP"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['B', 'i']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ']], [['b', 'r', 'e', 'a', 'k'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ü']], [['Q']]⟩, ⟨[['g', 'ɘ', 'ž', 'ɘ']], [['C', 'O', 'M', 'P']]⟩, ⟨[['m', 'ɘ', 'd', 'ɘ'], ['n', 'ɘ'], ['g', 'ü', 'i'], ['b']], [['k', 'n', 'o', 'w'], ['P', 'R', 'S'], ['N', 'E', 'G'], ['1', 'S', 'G']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['S', 'a', 'j', 'a', 'n', 'a']], [['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ']], [['b', 'r', 'e', 'a', 'k'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ɘ', 'ž', 'ɘ']], [['C', 'O', 'M', 'P']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker is ignorant about the issue, but wants to report Sajana's opinion/memory."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "CP"), ("test", "ignorance")] }

def ex_4b : Datum :=
  { id := "bondarenko2020_4b"
    source := ⟨"bondarenko-2020", "(4b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Garag-ai xojor-to Sajana Badm-i:n tɘrgɘ ɘmdɘl-ɘ:ʃ-i:jɘ-n’ han-a: Badma tɘrgɘ garag-ai nɘgɘn-dɘ ɘmdɘlɘ-ʒɘ ɘxil-ɘ:"
    glossedTokens := [("Garag-ai", "day-GEN"), ("xojor-to", "two-DAT"), ("Sajana", "Sajana.NOM"), ("Badm-i:n", "Badma-GEN"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:ʃ-i:jɘ-n’", "break-PART-ACC-3"), ("han-a:", "think-PST"), ("Badma", "Badma.NOM"), ("tɘrgɘ", "cart"), ("garag-ai", "day-GEN"), ("nɘgɘn-dɘ", "one-DAT"), ("ɘmdɘlɘ-ʒɘ", "break-CVB"), ("ɘxil-ɘ:", "begin-PST")]
    glossedWords := [⟨[['G', 'a', 'r', 'a', 'g'], ['a', 'i']], [['d', 'a', 'y'], ['G', 'E', 'N']]⟩, ⟨[['x', 'o', 'j', 'o', 'r'], ['t', 'o']], [['t', 'w', 'o'], ['D', 'A', 'T']]⟩, ⟨[['S', 'a', 'j', 'a', 'n', 'a']], [['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm'], ['i', 'n']], [['B', 'a', 'd', 'm', 'a'], ['G', 'E', 'N']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ'], ['n', '’']], [['b', 'r', 'e', 'a', 'k'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C'], ['3']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩, ⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['g', 'a', 'r', 'a', 'g'], ['a', 'i']], [['d', 'a', 'y'], ['G', 'E', 'N']]⟩, ⟨[['n', 'ɘ', 'g', 'ɘ', 'n'], ['d', 'ɘ']], [['o', 'n', 'e'], ['D', 'A', 'T']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l', 'ɘ'], ['ʒ', 'ɘ']], [['b', 'r', 'e', 'a', 'k'], ['C', 'V', 'B']]⟩, ⟨[['ɘ', 'x', 'i', 'l'], ['ɘ']], [['b', 'e', 'g', 'i', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("test", "pre-existence")] }

def ex_4c : Datum :=
  { id := "bondarenko2020_4c"
    source := ⟨"bondarenko-2020", "(4c)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Garag-ai xojor-to Sajana Badm-i:n tɘrgɘ ɘmdɘl-ɘ:ʃ-i:jɘ-n’ han-a: Badma tɘrgɘ garag-ai gurban-da ɘmdɘlɘ-ʒɘ ɘxil-ɘ:"
    glossedTokens := [("Garag-ai", "day-GEN"), ("xojor-to", "two-DAT"), ("Sajana", "Sajana.NOM"), ("Badm-i:n", "Badma-GEN"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:ʃ-i:jɘ-n’", "break-PART-ACC-3"), ("han-a:", "think-PST"), ("Badma", "Badma.NOM"), ("tɘrgɘ", "cart"), ("garag-ai", "day-GEN"), ("gurban-da", "three-DAT"), ("ɘmdɘlɘ-ʒɘ", "break-CVB"), ("ɘxil-ɘ:", "begin-PST")]
    glossedWords := [⟨[['G', 'a', 'r', 'a', 'g'], ['a', 'i']], [['d', 'a', 'y'], ['G', 'E', 'N']]⟩, ⟨[['x', 'o', 'j', 'o', 'r'], ['t', 'o']], [['t', 'w', 'o'], ['D', 'A', 'T']]⟩, ⟨[['S', 'a', 'j', 'a', 'n', 'a']], [['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm'], ['i', 'n']], [['B', 'a', 'd', 'm', 'a'], ['G', 'E', 'N']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ'], ['n', '’']], [['b', 'r', 'e', 'a', 'k'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C'], ['3']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩, ⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['g', 'a', 'r', 'a', 'g'], ['a', 'i']], [['d', 'a', 'y'], ['G', 'E', 'N']]⟩, ⟨[['g', 'u', 'r', 'b', 'a', 'n'], ['d', 'a']], [['t', 'h', 'r', 'e', 'e'], ['D', 'A', 'T']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l', 'ɘ'], ['ʒ', 'ɘ']], [['b', 'r', 'e', 'a', 'k'], ['C', 'V', 'B']]⟩, ⟨[['ɘ', 'x', 'i', 'l'], ['ɘ']], [['b', 'e', 'g', 'i', 'n'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("test", "pre-existence")] }

def ex_5a : Datum :=
  { id := "bondarenko2020_5a"
    source := ⟨"bondarenko-2020", "(5a)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Sɘsɘg gar-ga-x-a: bai-ga:n üxibü-jɘ: han-a:"
    glossedTokens := [("Sɘsɘg", "Seseg"), ("gar-ga-x-a:", "go.out-CAUS-POT-REFL"), ("bai-ga:n", "be-PFCT"), ("üxibü-jɘ:", "child-ACC.REFL"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['S', 'ɘ', 's', 'ɘ', 'g']], [['S', 'e', 's', 'e', 'g']]⟩, ⟨[['g', 'a', 'r'], ['g', 'a'], ['x'], ['a']], [['g', 'o', '.', 'o', 'u', 't'], ['C', 'A', 'U', 'S'], ['P', 'O', 'T'], ['R', 'E', 'F', 'L']]⟩, ⟨[['b', 'a', 'i'], ['g', 'a', 'n']], [['b', 'e'], ['P', 'F', 'C', 'T']]⟩, ⟨[['ü', 'x', 'i', 'b', 'ü'], ['j', 'ɘ']], [['c', 'h', 'i', 'l', 'd'], ['A', 'C', 'C', '.', 'R', 'E', 'F', 'L']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Currently Seseg has a child. The speaker is talking about some time 7 years ago. 7 years ago, Seseg was pregnant with a baby, she has seen her/him during an ultrasound."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("argument", "noun phrase"), ("test", "pre-existence")] }

def ex_5b : Datum :=
  { id := "bondarenko2020_5b"
    source := ⟨"bondarenko-2020", "(5b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Sɘsɘg gar-ga-x-a: bai-ga:n üxibü-jɘ: han-a:"
    glossedTokens := [("Sɘsɘg", "Seseg"), ("gar-ga-x-a:", "go.out-CAUS-POT-REFL"), ("bai-ga:n", "be-PFCT"), ("üxibü-jɘ:", "child-ACC.REFL"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['S', 'ɘ', 's', 'ɘ', 'g']], [['S', 'e', 's', 'e', 'g']]⟩, ⟨[['g', 'a', 'r'], ['g', 'a'], ['x'], ['a']], [['g', 'o', '.', 'o', 'u', 't'], ['C', 'A', 'U', 'S'], ['P', 'O', 'T'], ['R', 'E', 'F', 'L']]⟩, ⟨[['b', 'a', 'i'], ['g', 'a', 'n']], [['b', 'e'], ['P', 'F', 'C', 'T']]⟩, ⟨[['ü', 'x', 'i', 'b', 'ü'], ['j', 'ɘ']], [['c', 'h', 'i', 'l', 'd'], ['A', 'C', 'C', '.', 'R', 'E', 'F', 'L']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Currently Seseg has a child. The speaker is talking about some time 7 years ago. 7 years ago, Seseg was not pregnant. But she really wanted a baby and was planning to have one."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("argument", "noun phrase"), ("test", "pre-existence")] }

def ex_6a : Datum :=
  { id := "bondarenko2020_6a"
    source := ⟨"bondarenko-2020", "(6a)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Badma naiman tarxi-tai mi:sgɘi-ɘ hana-na"
    glossedTokens := [("Badma", "Badma"), ("naiman", "eight"), ("tarxi-tai", "head-COM"), ("mi:sgɘi-ɘ", "cat-ACC"), ("hana-na", "think-PRS")]
    glossedWords := [⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a']]⟩, ⟨[['n', 'a', 'i', 'm', 'a', 'n']], [['e', 'i', 'g', 'h', 't']]⟩, ⟨[['t', 'a', 'r', 'x', 'i'], ['t', 'a', 'i']], [['h', 'e', 'a', 'd'], ['C', 'O', 'M']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i'], ['ɘ']], [['c', 'a', 't'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'n', 'a'], ['n', 'a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'R', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Children at school are asked to imagine a magical animal that does not exist and draw it."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("argument", "noun phrase"), ("test", "pre-existence")] }

def ex_6b : Datum :=
  { id := "bondarenko2020_6b"
    source := ⟨"bondarenko-2020", "(6b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Badm-ain tarxi so: naiman tarxi-tai mi:sgɘi or-o:"
    glossedTokens := [("Badm-ain", "Badma-GEN"), ("tarxi", "head"), ("so:", "in"), ("naiman", "eight"), ("tarxi-tai", "head-COM"), ("mi:sgɘi", "cat"), ("or-o:", "come-PST")]
    glossedWords := [⟨[['B', 'a', 'd', 'm'], ['a', 'i', 'n']], [['B', 'a', 'd', 'm', 'a'], ['G', 'E', 'N']]⟩, ⟨[['t', 'a', 'r', 'x', 'i']], [['h', 'e', 'a', 'd']]⟩, ⟨[['s', 'o']], [['i', 'n']]⟩, ⟨[['n', 'a', 'i', 'm', 'a', 'n']], [['e', 'i', 'g', 'h', 't']]⟩, ⟨[['t', 'a', 'r', 'x', 'i'], ['t', 'a', 'i']], [['h', 'e', 'a', 'd'], ['C', 'O', 'M']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't']]⟩, ⟨[['o', 'r'], ['o']], [['c', 'o', 'm', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Children at school are asked to imagine a magical animal that does not exist and draw it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "came into head")] }

def ex_7a : Datum :=
  { id := "bondarenko2020_7a"
    source := ⟨"bondarenko-2020", "(7a)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Sɘsɘg gar-ga-x-a: bai-ga:n üxibü-n tuxai-ga: hana-na"
    glossedTokens := [("Sɘsɘg", "Seseg"), ("gar-ga-x-a:", "go.out-CAUS-POT-REFL"), ("bai-ga:n", "be-PFCT"), ("üxibü-n", "child-NOM"), ("tuxai-ga:", "about-ACC.REFL"), ("hana-na", "think-PRS")]
    glossedWords := [⟨[['S', 'ɘ', 's', 'ɘ', 'g']], [['S', 'e', 's', 'e', 'g']]⟩, ⟨[['g', 'a', 'r'], ['g', 'a'], ['x'], ['a']], [['g', 'o', '.', 'o', 'u', 't'], ['C', 'A', 'U', 'S'], ['P', 'O', 'T'], ['R', 'E', 'F', 'L']]⟩, ⟨[['b', 'a', 'i'], ['g', 'a', 'n']], [['b', 'e'], ['P', 'F', 'C', 'T']]⟩, ⟨[['ü', 'x', 'i', 'b', 'ü'], ['n']], [['c', 'h', 'i', 'l', 'd'], ['N', 'O', 'M']]⟩, ⟨[['t', 'u', 'x', 'a', 'i'], ['g', 'a']], [['a', 'b', 'o', 'u', 't'], ['A', 'C', 'C', '.', 'R', 'E', 'F', 'L']]⟩, ⟨[['h', 'a', 'n', 'a'], ['n', 'a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'R', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Seseg is not pregnant."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("argument", "tuxai phrase"), ("test", "pre-existence")] }

def ex_7b : Datum :=
  { id := "bondarenko2020_7b"
    source := ⟨"bondarenko-2020", "(7b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Badma naiman tarxi-tai mi:sgɘi tuxai hana-na"
    glossedTokens := [("Badma", "Badma"), ("naiman", "eight"), ("tarxi-tai", "head-COM"), ("mi:sgɘi", "cat"), ("tuxai", "about"), ("hana-na", "think-PRS")]
    glossedWords := [⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a']]⟩, ⟨[['n', 'a', 'i', 'm', 'a', 'n']], [['e', 'i', 'g', 'h', 't']]⟩, ⟨[['t', 'a', 'r', 'x', 'i'], ['t', 'a', 'i']], [['h', 'e', 'a', 'd'], ['C', 'O', 'M']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't']]⟩, ⟨[['t', 'u', 'x', 'a', 'i']], [['a', 'b', 'o', 'u', 't']]⟩, ⟨[['h', 'a', 'n', 'a'], ['n', 'a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'R', 'S']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Badma is imagining a non-existing magical animal."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("argument", "tuxai phrase"), ("test", "pre-existence")] }

def ex_8 : Datum :=
  { id := "bondarenko2020_8"
    source := ⟨"bondarenko-2020", "(8)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Sajana Badm-i:jɘ han-a:"
    glossedTokens := [("Sajana", "Sajana.NOM"), ("Badm-i:jɘ", "Badma-ACC"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['S', 'a', 'j', 'a', 'n', 'a']], [['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm'], ['i', 'j', 'ɘ']], [['B', 'a', 'd', 'm', 'a'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Badma is currently alive."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("argument", "noun phrase")] }

def ex_14 : Datum :=
  { id := "bondarenko2020_14"
    source := ⟨"bondarenko-2020", "(14)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Bi Badma tɘrgɘ ɘmdɘl-ɘ: gü gɘžɘ mɘdɘ-nɘ-güi-b Sajana Badm-i:n tɘrgɘ ɘmdɘl-ɘ:ʃ-i:jɘ hana-na gü?"
    glossedTokens := [("Bi", "1SG.NOM"), ("Badma", "Badma.NOM"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:", "break-PST"), ("gü", "Q"), ("gɘžɘ", "COMP"), ("mɘdɘ-nɘ-güi-b", "know-PRS-NEG-1SG,"), ("Sajana", "Sajana.NOM"), ("Badm-i:n", "Badma-GEN"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:ʃ-i:jɘ", "break-PART-ACC"), ("hana-na", "think-PRS"), ("gü", "Q")]
    glossedWords := [⟨[['B', 'i']], [['1', 'S', 'G', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ']], [['b', 'r', 'e', 'a', 'k'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ü']], [['Q']]⟩, ⟨[['g', 'ɘ', 'ž', 'ɘ']], [['C', 'O', 'M', 'P']]⟩, ⟨[['m', 'ɘ', 'd', 'ɘ'], ['n', 'ɘ'], ['g', 'ü', 'i'], ['b']], [['k', 'n', 'o', 'w'], ['P', 'R', 'S'], ['N', 'E', 'G'], ['1', 'S', 'G', ',']]⟩, ⟨[['S', 'a', 'j', 'a', 'n', 'a']], [['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['B', 'a', 'd', 'm'], ['i', 'n']], [['B', 'a', 'd', 'm', 'a'], ['G', 'E', 'N']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ']], [['b', 'r', 'e', 'a', 'k'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'n', 'a'], ['n', 'a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'R', 'S']]⟩, ⟨[['g', 'ü']], [['Q']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker is ignorant about whether Badma broke the cart or not, and is wondering whether Sajana might have thoughts on the matter."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("test", "question")] }

def ex_15 : Datum :=
  { id := "bondarenko2020_15"
    source := ⟨"bondarenko-2020", "(15)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Badm-i:n tɘrgɘ ɘmdɘl-ɘ:ʃ-i:jɘ Sajana han-a:-güi, Badma tɘrgɘ ɘmdɘl-ɘ:-güi"
    glossedTokens := [("Badm-i:n", "Badma-GEN"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:ʃ-i:jɘ", "break-PART-ACC"), ("Sajana", "Sajana.NOM"), ("han-a:-güi", "think-PST-NEG"), ("Badma", "Badma.NOM"), ("tɘrgɘ", "cart"), ("ɘmdɘl-ɘ:-güi", "break-PST-NEG")]
    glossedWords := [⟨[['B', 'a', 'd', 'm'], ['i', 'n']], [['B', 'a', 'd', 'm', 'a'], ['G', 'E', 'N']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ']], [['b', 'r', 'e', 'a', 'k'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C']]⟩, ⟨[['S', 'a', 'j', 'a', 'n', 'a']], [['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['h', 'a', 'n'], ['a'], ['g', 'ü', 'i']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T'], ['N', 'E', 'G']]⟩, ⟨[['B', 'a', 'd', 'm', 'a']], [['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['t', 'ɘ', 'r', 'g', 'ɘ']], [['c', 'a', 'r', 't']]⟩, ⟨[['ɘ', 'm', 'd', 'ɘ', 'l'], ['ɘ'], ['g', 'ü', 'i']], [['b', 'r', 'e', 'a', 'k'], ['P', 'S', 'T'], ['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The speaker wants to convey that Sajana's thoughts are consistent with reality."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("test", "negation")] }

def ex_43a : Datum :=
  { id := "bondarenko2020_43a"
    source := ⟨"bondarenko-2020", "(43a)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Darima gɘr-tɘ xulgaiʃan or-o: gɘžɘ hana-na, xarin tɘrɘ axa-n’ Xurumxa:n-ha: jɘrɘ-hɘn bai-ga:"
    glossedTokens := [("Darima", "Darima.NOM"), ("gɘr-tɘ", "house-DAT"), ("xulgaiʃan", "thief.NOM"), ("or-o:", "enter-PST"), ("gɘžɘ", "COMP"), ("hana-na", "think-PRS"), ("xarin", "but"), ("tɘrɘ", "that"), ("axa-n’", "brother-3.NOM"), ("Xurumxa:n-ha:", "Kurumkan-ABL"), ("jɘrɘ-hɘn", "come-PFCT"), ("bai-ga:", "be-PST")]
    glossedWords := [⟨[['D', 'a', 'r', 'i', 'm', 'a']], [['D', 'a', 'r', 'i', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['g', 'ɘ', 'r'], ['t', 'ɘ']], [['h', 'o', 'u', 's', 'e'], ['D', 'A', 'T']]⟩, ⟨[['x', 'u', 'l', 'g', 'a', 'i', 'ʃ', 'a', 'n']], [['t', 'h', 'i', 'e', 'f', '.', 'N', 'O', 'M']]⟩, ⟨[['o', 'r'], ['o']], [['e', 'n', 't', 'e', 'r'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ɘ', 'ž', 'ɘ']], [['C', 'O', 'M', 'P']]⟩, ⟨[['h', 'a', 'n', 'a'], ['n', 'a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'R', 'S']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['t', 'ɘ', 'r', 'ɘ']], [['t', 'h', 'a', 't']]⟩, ⟨[['a', 'x', 'a'], ['n', '’']], [['b', 'r', 'o', 't', 'h', 'e', 'r'], ['3', '.', 'N', 'O', 'M']]⟩, ⟨[['X', 'u', 'r', 'u', 'm', 'x', 'a', 'n'], ['h', 'a']], [['K', 'u', 'r', 'u', 'm', 'k', 'a', 'n'], ['A', 'B', 'L']]⟩, ⟨[['j', 'ɘ', 'r', 'ɘ'], ['h', 'ɘ', 'n']], [['c', 'o', 'm', 'e'], ['P', 'F', 'C', 'T']]⟩, ⟨[['b', 'a', 'i'], ['g', 'a']], [['b', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Darima recalled a situation that happened recently. She heard some unexpected noise in the back yard while she was alone at home. She was afraid to look who it was. Now she is convinced that it was a thief entering the house, but I know for a fact that it was just her brother coming home earlier than expected from Kurumkan."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "CP"), ("test", "false memory")] }

def ex_43b : Datum :=
  { id := "bondarenko2020_43b"
    source := ⟨"bondarenko-2020", "(43b)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Darima gɘr-tɘ xulgaiʃan-ai or-o:ʃ-i:jɘ hana-na, xarin tɘrɘ axa-n’ Xurumxa:n-ha: jɘrɘ-hɘn bai-ga:"
    glossedTokens := [("Darima", "Darima.NOM"), ("gɘr-tɘ", "house-DAT"), ("xulgaiʃan-ai", "thief-GEN"), ("or-o:ʃ-i:jɘ", "enter-PART-ACC"), ("hana-na", "think-PRS"), ("xarin", "but"), ("tɘrɘ", "that"), ("axa-n’", "brother-3.NOM"), ("Xurumxa:n-ha:", "Kurumkan-ABL"), ("jɘrɘ-hɘn", "come-PFCT"), ("bai-ga:", "be-PST")]
    glossedWords := [⟨[['D', 'a', 'r', 'i', 'm', 'a']], [['D', 'a', 'r', 'i', 'm', 'a', '.', 'N', 'O', 'M']]⟩, ⟨[['g', 'ɘ', 'r'], ['t', 'ɘ']], [['h', 'o', 'u', 's', 'e'], ['D', 'A', 'T']]⟩, ⟨[['x', 'u', 'l', 'g', 'a', 'i', 'ʃ', 'a', 'n'], ['a', 'i']], [['t', 'h', 'i', 'e', 'f'], ['G', 'E', 'N']]⟩, ⟨[['o', 'r'], ['o', 'ʃ'], ['i', 'j', 'ɘ']], [['e', 'n', 't', 'e', 'r'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'n', 'a'], ['n', 'a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'R', 'S']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['t', 'ɘ', 'r', 'ɘ']], [['t', 'h', 'a', 't']]⟩, ⟨[['a', 'x', 'a'], ['n', '’']], [['b', 'r', 'o', 't', 'h', 'e', 'r'], ['3', '.', 'N', 'O', 'M']]⟩, ⟨[['X', 'u', 'r', 'u', 'm', 'x', 'a', 'n'], ['h', 'a']], [['K', 'u', 'r', 'u', 'm', 'k', 'a', 'n'], ['A', 'B', 'L']]⟩, ⟨[['j', 'ɘ', 'r', 'ɘ'], ['h', 'ɘ', 'n']], [['c', 'o', 'm', 'e'], ['P', 'F', 'C', 'T']]⟩, ⟨[['b', 'a', 'i'], ['g', 'a']], [['b', 'e'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Darima recalled a situation that happened recently. She heard some unexpected noise in the back yard while she was alone at home. She was afraid to look who it was. Now she is convinced that it was a thief entering the house, but I know for a fact that it was just her brother coming home earlier than expected from Kurumkan."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "NMN"), ("test", "false memory")] }

def ex_65 : Datum :=
  { id := "bondarenko2020_65"
    source := ⟨"bondarenko-2020", "(65)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Dugar mi:sgɘi-n zagaha ɘdj-ɘ: g-ɘ:ʃ-i:jɘ han-a:, xarin mi:sgɘi zagaha ɘdj-ɘ:-güi"
    glossedTokens := [("Dugar", "Dugar"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("g-ɘ:ʃ-i:jɘ", "say-PART-ACC"), ("han-a:", "think-PST"), ("xarin", "but"), ("mi:sgɘi", "cat"), ("zagaha", "fish"), ("ɘdj-ɘ:-güi", "eat-PST-NEG")]
    glossedWords := [⟨[['D', 'u', 'g', 'a', 'r']], [['D', 'u', 'g', 'a', 'r']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i'], ['n']], [['c', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ']], [['e', 'a', 't'], ['P', 'S', 'T']]⟩, ⟨[['g'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ']], [['s', 'a', 'y'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ'], ['g', 'ü', 'i']], [['e', 'a', 't'], ['P', 'S', 'T'], ['N', 'E', 'G']]⟩]
    lgrConformance := some .morphemeAligned
    context := "The cat didn't eat the fish, but someone made a false claim that it did."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "nominalized CP"), ("test", "denial")] }

def ex_66 : Datum :=
  { id := "bondarenko2020_66"
    source := ⟨"bondarenko-2020", "(66)"⟩
    reportedIn := none
    language := "russ1264"
    primaryText := "Mi:sgɘi zagaha ɘdj-ɘ: gɘ-žɘ xɘn-ʃjɘ xɘzɘ:-ʃjɘ han-a:-güi, xarin Dugar mi:sgɘi-n zagaha ɘdj-ɘ: g-ɘ:ʃ-i:jɘ han-a:"
    glossedTokens := [("Mi:sgɘi", "cat"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("gɘ-žɘ", "say-CVB"), ("xɘn-ʃjɘ", "who-PTCL"), ("xɘzɘ:-ʃjɘ", "when-PTCL"), ("han-a:-güi", "think-PST-NEG"), ("xarin", "but"), ("Dugar", "Dugar"), ("mi:sgɘi-n", "cat-GEN"), ("zagaha", "fish"), ("ɘdj-ɘ:", "eat-PST"), ("g-ɘ:ʃ-i:jɘ", "say-PART-ACC"), ("han-a:", "think-PST")]
    glossedWords := [⟨[['M', 'i', 's', 'g', 'ɘ', 'i']], [['c', 'a', 't']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ']], [['e', 'a', 't'], ['P', 'S', 'T']]⟩, ⟨[['g', 'ɘ'], ['ž', 'ɘ']], [['s', 'a', 'y'], ['C', 'V', 'B']]⟩, ⟨[['x', 'ɘ', 'n'], ['ʃ', 'j', 'ɘ']], [['w', 'h', 'o'], ['P', 'T', 'C', 'L']]⟩, ⟨[['x', 'ɘ', 'z', 'ɘ'], ['ʃ', 'j', 'ɘ']], [['w', 'h', 'e', 'n'], ['P', 'T', 'C', 'L']]⟩, ⟨[['h', 'a', 'n'], ['a'], ['g', 'ü', 'i']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T'], ['N', 'E', 'G']]⟩, ⟨[['x', 'a', 'r', 'i', 'n']], [['b', 'u', 't']]⟩, ⟨[['D', 'u', 'g', 'a', 'r']], [['D', 'u', 'g', 'a', 'r']]⟩, ⟨[['m', 'i', 's', 'g', 'ɘ', 'i'], ['n']], [['c', 'a', 't'], ['G', 'E', 'N']]⟩, ⟨[['z', 'a', 'g', 'a', 'h', 'a']], [['f', 'i', 's', 'h']]⟩, ⟨[['ɘ', 'd', 'j'], ['ɘ']], [['e', 'a', 't'], ['P', 'S', 'T']]⟩, ⟨[['g'], ['ɘ', 'ʃ'], ['i', 'j', 'ɘ']], [['s', 'a', 'y'], ['P', 'A', 'R', 'T'], ['A', 'C', 'C']]⟩, ⟨[['h', 'a', 'n'], ['a']], [['t', 'h', 'i', 'n', 'k'], ['P', 'S', 'T']]⟩]
    lgrConformance := some .morphemeAligned
    context := "Dugar was the first person to think that the cat ate the fish."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "nominalized CP"), ("test", "pre-existence")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4b, ex_4c, ex_5a, ex_5b, ex_6a, ex_6b, ex_7a, ex_7b, ex_8, ex_14, ex_15, ex_43a, ex_43b, ex_65, ex_66]

end Bondarenko2020.Examples
