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
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't', '.', 'N', 'O', 'M'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':'], ['e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], [⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't', '.', 'N', 'O', 'M'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':'], ['e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], [⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':', '-', 'g', 'ü', 'i'], ['e', 'a', 't', '-', 'P', 'S', 'T', '-', 'N', 'E', 'G'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩]
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
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i', '-', 'n'], ['c', 'a', 't', '-', 'G', 'E', 'N'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩, ⟨['n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ', '-', 'n', '’'], ['e', 'a', 't', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C', '-', '3'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩, ⟨['n', '’'], ['3'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i', '-', 'n'], ['c', 'a', 't', '-', 'G', 'E', 'N'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩, ⟨['n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ', '-', 'n', '’'], ['e', 'a', 't', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C', '-', '3'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩, ⟨['n', '’'], ['3'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':', '-', 'g', 'ü', 'i'], ['e', 'a', 't', '-', 'P', 'S', 'T', '-', 'N', 'E', 'G'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩]
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
    glossedWords := [⟨['B', 'i'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['B', 'i'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'S', 'T'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ü'], ['Q'], [⟨['g', 'ü'], ['Q'], none⟩]⟩, ⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], [⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['m', 'ɘ', 'd', 'ɘ', '-', 'n', 'ɘ', '-', 'g', 'ü', 'i', '-', 'b'], ['k', 'n', 'o', 'w', '-', 'P', 'R', 'S', '-', 'N', 'E', 'G', '-', '1', 'S', 'G'], [⟨['m', 'ɘ', 'd', 'ɘ'], ['k', 'n', 'o', 'w'], none⟩, ⟨['n', 'ɘ'], ['P', 'R', 'S'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩, ⟨['b'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', '-', 'i', ':', 'n'], ['B', 'a', 'd', 'm', 'a', '-', 'G', 'E', 'N'], [⟨['B', 'a', 'd', 'm'], ['B', 'a', 'd', 'm', 'a'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['B', 'i'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['B', 'i'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'S', 'T'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ü'], ['Q'], [⟨['g', 'ü'], ['Q'], none⟩]⟩, ⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], [⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['m', 'ɘ', 'd', 'ɘ', '-', 'n', 'ɘ', '-', 'g', 'ü', 'i', '-', 'b'], ['k', 'n', 'o', 'w', '-', 'P', 'R', 'S', '-', 'N', 'E', 'G', '-', '1', 'S', 'G'], [⟨['m', 'ɘ', 'd', 'ɘ'], ['k', 'n', 'o', 'w'], none⟩, ⟨['n', 'ɘ'], ['P', 'R', 'S'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩, ⟨['b'], ['1', 'S', 'G'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'S', 'T'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], [⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['G', 'a', 'r', 'a', 'g', '-', 'a', 'i'], ['d', 'a', 'y', '-', 'G', 'E', 'N'], [⟨['G', 'a', 'r', 'a', 'g'], ['d', 'a', 'y'], none⟩, ⟨['a', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['x', 'o', 'j', 'o', 'r', '-', 't', 'o'], ['t', 'w', 'o', '-', 'D', 'A', 'T'], [⟨['x', 'o', 'j', 'o', 'r'], ['t', 'w', 'o'], none⟩, ⟨['t', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', '-', 'i', ':', 'n'], ['B', 'a', 'd', 'm', 'a', '-', 'G', 'E', 'N'], [⟨['B', 'a', 'd', 'm'], ['B', 'a', 'd', 'm', 'a'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ', '-', 'n', '’'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C', '-', '3'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩, ⟨['n', '’'], ['3'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['g', 'a', 'r', 'a', 'g', '-', 'a', 'i'], ['d', 'a', 'y', '-', 'G', 'E', 'N'], [⟨['g', 'a', 'r', 'a', 'g'], ['d', 'a', 'y'], none⟩, ⟨['a', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['n', 'ɘ', 'g', 'ɘ', 'n', '-', 'd', 'ɘ'], ['o', 'n', 'e', '-', 'D', 'A', 'T'], [⟨['n', 'ɘ', 'g', 'ɘ', 'n'], ['o', 'n', 'e'], none⟩, ⟨['d', 'ɘ'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', 'ɘ', '-', 'ʒ', 'ɘ'], ['b', 'r', 'e', 'a', 'k', '-', 'C', 'V', 'B'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l', 'ɘ'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ʒ', 'ɘ'], ['C', 'V', 'B'], some '-'⟩]⟩, ⟨['ɘ', 'x', 'i', 'l', '-', 'ɘ', ':'], ['b', 'e', 'g', 'i', 'n', '-', 'P', 'S', 'T'], [⟨['ɘ', 'x', 'i', 'l'], ['b', 'e', 'g', 'i', 'n'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['G', 'a', 'r', 'a', 'g', '-', 'a', 'i'], ['d', 'a', 'y', '-', 'G', 'E', 'N'], [⟨['G', 'a', 'r', 'a', 'g'], ['d', 'a', 'y'], none⟩, ⟨['a', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['x', 'o', 'j', 'o', 'r', '-', 't', 'o'], ['t', 'w', 'o', '-', 'D', 'A', 'T'], [⟨['x', 'o', 'j', 'o', 'r'], ['t', 'w', 'o'], none⟩, ⟨['t', 'o'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', '-', 'i', ':', 'n'], ['B', 'a', 'd', 'm', 'a', '-', 'G', 'E', 'N'], [⟨['B', 'a', 'd', 'm'], ['B', 'a', 'd', 'm', 'a'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ', '-', 'n', '’'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C', '-', '3'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩, ⟨['n', '’'], ['3'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['g', 'a', 'r', 'a', 'g', '-', 'a', 'i'], ['d', 'a', 'y', '-', 'G', 'E', 'N'], [⟨['g', 'a', 'r', 'a', 'g'], ['d', 'a', 'y'], none⟩, ⟨['a', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['g', 'u', 'r', 'b', 'a', 'n', '-', 'd', 'a'], ['t', 'h', 'r', 'e', 'e', '-', 'D', 'A', 'T'], [⟨['g', 'u', 'r', 'b', 'a', 'n'], ['t', 'h', 'r', 'e', 'e'], none⟩, ⟨['d', 'a'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', 'ɘ', '-', 'ʒ', 'ɘ'], ['b', 'r', 'e', 'a', 'k', '-', 'C', 'V', 'B'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l', 'ɘ'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ʒ', 'ɘ'], ['C', 'V', 'B'], some '-'⟩]⟩, ⟨['ɘ', 'x', 'i', 'l', '-', 'ɘ', ':'], ['b', 'e', 'g', 'i', 'n', '-', 'P', 'S', 'T'], [⟨['ɘ', 'x', 'i', 'l'], ['b', 'e', 'g', 'i', 'n'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['S', 'ɘ', 's', 'ɘ', 'g'], ['S', 'e', 's', 'e', 'g'], [⟨['S', 'ɘ', 's', 'ɘ', 'g'], ['S', 'e', 's', 'e', 'g'], none⟩]⟩, ⟨['g', 'a', 'r', '-', 'g', 'a', '-', 'x', '-', 'a', ':'], ['g', 'o', '.', 'o', 'u', 't', '-', 'C', 'A', 'U', 'S', '-', 'P', 'O', 'T', '-', 'R', 'E', 'F', 'L'], [⟨['g', 'a', 'r'], ['g', 'o', '.', 'o', 'u', 't'], none⟩, ⟨['g', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['x'], ['P', 'O', 'T'], some '-'⟩, ⟨['a'], ['R', 'E', 'F', 'L'], some '-'⟩]⟩, ⟨['b', 'a', 'i', '-', 'g', 'a', ':', 'n'], ['b', 'e', '-', 'P', 'F', 'C', 'T'], [⟨['b', 'a', 'i'], ['b', 'e'], none⟩, ⟨['g', 'a', 'n'], ['P', 'F', 'C', 'T'], some '-'⟩]⟩, ⟨['ü', 'x', 'i', 'b', 'ü', '-', 'j', 'ɘ', ':'], ['c', 'h', 'i', 'l', 'd', '-', 'A', 'C', 'C', '.', 'R', 'E', 'F', 'L'], [⟨['ü', 'x', 'i', 'b', 'ü'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['j', 'ɘ'], ['A', 'C', 'C', '.', 'R', 'E', 'F', 'L'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['S', 'ɘ', 's', 'ɘ', 'g'], ['S', 'e', 's', 'e', 'g'], [⟨['S', 'ɘ', 's', 'ɘ', 'g'], ['S', 'e', 's', 'e', 'g'], none⟩]⟩, ⟨['g', 'a', 'r', '-', 'g', 'a', '-', 'x', '-', 'a', ':'], ['g', 'o', '.', 'o', 'u', 't', '-', 'C', 'A', 'U', 'S', '-', 'P', 'O', 'T', '-', 'R', 'E', 'F', 'L'], [⟨['g', 'a', 'r'], ['g', 'o', '.', 'o', 'u', 't'], none⟩, ⟨['g', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['x'], ['P', 'O', 'T'], some '-'⟩, ⟨['a'], ['R', 'E', 'F', 'L'], some '-'⟩]⟩, ⟨['b', 'a', 'i', '-', 'g', 'a', ':', 'n'], ['b', 'e', '-', 'P', 'F', 'C', 'T'], [⟨['b', 'a', 'i'], ['b', 'e'], none⟩, ⟨['g', 'a', 'n'], ['P', 'F', 'C', 'T'], some '-'⟩]⟩, ⟨['ü', 'x', 'i', 'b', 'ü', '-', 'j', 'ɘ', ':'], ['c', 'h', 'i', 'l', 'd', '-', 'A', 'C', 'C', '.', 'R', 'E', 'F', 'L'], [⟨['ü', 'x', 'i', 'b', 'ü'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['j', 'ɘ'], ['A', 'C', 'C', '.', 'R', 'E', 'F', 'L'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a'], none⟩]⟩, ⟨['n', 'a', 'i', 'm', 'a', 'n'], ['e', 'i', 'g', 'h', 't'], [⟨['n', 'a', 'i', 'm', 'a', 'n'], ['e', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['t', 'a', 'r', 'x', 'i', '-', 't', 'a', 'i'], ['h', 'e', 'a', 'd', '-', 'C', 'O', 'M'], [⟨['t', 'a', 'r', 'x', 'i'], ['h', 'e', 'a', 'd'], none⟩, ⟨['t', 'a', 'i'], ['C', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i', '-', 'ɘ'], ['c', 'a', 't', '-', 'A', 'C', 'C'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩, ⟨['ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', 'a', '-', 'n', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'R', 'S'], [⟨['h', 'a', 'n', 'a'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['n', 'a'], ['P', 'R', 'S'], some '-'⟩]⟩]
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
    glossedWords := [⟨['B', 'a', 'd', 'm', '-', 'a', 'i', 'n'], ['B', 'a', 'd', 'm', 'a', '-', 'G', 'E', 'N'], [⟨['B', 'a', 'd', 'm'], ['B', 'a', 'd', 'm', 'a'], none⟩, ⟨['a', 'i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'a', 'r', 'x', 'i'], ['h', 'e', 'a', 'd'], [⟨['t', 'a', 'r', 'x', 'i'], ['h', 'e', 'a', 'd'], none⟩]⟩, ⟨['s', 'o', ':'], ['i', 'n'], [⟨['s', 'o'], ['i', 'n'], none⟩]⟩, ⟨['n', 'a', 'i', 'm', 'a', 'n'], ['e', 'i', 'g', 'h', 't'], [⟨['n', 'a', 'i', 'm', 'a', 'n'], ['e', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['t', 'a', 'r', 'x', 'i', '-', 't', 'a', 'i'], ['h', 'e', 'a', 'd', '-', 'C', 'O', 'M'], [⟨['t', 'a', 'r', 'x', 'i'], ['h', 'e', 'a', 'd'], none⟩, ⟨['t', 'a', 'i'], ['C', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩]⟩, ⟨['o', 'r', '-', 'o', ':'], ['c', 'o', 'm', 'e', '-', 'P', 'S', 'T'], [⟨['o', 'r'], ['c', 'o', 'm', 'e'], none⟩, ⟨['o'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['S', 'ɘ', 's', 'ɘ', 'g'], ['S', 'e', 's', 'e', 'g'], [⟨['S', 'ɘ', 's', 'ɘ', 'g'], ['S', 'e', 's', 'e', 'g'], none⟩]⟩, ⟨['g', 'a', 'r', '-', 'g', 'a', '-', 'x', '-', 'a', ':'], ['g', 'o', '.', 'o', 'u', 't', '-', 'C', 'A', 'U', 'S', '-', 'P', 'O', 'T', '-', 'R', 'E', 'F', 'L'], [⟨['g', 'a', 'r'], ['g', 'o', '.', 'o', 'u', 't'], none⟩, ⟨['g', 'a'], ['C', 'A', 'U', 'S'], some '-'⟩, ⟨['x'], ['P', 'O', 'T'], some '-'⟩, ⟨['a'], ['R', 'E', 'F', 'L'], some '-'⟩]⟩, ⟨['b', 'a', 'i', '-', 'g', 'a', ':', 'n'], ['b', 'e', '-', 'P', 'F', 'C', 'T'], [⟨['b', 'a', 'i'], ['b', 'e'], none⟩, ⟨['g', 'a', 'n'], ['P', 'F', 'C', 'T'], some '-'⟩]⟩, ⟨['ü', 'x', 'i', 'b', 'ü', '-', 'n'], ['c', 'h', 'i', 'l', 'd', '-', 'N', 'O', 'M'], [⟨['ü', 'x', 'i', 'b', 'ü'], ['c', 'h', 'i', 'l', 'd'], none⟩, ⟨['n'], ['N', 'O', 'M'], some '-'⟩]⟩, ⟨['t', 'u', 'x', 'a', 'i', '-', 'g', 'a', ':'], ['a', 'b', 'o', 'u', 't', '-', 'A', 'C', 'C', '.', 'R', 'E', 'F', 'L'], [⟨['t', 'u', 'x', 'a', 'i'], ['a', 'b', 'o', 'u', 't'], none⟩, ⟨['g', 'a'], ['A', 'C', 'C', '.', 'R', 'E', 'F', 'L'], some '-'⟩]⟩, ⟨['h', 'a', 'n', 'a', '-', 'n', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'R', 'S'], [⟨['h', 'a', 'n', 'a'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['n', 'a'], ['P', 'R', 'S'], some '-'⟩]⟩]
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
    glossedWords := [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a'], none⟩]⟩, ⟨['n', 'a', 'i', 'm', 'a', 'n'], ['e', 'i', 'g', 'h', 't'], [⟨['n', 'a', 'i', 'm', 'a', 'n'], ['e', 'i', 'g', 'h', 't'], none⟩]⟩, ⟨['t', 'a', 'r', 'x', 'i', '-', 't', 'a', 'i'], ['h', 'e', 'a', 'd', '-', 'C', 'O', 'M'], [⟨['t', 'a', 'r', 'x', 'i'], ['h', 'e', 'a', 'd'], none⟩, ⟨['t', 'a', 'i'], ['C', 'O', 'M'], some '-'⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩]⟩, ⟨['t', 'u', 'x', 'a', 'i'], ['a', 'b', 'o', 'u', 't'], [⟨['t', 'u', 'x', 'a', 'i'], ['a', 'b', 'o', 'u', 't'], none⟩]⟩, ⟨['h', 'a', 'n', 'a', '-', 'n', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'R', 'S'], [⟨['h', 'a', 'n', 'a'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['n', 'a'], ['P', 'R', 'S'], some '-'⟩]⟩]
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
    glossedWords := [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', '-', 'i', ':', 'j', 'ɘ'], ['B', 'a', 'd', 'm', 'a', '-', 'A', 'C', 'C'], [⟨['B', 'a', 'd', 'm'], ['B', 'a', 'd', 'm', 'a'], none⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['B', 'i'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], [⟨['B', 'i'], ['1', 'S', 'G', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'S', 'T'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ü'], ['Q'], [⟨['g', 'ü'], ['Q'], none⟩]⟩, ⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], [⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['m', 'ɘ', 'd', 'ɘ', '-', 'n', 'ɘ', '-', 'g', 'ü', 'i', '-', 'b'], ['k', 'n', 'o', 'w', '-', 'P', 'R', 'S', '-', 'N', 'E', 'G', '-', '1', 'S', 'G', ','], [⟨['m', 'ɘ', 'd', 'ɘ'], ['k', 'n', 'o', 'w'], none⟩, ⟨['n', 'ɘ'], ['P', 'R', 'S'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩, ⟨['b'], ['1', 'S', 'G', ','], some '-'⟩]⟩, ⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['B', 'a', 'd', 'm', '-', 'i', ':', 'n'], ['B', 'a', 'd', 'm', 'a', '-', 'G', 'E', 'N'], [⟨['B', 'a', 'd', 'm'], ['B', 'a', 'd', 'm', 'a'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', 'a', '-', 'n', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'R', 'S'], [⟨['h', 'a', 'n', 'a'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['n', 'a'], ['P', 'R', 'S'], some '-'⟩]⟩, ⟨['g', 'ü'], ['Q'], [⟨['g', 'ü'], ['Q'], none⟩]⟩]
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
    glossedWords := [⟨['B', 'a', 'd', 'm', '-', 'i', ':', 'n'], ['B', 'a', 'd', 'm', 'a', '-', 'G', 'E', 'N'], [⟨['B', 'a', 'd', 'm'], ['B', 'a', 'd', 'm', 'a'], none⟩, ⟨['i', 'n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], [⟨['S', 'a', 'j', 'a', 'n', 'a'], ['S', 'a', 'j', 'a', 'n', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':', '-', 'g', 'ü', 'i'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T', '-', 'N', 'E', 'G'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['B', 'a', 'd', 'm', 'a'], ['B', 'a', 'd', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], [⟨['t', 'ɘ', 'r', 'g', 'ɘ'], ['c', 'a', 'r', 't'], none⟩]⟩, ⟨['ɘ', 'm', 'd', 'ɘ', 'l', '-', 'ɘ', ':', '-', 'g', 'ü', 'i'], ['b', 'r', 'e', 'a', 'k', '-', 'P', 'S', 'T', '-', 'N', 'E', 'G'], [⟨['ɘ', 'm', 'd', 'ɘ', 'l'], ['b', 'r', 'e', 'a', 'k'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩]
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
    glossedWords := [⟨['D', 'a', 'r', 'i', 'm', 'a'], ['D', 'a', 'r', 'i', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['D', 'a', 'r', 'i', 'm', 'a'], ['D', 'a', 'r', 'i', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['g', 'ɘ', 'r', '-', 't', 'ɘ'], ['h', 'o', 'u', 's', 'e', '-', 'D', 'A', 'T'], [⟨['g', 'ɘ', 'r'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['t', 'ɘ'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['x', 'u', 'l', 'g', 'a', 'i', 'ʃ', 'a', 'n'], ['t', 'h', 'i', 'e', 'f', '.', 'N', 'O', 'M'], [⟨['x', 'u', 'l', 'g', 'a', 'i', 'ʃ', 'a', 'n'], ['t', 'h', 'i', 'e', 'f', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['o', 'r', '-', 'o', ':'], ['e', 'n', 't', 'e', 'r', '-', 'P', 'S', 'T'], [⟨['o', 'r'], ['e', 'n', 't', 'e', 'r'], none⟩, ⟨['o'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], [⟨['g', 'ɘ', 'ž', 'ɘ'], ['C', 'O', 'M', 'P'], none⟩]⟩, ⟨['h', 'a', 'n', 'a', '-', 'n', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'R', 'S'], [⟨['h', 'a', 'n', 'a'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['n', 'a'], ['P', 'R', 'S'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'ɘ'], ['t', 'h', 'a', 't'], [⟨['t', 'ɘ', 'r', 'ɘ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['a', 'x', 'a', '-', 'n', '’'], ['b', 'r', 'o', 't', 'h', 'e', 'r', '-', '3', '.', 'N', 'O', 'M'], [⟨['a', 'x', 'a'], ['b', 'r', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', '’'], ['3', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['X', 'u', 'r', 'u', 'm', 'x', 'a', ':', 'n', '-', 'h', 'a', ':'], ['K', 'u', 'r', 'u', 'm', 'k', 'a', 'n', '-', 'A', 'B', 'L'], [⟨['X', 'u', 'r', 'u', 'm', 'x', 'a', 'n'], ['K', 'u', 'r', 'u', 'm', 'k', 'a', 'n'], none⟩, ⟨['h', 'a'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['j', 'ɘ', 'r', 'ɘ', '-', 'h', 'ɘ', 'n'], ['c', 'o', 'm', 'e', '-', 'P', 'F', 'C', 'T'], [⟨['j', 'ɘ', 'r', 'ɘ'], ['c', 'o', 'm', 'e'], none⟩, ⟨['h', 'ɘ', 'n'], ['P', 'F', 'C', 'T'], some '-'⟩]⟩, ⟨['b', 'a', 'i', '-', 'g', 'a', ':'], ['b', 'e', '-', 'P', 'S', 'T'], [⟨['b', 'a', 'i'], ['b', 'e'], none⟩, ⟨['g', 'a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['D', 'a', 'r', 'i', 'm', 'a'], ['D', 'a', 'r', 'i', 'm', 'a', '.', 'N', 'O', 'M'], [⟨['D', 'a', 'r', 'i', 'm', 'a'], ['D', 'a', 'r', 'i', 'm', 'a', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['g', 'ɘ', 'r', '-', 't', 'ɘ'], ['h', 'o', 'u', 's', 'e', '-', 'D', 'A', 'T'], [⟨['g', 'ɘ', 'r'], ['h', 'o', 'u', 's', 'e'], none⟩, ⟨['t', 'ɘ'], ['D', 'A', 'T'], some '-'⟩]⟩, ⟨['x', 'u', 'l', 'g', 'a', 'i', 'ʃ', 'a', 'n', '-', 'a', 'i'], ['t', 'h', 'i', 'e', 'f', '-', 'G', 'E', 'N'], [⟨['x', 'u', 'l', 'g', 'a', 'i', 'ʃ', 'a', 'n'], ['t', 'h', 'i', 'e', 'f'], none⟩, ⟨['a', 'i'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['o', 'r', '-', 'o', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ'], ['e', 'n', 't', 'e', 'r', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C'], [⟨['o', 'r'], ['e', 'n', 't', 'e', 'r'], none⟩, ⟨['o', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', 'a', '-', 'n', 'a'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'R', 'S'], [⟨['h', 'a', 'n', 'a'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['n', 'a'], ['P', 'R', 'S'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['t', 'ɘ', 'r', 'ɘ'], ['t', 'h', 'a', 't'], [⟨['t', 'ɘ', 'r', 'ɘ'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['a', 'x', 'a', '-', 'n', '’'], ['b', 'r', 'o', 't', 'h', 'e', 'r', '-', '3', '.', 'N', 'O', 'M'], [⟨['a', 'x', 'a'], ['b', 'r', 'o', 't', 'h', 'e', 'r'], none⟩, ⟨['n', '’'], ['3', '.', 'N', 'O', 'M'], some '-'⟩]⟩, ⟨['X', 'u', 'r', 'u', 'm', 'x', 'a', ':', 'n', '-', 'h', 'a', ':'], ['K', 'u', 'r', 'u', 'm', 'k', 'a', 'n', '-', 'A', 'B', 'L'], [⟨['X', 'u', 'r', 'u', 'm', 'x', 'a', 'n'], ['K', 'u', 'r', 'u', 'm', 'k', 'a', 'n'], none⟩, ⟨['h', 'a'], ['A', 'B', 'L'], some '-'⟩]⟩, ⟨['j', 'ɘ', 'r', 'ɘ', '-', 'h', 'ɘ', 'n'], ['c', 'o', 'm', 'e', '-', 'P', 'F', 'C', 'T'], [⟨['j', 'ɘ', 'r', 'ɘ'], ['c', 'o', 'm', 'e'], none⟩, ⟨['h', 'ɘ', 'n'], ['P', 'F', 'C', 'T'], some '-'⟩]⟩, ⟨['b', 'a', 'i', '-', 'g', 'a', ':'], ['b', 'e', '-', 'P', 'S', 'T'], [⟨['b', 'a', 'i'], ['b', 'e'], none⟩, ⟨['g', 'a'], ['P', 'S', 'T'], some '-'⟩]⟩]
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
    glossedWords := [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i', '-', 'n'], ['c', 'a', 't', '-', 'G', 'E', 'N'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩, ⟨['n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':'], ['e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ'], ['s', 'a', 'y', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C'], [⟨['g'], ['s', 'a', 'y'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':', '-', 'g', 'ü', 'i'], ['e', 'a', 't', '-', 'P', 'S', 'T', '-', 'N', 'E', 'G'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩]
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
    glossedWords := [⟨['M', 'i', ':', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], [⟨['M', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':'], ['e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', 'ɘ', '-', 'ž', 'ɘ'], ['s', 'a', 'y', '-', 'C', 'V', 'B'], [⟨['g', 'ɘ'], ['s', 'a', 'y'], none⟩, ⟨['ž', 'ɘ'], ['C', 'V', 'B'], some '-'⟩]⟩, ⟨['x', 'ɘ', 'n', '-', 'ʃ', 'j', 'ɘ'], ['w', 'h', 'o', '-', 'P', 'T', 'C', 'L'], [⟨['x', 'ɘ', 'n'], ['w', 'h', 'o'], none⟩, ⟨['ʃ', 'j', 'ɘ'], ['P', 'T', 'C', 'L'], some '-'⟩]⟩, ⟨['x', 'ɘ', 'z', 'ɘ', ':', '-', 'ʃ', 'j', 'ɘ'], ['w', 'h', 'e', 'n', '-', 'P', 'T', 'C', 'L'], [⟨['x', 'ɘ', 'z', 'ɘ'], ['w', 'h', 'e', 'n'], none⟩, ⟨['ʃ', 'j', 'ɘ'], ['P', 'T', 'C', 'L'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':', '-', 'g', 'ü', 'i'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T', '-', 'N', 'E', 'G'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩, ⟨['g', 'ü', 'i'], ['N', 'E', 'G'], some '-'⟩]⟩, ⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], [⟨['x', 'a', 'r', 'i', 'n'], ['b', 'u', 't'], none⟩]⟩, ⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], [⟨['D', 'u', 'g', 'a', 'r'], ['D', 'u', 'g', 'a', 'r'], none⟩]⟩, ⟨['m', 'i', ':', 's', 'g', 'ɘ', 'i', '-', 'n'], ['c', 'a', 't', '-', 'G', 'E', 'N'], [⟨['m', 'i', 's', 'g', 'ɘ', 'i'], ['c', 'a', 't'], none⟩, ⟨['n'], ['G', 'E', 'N'], some '-'⟩]⟩, ⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], [⟨['z', 'a', 'g', 'a', 'h', 'a'], ['f', 'i', 's', 'h'], none⟩]⟩, ⟨['ɘ', 'd', 'j', '-', 'ɘ', ':'], ['e', 'a', 't', '-', 'P', 'S', 'T'], [⟨['ɘ', 'd', 'j'], ['e', 'a', 't'], none⟩, ⟨['ɘ'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['g', '-', 'ɘ', ':', 'ʃ', '-', 'i', ':', 'j', 'ɘ'], ['s', 'a', 'y', '-', 'P', 'A', 'R', 'T', '-', 'A', 'C', 'C'], [⟨['g'], ['s', 'a', 'y'], none⟩, ⟨['ɘ', 'ʃ'], ['P', 'A', 'R', 'T'], some '-'⟩, ⟨['i', 'j', 'ɘ'], ['A', 'C', 'C'], some '-'⟩]⟩, ⟨['h', 'a', 'n', '-', 'a', ':'], ['t', 'h', 'i', 'n', 'k', '-', 'P', 'S', 'T'], [⟨['h', 'a', 'n'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['a'], ['P', 'S', 'T'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "Dugar was the first person to think that the cat ate the fish."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("complement", "nominalized CP"), ("test", "pre-existence")] }

def all : List Datum := [ex_1a, ex_1b, ex_2a, ex_2b, ex_3a, ex_3b, ex_4b, ex_4c, ex_5a, ex_5b, ex_6a, ex_6b, ex_7a, ex_7b, ex_8, ex_14, ex_15, ex_43a, ex_43b, ex_65, ex_66]

end Bondarenko2020.Examples
