module

public import Linglib.Data.Examples.Schema

/-!
# `Wood2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Wood2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wood2023.Examples`.
-/

@[expose] public section

namespace Wood2023.Examples

def ex_1 : Datum :=
  { id := "wood2023_1"
    source := ⟨"wood-2023", "(6.37)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún þvoði fötin."
    glossedTokens := [("Guðrún", "Guðrún.NOM"), ("þvoði", "washed"), ("fötin", "clothes.the.ACC")]
    glossedWords := [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'N', 'O', 'M'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['þ', 'v', 'o', 'ð', 'i'], ['w', 'a', 's', 'h', 'e', 'd'], [⟨['þ', 'v', 'o', 'ð', 'i'], ['w', 'a', 's', 'h', 'e', 'd'], none⟩]⟩, ⟨['f', 'ö', 't', 'i', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['f', 'ö', 't', 'i', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þvo")] }

def ex_2 : Datum :=
  { id := "wood2023_2"
    source := ⟨"wood-2023", "(6.37a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "þvo-ttur Guðrúnar á fötunum"
    glossedTokens := [("þvo-ttur", "wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    glossedWords := [⟨['þ', 'v', 'o', '-', 't', 't', 'u', 'r'], ['w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z'], [⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], none⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['á'], ['o', 'n'], [⟨['á'], ['o', 'n'], none⟩]⟩, ⟨['f', 'ö', 't', 'u', 'n', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], [⟨['f', 'ö', 't', 'u', 'n', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("reading", "CEN")] }

def ex_3 : Datum :=
  { id := "wood2023_3"
    source := ⟨"wood-2023", "(6.37c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þvo-ttur-inn tók langan tíma."
    glossedTokens := [("Þvo-ttur-inn", "wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    glossedWords := [⟨['Þ', 'v', 'o', '-', 't', 't', 'u', 'r', '-', 'i', 'n', 'n'], ['w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['Þ', 'v', 'o'], ['w', 'a', 's', 'h'], none⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['t', 'ó', 'k'], ['t', 'o', 'o', 'k'], [⟨['t', 'ó', 'k'], ['t', 'o', 'o', 'k'], none⟩]⟩, ⟨['l', 'a', 'n', 'g', 'a', 'n'], ['l', 'o', 'n', 'g'], [⟨['l', 'a', 'n', 'g', 'a', 'n'], ['l', 'o', 'n', 'g'], none⟩]⟩, ⟨['t', 'í', 'm', 'a'], ['t', 'i', 'm', 'e'], [⟨['t', 'í', 'm', 'a'], ['t', 'i', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple event", .acceptable)]
    paperFeatures := [("reading", "SEN")] }

def ex_4 : Datum :=
  { id := "wood2023_4"
    source := ⟨"wood-2023", "(6.37d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þvo-ttur-inn á að fara í vélina."
    glossedTokens := [("Þvo-ttur-inn", "wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    glossedWords := [⟨['Þ', 'v', 'o', '-', 't', 't', 'u', 'r', '-', 'i', 'n', 'n'], ['w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['Þ', 'v', 'o'], ['w', 'a', 's', 'h'], none⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['á'], ['o', 'u', 'g', 'h', 't'], [⟨['á'], ['o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['a', 'ð'], ['t', 'o'], [⟨['a', 'ð'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'r', 'a'], ['g', 'o'], [⟨['f', 'a', 'r', 'a'], ['g', 'o'], none⟩]⟩, ⟨['í'], ['i', 'n'], [⟨['í'], ['i', 'n'], none⟩]⟩, ⟨['v', 'é', 'l', 'i', 'n', 'a'], ['m', 'a', 'c', 'h', 'i', 'n', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['v', 'é', 'l', 'i', 'n', 'a'], ['m', 'a', 'c', 'h', 'i', 'n', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple entity", .acceptable)]
    paperFeatures := [("reading", "RN")] }

def ex_5 : Datum :=
  { id := "wood2023_5"
    source := ⟨"wood-2023", "(6.38)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún marg-þvoði fötin."
    glossedTokens := [("Guðrún", "Guðrún.NOM"), ("marg-þvoði", "many-washed"), ("fötin", "clothes.the.ACC")]
    glossedWords := [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'N', 'O', 'M'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['m', 'a', 'r', 'g', '-', 'þ', 'v', 'o', 'ð', 'i'], ['m', 'a', 'n', 'y', '-', 'w', 'a', 's', 'h', 'e', 'd'], [⟨['m', 'a', 'r', 'g'], ['m', 'a', 'n', 'y'], none⟩, ⟨['þ', 'v', 'o', 'ð', 'i'], ['w', 'a', 's', 'h', 'e', 'd'], some '-'⟩]⟩, ⟨['f', 'ö', 't', 'i', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['f', 'ö', 't', 'i', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prefix", "marg-")] }

def ex_6 : Datum :=
  { id := "wood2023_6"
    source := ⟨"wood-2023", "(6.38a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "marg-þvo-ttur Guðrúnar á fötunum"
    glossedTokens := [("marg-þvo-ttur", "many-wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    glossedWords := [⟨['m', 'a', 'r', 'g', '-', 'þ', 'v', 'o', '-', 't', 't', 'u', 'r'], ['m', 'a', 'n', 'y', '-', 'w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z'], [⟨['m', 'a', 'r', 'g'], ['m', 'a', 'n', 'y'], none⟩, ⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], some '-'⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['á'], ['o', 'n'], [⟨['á'], ['o', 'n'], none⟩]⟩, ⟨['f', 'ö', 't', 'u', 'n', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], [⟨['f', 'ö', 't', 'u', 'n', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "marg-"), ("reading", "CEN")] }

def ex_7 : Datum :=
  { id := "wood2023_7"
    source := ⟨"wood-2023", "(6.38c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "marg-þvo-ttur fatanna"
    glossedTokens := [("marg-þvo-ttur", "many-wash-NMLZ"), ("fatanna", "clothes.the.GEN")]
    glossedWords := [⟨['m', 'a', 'r', 'g', '-', 'þ', 'v', 'o', '-', 't', 't', 'u', 'r'], ['m', 'a', 'n', 'y', '-', 'w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z'], [⟨['m', 'a', 'r', 'g'], ['m', 'a', 'n', 'y'], none⟩, ⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], some '-'⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['f', 'a', 't', 'a', 'n', 'n', 'a'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'G', 'E', 'N'], [⟨['f', 'a', 't', 'a', 'n', 'n', 'a'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'G', 'E', 'N'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "marg-"), ("reading", "CEN")] }

def ex_8 : Datum :=
  { id := "wood2023_8"
    source := ⟨"wood-2023", "(6.38d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Marg-þvo-ttur-inn tók langan tíma."
    glossedTokens := [("Marg-þvo-ttur-inn", "many-wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    glossedWords := [⟨['M', 'a', 'r', 'g', '-', 'þ', 'v', 'o', '-', 't', 't', 'u', 'r', '-', 'i', 'n', 'n'], ['m', 'a', 'n', 'y', '-', 'w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['M', 'a', 'r', 'g'], ['m', 'a', 'n', 'y'], none⟩, ⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], some '-'⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['t', 'ó', 'k'], ['t', 'o', 'o', 'k'], [⟨['t', 'ó', 'k'], ['t', 'o', 'o', 'k'], none⟩]⟩, ⟨['l', 'a', 'n', 'g', 'a', 'n'], ['l', 'o', 'n', 'g'], [⟨['l', 'a', 'n', 'g', 'a', 'n'], ['l', 'o', 'n', 'g'], none⟩]⟩, ⟨['t', 'í', 'm', 'a'], ['t', 'i', 'm', 'e'], [⟨['t', 'í', 'm', 'a'], ['t', 'i', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple event", .ungrammatical)]
    paperFeatures := [("prefix", "marg-"), ("reading", "SEN")] }

def ex_9 : Datum :=
  { id := "wood2023_9"
    source := ⟨"wood-2023", "(6.38e)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Marg-þvo-ttur-inn á að fara í vélina."
    glossedTokens := [("Marg-þvo-ttur-inn", "many-wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    glossedWords := [⟨['M', 'a', 'r', 'g', '-', 'þ', 'v', 'o', '-', 't', 't', 'u', 'r', '-', 'i', 'n', 'n'], ['m', 'a', 'n', 'y', '-', 'w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['M', 'a', 'r', 'g'], ['m', 'a', 'n', 'y'], none⟩, ⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], some '-'⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['á'], ['o', 'u', 'g', 'h', 't'], [⟨['á'], ['o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['a', 'ð'], ['t', 'o'], [⟨['a', 'ð'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'r', 'a'], ['g', 'o'], [⟨['f', 'a', 'r', 'a'], ['g', 'o'], none⟩]⟩, ⟨['í'], ['i', 'n'], [⟨['í'], ['i', 'n'], none⟩]⟩, ⟨['v', 'é', 'l', 'i', 'n', 'a'], ['m', 'a', 'c', 'h', 'i', 'n', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['v', 'é', 'l', 'i', 'n', 'a'], ['m', 'a', 'c', 'h', 'i', 'n', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("prefix", "marg-"), ("reading", "RN")] }

def ex_10 : Datum :=
  { id := "wood2023_10"
    source := ⟨"wood-2023", "(6.46)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég endur-þvoði fötin."
    glossedTokens := [("Ég", "I.NOM"), ("endur-þvoði", "re-washed"), ("fötin", "clothes.the.ACC")]
    glossedWords := [⟨['É', 'g'], ['I', '.', 'N', 'O', 'M'], [⟨['É', 'g'], ['I', '.', 'N', 'O', 'M'], none⟩]⟩, ⟨['e', 'n', 'd', 'u', 'r', '-', 'þ', 'v', 'o', 'ð', 'i'], ['r', 'e', '-', 'w', 'a', 's', 'h', 'e', 'd'], [⟨['e', 'n', 'd', 'u', 'r'], ['r', 'e'], none⟩, ⟨['þ', 'v', 'o', 'ð', 'i'], ['w', 'a', 's', 'h', 'e', 'd'], some '-'⟩]⟩, ⟨['f', 'ö', 't', 'i', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['f', 'ö', 't', 'i', 'n'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prefix", "endur-")] }

def ex_11 : Datum :=
  { id := "wood2023_11"
    source := ⟨"wood-2023", "(6.46a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "endur-þvo-ttur Guðrúnar á fötunum"
    glossedTokens := [("endur-þvo-ttur", "re-wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    glossedWords := [⟨['e', 'n', 'd', 'u', 'r', '-', 'þ', 'v', 'o', '-', 't', 't', 'u', 'r'], ['r', 'e', '-', 'w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z'], [⟨['e', 'n', 'd', 'u', 'r'], ['r', 'e'], none⟩, ⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], some '-'⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['á'], ['o', 'n'], [⟨['á'], ['o', 'n'], none⟩]⟩, ⟨['f', 'ö', 't', 'u', 'n', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], [⟨['f', 'ö', 't', 'u', 'n', 'u', 'm'], ['c', 'l', 'o', 't', 'h', 'e', 's', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "CEN")] }

def ex_12 : Datum :=
  { id := "wood2023_12"
    source := ⟨"wood-2023", "(6.46c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Endur-þvo-ttur-inn tók langan tíma."
    glossedTokens := [("Endur-þvo-ttur-inn", "re-wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    glossedWords := [⟨['E', 'n', 'd', 'u', 'r', '-', 'þ', 'v', 'o', '-', 't', 't', 'u', 'r', '-', 'i', 'n', 'n'], ['r', 'e', '-', 'w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['E', 'n', 'd', 'u', 'r'], ['r', 'e'], none⟩, ⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], some '-'⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['t', 'ó', 'k'], ['t', 'o', 'o', 'k'], [⟨['t', 'ó', 'k'], ['t', 'o', 'o', 'k'], none⟩]⟩, ⟨['l', 'a', 'n', 'g', 'a', 'n'], ['l', 'o', 'n', 'g'], [⟨['l', 'a', 'n', 'g', 'a', 'n'], ['l', 'o', 'n', 'g'], none⟩]⟩, ⟨['t', 'í', 'm', 'a'], ['t', 'i', 'm', 'e'], [⟨['t', 'í', 'm', 'a'], ['t', 'i', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple event", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "SEN")] }

def ex_13 : Datum :=
  { id := "wood2023_13"
    source := ⟨"wood-2023", "(6.46d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Endur-þvo-ttur-inn á að fara í vélina."
    glossedTokens := [("Endur-þvo-ttur-inn", "re-wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    glossedWords := [⟨['E', 'n', 'd', 'u', 'r', '-', 'þ', 'v', 'o', '-', 't', 't', 'u', 'r', '-', 'i', 'n', 'n'], ['r', 'e', '-', 'w', 'a', 's', 'h', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['E', 'n', 'd', 'u', 'r'], ['r', 'e'], none⟩, ⟨['þ', 'v', 'o'], ['w', 'a', 's', 'h'], some '-'⟩, ⟨['t', 't', 'u', 'r'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['á'], ['o', 'u', 'g', 'h', 't'], [⟨['á'], ['o', 'u', 'g', 'h', 't'], none⟩]⟩, ⟨['a', 'ð'], ['t', 'o'], [⟨['a', 'ð'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'r', 'a'], ['g', 'o'], [⟨['f', 'a', 'r', 'a'], ['g', 'o'], none⟩]⟩, ⟨['í'], ['i', 'n'], [⟨['í'], ['i', 'n'], none⟩]⟩, ⟨['v', 'é', 'l', 'i', 'n', 'a'], ['m', 'a', 'c', 'h', 'i', 'n', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['v', 'é', 'l', 'i', 'n', 'a'], ['m', 'a', 'c', 'h', 'i', 'n', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("prefix", "endur-"), ("reading", "RN")] }

def ex_14 : Datum :=
  { id := "wood2023_14"
    source := ⟨"wood-2023", "(6.52)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vona að hún týni ekki endur-prent-un-inni."
    glossedTokens := [("Ég", "I"), ("vona", "hope"), ("að", "that"), ("hún", "she"), ("týni", "loses"), ("ekki", "not"), ("endur-prent-un-inni", "re-print-NMLZ-the")]
    glossedWords := [⟨['É', 'g'], ['I'], [⟨['É', 'g'], ['I'], none⟩]⟩, ⟨['v', 'o', 'n', 'a'], ['h', 'o', 'p', 'e'], [⟨['v', 'o', 'n', 'a'], ['h', 'o', 'p', 'e'], none⟩]⟩, ⟨['a', 'ð'], ['t', 'h', 'a', 't'], [⟨['a', 'ð'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['h', 'ú', 'n'], ['s', 'h', 'e'], [⟨['h', 'ú', 'n'], ['s', 'h', 'e'], none⟩]⟩, ⟨['t', 'ý', 'n', 'i'], ['l', 'o', 's', 'e', 's'], [⟨['t', 'ý', 'n', 'i'], ['l', 'o', 's', 'e', 's'], none⟩]⟩, ⟨['e', 'k', 'k', 'i'], ['n', 'o', 't'], [⟨['e', 'k', 'k', 'i'], ['n', 'o', 't'], none⟩]⟩, ⟨['e', 'n', 'd', 'u', 'r', '-', 'p', 'r', 'e', 'n', 't', '-', 'u', 'n', '-', 'i', 'n', 'n', 'i'], ['r', 'e', '-', 'p', 'r', 'i', 'n', 't', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['e', 'n', 'd', 'u', 'r'], ['r', 'e'], none⟩, ⟨['p', 'r', 'e', 'n', 't'], ['p', 'r', 'i', 'n', 't'], some '-'⟩, ⟨['u', 'n'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'n', 'i'], ['t', 'h', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := "I printed the rules for her yesterday, but now she can't find the print out. I need to reprint the rules today."
    judgment := .acceptable
    alternatives := []
    readings := [("result", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "result RN")] }

def ex_15 : Datum :=
  { id := "wood2023_15"
    source := ⟨"wood-2023", "(4.28a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "að ræða um þetta"
    glossedTokens := [("að", "to"), ("ræða", "discuss"), ("um", "about"), ("þetta", "this")]
    glossedWords := [⟨['a', 'ð'], ['t', 'o'], [⟨['a', 'ð'], ['t', 'o'], none⟩]⟩, ⟨['r', 'æ', 'ð', 'a'], ['d', 'i', 's', 'c', 'u', 's', 's'], [⟨['r', 'æ', 'ð', 'a'], ['d', 'i', 's', 'c', 'u', 's', 's'], none⟩]⟩, ⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], [⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], none⟩]⟩, ⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], [⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := [("að um-ræða þetta", .ungrammatical)]
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "1")] }

def ex_16 : Datum :=
  { id := "wood2023_16"
    source := ⟨"wood-2023", "(4.28b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "um-ræð-a um þetta"
    glossedTokens := [("um-ræð-a", "about-discussion-NMLZ"), ("um", "about"), ("þetta", "this")]
    glossedWords := [⟨['u', 'm', '-', 'r', 'æ', 'ð', '-', 'a'], ['a', 'b', 'o', 'u', 't', '-', 'd', 'i', 's', 'c', 'u', 's', 's', 'i', 'o', 'n', '-', 'N', 'M', 'L', 'Z'], [⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], none⟩, ⟨['r', 'æ', 'ð'], ['d', 'i', 's', 'c', 'u', 's', 's', 'i', 'o', 'n'], some '-'⟩, ⟨['a'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], [⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], none⟩]⟩, ⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], [⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "1")] }

def ex_17 : Datum :=
  { id := "wood2023_17"
    source := ⟨"wood-2023", "(4.50a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún hug-sa-ði um þetta."
    glossedTokens := [("Guðrún", "Guðrún"), ("hug-sa-ði", "think-VBLZ-PST"), ("um", "about"), ("þetta", "this")]
    glossedWords := [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n'], none⟩]⟩, ⟨['h', 'u', 'g', '-', 's', 'a', '-', 'ð', 'i'], ['t', 'h', 'i', 'n', 'k', '-', 'V', 'B', 'L', 'Z', '-', 'P', 'S', 'T'], [⟨['h', 'u', 'g'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['s', 'a'], ['V', 'B', 'L', 'Z'], some '-'⟩, ⟨['ð', 'i'], ['P', 'S', 'T'], some '-'⟩]⟩, ⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], [⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], none⟩]⟩, ⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], [⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "3")] }

def ex_18 : Datum :=
  { id := "wood2023_18"
    source := ⟨"wood-2023", "(4.50c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hug-s-un-in um þetta"
    glossedTokens := [("hug-s-un-in", "think-VBLZ-NMLZ-the"), ("um", "about"), ("þetta", "this")]
    glossedWords := [⟨['h', 'u', 'g', '-', 's', '-', 'u', 'n', '-', 'i', 'n'], ['t', 'h', 'i', 'n', 'k', '-', 'V', 'B', 'L', 'Z', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['h', 'u', 'g'], ['t', 'h', 'i', 'n', 'k'], none⟩, ⟨['s'], ['V', 'B', 'L', 'Z'], some '-'⟩, ⟨['u', 'n'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n'], ['t', 'h', 'e'], some '-'⟩]⟩, ⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], [⟨['u', 'm'], ['a', 'b', 'o', 'u', 't'], none⟩]⟩, ⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], [⟨['þ', 'e', 't', 't', 'a'], ['t', 'h', 'i', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "3")] }

def ex_19 : Datum :=
  { id := "wood2023_19"
    source := ⟨"wood-2023", "(4.12b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "við-ger-ð Guðrúnar á bílnum mínum með sleggju"
    glossedTokens := [("við-ger-ð", "with-do-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("bílnum", "car.the.DAT"), ("mínum", "my"), ("með", "with"), ("sleggju", "sledge.hammer")]
    glossedWords := [⟨['v', 'i', 'ð', '-', 'g', 'e', 'r', '-', 'ð'], ['w', 'i', 't', 'h', '-', 'd', 'o', '-', 'N', 'M', 'L', 'Z'], [⟨['v', 'i', 'ð'], ['w', 'i', 't', 'h'], none⟩, ⟨['g', 'e', 'r'], ['d', 'o'], some '-'⟩, ⟨['ð'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩, ⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n', 'a', 'r'], ['G', 'u', 'ð', 'r', 'ú', 'n', '.', 'G', 'E', 'N'], none⟩]⟩, ⟨['á'], ['o', 'n'], [⟨['á'], ['o', 'n'], none⟩]⟩, ⟨['b', 'í', 'l', 'n', 'u', 'm'], ['c', 'a', 'r', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], [⟨['b', 'í', 'l', 'n', 'u', 'm'], ['c', 'a', 'r', '.', 't', 'h', 'e', '.', 'D', 'A', 'T'], none⟩]⟩, ⟨['m', 'í', 'n', 'u', 'm'], ['m', 'y'], [⟨['m', 'í', 'n', 'u', 'm'], ['m', 'y'], none⟩]⟩, ⟨['m', 'e', 'ð'], ['w', 'i', 't', 'h'], [⟨['m', 'e', 'ð'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['s', 'l', 'e', 'g', 'g', 'j', 'u'], ['s', 'l', 'e', 'd', 'g', 'e', '.', 'h', 'a', 'm', 'm', 'e', 'r'], [⟨['s', 'l', 'e', 'g', 'g', 'j', 'u'], ['s', 'l', 'e', 'd', 'g', 'e', '.', 'h', 'a', 'm', 'm', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("preposition", "við"), ("pattern", "2"), ("reading", "CEN")] }

def ex_20 : Datum :=
  { id := "wood2023_20"
    source := ⟨"wood-2023", "(6.62a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "að versl-un-ar-væða heilbrigðisþjónustuna"
    glossedTokens := [("að", "to"), ("versl-un-ar-væða", "shop-NMLZ-GEN-væða"), ("heilbrigðisþjónustuna", "health.care.service.the.ACC")]
    glossedWords := [⟨['a', 'ð'], ['t', 'o'], [⟨['a', 'ð'], ['t', 'o'], none⟩]⟩, ⟨['v', 'e', 'r', 's', 'l', '-', 'u', 'n', '-', 'a', 'r', '-', 'v', 'æ', 'ð', 'a'], ['s', 'h', 'o', 'p', '-', 'N', 'M', 'L', 'Z', '-', 'G', 'E', 'N', '-', 'v', 'æ', 'ð', 'a'], [⟨['v', 'e', 'r', 's', 'l'], ['s', 'h', 'o', 'p'], none⟩, ⟨['u', 'n'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['a', 'r'], ['G', 'E', 'N'], some '-'⟩, ⟨['v', 'æ', 'ð', 'a'], ['v', 'æ', 'ð', 'a'], some '-'⟩]⟩, ⟨['h', 'e', 'i', 'l', 'b', 'r', 'i', 'g', 'ð', 'i', 's', 'þ', 'j', 'ó', 'n', 'u', 's', 't', 'u', 'n', 'a'], ['h', 'e', 'a', 'l', 't', 'h', '.', 'c', 'a', 'r', 'e', '.', 's', 'e', 'r', 'v', 'i', 'c', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['h', 'e', 'i', 'l', 'b', 'r', 'i', 'g', 'ð', 'i', 's', 'þ', 'j', 'ó', 'n', 'u', 's', 't', 'u', 'n', 'a'], ['h', 'e', 'a', 'l', 't', 'h', '.', 'c', 'a', 'r', 'e', '.', 's', 'e', 'r', 'v', 'i', 'c', 'e', '.', 't', 'h', 'e', '.', 'A', 'C', 'C'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-væða")] }

def ex_21 : Datum :=
  { id := "wood2023_21"
    source := ⟨"wood-2023", "(6.63a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stofn-an-a-væð-ing"
    glossedTokens := [("stofn-an-a-væð-ing", "office-NMLZ-GEN-væða-NMLZ")]
    glossedWords := [⟨['s', 't', 'o', 'f', 'n', '-', 'a', 'n', '-', 'a', '-', 'v', 'æ', 'ð', '-', 'i', 'n', 'g'], ['o', 'f', 'f', 'i', 'c', 'e', '-', 'N', 'M', 'L', 'Z', '-', 'G', 'E', 'N', '-', 'v', 'æ', 'ð', 'a', '-', 'N', 'M', 'L', 'Z'], [⟨['s', 't', 'o', 'f', 'n'], ['o', 'f', 'f', 'i', 'c', 'e'], none⟩, ⟨['a', 'n'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['a'], ['G', 'E', 'N'], some '-'⟩, ⟨['v', 'æ', 'ð'], ['v', 'æ', 'ð', 'a'], some '-'⟩, ⟨['i', 'n', 'g'], ['N', 'M', 'L', 'Z'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-væðing")] }

def ex_22 : Datum :=
  { id := "wood2023_22"
    source := ⟨"wood-2023", "(6.13c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún snerti að-dá-un-ina."
    glossedTokens := [("Guðrún", "Guðrún"), ("snerti", "touched"), ("að-dá-un-ina", "to-admire-NMLZ-the.ACC")]
    glossedWords := [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n'], [⟨['G', 'u', 'ð', 'r', 'ú', 'n'], ['G', 'u', 'ð', 'r', 'ú', 'n'], none⟩]⟩, ⟨['s', 'n', 'e', 'r', 't', 'i'], ['t', 'o', 'u', 'c', 'h', 'e', 'd'], [⟨['s', 'n', 'e', 'r', 't', 'i'], ['t', 'o', 'u', 'c', 'h', 'e', 'd'], none⟩]⟩, ⟨['a', 'ð', '-', 'd', 'á', '-', 'u', 'n', '-', 'i', 'n', 'a'], ['t', 'o', '-', 'a', 'd', 'm', 'i', 'r', 'e', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e', '.', 'A', 'C', 'C'], [⟨['a', 'ð'], ['t', 'o'], none⟩, ⟨['d', 'á'], ['a', 'd', 'm', 'i', 'r', 'e'], some '-'⟩, ⟨['u', 'n'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'a'], ['t', 'h', 'e', '.', 'A', 'C', 'C'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("nominal", "að-dá-un"), ("reading", "RN")] }

def ex_23 : Datum :=
  { id := "wood2023_23"
    source := ⟨"wood-2023", "(6.14d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég snerti við-vör-un-ina."
    glossedTokens := [("Ég", "I"), ("snerti", "touched"), ("við-vör-un-ina", "with-warn-NMLZ-the")]
    glossedWords := [⟨['É', 'g'], ['I'], [⟨['É', 'g'], ['I'], none⟩]⟩, ⟨['s', 'n', 'e', 'r', 't', 'i'], ['t', 'o', 'u', 'c', 'h', 'e', 'd'], [⟨['s', 'n', 'e', 'r', 't', 'i'], ['t', 'o', 'u', 'c', 'h', 'e', 'd'], none⟩]⟩, ⟨['v', 'i', 'ð', '-', 'v', 'ö', 'r', '-', 'u', 'n', '-', 'i', 'n', 'a'], ['w', 'i', 't', 'h', '-', 'w', 'a', 'r', 'n', '-', 'N', 'M', 'L', 'Z', '-', 't', 'h', 'e'], [⟨['v', 'i', 'ð'], ['w', 'i', 't', 'h'], none⟩, ⟨['v', 'ö', 'r'], ['w', 'a', 'r', 'n'], some '-'⟩, ⟨['u', 'n'], ['N', 'M', 'L', 'Z'], some '-'⟩, ⟨['i', 'n', 'a'], ['t', 'h', 'e'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple entity", .acceptable)]
    paperFeatures := [("nominal", "við-vör-un"), ("reading", "RN")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Wood2023.Examples
