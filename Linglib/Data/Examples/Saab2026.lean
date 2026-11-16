module

public import Linglib.Data.Examples.Schema

/-!
# `Saab2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Saab2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Saab2026.Examples`.
-/

@[expose] public section

namespace Saab2026.Examples

def ex1a : Datum :=
  { id := "saab2026_ex1a"
    source := ⟨"saab-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un grupo de estudiantes"
    glossedTokens := [("un", "a"), ("grupo", "group"), ("de", "of"), ("estudiantes", "students")]
    glossedWords := [⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], [⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo")] }

def ex1b : Datum :=
  { id := "saab2026_ex1b"
    source := ⟨"saab-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un montón de estudiantes"
    glossedTokens := [("un", "a"), ("montón", "lot"), ("de", "of"), ("estudiantes", "students")]
    glossedWords := [⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], [⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón")] }

def ex1c : Datum :=
  { id := "saab2026_ex1c"
    source := ⟨"saab-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de departamento"
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("departamento", "apartment")]
    glossedWords := [⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o'], ['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't'], [⟨['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o'], ['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda")] }

def ex2a : Datum :=
  { id := "saab2026_ex2a"
    source := ⟨"saab-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Vinieron un grupo de estudiantes."
    glossedTokens := [("Vinieron", "came.3PL"), ("un", "a"), ("grupo", "group.SG"), ("de", "of"), ("estudiantes", "students")]
    glossedWords := [⟨['V', 'i', 'n', 'i', 'e', 'r', 'o', 'n'], ['c', 'a', 'm', 'e', '.', '3', 'P', 'L'], [⟨['V', 'i', 'n', 'i', 'e', 'r', 'o', 'n'], ['c', 'a', 'm', 'e', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p', '.', 'S', 'G'], [⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p', '.', 'S', 'G'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex2b : Datum :=
  { id := "saab2026_ex2b"
    source := ⟨"saab-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Vinieron un montón de estudiantes."
    glossedTokens := [("Vinieron", "came.3PL"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("estudiantes", "students")]
    glossedWords := [⟨['V', 'i', 'n', 'i', 'e', 'r', 'o', 'n'], ['c', 'a', 'm', 'e', '.', '3', 'P', 'L'], [⟨['V', 'i', 'n', 'i', 'e', 'r', 'o', 'n'], ['c', 'a', 'm', 'e', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], [⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], [⟨['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's'], ['s', 't', 'u', 'd', 'e', 'n', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex2c : Datum :=
  { id := "saab2026_ex2c"
    source := ⟨"saab-2026", "(2c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Se derrumbaron una mierda de departamentos."
    glossedTokens := [("Se", "se"), ("derrumbaron", "demolish.3PL"), ("una", "a"), ("mierda", "shit.SG"), ("de", "of"), ("departamentos", "apartments")]
    glossedWords := [⟨['S', 'e'], ['s', 'e'], [⟨['S', 'e'], ['s', 'e'], none⟩]⟩, ⟨['d', 'e', 'r', 'r', 'u', 'm', 'b', 'a', 'r', 'o', 'n'], ['d', 'e', 'm', 'o', 'l', 'i', 's', 'h', '.', '3', 'P', 'L'], [⟨['d', 'e', 'r', 'r', 'u', 'm', 'b', 'a', 'r', 'o', 'n'], ['d', 'e', 'm', 'o', 'l', 'i', 's', 'h', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't', '.', 'S', 'G'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't', '.', 'S', 'G'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o', 's'], ['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't', 's'], [⟨['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o', 's'], ['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex5_bocha : Datum :=
  { id := "saab2026_ex5_bocha"
    source := ⟨"saab-2026", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Vinieron muchos estudiantes? B: Una bocha."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bocha"), ("elided", "coda")] }

def ex5_grupo : Datum :=
  { id := "saab2026_ex5_grupo"
    source := ⟨"saab-2026", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Vinieron muchos estudiantes? B: Un grupo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("elided", "coda")] }

def ex6 : Datum :=
  { id := "saab2026_ex6"
    source := ⟨"saab-2026", "(6)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de departamento en San Telmo y una mierda en La Boca"
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("departamento", "apartment"), ("en", "in"), ("San Telmo", "San Telmo"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("en", "in"), ("La Boca", "La Boca")]
    glossedWords := [⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o'], ['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't'], [⟨['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o'], ['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't'], none⟩]⟩, ⟨['e', 'n'], ['i', 'n'], [⟨['e', 'n'], ['i', 'n'], none⟩]⟩, ⟨['S', 'a', 'n', ' ', 'T', 'e', 'l', 'm', 'o'], ['S', 'a', 'n', ' ', 'T', 'e', 'l', 'm', 'o'], [⟨['S', 'a', 'n', ' ', 'T', 'e', 'l', 'm', 'o'], ['S', 'a', 'n', ' ', 'T', 'e', 'l', 'm', 'o'], none⟩]⟩, ⟨['y'], ['a', 'n', 'd'], [⟨['y'], ['a', 'n', 'd'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], none⟩]⟩, ⟨['e', 'n'], ['i', 'n'], [⟨['e', 'n'], ['i', 'n'], none⟩]⟩, ⟨['L', 'a', ' ', 'B', 'o', 'c', 'a'], ['L', 'a', ' ', 'B', 'o', 'c', 'a'], [⟨['L', 'a', ' ', 'B', 'o', 'c', 'a'], ['L', 'a', ' ', 'B', 'o', 'c', 'a'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("ellipsis", .unacceptable)]
    paperFeatures := [("noun", "mierda"), ("elided", "coda")] }

def ex43 : Datum :=
  { id := "saab2026_ex43"
    source := ⟨"saab-2026", "(43)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Hay muchos estudiantes de física? B: No, pero de química hay una bocha."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bocha"), ("elided", "coda"), ("diagnostic", "subextraction")] }

def ex45 : Datum :=
  { id := "saab2026_ex45"
    source := ⟨"saab-2026", "(45)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Hubo un montón de envíos de libros a Ecuador. B: A COLOMBIA, hubo un montón."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "subextraction")] }

def ex52a : Datum :=
  { id := "saab2026_ex52a"
    source := ⟨"saab-2026", "(52a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un profesor de química y una mierda de física"
    glossedTokens := [("un", "a"), ("profesor", "professor"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("de", "of"), ("física", "physics")]
    glossedWords := [⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r'], [⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], [⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], none⟩]⟩, ⟨['y'], ['a', 'n', 'd'], [⟨['y'], ['a', 'n', 'd'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], [⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex52b : Datum :=
  { id := "saab2026_ex52b"
    source := ⟨"saab-2026", "(52b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de profesor de química y una mierda de física"
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("profesor", "professor"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("de", "of"), ("física", "physics")]
    glossedWords := [⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r'], [⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], [⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], none⟩]⟩, ⟨['y'], ['a', 'n', 'd'], [⟨['y'], ['a', 'n', 'd'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], [⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex53a : Datum :=
  { id := "saab2026_ex53a"
    source := ⟨"saab-2026", "(53a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "algunos profesores de química y un montón de física"
    glossedTokens := [("algunos", "some"), ("profesores", "professors"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("física", "physics")]
    glossedWords := [⟨['a', 'l', 'g', 'u', 'n', 'o', 's'], ['s', 'o', 'm', 'e'], [⟨['a', 'l', 'g', 'u', 'n', 'o', 's'], ['s', 'o', 'm', 'e'], none⟩]⟩, ⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's'], [⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], [⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], none⟩]⟩, ⟨['y'], ['a', 'n', 'd'], [⟨['y'], ['a', 'n', 'd'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], [⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], [⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex53b : Datum :=
  { id := "saab2026_ex53b"
    source := ⟨"saab-2026", "(53b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un montón de profesores de química y un montón de física"
    glossedTokens := [("un", "a"), ("montón", "lot"), ("de", "of"), ("profesores", "professors"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("física", "physics")]
    glossedWords := [⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], [⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's'], [⟨['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's'], ['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], [⟨['q', 'u', 'í', 'm', 'i', 'c', 'a'], ['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y'], none⟩]⟩, ⟨['y'], ['a', 'n', 'd'], [⟨['y'], ['a', 'n', 'd'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], [⟨['m', 'o', 'n', 't', 'ó', 'n'], ['l', 'o', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], [⟨['f', 'í', 's', 'i', 'c', 'a'], ['p', 'h', 'y', 's', 'i', 'c', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex54 : Datum :=
  { id := "saab2026_ex54"
    source := ⟨"saab-2026", "(54)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Contrataron a algún profesor? B: Sí, a una mierda."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("ellipsis", .unacceptable)]
    paperFeatures := [("noun", "mierda"), ("elided", "coda")] }

def ex48 : Datum :=
  { id := "saab2026_ex48"
    source := ⟨"saab-2026", "(48)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Qué mierda!"
    glossedTokens := [("Qué", "what"), ("mierda", "shit.F.SG")]
    glossedWords := [⟨['Q', 'u', 'é'], ['w', 'h', 'a', 't'], [⟨['Q', 'u', 'é'], ['w', 'h', 'a', 't'], none⟩]⟩, ⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't', '.', 'F', '.', 'S', 'G'], [⟨['m', 'i', 'e', 'r', 'd', 'a'], ['s', 'h', 'i', 't', '.', 'F', '.', 'S', 'G'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := "Said after watching a bad movie."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("diagnostic", "contextResolved")] }

def ex62a : Datum :=
  { id := "saab2026_ex62a"
    source := ⟨"saab-2026", "(62a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Un grupo de senadores votó a favor de la ley, pero uno de diputados votó en contra."
    glossedTokens := [("Un", "a"), ("grupo", "group"), ("de", "of"), ("senadores", "senators"), ("votó", "voted.3SG"), ("a", "to"), ("favor", "favor"), ("de", "of"), ("la", "the"), ("ley", "law"), ("pero", "but"), ("uno", "a"), ("de", "of"), ("diputados", "delegates"), ("votó", "voted.3SG"), ("en", "in"), ("contra", "against")]
    glossedWords := [⟨['U', 'n'], ['a'], [⟨['U', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], [⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['s', 'e', 'n', 'a', 'd', 'o', 'r', 'e', 's'], ['s', 'e', 'n', 'a', 't', 'o', 'r', 's'], [⟨['s', 'e', 'n', 'a', 'd', 'o', 'r', 'e', 's'], ['s', 'e', 'n', 'a', 't', 'o', 'r', 's'], none⟩]⟩, ⟨['v', 'o', 't', 'ó'], ['v', 'o', 't', 'e', 'd', '.', '3', 'S', 'G'], [⟨['v', 'o', 't', 'ó'], ['v', 'o', 't', 'e', 'd', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'v', 'o', 'r'], ['f', 'a', 'v', 'o', 'r'], [⟨['f', 'a', 'v', 'o', 'r'], ['f', 'a', 'v', 'o', 'r'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'e', 'y'], ['l', 'a', 'w'], [⟨['l', 'e', 'y'], ['l', 'a', 'w'], none⟩]⟩, ⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], none⟩]⟩, ⟨['u', 'n', 'o'], ['a'], [⟨['u', 'n', 'o'], ['a'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['d', 'i', 'p', 'u', 't', 'a', 'd', 'o', 's'], ['d', 'e', 'l', 'e', 'g', 'a', 't', 'e', 's'], [⟨['d', 'i', 'p', 'u', 't', 'a', 'd', 'o', 's'], ['d', 'e', 'l', 'e', 'g', 'a', 't', 'e', 's'], none⟩]⟩, ⟨['v', 'o', 't', 'ó'], ['v', 'o', 't', 'e', 'd', '.', '3', 'S', 'G'], [⟨['v', 'o', 't', 'ó'], ['v', 'o', 't', 'e', 'd', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'n'], ['i', 'n'], [⟨['e', 'n'], ['i', 'n'], none⟩]⟩, ⟨['c', 'o', 'n', 't', 'r', 'a'], ['a', 'g', 'a', 'i', 'n', 's', 't'], [⟨['c', 'o', 'n', 't', 'r', 'a'], ['a', 'g', 'a', 'i', 'n', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("reading", "descriptive"), ("elided", "first"), ("agreement", "singular"), ("codaNumber", "plural")] }

def ex62b : Datum :=
  { id := "saab2026_ex62b"
    source := ⟨"saab-2026", "(62b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Un grupo de senadores votaron a favor de la ley, pero uno de diputados votaron en contra."
    glossedTokens := [("Un", "a"), ("grupo", "group"), ("de", "of"), ("senadores", "senators"), ("votaron", "voted.3PL"), ("a", "to"), ("favor", "favor"), ("de", "of"), ("la", "the"), ("ley", "law"), ("pero", "but"), ("uno", "a"), ("de", "of"), ("diputados", "delegates"), ("votaron", "voted.3PL"), ("en", "in"), ("contra", "against")]
    glossedWords := [⟨['U', 'n'], ['a'], [⟨['U', 'n'], ['a'], none⟩]⟩, ⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], [⟨['g', 'r', 'u', 'p', 'o'], ['g', 'r', 'o', 'u', 'p'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['s', 'e', 'n', 'a', 'd', 'o', 'r', 'e', 's'], ['s', 'e', 'n', 'a', 't', 'o', 'r', 's'], [⟨['s', 'e', 'n', 'a', 'd', 'o', 'r', 'e', 's'], ['s', 'e', 'n', 'a', 't', 'o', 'r', 's'], none⟩]⟩, ⟨['v', 'o', 't', 'a', 'r', 'o', 'n'], ['v', 'o', 't', 'e', 'd', '.', '3', 'P', 'L'], [⟨['v', 'o', 't', 'a', 'r', 'o', 'n'], ['v', 'o', 't', 'e', 'd', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['a'], ['t', 'o'], [⟨['a'], ['t', 'o'], none⟩]⟩, ⟨['f', 'a', 'v', 'o', 'r'], ['f', 'a', 'v', 'o', 'r'], [⟨['f', 'a', 'v', 'o', 'r'], ['f', 'a', 'v', 'o', 'r'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'e', 'y'], ['l', 'a', 'w'], [⟨['l', 'e', 'y'], ['l', 'a', 'w'], none⟩]⟩, ⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], [⟨['p', 'e', 'r', 'o'], ['b', 'u', 't'], none⟩]⟩, ⟨['u', 'n', 'o'], ['a'], [⟨['u', 'n', 'o'], ['a'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['d', 'i', 'p', 'u', 't', 'a', 'd', 'o', 's'], ['d', 'e', 'l', 'e', 'g', 'a', 't', 'e', 's'], [⟨['d', 'i', 'p', 'u', 't', 'a', 'd', 'o', 's'], ['d', 'e', 'l', 'e', 'g', 'a', 't', 'e', 's'], none⟩]⟩, ⟨['v', 'o', 't', 'a', 'r', 'o', 'n'], ['v', 'o', 't', 'e', 'd', '.', '3', 'P', 'L'], [⟨['v', 'o', 't', 'a', 'r', 'o', 'n'], ['v', 'o', 't', 'e', 'd', '.', '3', 'P', 'L'], none⟩]⟩, ⟨['e', 'n'], ['i', 'n'], [⟨['e', 'n'], ['i', 'n'], none⟩]⟩, ⟨['c', 'o', 'n', 't', 'r', 'a'], ['a', 'g', 'a', 'i', 'n', 's', 't'], [⟨['c', 'o', 'n', 't', 'r', 'a'], ['a', 'g', 'a', 'i', 'n', 's', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("reading", "quantificational"), ("elided", "first"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex63 : Datum :=
  { id := "saab2026_ex63"
    source := ⟨"saab-2026", "(63)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Se me cayó un montón de libros. B: Y, a mí, se me cayó uno de revistas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("reading", "descriptive"), ("elided", "first"), ("agreement", "singular"), ("codaNumber", "plural")] }

def ex64 : Datum :=
  { id := "saab2026_ex64"
    source := ⟨"saab-2026", "(64)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Se me cayeron un montón de libros. B: Y, a mí, se me cayeron uno de revistas."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("reading", "quantificational"), ("elided", "first"), ("agreement", "plural"), ("codaNumber", "plural")] }

def all : List Datum := [ex1a, ex1b, ex1c, ex2a, ex2b, ex2c, ex5_bocha, ex5_grupo, ex6, ex43, ex45, ex52a, ex52b, ex53a, ex53b, ex54, ex48, ex62a, ex62b, ex63, ex64]

end Saab2026.Examples
