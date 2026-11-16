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
    glossedWords := [⟨[['u', 'n']], [['a']]⟩, ⟨[['g', 'r', 'u', 'p', 'o']], [['g', 'r', 'o', 'u', 'p']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩]
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
    glossedWords := [⟨[['u', 'n']], [['a']]⟩, ⟨[['m', 'o', 'n', 't', 'ó', 'n']], [['l', 'o', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩]
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
    glossedWords := [⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o']], [['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't']]⟩]
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
    glossedWords := [⟨[['V', 'i', 'n', 'i', 'e', 'r', 'o', 'n']], [['c', 'a', 'm', 'e', '.', '3', 'P', 'L']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['g', 'r', 'u', 'p', 'o']], [['g', 'r', 'o', 'u', 'p', '.', 'S', 'G']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩]
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
    glossedWords := [⟨[['V', 'i', 'n', 'i', 'e', 'r', 'o', 'n']], [['c', 'a', 'm', 'e', '.', '3', 'P', 'L']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['m', 'o', 'n', 't', 'ó', 'n']], [['l', 'o', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['e', 's', 't', 'u', 'd', 'i', 'a', 'n', 't', 'e', 's']], [['s', 't', 'u', 'd', 'e', 'n', 't', 's']]⟩]
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
    glossedWords := [⟨[['S', 'e']], [['s', 'e']]⟩, ⟨[['d', 'e', 'r', 'r', 'u', 'm', 'b', 'a', 'r', 'o', 'n']], [['d', 'e', 'm', 'o', 'l', 'i', 's', 'h', '.', '3', 'P', 'L']]⟩, ⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't', '.', 'S', 'G']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o', 's']], [['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't', 's']]⟩]
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
    glossedWords := [⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['d', 'e', 'p', 'a', 'r', 't', 'a', 'm', 'e', 'n', 't', 'o']], [['a', 'p', 'a', 'r', 't', 'm', 'e', 'n', 't']]⟩, ⟨[['e', 'n']], [['i', 'n']]⟩, ⟨[['S', 'a', 'n', ' ', 'T', 'e', 'l', 'm', 'o']], [['S', 'a', 'n', ' ', 'T', 'e', 'l', 'm', 'o']]⟩, ⟨[['y']], [['a', 'n', 'd']]⟩, ⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't']]⟩, ⟨[['e', 'n']], [['i', 'n']]⟩, ⟨[['L', 'a', ' ', 'B', 'o', 'c', 'a']], [['L', 'a', ' ', 'B', 'o', 'c', 'a']]⟩]
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
    glossedWords := [⟨[['u', 'n']], [['a']]⟩, ⟨[['p', 'r', 'o', 'f', 'e', 's', 'o', 'r']], [['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['q', 'u', 'í', 'm', 'i', 'c', 'a']], [['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y']]⟩, ⟨[['y']], [['a', 'n', 'd']]⟩, ⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['f', 'í', 's', 'i', 'c', 'a']], [['p', 'h', 'y', 's', 'i', 'c', 's']]⟩]
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
    glossedWords := [⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['p', 'r', 'o', 'f', 'e', 's', 'o', 'r']], [['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['q', 'u', 'í', 'm', 'i', 'c', 'a']], [['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y']]⟩, ⟨[['y']], [['a', 'n', 'd']]⟩, ⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['f', 'í', 's', 'i', 'c', 'a']], [['p', 'h', 'y', 's', 'i', 'c', 's']]⟩]
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
    glossedWords := [⟨[['a', 'l', 'g', 'u', 'n', 'o', 's']], [['s', 'o', 'm', 'e']]⟩, ⟨[['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's']], [['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['q', 'u', 'í', 'm', 'i', 'c', 'a']], [['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y']]⟩, ⟨[['y']], [['a', 'n', 'd']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['m', 'o', 'n', 't', 'ó', 'n']], [['l', 'o', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['f', 'í', 's', 'i', 'c', 'a']], [['p', 'h', 'y', 's', 'i', 'c', 's']]⟩]
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
    glossedWords := [⟨[['u', 'n']], [['a']]⟩, ⟨[['m', 'o', 'n', 't', 'ó', 'n']], [['l', 'o', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['p', 'r', 'o', 'f', 'e', 's', 'o', 'r', 'e', 's']], [['p', 'r', 'o', 'f', 'e', 's', 's', 'o', 'r', 's']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['q', 'u', 'í', 'm', 'i', 'c', 'a']], [['c', 'h', 'e', 'm', 'i', 's', 't', 'r', 'y']]⟩, ⟨[['y']], [['a', 'n', 'd']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['m', 'o', 'n', 't', 'ó', 'n']], [['l', 'o', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['f', 'í', 's', 'i', 'c', 'a']], [['p', 'h', 'y', 's', 'i', 'c', 's']]⟩]
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
    glossedWords := [⟨[['Q', 'u', 'é']], [['w', 'h', 'a', 't']]⟩, ⟨[['m', 'i', 'e', 'r', 'd', 'a']], [['s', 'h', 'i', 't', '.', 'F', '.', 'S', 'G']]⟩]
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
    glossedWords := [⟨[['U', 'n']], [['a']]⟩, ⟨[['g', 'r', 'u', 'p', 'o']], [['g', 'r', 'o', 'u', 'p']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['s', 'e', 'n', 'a', 'd', 'o', 'r', 'e', 's']], [['s', 'e', 'n', 'a', 't', 'o', 'r', 's']]⟩, ⟨[['v', 'o', 't', 'ó']], [['v', 'o', 't', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['a']], [['t', 'o']]⟩, ⟨[['f', 'a', 'v', 'o', 'r']], [['f', 'a', 'v', 'o', 'r']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['l', 'e', 'y']], [['l', 'a', 'w']]⟩, ⟨[['p', 'e', 'r', 'o']], [['b', 'u', 't']]⟩, ⟨[['u', 'n', 'o']], [['a']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['d', 'i', 'p', 'u', 't', 'a', 'd', 'o', 's']], [['d', 'e', 'l', 'e', 'g', 'a', 't', 'e', 's']]⟩, ⟨[['v', 'o', 't', 'ó']], [['v', 'o', 't', 'e', 'd', '.', '3', 'S', 'G']]⟩, ⟨[['e', 'n']], [['i', 'n']]⟩, ⟨[['c', 'o', 'n', 't', 'r', 'a']], [['a', 'g', 'a', 'i', 'n', 's', 't']]⟩]
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
    glossedWords := [⟨[['U', 'n']], [['a']]⟩, ⟨[['g', 'r', 'u', 'p', 'o']], [['g', 'r', 'o', 'u', 'p']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['s', 'e', 'n', 'a', 'd', 'o', 'r', 'e', 's']], [['s', 'e', 'n', 'a', 't', 'o', 'r', 's']]⟩, ⟨[['v', 'o', 't', 'a', 'r', 'o', 'n']], [['v', 'o', 't', 'e', 'd', '.', '3', 'P', 'L']]⟩, ⟨[['a']], [['t', 'o']]⟩, ⟨[['f', 'a', 'v', 'o', 'r']], [['f', 'a', 'v', 'o', 'r']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['l', 'e', 'y']], [['l', 'a', 'w']]⟩, ⟨[['p', 'e', 'r', 'o']], [['b', 'u', 't']]⟩, ⟨[['u', 'n', 'o']], [['a']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['d', 'i', 'p', 'u', 't', 'a', 'd', 'o', 's']], [['d', 'e', 'l', 'e', 'g', 'a', 't', 'e', 's']]⟩, ⟨[['v', 'o', 't', 'a', 'r', 'o', 'n']], [['v', 'o', 't', 'e', 'd', '.', '3', 'P', 'L']]⟩, ⟨[['e', 'n']], [['i', 'n']]⟩, ⟨[['c', 'o', 'n', 't', 'r', 'a']], [['a', 'g', 'a', 'i', 'n', 's', 't']]⟩]
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
