module

public import Linglib.Data.Examples.Schema

/-!
# `SpalekMcNally2026` — typed example data

Auto-generated from `Linglib/Data/Examples/SpalekMcNally2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SpalekMcNally2026.Examples`.
-/

@[expose] public section

namespace SpalekMcNally2026.Examples

def ex_14a : Datum :=
  { id := "spalekmcnally2026_14a"
    source := ⟨"spalek-mcnally-2026", "(14a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "she tore a chunk off her slice of bread"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "spalekmcnally2026_14b"
    source := ⟨"spalek-mcnally-2026", "(14b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "rasgó un trozo de pan"
    glossedTokens := [("rasgó", "tear.PST.3SG"), ("un", "a"), ("trozo", "piece"), ("de", "of"), ("pan", "bread")]
    glossedWords := [⟨[['r', 'a', 's', 'g', 'ó']], [['t', 'e', 'a', 'r', '.', 'P', 'S', 'T', '.', '3', 'S', 'G']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['t', 'r', 'o', 'z', 'o']], [['p', 'i', 'e', 'c', 'e']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['p', 'a', 'n']], [['b', 'r', 'e', 'a', 'd']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_16a : Datum :=
  { id := "spalekmcnally2026_16a"
    source := ⟨"spalek-mcnally-2026", "(16a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1288"
    primaryText := "Asegúrese de tener las uñas cortas […] para evitar rasgar las lentes de contacto blandas"
    glossedTokens := [("Asegúrese", "ensure.IMP.3SG"), ("de", "of"), ("tener", "have.INF"), ("las", "the"), ("uñas", "nails"), ("cortas", "short"), ("[…]", "[…]"), ("para", "for"), ("evitar", "avoid.INF"), ("rasgar", "tear.INF"), ("las", "the"), ("lentes", "lenses"), ("de", "of"), ("contacto", "contact"), ("blandas", "soft")]
    glossedWords := [⟨[['A', 's', 'e', 'g', 'ú', 'r', 'e', 's', 'e']], [['e', 'n', 's', 'u', 'r', 'e', '.', 'I', 'M', 'P', '.', '3', 'S', 'G']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['t', 'e', 'n', 'e', 'r']], [['h', 'a', 'v', 'e', '.', 'I', 'N', 'F']]⟩, ⟨[['l', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['u', 'ñ', 'a', 's']], [['n', 'a', 'i', 'l', 's']]⟩, ⟨[['c', 'o', 'r', 't', 'a', 's']], [['s', 'h', 'o', 'r', 't']]⟩, ⟨[[]], [['[', '…', ']']]⟩, ⟨[['p', 'a', 'r', 'a']], [['f', 'o', 'r']]⟩, ⟨[['e', 'v', 'i', 't', 'a', 'r']], [['a', 'v', 'o', 'i', 'd', '.', 'I', 'N', 'F']]⟩, ⟨[['r', 'a', 's', 'g', 'a', 'r']], [['t', 'e', 'a', 'r', '.', 'I', 'N', 'F']]⟩, ⟨[['l', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['l', 'e', 'n', 't', 'e', 's']], [['l', 'e', 'n', 's', 'e', 's']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['c', 'o', 'n', 't', 'a', 'c', 't', 'o']], [['c', 'o', 'n', 't', 'a', 'c', 't']]⟩, ⟨[['b', 'l', 'a', 'n', 'd', 'a', 's']], [['s', 'o', 'f', 't']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_16b : Datum :=
  { id := "spalekmcnally2026_16b"
    source := ⟨"spalek-mcnally-2026", "(16b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1288"
    primaryText := "el punzón del albañil rasgó el cemento con su nombre"
    glossedTokens := [("el", "the"), ("punzón", "awl"), ("del", "of.the"), ("albañil", "workman"), ("rasgó", "tore"), ("el", "the"), ("cemento", "cement"), ("con", "with"), ("su", "his"), ("nombre", "name")]
    glossedWords := [⟨[['e', 'l']], [['t', 'h', 'e']]⟩, ⟨[['p', 'u', 'n', 'z', 'ó', 'n']], [['a', 'w', 'l']]⟩, ⟨[['d', 'e', 'l']], [['o', 'f', '.', 't', 'h', 'e']]⟩, ⟨[['a', 'l', 'b', 'a', 'ñ', 'i', 'l']], [['w', 'o', 'r', 'k', 'm', 'a', 'n']]⟩, ⟨[['r', 'a', 's', 'g', 'ó']], [['t', 'o', 'r', 'e']]⟩, ⟨[['e', 'l']], [['t', 'h', 'e']]⟩, ⟨[['c', 'e', 'm', 'e', 'n', 't', 'o']], [['c', 'e', 'm', 'e', 'n', 't']]⟩, ⟨[['c', 'o', 'n']], [['w', 'i', 't', 'h']]⟩, ⟨[['s', 'u']], [['h', 'i', 's']]⟩, ⟨[['n', 'o', 'm', 'b', 'r', 'e']], [['n', 'a', 'm', 'e']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_17a : Datum :=
  { id := "spalekmcnally2026_17a"
    source := ⟨"spalek-mcnally-2026", "(17a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "The kids who got gum carefully tore the tin foil"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_17b : Datum :=
  { id := "spalekmcnally2026_17b"
    source := ⟨"spalek-mcnally-2026", "(17b)"⟩
    reportedIn := none
    method := some .elicitation
    language := "stan1288"
    primaryText := "Los niños que recibieron chicle rasgaron con cuidado el papel de aluminio"
    glossedTokens := [("Los", "the"), ("niños", "children"), ("que", "who"), ("recibieron", "received"), ("chicle", "gum"), ("rasgaron", "tore"), ("con", "with"), ("cuidado", "care"), ("el", "the"), ("papel", "paper"), ("de", "of"), ("aluminio", "aluminium")]
    glossedWords := [⟨[['L', 'o', 's']], [['t', 'h', 'e']]⟩, ⟨[['n', 'i', 'ñ', 'o', 's']], [['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']]⟩, ⟨[['q', 'u', 'e']], [['w', 'h', 'o']]⟩, ⟨[['r', 'e', 'c', 'i', 'b', 'i', 'e', 'r', 'o', 'n']], [['r', 'e', 'c', 'e', 'i', 'v', 'e', 'd']]⟩, ⟨[['c', 'h', 'i', 'c', 'l', 'e']], [['g', 'u', 'm']]⟩, ⟨[['r', 'a', 's', 'g', 'a', 'r', 'o', 'n']], [['t', 'o', 'r', 'e']]⟩, ⟨[['c', 'o', 'n']], [['w', 'i', 't', 'h']]⟩, ⟨[['c', 'u', 'i', 'd', 'a', 'd', 'o']], [['c', 'a', 'r', 'e']]⟩, ⟨[['e', 'l']], [['t', 'h', 'e']]⟩, ⟨[['p', 'a', 'p', 'e', 'l']], [['p', 'a', 'p', 'e', 'r']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['a', 'l', 'u', 'm', 'i', 'n', 'i', 'o']], [['a', 'l', 'u', 'm', 'i', 'n', 'i', 'u', 'm']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_18b : Datum :=
  { id := "spalekmcnally2026_18b"
    source := ⟨"spalek-mcnally-2026", "(18b)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1288"
    primaryText := "La oscuridad se rasga de improviso por la repentina llamarada que produce un poco de romero"
    glossedTokens := [("La", "the"), ("oscuridad", "darkness"), ("se", "REFL"), ("rasga", "tears"), ("de", "of"), ("improviso", "spontaneous"), ("por", "by"), ("la", "the"), ("repentina", "sudden"), ("llamarada", "blaze"), ("que", "that"), ("produce", "produces"), ("un", "a"), ("poco", "bit"), ("de", "of"), ("romero", "rosemary")]
    glossedWords := [⟨[['L', 'a']], [['t', 'h', 'e']]⟩, ⟨[['o', 's', 'c', 'u', 'r', 'i', 'd', 'a', 'd']], [['d', 'a', 'r', 'k', 'n', 'e', 's', 's']]⟩, ⟨[['s', 'e']], [['R', 'E', 'F', 'L']]⟩, ⟨[['r', 'a', 's', 'g', 'a']], [['t', 'e', 'a', 'r', 's']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['i', 'm', 'p', 'r', 'o', 'v', 'i', 's', 'o']], [['s', 'p', 'o', 'n', 't', 'a', 'n', 'e', 'o', 'u', 's']]⟩, ⟨[['p', 'o', 'r']], [['b', 'y']]⟩, ⟨[['l', 'a']], [['t', 'h', 'e']]⟩, ⟨[['r', 'e', 'p', 'e', 'n', 't', 'i', 'n', 'a']], [['s', 'u', 'd', 'd', 'e', 'n']]⟩, ⟨[['l', 'l', 'a', 'm', 'a', 'r', 'a', 'd', 'a']], [['b', 'l', 'a', 'z', 'e']]⟩, ⟨[['q', 'u', 'e']], [['t', 'h', 'a', 't']]⟩, ⟨[['p', 'r', 'o', 'd', 'u', 'c', 'e']], [['p', 'r', 'o', 'd', 'u', 'c', 'e', 's']]⟩, ⟨[['u', 'n']], [['a']]⟩, ⟨[['p', 'o', 'c', 'o']], [['b', 'i', 't']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['r', 'o', 'm', 'e', 'r', 'o']], [['r', 'o', 's', 'e', 'm', 'a', 'r', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19a : Datum :=
  { id := "spalekmcnally2026_19a"
    source := ⟨"spalek-mcnally-2026", "(19a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1288"
    primaryText := "una inquietante melodía rasgaba el silencio de las calles desiertas en el estío de mi Córdoba natal. Era el soniquete de una armónica de juguete"
    glossedTokens := [("una", "a"), ("inquietante", "disqueting"), ("melodía", "melody"), ("rasgaba", "tear.IPFV.3SG"), ("el", "the"), ("silencio", "silence"), ("de", "of"), ("las", "the"), ("calles", "streets"), ("desiertas", "empty"), ("en", "in"), ("el", "the"), ("estío", "summer"), ("de", "of"), ("mi", "my"), ("Córdoba", "Córdoba"), ("natal.", "native"), ("Era", "be.IPFV.3SG"), ("el", "the"), ("soniquete", "little.sound"), ("de", "of"), ("una", "a"), ("armónica", "harmonica"), ("de", "of"), ("juguete", "toy")]
    glossedWords := [⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['i', 'n', 'q', 'u', 'i', 'e', 't', 'a', 'n', 't', 'e']], [['d', 'i', 's', 'q', 'u', 'e', 't', 'i', 'n', 'g']]⟩, ⟨[['m', 'e', 'l', 'o', 'd', 'í', 'a']], [['m', 'e', 'l', 'o', 'd', 'y']]⟩, ⟨[['r', 'a', 's', 'g', 'a', 'b', 'a']], [['t', 'e', 'a', 'r', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G']]⟩, ⟨[['e', 'l']], [['t', 'h', 'e']]⟩, ⟨[['s', 'i', 'l', 'e', 'n', 'c', 'i', 'o']], [['s', 'i', 'l', 'e', 'n', 'c', 'e']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['l', 'a', 's']], [['t', 'h', 'e']]⟩, ⟨[['c', 'a', 'l', 'l', 'e', 's']], [['s', 't', 'r', 'e', 'e', 't', 's']]⟩, ⟨[['d', 'e', 's', 'i', 'e', 'r', 't', 'a', 's']], [['e', 'm', 'p', 't', 'y']]⟩, ⟨[['e', 'n']], [['i', 'n']]⟩, ⟨[['e', 'l']], [['t', 'h', 'e']]⟩, ⟨[['e', 's', 't', 'í', 'o']], [['s', 'u', 'm', 'm', 'e', 'r']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['m', 'i']], [['m', 'y']]⟩, ⟨[['C', 'ó', 'r', 'd', 'o', 'b', 'a']], [['C', 'ó', 'r', 'd', 'o', 'b', 'a']]⟩, ⟨[['n', 'a', 't', 'a', 'l']], [['n', 'a', 't', 'i', 'v', 'e']]⟩, ⟨[['E', 'r', 'a']], [['b', 'e', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G']]⟩, ⟨[['e', 'l']], [['t', 'h', 'e']]⟩, ⟨[['s', 'o', 'n', 'i', 'q', 'u', 'e', 't', 'e']], [['l', 'i', 't', 't', 'l', 'e', '.', 's', 'o', 'u', 'n', 'd']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['u', 'n', 'a']], [['a']]⟩, ⟨[['a', 'r', 'm', 'ó', 'n', 'i', 'c', 'a']], [['h', 'a', 'r', 'm', 'o', 'n', 'i', 'c', 'a']]⟩, ⟨[['d', 'e']], [['o', 'f']]⟩, ⟨[['j', 'u', 'g', 'u', 'e', 't', 'e']], [['t', 'o', 'y']]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_23a : Datum :=
  { id := "spalekmcnally2026_23a"
    source := ⟨"spalek-mcnally-2026", "(23a)"⟩
    reportedIn := none
    method := some .corpus
    language := "stan1293"
    primaryText := "the ball tore through the rough edging the green and bounced onto the front of the putting surface"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_14a, ex_14b, ex_16a, ex_16b, ex_17a, ex_17b, ex_18b, ex_19a, ex_23a]

end SpalekMcNally2026.Examples
