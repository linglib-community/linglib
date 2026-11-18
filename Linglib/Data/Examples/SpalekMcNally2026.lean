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
    contrasts := []
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
    glossedWords := [⟨['r', 'a', 's', 'g', 'ó'], ['t', 'e', 'a', 'r', '.', 'P', 'S', 'T', '.', '3', 'S', 'G'], [⟨['r', 'a', 's', 'g', 'ó'], ['t', 'e', 'a', 'r', '.', 'P', 'S', 'T', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['t', 'r', 'o', 'z', 'o'], ['p', 'i', 'e', 'c', 'e'], [⟨['t', 'r', 'o', 'z', 'o'], ['p', 'i', 'e', 'c', 'e'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['p', 'a', 'n'], ['b', 'r', 'e', 'a', 'd'], [⟨['p', 'a', 'n'], ['b', 'r', 'e', 'a', 'd'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    contrasts := []
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
    glossedWords := [⟨['A', 's', 'e', 'g', 'ú', 'r', 'e', 's', 'e'], ['e', 'n', 's', 'u', 'r', 'e', '.', 'I', 'M', 'P', '.', '3', 'S', 'G'], [⟨['A', 's', 'e', 'g', 'ú', 'r', 'e', 's', 'e'], ['e', 'n', 's', 'u', 'r', 'e', '.', 'I', 'M', 'P', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['t', 'e', 'n', 'e', 'r'], ['h', 'a', 'v', 'e', '.', 'I', 'N', 'F'], [⟨['t', 'e', 'n', 'e', 'r'], ['h', 'a', 'v', 'e', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['l', 'a', 's'], ['t', 'h', 'e'], [⟨['l', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['u', 'ñ', 'a', 's'], ['n', 'a', 'i', 'l', 's'], [⟨['u', 'ñ', 'a', 's'], ['n', 'a', 'i', 'l', 's'], none⟩]⟩, ⟨['c', 'o', 'r', 't', 'a', 's'], ['s', 'h', 'o', 'r', 't'], [⟨['c', 'o', 'r', 't', 'a', 's'], ['s', 'h', 'o', 'r', 't'], none⟩]⟩, ⟨['[', '…', ']'], ['[', '…', ']'], []⟩, ⟨['p', 'a', 'r', 'a'], ['f', 'o', 'r'], [⟨['p', 'a', 'r', 'a'], ['f', 'o', 'r'], none⟩]⟩, ⟨['e', 'v', 'i', 't', 'a', 'r'], ['a', 'v', 'o', 'i', 'd', '.', 'I', 'N', 'F'], [⟨['e', 'v', 'i', 't', 'a', 'r'], ['a', 'v', 'o', 'i', 'd', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['r', 'a', 's', 'g', 'a', 'r'], ['t', 'e', 'a', 'r', '.', 'I', 'N', 'F'], [⟨['r', 'a', 's', 'g', 'a', 'r'], ['t', 'e', 'a', 'r', '.', 'I', 'N', 'F'], none⟩]⟩, ⟨['l', 'a', 's'], ['t', 'h', 'e'], [⟨['l', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['l', 'e', 'n', 't', 'e', 's'], ['l', 'e', 'n', 's', 'e', 's'], [⟨['l', 'e', 'n', 't', 'e', 's'], ['l', 'e', 'n', 's', 'e', 's'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['c', 'o', 'n', 't', 'a', 'c', 't', 'o'], ['c', 'o', 'n', 't', 'a', 'c', 't'], [⟨['c', 'o', 'n', 't', 'a', 'c', 't', 'o'], ['c', 'o', 'n', 't', 'a', 'c', 't'], none⟩]⟩, ⟨['b', 'l', 'a', 'n', 'd', 'a', 's'], ['s', 'o', 'f', 't'], [⟨['b', 'l', 'a', 'n', 'd', 'a', 's'], ['s', 'o', 'f', 't'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
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
    glossedWords := [⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'u', 'n', 'z', 'ó', 'n'], ['a', 'w', 'l'], [⟨['p', 'u', 'n', 'z', 'ó', 'n'], ['a', 'w', 'l'], none⟩]⟩, ⟨['d', 'e', 'l'], ['o', 'f', '.', 't', 'h', 'e'], [⟨['d', 'e', 'l'], ['o', 'f', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['a', 'l', 'b', 'a', 'ñ', 'i', 'l'], ['w', 'o', 'r', 'k', 'm', 'a', 'n'], [⟨['a', 'l', 'b', 'a', 'ñ', 'i', 'l'], ['w', 'o', 'r', 'k', 'm', 'a', 'n'], none⟩]⟩, ⟨['r', 'a', 's', 'g', 'ó'], ['t', 'o', 'r', 'e'], [⟨['r', 'a', 's', 'g', 'ó'], ['t', 'o', 'r', 'e'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'e', 'm', 'e', 'n', 't', 'o'], ['c', 'e', 'm', 'e', 'n', 't'], [⟨['c', 'e', 'm', 'e', 'n', 't', 'o'], ['c', 'e', 'm', 'e', 'n', 't'], none⟩]⟩, ⟨['c', 'o', 'n'], ['w', 'i', 't', 'h'], [⟨['c', 'o', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['s', 'u'], ['h', 'i', 's'], [⟨['s', 'u'], ['h', 'i', 's'], none⟩]⟩, ⟨['n', 'o', 'm', 'b', 'r', 'e'], ['n', 'a', 'm', 'e'], [⟨['n', 'o', 'm', 'b', 'r', 'e'], ['n', 'a', 'm', 'e'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
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
    contrasts := []
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
    glossedWords := [⟨['L', 'o', 's'], ['t', 'h', 'e'], [⟨['L', 'o', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['n', 'i', 'ñ', 'o', 's'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], [⟨['n', 'i', 'ñ', 'o', 's'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], none⟩]⟩, ⟨['q', 'u', 'e'], ['w', 'h', 'o'], [⟨['q', 'u', 'e'], ['w', 'h', 'o'], none⟩]⟩, ⟨['r', 'e', 'c', 'i', 'b', 'i', 'e', 'r', 'o', 'n'], ['r', 'e', 'c', 'e', 'i', 'v', 'e', 'd'], [⟨['r', 'e', 'c', 'i', 'b', 'i', 'e', 'r', 'o', 'n'], ['r', 'e', 'c', 'e', 'i', 'v', 'e', 'd'], none⟩]⟩, ⟨['c', 'h', 'i', 'c', 'l', 'e'], ['g', 'u', 'm'], [⟨['c', 'h', 'i', 'c', 'l', 'e'], ['g', 'u', 'm'], none⟩]⟩, ⟨['r', 'a', 's', 'g', 'a', 'r', 'o', 'n'], ['t', 'o', 'r', 'e'], [⟨['r', 'a', 's', 'g', 'a', 'r', 'o', 'n'], ['t', 'o', 'r', 'e'], none⟩]⟩, ⟨['c', 'o', 'n'], ['w', 'i', 't', 'h'], [⟨['c', 'o', 'n'], ['w', 'i', 't', 'h'], none⟩]⟩, ⟨['c', 'u', 'i', 'd', 'a', 'd', 'o'], ['c', 'a', 'r', 'e'], [⟨['c', 'u', 'i', 'd', 'a', 'd', 'o'], ['c', 'a', 'r', 'e'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['p', 'a', 'p', 'e', 'l'], ['p', 'a', 'p', 'e', 'r'], [⟨['p', 'a', 'p', 'e', 'l'], ['p', 'a', 'p', 'e', 'r'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['a', 'l', 'u', 'm', 'i', 'n', 'i', 'o'], ['a', 'l', 'u', 'm', 'i', 'n', 'i', 'u', 'm'], [⟨['a', 'l', 'u', 'm', 'i', 'n', 'i', 'o'], ['a', 'l', 'u', 'm', 'i', 'n', 'i', 'u', 'm'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .questionable
    contrasts := []
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
    glossedWords := [⟨['L', 'a'], ['t', 'h', 'e'], [⟨['L', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['o', 's', 'c', 'u', 'r', 'i', 'd', 'a', 'd'], ['d', 'a', 'r', 'k', 'n', 'e', 's', 's'], [⟨['o', 's', 'c', 'u', 'r', 'i', 'd', 'a', 'd'], ['d', 'a', 'r', 'k', 'n', 'e', 's', 's'], none⟩]⟩, ⟨['s', 'e'], ['R', 'E', 'F', 'L'], [⟨['s', 'e'], ['R', 'E', 'F', 'L'], none⟩]⟩, ⟨['r', 'a', 's', 'g', 'a'], ['t', 'e', 'a', 'r', 's'], [⟨['r', 'a', 's', 'g', 'a'], ['t', 'e', 'a', 'r', 's'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['i', 'm', 'p', 'r', 'o', 'v', 'i', 's', 'o'], ['s', 'p', 'o', 'n', 't', 'a', 'n', 'e', 'o', 'u', 's'], [⟨['i', 'm', 'p', 'r', 'o', 'v', 'i', 's', 'o'], ['s', 'p', 'o', 'n', 't', 'a', 'n', 'e', 'o', 'u', 's'], none⟩]⟩, ⟨['p', 'o', 'r'], ['b', 'y'], [⟨['p', 'o', 'r'], ['b', 'y'], none⟩]⟩, ⟨['l', 'a'], ['t', 'h', 'e'], [⟨['l', 'a'], ['t', 'h', 'e'], none⟩]⟩, ⟨['r', 'e', 'p', 'e', 'n', 't', 'i', 'n', 'a'], ['s', 'u', 'd', 'd', 'e', 'n'], [⟨['r', 'e', 'p', 'e', 'n', 't', 'i', 'n', 'a'], ['s', 'u', 'd', 'd', 'e', 'n'], none⟩]⟩, ⟨['l', 'l', 'a', 'm', 'a', 'r', 'a', 'd', 'a'], ['b', 'l', 'a', 'z', 'e'], [⟨['l', 'l', 'a', 'm', 'a', 'r', 'a', 'd', 'a'], ['b', 'l', 'a', 'z', 'e'], none⟩]⟩, ⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], [⟨['q', 'u', 'e'], ['t', 'h', 'a', 't'], none⟩]⟩, ⟨['p', 'r', 'o', 'd', 'u', 'c', 'e'], ['p', 'r', 'o', 'd', 'u', 'c', 'e', 's'], [⟨['p', 'r', 'o', 'd', 'u', 'c', 'e'], ['p', 'r', 'o', 'd', 'u', 'c', 'e', 's'], none⟩]⟩, ⟨['u', 'n'], ['a'], [⟨['u', 'n'], ['a'], none⟩]⟩, ⟨['p', 'o', 'c', 'o'], ['b', 'i', 't'], [⟨['p', 'o', 'c', 'o'], ['b', 'i', 't'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['r', 'o', 'm', 'e', 'r', 'o'], ['r', 'o', 's', 'e', 'm', 'a', 'r', 'y'], [⟨['r', 'o', 'm', 'e', 'r', 'o'], ['r', 'o', 's', 'e', 'm', 'a', 'r', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
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
    glossedWords := [⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['i', 'n', 'q', 'u', 'i', 'e', 't', 'a', 'n', 't', 'e'], ['d', 'i', 's', 'q', 'u', 'e', 't', 'i', 'n', 'g'], [⟨['i', 'n', 'q', 'u', 'i', 'e', 't', 'a', 'n', 't', 'e'], ['d', 'i', 's', 'q', 'u', 'e', 't', 'i', 'n', 'g'], none⟩]⟩, ⟨['m', 'e', 'l', 'o', 'd', 'í', 'a'], ['m', 'e', 'l', 'o', 'd', 'y'], [⟨['m', 'e', 'l', 'o', 'd', 'í', 'a'], ['m', 'e', 'l', 'o', 'd', 'y'], none⟩]⟩, ⟨['r', 'a', 's', 'g', 'a', 'b', 'a'], ['t', 'e', 'a', 'r', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], [⟨['r', 'a', 's', 'g', 'a', 'b', 'a'], ['t', 'e', 'a', 'r', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'i', 'l', 'e', 'n', 'c', 'i', 'o'], ['s', 'i', 'l', 'e', 'n', 'c', 'e'], [⟨['s', 'i', 'l', 'e', 'n', 'c', 'i', 'o'], ['s', 'i', 'l', 'e', 'n', 'c', 'e'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['l', 'a', 's'], ['t', 'h', 'e'], [⟨['l', 'a', 's'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'l', 'l', 'e', 's'], ['s', 't', 'r', 'e', 'e', 't', 's'], [⟨['c', 'a', 'l', 'l', 'e', 's'], ['s', 't', 'r', 'e', 'e', 't', 's'], none⟩]⟩, ⟨['d', 'e', 's', 'i', 'e', 'r', 't', 'a', 's'], ['e', 'm', 'p', 't', 'y'], [⟨['d', 'e', 's', 'i', 'e', 'r', 't', 'a', 's'], ['e', 'm', 'p', 't', 'y'], none⟩]⟩, ⟨['e', 'n'], ['i', 'n'], [⟨['e', 'n'], ['i', 'n'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['e', 's', 't', 'í', 'o'], ['s', 'u', 'm', 'm', 'e', 'r'], [⟨['e', 's', 't', 'í', 'o'], ['s', 'u', 'm', 'm', 'e', 'r'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['m', 'i'], ['m', 'y'], [⟨['m', 'i'], ['m', 'y'], none⟩]⟩, ⟨['C', 'ó', 'r', 'd', 'o', 'b', 'a'], ['C', 'ó', 'r', 'd', 'o', 'b', 'a'], [⟨['C', 'ó', 'r', 'd', 'o', 'b', 'a'], ['C', 'ó', 'r', 'd', 'o', 'b', 'a'], none⟩]⟩, ⟨['n', 'a', 't', 'a', 'l', '.'], ['n', 'a', 't', 'i', 'v', 'e'], [⟨['n', 'a', 't', 'a', 'l'], ['n', 'a', 't', 'i', 'v', 'e'], none⟩]⟩, ⟨['E', 'r', 'a'], ['b', 'e', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], [⟨['E', 'r', 'a'], ['b', 'e', '.', 'I', 'P', 'F', 'V', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['e', 'l'], ['t', 'h', 'e'], [⟨['e', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['s', 'o', 'n', 'i', 'q', 'u', 'e', 't', 'e'], ['l', 'i', 't', 't', 'l', 'e', '.', 's', 'o', 'u', 'n', 'd'], [⟨['s', 'o', 'n', 'i', 'q', 'u', 'e', 't', 'e'], ['l', 'i', 't', 't', 'l', 'e', '.', 's', 'o', 'u', 'n', 'd'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['u', 'n', 'a'], ['a'], [⟨['u', 'n', 'a'], ['a'], none⟩]⟩, ⟨['a', 'r', 'm', 'ó', 'n', 'i', 'c', 'a'], ['h', 'a', 'r', 'm', 'o', 'n', 'i', 'c', 'a'], [⟨['a', 'r', 'm', 'ó', 'n', 'i', 'c', 'a'], ['h', 'a', 'r', 'm', 'o', 'n', 'i', 'c', 'a'], none⟩]⟩, ⟨['d', 'e'], ['o', 'f'], [⟨['d', 'e'], ['o', 'f'], none⟩]⟩, ⟨['j', 'u', 'g', 'u', 'e', 't', 'e'], ['t', 'o', 'y'], [⟨['j', 'u', 'g', 'u', 'e', 't', 'e'], ['t', 'o', 'y'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
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
    contrasts := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_14a, ex_14b, ex_16a, ex_16b, ex_17a, ex_17b, ex_18b, ex_19a, ex_23a]

end SpalekMcNally2026.Examples
