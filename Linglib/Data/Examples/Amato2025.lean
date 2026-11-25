module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.Examples.Readers
public import Mathlib.Tactic.DeriveFintype

/-!
# `Amato2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Amato2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Amato2025.Examples`.
-/

@[expose] public section

namespace Amato2025.Examples

def ex_4a : Datum :=
  { id := "amato2025_4a"
    source := ⟨"amato-2025", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa ha lavato le camicie."
    glossedTokens := [("Teresa", "Teresa"), ("ha", "have.PRS.3SG"), ("lavato", "wash.PRTC"), ("le", "the"), ("camicie.", "shirts")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['l', 'a', 'v', 'a', 't', 'o'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], [⟨['l', 'a', 'v', 'a', 't', 'o'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], none⟩]⟩, ⟨['l', 'e'], ['t', 'h', 'e'], [⟨['l', 'e'], ['t', 'h', 'e'], none⟩]⟩, ⟨['c', 'a', 'm', 'i', 'c', 'i', 'e', '.'], ['s', 'h', 'i', 'r', 't', 's'], [⟨['c', 'a', 'm', 'i', 'c', 'i', 'e'], ['s', 'h', 'i', 'r', 't', 's'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩]
    paperFeatures := [("clause", "transitive")] }

def ex_4b : Datum :=
  { id := "amato2025_4b"
    source := ⟨"amato-2025", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa ha risposto a sua madre."
    glossedTokens := [("Teresa", "Teresa"), ("ha", "have.PRS.3SG"), ("risposto", "answer.PRTC"), ("a", "at"), ("sua", "her"), ("madre.", "mother")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['h', 'a'], ['h', 'a', 'v', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['r', 'i', 's', 'p', 'o', 's', 't', 'o'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C'], [⟨['r', 'i', 's', 'p', 'o', 's', 't', 'o'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C'], none⟩]⟩, ⟨['a'], ['a', 't'], [⟨['a'], ['a', 't'], none⟩]⟩, ⟨['s', 'u', 'a'], ['h', 'e', 'r'], [⟨['s', 'u', 'a'], ['h', 'e', 'r'], none⟩]⟩, ⟨['m', 'a', 'd', 'r', 'e', '.'], ['m', 'o', 't', 'h', 'e', 'r'], [⟨['m', 'a', 'd', 'r', 'e'], ['m', 'o', 't', 'h', 'e', 'r'], none⟩]⟩]
    lgrConformance := some .wordAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "avere"⟩]
    paperFeatures := [("clause", "unergative")] }

def ex_4c : Datum :=
  { id := "amato2025_4c"
    source := ⟨"amato-2025", "(4c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa è venut-a alla festa."
    glossedTokens := [("Teresa", "Teresa"), ("è", "be.PRS.3SG"), ("venut-a", "come.PRTC-SG.F"), ("alla", "to.the"), ("festa.", "party")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], none⟩]⟩, ⟨['v', 'e', 'n', 'u', 't', '-', 'a'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['v', 'e', 'n', 'u', 't'], ['c', 'o', 'm', 'e', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩, ⟨['a', 'l', 'l', 'a'], ['t', 'o', '.', 't', 'h', 'e'], [⟨['a', 'l', 'l', 'a'], ['t', 'o', '.', 't', 'h', 'e'], none⟩]⟩, ⟨['f', 'e', 's', 't', 'a', '.'], ['p', 'a', 'r', 't', 'y'], [⟨['f', 'e', 's', 't', 'a'], ['p', 'a', 'r', 't', 'y'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩]
    paperFeatures := [("clause", "unaccusative")] }

def ex_5a : Datum :=
  { id := "amato2025_5a"
    source := ⟨"amato-2025", "(5a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa si=è lavat-a."
    glossedTokens := [("Teresa", "Teresa"), ("si=è", "REFL.ACC.3SG=be.PRS.3SG"), ("lavat-a.", "wash.PRTC-SG.F")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C', '.', '3', 'S', 'G', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['R', 'E', 'F', 'L', '.', 'A', 'C', 'C', '.', '3', 'S', 'G'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['l', 'a', 'v', 'a', 't', '-', 'a', '.'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['l', 'a', 'v', 'a', 't'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩]
    paperFeatures := [("clause", "directReflexive")] }

def ex_5b : Datum :=
  { id := "amato2025_5b"
    source := ⟨"amato-2025", "(5b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa si=è lavat-a il vestito."
    glossedTokens := [("Teresa", "Teresa"), ("si=è", "REFL.DAT.3SG=be.PRS.3SG"), ("lavat-a", "wash.PRTC-SG.F"), ("il", "the"), ("vestito.", "dress")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['l', 'a', 'v', 'a', 't', '-', 'a'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['l', 'a', 'v', 'a', 't'], ['w', 'a', 's', 'h', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['v', 'e', 's', 't', 'i', 't', 'o', '.'], ['d', 'r', 'e', 's', 's'], [⟨['v', 'e', 's', 't', 'i', 't', 'o'], ['d', 'r', 'e', 's', 's'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩]
    paperFeatures := [("clause", "indirectReflexive")] }

def ex_5c : Datum :=
  { id := "amato2025_5c"
    source := ⟨"amato-2025", "(5c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Teresa si=è rispost-a."
    glossedTokens := [("Teresa", "Teresa"), ("si=è", "REFL.DAT.3SG=be.PRS.3SG"), ("rispost-a.", "answer.PRTC-SG.F")]
    glossedWords := [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], [⟨['T', 'e', 'r', 'e', 's', 'a'], ['T', 'e', 'r', 'e', 's', 'a'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['R', 'E', 'F', 'L', '.', 'D', 'A', 'T', '.', '3', 'S', 'G'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['r', 'i', 's', 'p', 'o', 's', 't', '-', 'a', '.'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C', '-', 'S', 'G', '.', 'F'], [⟨['r', 'i', 's', 'p', 'o', 's', 't'], ['a', 'n', 's', 'w', 'e', 'r', '.', 'P', 'R', 'T', 'C'], none⟩, ⟨['a'], ['S', 'G', '.', 'F'], some '-'⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩]
    paperFeatures := [("clause", "indirectReflexive")] }

def ex_5d : Datum :=
  { id := "amato2025_5d"
    source := ⟨"amato-2025", "(5d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri si=è mangiato il gelato."
    glossedTokens := [("Ieri", "yesterday"), ("si=è", "IMPERS=be.PRS.3SG"), ("mangiato", "eat.PRTC"), ("il", "the"), ("gelato.", "ice_cream")]
    glossedWords := [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], [⟨['I', 'e', 'r', 'i'], ['y', 'e', 's', 't', 'e', 'r', 'd', 'a', 'y'], none⟩]⟩, ⟨['s', 'i', '=', 'è'], ['I', 'M', 'P', 'E', 'R', 'S', '=', 'b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], [⟨['s', 'i'], ['I', 'M', 'P', 'E', 'R', 'S'], none⟩, ⟨['è'], ['b', 'e', '.', 'P', 'R', 'S', '.', '3', 'S', 'G'], some '='⟩]⟩, ⟨['m', 'a', 'n', 'g', 'i', 'a', 't', 'o'], ['e', 'a', 't', '.', 'P', 'R', 'T', 'C'], [⟨['m', 'a', 'n', 'g', 'i', 'a', 't', 'o'], ['e', 'a', 't', '.', 'P', 'R', 'T', 'C'], none⟩]⟩, ⟨['i', 'l'], ['t', 'h', 'e'], [⟨['i', 'l'], ['t', 'h', 'e'], none⟩]⟩, ⟨['g', 'e', 'l', 'a', 't', 'o', '.'], ['i', 'c', 'e', '_', 'c', 'r', 'e', 'a', 'm'], [⟨['g', 'e', 'l', 'a', 't', 'o'], ['i', 'c', 'e', '_', 'c', 'r', 'e', 'a', 'm'], none⟩]⟩]
    lgrConformance := some .morphemeAligned
    context := ""
    judgment := .acceptable
    contrasts := []
    readings := []
    spans := [⟨1, 1, "auxiliary", some "essere"⟩]
    paperFeatures := [("clause", "impersonal")] }

def all : List Datum := [ex_4a, ex_4b, ex_4c, ex_5a, ex_5b, ex_5c, ex_5d]

/-- The clause types whose perfect auxiliary the paper compares (§3.1). -/
inductive Clause where
  /-- transitive: a transitive verb with canonical arguments -/
  | transitive
  /-- unergative: an unergative verb -/
  | unergative
  /-- unaccusative: an unaccusative verb -/
  | unaccusative
  /-- directReflexive: a reflexive clitic as the direct object -/
  | directReflexive
  /-- indirectReflexive: a reflexive clitic as the indirect object -/
  | indirectReflexive
  /-- impersonal: the impersonal pronoun si -/
  | impersonal
  deriving DecidableEq, Repr, Fintype

/-- The value a row records under `clause`. -/
def clause (e : Datum) : Option Clause :=
  e.parse? "clause" [("transitive", .transitive), ("unergative", .unergative), ("unaccusative", .unaccusative),
    ("directReflexive", .directReflexive), ("indirectReflexive", .indirectReflexive),
    ("impersonal", .impersonal)]

/-- The labels of the spans the rows mark. -/
inductive SpanLabel where
  /-- auxiliary: the word holding the perfect auxiliary -/
  | auxiliary
  deriving DecidableEq, Repr, Fintype

/-- The label of a span, where it is a declared one. -/
def label? (p : Datum.Span) : Option SpanLabel :=
  List.lookup p.label [("auxiliary", .auxiliary)]

/-- The perfect auxiliaries. -/
inductive Lexeme where
  /-- avere: avere 'have' -/
  | avere
  /-- essere: essere 'be' -/
  | essere
  deriving DecidableEq, Repr, Fintype

/-- The lexeme a span is a form of, where it names a declared one. -/
def lexeme? (p : Datum.Span) : Option Lexeme :=
  p.lexeme.bind (List.lookup · [("avere", .avere), ("essere", .essere)])

/-- The examples of the file. -/
inductive Example where
  | ex_4a
  | ex_4b
  | ex_4c
  | ex_5a
  | ex_5b
  | ex_5c
  | ex_5d
  deriving DecidableEq, Repr, Fintype

/-- Every example of the file, in its order. -/
def Example.all : List Example :=
  [.ex_4a, .ex_4b, .ex_4c, .ex_5a, .ex_5b, .ex_5c, .ex_5d]

/-- The row of an example. -/
def Example.datum : Example → Datum
  | .ex_4a => _root_.Amato2025.Examples.ex_4a
  | .ex_4b => _root_.Amato2025.Examples.ex_4b
  | .ex_4c => _root_.Amato2025.Examples.ex_4c
  | .ex_5a => _root_.Amato2025.Examples.ex_5a
  | .ex_5b => _root_.Amato2025.Examples.ex_5b
  | .ex_5c => _root_.Amato2025.Examples.ex_5c
  | .ex_5d => _root_.Amato2025.Examples.ex_5d

theorem Example.map_datum_all :
    Example.all.map Example.datum = _root_.Amato2025.Examples.all := rfl

/-- The value the example records under `clause`. -/
def Example.clause : Example → Option Clause
  | .ex_4a => some .transitive
  | .ex_4b => some .unergative
  | .ex_4c => some .unaccusative
  | .ex_5a => some .directReflexive
  | .ex_5b => some .indirectReflexive
  | .ex_5c => some .indirectReflexive
  | .ex_5d => some .impersonal

theorem Example.clause_datum :
    ∀ x : Example, _root_.Amato2025.Examples.clause x.datum = x.clause := by
  decide +kernel

/-- The lexemes the spans of the example name, each with the span's label, in order. -/
def Example.labelledLexemes : Example → List (SpanLabel × Lexeme)
  | .ex_4a => [(.auxiliary, .avere)]
  | .ex_4b => [(.auxiliary, .avere)]
  | .ex_4c => [(.auxiliary, .essere)]
  | .ex_5a => [(.auxiliary, .essere)]
  | .ex_5b => [(.auxiliary, .essere)]
  | .ex_5c => [(.auxiliary, .essere)]
  | .ex_5d => [(.auxiliary, .essere)]

/-- The lexemes the spans of the example labelled `l` name, in order. -/
def Example.lexemes (x : Example) (l : SpanLabel) : List Lexeme :=
  (x.labelledLexemes.filter (·.1 = l)).map (·.2)

theorem Example.lexemes_datum : ∀ (x : Example) (l : SpanLabel),
    (x.datum.spans.filter (_root_.Amato2025.Examples.label? · = some l)).filterMap _root_.Amato2025.Examples.lexeme? =
      x.lexemes l := by
  decide +kernel

end Amato2025.Examples
