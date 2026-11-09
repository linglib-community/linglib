module

public import Linglib.Core.ModelTheory.ManySorted.Simulation

/-!
# Type-driven interpreters

A type-driven grammar says how the meanings of constituents combine, knowing only their types: it
has binary rules, the modes of combination, and unary rules, the type shifts. It is a many-sorted
language whose symbols take one argument or a pair, a derivation is a term of that language over
typed lexical items, and a structure for it gives each derivation a value.

What an interpreter asks of the syntax is a bare structure, the words in their constituency and
order with a label at each node, and an interpreter says which rules a node admits, by its label
and the types of its daughters. The derivations over a bare structure are found from the types
alone. Two interpreters over one grammar are two theories of what a structure can mean.

## Main definitions

* `Interpreter.Grammar`: the unary and binary rules over a type of semantic types.
* `Interpreter.Grammar.language`, `Interpreter.Grammar.structure`: the many-sorted language of a
  grammar, and the structure that operations for its rules make.
* `Interpreter.Grammar.Deriv`: the derivations of a type over typed lexical items.
* `Interpreter.Grammar.Skeleton`: a bare structure.
* `Interpreter`: the rules a node admits by its label and its daughters' types.
* `Interpreter.derivs`, `Interpreter.values`: the derivations over a bare structure, and their
  values.

## Implementation notes

`Interpreter.derivs` matches on the derivations of the daughters and does not project from them:
a projection is unfolded again wherever it is inspected, which made checking a sentence's value
some fifty times dearer. A lexicon gives each word typed items and their values separately. With
the values inside the items, as `Interpreter.meanings` has them, a statement over a model with
variables in it is still slow to check, and `Interpreter.values` is the form to use there.

## References

* [bumford-charlow-2026]
* [klein-sag-1985]
* [montague-1970]
-/

@[expose] public section

universe u v w x

open MSFirstOrder

namespace Interpreter

/-- A type-driven grammar over semantic types `T`: its type shifts and its modes of combination,
each typed by what it takes and what it yields. -/
structure Grammar (T : Type u) where
  /-- The unary rules from one type to another. -/
  Unary : T → T → Type v
  /-- The binary rules combining a left and a right daughter into a mother. -/
  Binary : T → T → T → Type v

namespace Grammar

variable {T : Type u} {G : Grammar.{u, v} T} {W : T → Type w} {D : T → Type x}

/-- The symbols of a grammar: a unary rule takes one argument and a binary rule a pair. -/
inductive Sym (G : Grammar.{u, v} T) : Signature T → T → Type (max u v)
  /-- A unary rule. -/
  | unary {a b : T} (s : G.Unary a b) : Sym G (.of a) b
  /-- A binary rule. -/
  | binary {a b c : T} (m : G.Binary a b c) : Sym G (.prod (.of a) (.of b)) c

/-- The many-sorted language of a grammar. -/
def language (G : Grammar.{u, v} T) : Language.{u, max u v} T := ⟨G.Sym⟩

/-- The structure for a grammar's language that operations for its rules make. -/
def «structure» (unary : ∀ {a b : T}, G.Unary a b → D a → D b)
    (binary : ∀ {a b c : T}, G.Binary a b c → D a → D b → D c) : G.language.Structure D where
  funMap
    | .unary s, x => unary s x
    | .binary m, (x, y) => binary m x y

/-- A derivation of a type from lexical items of the types `W` supplies. -/
abbrev Deriv (G : Grammar.{u, v} T) (W : T → Type w) (a : T) : Type (max u v w) :=
  G.language.Term W (.of a)

namespace Deriv

/-- A lexical item. -/
abbrev leaf {a : T} (x : W a) : Deriv G W a := .var x

/-- A unary rule applied to a derivation. -/
abbrev unary {a b : T} (s : G.Unary a b) (d : Deriv G W a) : Deriv G W b :=
  .func (L := G.language) (Sym.unary s) d

/-- A binary rule applied to two derivations. -/
abbrev binary {a b c : T} (m : G.Binary a b c) (d₁ : Deriv G W a) (d₂ : Deriv G W b) :
    Deriv G W c :=
  .func (L := G.language) (Sym.binary m) (.prod d₁ d₂)

end Deriv

/-- A bare structure over node labels `N` and leaves `L`: what a type-driven interpreter asks of
the syntax. -/
inductive Skeleton (N : Type v) (L : Type w) : Type (max v w)
  /-- A leaf. -/
  | leaf (x : L) : Skeleton N L
  /-- A unary node. -/
  | unary (n : N) (s : Skeleton N L) : Skeleton N L
  /-- A binary node. -/
  | binary (n : N) (s₁ s₂ : Skeleton N L) : Skeleton N L

end Grammar

end Interpreter

/-- A type-driven interpreter for a grammar: the rules a node admits, by its label and the types
of its daughters. -/
structure Interpreter {T : Type u} (G : Interpreter.Grammar.{u, v} T) (N : Type v) where
  /-- The unary rules a node labelled `n` over a daughter of type `a` admits. -/
  unary : N → (a : T) → List (Σ b, G.Unary a b)
  /-- The binary rules a node labelled `n` over daughters of types `l` and `r` admits. -/
  binary : N → (l r : T) → List (Σ u, G.Binary l r u)

namespace Interpreter

open Grammar

variable {T : Type u} {G : Grammar.{u, v} T} {N : Type v} {L : Type w} {W : T → Type w}
  {D : T → Type x}

/-- The derivations over a bare structure that an interpreter admits, given the typed items each
word may be. -/
def derivs (I : Interpreter G N) (lex : L → List (Σ a, W a)) :
    Skeleton N L → List (Σ a, Deriv G W a)
  | .leaf x => (lex x).map fun ⟨a, w⟩ ↦ ⟨a, .leaf w⟩
  | .unary n s => (I.derivs lex s).flatMap fun ⟨a, d⟩ ↦
      (I.unary n a).map fun ⟨b, r⟩ ↦ ⟨b, .unary r d⟩
  | .binary n s₁ s₂ => (I.derivs lex s₁).flatMap fun ⟨a, d₁⟩ ↦
      (I.derivs lex s₂).flatMap fun ⟨b, d₂⟩ ↦
        (I.binary n a b).map fun ⟨c, m⟩ ↦ ⟨c, .binary m d₁ d₂⟩

/-- The values of the derivations over a bare structure, for a lexicon of typed items whose
values `ρ` gives. The derivations are found from the types alone. -/
def values (I : Interpreter G N) (M : G.language.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L → List (Σ a, W a)) (s : Skeleton N L) : List (Σ a, D a) :=
  (I.derivs lex s).map fun ⟨a, d⟩ ↦ ⟨a, d.realize M ρ⟩

/-- The meanings of a bare structure, for a lexicon whose items are their values. -/
def meanings {D : T → Type w} (I : Interpreter G N) (M : G.language.Structure D)
    (lex : L → List (Σ a, D a)) : Skeleton N L → List (Σ a, D a) :=
  I.values M id lex

end Interpreter
