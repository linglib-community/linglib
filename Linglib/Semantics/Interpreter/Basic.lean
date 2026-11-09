module

public import Linglib.Core.ModelTheory.Signature

/-!
# Type-driven interpreters

A type-driven grammar says how the meanings of constituents combine, knowing only their types: it
has binary rules, the modes of combination, and unary rules, the type shifts. What an interpreter
asks of the syntax is a bare structure, the words in their constituency and order with a label at
each node, and an interpreter says which rules a node admits, by its label and the types of its
daughters. The derivations over a bare structure are then found from the types alone, and a model
of the grammar gives each its value. Two interpreters over one grammar are two theories of what a
structure can mean.

A grammar is a many-sorted signature whose operations have one or two arguments, and [a
derivation's value is the value of the term it
presents](##Interpreter.Grammar.Deriv.realize_toTerm), so what holds of signatures and their
simulations holds of grammars.

## Main definitions

* `Interpreter.Grammar`: the unary and binary rules over a type of semantic types.
* `Interpreter.Grammar.Deriv`, `Interpreter.Grammar.Model`: the derivations over typed leaves, and
  an operation for each rule over a family of domains.
* `Interpreter.Grammar.Skeleton`: a bare structure.
* `Interpreter`: the rules a node admits by its label and its daughters' types.
* `Interpreter.derivs`, `Interpreter.values`: the derivations over a bare structure, and their
  values.

## Implementation notes

Derivations have a left and a right daughter where a term has a family of arguments indexed by
position, since a whole sentence's value is checked by unfolding, and unfolding the indexed family
costs about ten times as much. A lexicon gives each word typed items and their values separately:
with the values inside the items, as `Interpreter.meanings` has them, a statement whose values are
variables is slow to check, since the search over types is repeated wherever a type is inspected.

## References

* [bumford-charlow-2026]
* [klein-sag-1985]
* [montague-1970]
-/

@[expose] public section

universe u v w

namespace Interpreter

/-- A type-driven grammar over semantic types `T`: its type shifts and its modes of combination,
each typed by what it takes and what it yields. -/
structure Grammar (T : Type u) where
  /-- The unary rules from one type to another. -/
  Unary : T → T → Type v
  /-- The binary rules combining a left and a right daughter into a mother. -/
  Binary : T → T → T → Type v

namespace Grammar

variable {T : Type u} {G : Grammar.{u, v} T} {W : T → Type w} {D : T → Type w}

/-- The signature of a grammar: its unary rules as operations of one argument and its binary
rules as operations of two. -/
def signature (G : Grammar.{u, v} T) : Signature.{u, v} T where
  Op
    | [a], b => G.Unary a b
    | [a, b], c => G.Binary a b c
    | _, _ => PEmpty

/-- A derivation of a type from leaves of the types `W` supplies. -/
inductive Deriv (G : Grammar.{u, v} T) (W : T → Type w) : T → Type (max u v w)
  /-- A leaf. -/
  | leaf {a : T} (x : W a) : Deriv G W a
  /-- A unary rule applied to a derivation. -/
  | unary {a b : T} (s : G.Unary a b) (d : Deriv G W a) : Deriv G W b
  /-- A binary rule applied to two derivations. -/
  | binary {a b c : T} (m : G.Binary a b c) (d₁ : Deriv G W a) (d₂ : Deriv G W b) : Deriv G W c

/-- A model of a grammar over the domains `D`: an operation for each rule. -/
structure Model (G : Grammar.{u, v} T) (D : T → Type w) where
  /-- The operation of a unary rule. -/
  unary {a b : T} : G.Unary a b → D a → D b
  /-- The operation of a binary rule. -/
  binary {a b c : T} : G.Binary a b c → D a → D b → D c

/-- The structure of the grammar's signature that a model is. -/
def Model.structure (M : Model G D) : Signature.Structure G.signature D where
  op {ss _} f args :=
    match ss, f, args with
    | [_], f, args => M.unary f (args ⟨0, Nat.zero_lt_one⟩)
    | [_, _], f, args => M.binary f (args ⟨0, Nat.zero_lt_two⟩) (args ⟨1, Nat.one_lt_two⟩)
    | [], f, _ => f.elim
    | _ :: _ :: _ :: _, f, _ => f.elim

namespace Deriv

/-- The value of a derivation, given the values of its leaves. -/
def eval (M : Model G D) (ρ : ∀ {a : T}, W a → D a) {a : T} : Deriv G W a → D a
  | leaf x => ρ x
  | unary s d => M.unary s (d.eval M ρ)
  | binary m d₁ d₂ => M.binary m (d₁.eval M ρ) (d₂.eval M ρ)

/-- The term of the grammar's signature that a derivation presents. -/
def toTerm {a : T} : Deriv G W a → Signature.Term G.signature W a
  | leaf x => .var x
  | unary (a := a) s d => .op (ss := [a]) s fun | ⟨0, _⟩ => d.toTerm
  | binary (a := a) (b := b) m d₁ d₂ => .op (ss := [a, b]) m fun
    | ⟨0, _⟩ => d₁.toTerm
    | ⟨1, _⟩ => d₂.toTerm

/-- A derivation's value is the value of the term it presents. -/
theorem realize_toTerm (M : Model G D) (ρ : ∀ {a : T}, W a → D a) {a : T} (d : Deriv G W a) :
    d.toTerm.realize M.structure ρ = d.eval M ρ := by
  induction d with
  | leaf x => rfl
  | unary s d ih => exact congrArg (M.unary s) ih
  | binary m d₁ d₂ ih₁ ih₂ => exact congrArg₂ (M.binary m) ih₁ ih₂

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
  {D : T → Type w}

/-- The derivations over a bare structure that an interpreter admits, given the typed items each
word may be. -/
def derivs (I : Interpreter G N) (lex : L → List (Σ a, W a)) :
    Skeleton N L → List (Σ a, Deriv G W a)
  | .leaf x => (lex x).map fun p ↦ ⟨p.1, .leaf p.2⟩
  | .unary n s => (I.derivs lex s).flatMap fun d ↦
      (I.unary n d.1).map fun p ↦ ⟨p.1, .unary p.2 d.2⟩
  | .binary n s₁ s₂ => (I.derivs lex s₁).flatMap fun d₁ ↦ (I.derivs lex s₂).flatMap fun d₂ ↦
      (I.binary n d₁.1 d₂.1).map fun p ↦ ⟨p.1, .binary p.2 d₁.2 d₂.2⟩

/-- The values of the derivations over a bare structure, for a lexicon of typed items whose
values `ρ` gives. The derivations are found from the types alone. -/
def values (I : Interpreter G N) (M : Model G D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L → List (Σ a, W a)) (s : Skeleton N L) : List (Σ a, D a) :=
  (I.derivs lex s).map fun d ↦ ⟨d.1, d.2.eval M ρ⟩

/-- The meanings of a bare structure, for a lexicon whose items are their values. -/
def meanings (I : Interpreter G N) (M : Model G D) (lex : L → List (Σ a, D a)) :
    Skeleton N L → List (Σ a, D a) :=
  I.values M id lex

theorem values_eq_of_derivs_eq (I : Interpreter G N) (M : Model G D)
    (ρ : ∀ {a : T}, W a → D a) {lex : L → List (Σ a, W a)} {s : Skeleton N L}
    {ds : List (Σ a, Deriv G W a)} (h : I.derivs lex s = ds) :
    I.values M ρ lex s = ds.map fun d ↦ ⟨d.1, d.2.eval M ρ⟩ := by
  rw [values, h]

end Interpreter
