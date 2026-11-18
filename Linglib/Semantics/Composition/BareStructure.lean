module

public import Linglib.Semantics.Composition.Basic
public import Linglib.Syntax.Skeleton

/-!
# Type-driven interpretation of a bare structure

A bare structure is interpreted as a constituency tree is, by what each node makes of the values
of its daughters: a leaf is the items its word may be, a unary node admits the rules of its
label, and a binary node the rules that apply to the types of its daughters. A syntax whose
objects are not trees, such as a complex head, gives its objects a bare structure and is
interpreted through it.

## Main definitions

* `Interpreter.derivs`: the derivations over a bare structure that an interpreter admits.
* `Interpreter.values`: their values.

## References

* [klein-sag-1985]
* [bumford-charlow-2026]
-/

@[expose] public section

universe u v w x

open ManySorted ManySorted.Language

namespace Interpreter

variable {T : Type u} {L : Language.{u, v} T} {N : Type v} {Lx : Type w} {W : T → Type w}
  {D : T → Type x}

/-- The derivations over a bare structure that an interpreter admits, given the typed items
each word may be. -/
def derivs (I : Interpreter L N) (lex : Lx → List (Sigma W)) :
    Skeleton N Lx → List (Sigma (Deriv L W))
  | .leaf x => (lex x).map fun ⟨a, w⟩ ↦ ⟨a, .leaf w⟩
  | .unary n s => I.unaryValues (Term.structure L W) n (I.derivs lex s)
  | .binary _ s₁ s₂ => I.binaryValues (Term.structure L W) (I.derivs lex s₁) (I.derivs lex s₂)

/-- The values of the derivations over a bare structure, for a lexicon of typed items whose
values `ρ` gives. -/
def values (I : Interpreter L N) (M : L.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : Lx → List (Sigma W)) (s : Skeleton N Lx) : List (Sigma D) :=
  (I.derivs lex s).map fun ⟨a, d⟩ ↦ ⟨a, d.realize M ρ⟩

end Interpreter
