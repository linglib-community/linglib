module

public import Linglib.Core.ModelTheory.ManySorted.Simulation
public import Mathlib.Data.Nat.Notation

/-!
# Rules and derivations

The rules by which meanings combine are the symbols of a many-sorted language over the semantic
types: its binary symbols are the modes of combination and its unary symbols the type shifts. A
derivation is a term of the language over typed lexical items, and a structure for the language
gives each derivation a value.

A derivation is all the semantics is given, and nothing is assumed of where it comes from: a
syntactic theory says which derivations its objects have.

## Main definitions

* `ManySorted.Language.Deriv`: the derivations of a type over typed lexical items.
* `ManySorted.Language.LocallyFinite.unaryRules`, `binaryRules`: the rules that apply to given
  daughters, and `ManySorted.Language.motherTypes`, the types they give the mother.

## Implementation notes

The node operations match on the values of the daughters and do not project from them:
a projection is unfolded again wherever it is inspected, which made checking a sentence's value
some fifty times dearer. A lexicon gives each word typed items and their values separately. With
the values inside the items, a statement over a model with variables in it is still slow to
check. A language has more than one structure on the same domains, values at an index and values
that depend on it, so a structure is an argument and not an instance.

## References

* [bumford-charlow-2026]
* [klein-sag-1985]
* [montague-1970]
-/

@[expose] public section

universe u v w x

open ManySorted

namespace ManySorted.Language

variable {T : Type u} {L : Language.{u, v} T} {W : T → Type w} {D : T → Type x}

/-- The unary rules that apply to a daughter of type `a`. -/
abbrev LocallyFinite.unaryRules [L.LocallyFinite] (a : T) : List (Sigma (L.Unary a)) :=
  LocallyFinite.symbols (.of a)

/-- The binary rules that apply to daughters of types `l` and `r`. -/
abbrev LocallyFinite.binaryRules [L.LocallyFinite] (l r : T) : List (Sigma (L.Binary l r)) :=
  LocallyFinite.symbols (.prod (.of l) (.of r))

/-- The types of the mothers that the rules of a language give two daughters. -/
def motherTypes (L : Language.{u, v} T) [L.LocallyFinite] (l r : T) : List T :=
  (LocallyFinite.binaryRules (L := L) l r).map (·.1)

/-- A derivation of a type from lexical items of the types `W` supplies. -/
abbrev Deriv (L : Language.{u, v} T) (W : T → Type w) (a : T) : Type (max u v w) :=
  L.Term W (.of a)

namespace Deriv

/-- A lexical item. -/
abbrev leaf {a : T} (x : W a) : Deriv L W a := .var x

/-- A unary rule applied to a derivation. -/
abbrev unary {a b : T} (s : L.Unary a b) (d : Deriv L W a) : Deriv L W b := .func s d

/-- A binary rule applied to two derivations. -/
abbrev binary {a b c : T} (m : L.Binary a b c) (d₁ : Deriv L W a) (d₂ : Deriv L W b) :
    Deriv L W c :=
  .func m (.prod d₁ d₂)

variable (M : L.Structure D) (ρ : ∀ {a : T}, W a → D a)

@[simp] theorem realize_leaf {a : T} (x : W a) : (leaf x : Deriv L W a).realize M ρ = ρ x := rfl

@[simp] theorem realize_unary {a b : T} (s : L.Unary a b) (d : Deriv L W a) :
    (unary s d).realize M ρ = M.funMap s (d.realize M ρ) := rfl

@[simp] theorem realize_binary {a b c : T} (m : L.Binary a b c) (d₁ : Deriv L W a)
    (d₂ : Deriv L W b) :
    (binary m d₁ d₂).realize M ρ = M.funMap m (d₁.realize M ρ, d₂.realize M ρ) := rfl

end Deriv

end ManySorted.Language
