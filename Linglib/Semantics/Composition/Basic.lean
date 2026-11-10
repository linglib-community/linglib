module

public import Linglib.Core.ModelTheory.ManySorted.Simulation
public import Mathlib.Data.Nat.Notation

/-!
# Type-driven interpreters

The rules by which meanings combine are the symbols of a many-sorted language over the semantic
types: its binary symbols are the modes of combination and its unary symbols the type shifts. A
derivation is a term of the language over typed lexical items, and a structure for the language
gives each derivation a value.

A derivation is all the semantics is given, and nothing is assumed of where it comes from: a
syntactic theory says which derivations its objects have. One way is type-driven: an interpreter
reads a bare structure, the words in their constituency and order with a label at each node, and
says which rules a node admits by its label and the types of its daughters, so that the
derivations over a bare structure are found from the types alone.

## Main definitions

* `ManySorted.Language.Deriv`: the derivations of a type over typed lexical items.
* `ManySorted.Language.LocallyFinite.unaryRules`, `binaryRules`: the rules that apply to given
  daughters, and `ManySorted.Language.motherTypes`, the types they give the mother.
* `Interpreter.Skeleton`, `Interpreter.Node`: a bare structure, and the labels a constituency
  tree gives its nodes.
* `Interpreter`: the rules a node admits by its label and its daughters' types, and
  `Interpreter.typeDriven`, the interpreter that admits every rule that applies.
* `Interpreter.derivs`, `Interpreter.values`: the derivations over a bare structure, and their
  values.

## Implementation notes

`Interpreter.derivs` matches on the derivations of the daughters and does not project from them:
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
abbrev LocallyFinite.unaryRules [L.LocallyFinite] (a : T) : List (Σ b, L.Unary a b) :=
  LocallyFinite.symbols (.of a)

/-- The binary rules that apply to daughters of types `l` and `r`. -/
abbrev LocallyFinite.binaryRules [L.LocallyFinite] (l r : T) : List (Σ u, L.Binary l r u) :=
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

namespace Interpreter

/-- A bare structure over node labels `N` and leaves `L`: what a type-driven interpreter asks of
the syntax. -/
inductive Skeleton (N : Type v) (L : Type w) : Type (max v w)
  /-- A leaf. -/
  | leaf (x : L) : Skeleton N L
  /-- A unary node. -/
  | unary (n : N) (s : Skeleton N L) : Skeleton N L
  /-- A binary node. -/
  | binary (n : N) (s₁ s₂ : Skeleton N L) : Skeleton N L

/-- What the semantics reads off a node of the syntax: a plain branching node, an island, or the
index a moved phrase leaves. -/
inductive Node where
  /-- A plain node. -/
  | branch
  /-- An island for continuations. -/
  | island
  /-- The index `n` of a moved phrase. -/
  | index (n : ℕ)
  deriving DecidableEq, Repr

end Interpreter

/-- A type-driven interpreter for a language of rules: the rules a node admits, by its label and
the types of its daughters. -/
structure Interpreter {T : Type u} (L : ManySorted.Language.{u, v} T) (N : Type v) where
  /-- The unary rules a node labelled `n` over a daughter of type `a` admits. -/
  unary : N → (a : T) → List (Σ b, L.Unary a b)
  /-- The binary rules a node labelled `n` over daughters of types `l` and `r` admits. -/
  binary : N → (l r : T) → List (Σ u, L.Binary l r u)

namespace Interpreter

open ManySorted.Language

variable {T : Type u} {L : Language.{u, v} T} {N : Type v} {Lx : Type w} {W : T → Type w}
  {D : T → Type x}

/-- The type-driven interpreter of a language: a node admits every rule that applies to the
types of its daughters, whatever its label. -/
def typeDriven (L : Language.{u, v} T) [L.LocallyFinite] : Interpreter L N where
  unary _ := LocallyFinite.unaryRules
  binary _ := LocallyFinite.binaryRules

/-- The type-driven interpreter admits every binary rule of the language. -/
@[simp] theorem mem_binary_typeDriven [L.LocallyFinite] {n : N} {l r : T}
    (m : Σ u, L.Binary l r u) : m ∈ (typeDriven L : Interpreter L N).binary n l r :=
  LocallyFinite.mem_symbols m.2

/-- The derivations over a bare structure that an interpreter admits, given the typed items each
word may be. -/
def derivs (I : Interpreter L N) (lex : Lx → List (Σ a, W a)) :
    Skeleton N Lx → List (Σ a, Deriv L W a)
  | .leaf x => (lex x).map fun ⟨a, w⟩ ↦ ⟨a, .leaf w⟩
  | .unary n s => (I.derivs lex s).flatMap fun ⟨a, d⟩ ↦
      (I.unary n a).map fun ⟨b, r⟩ ↦ ⟨b, .unary r d⟩
  | .binary n s₁ s₂ => (I.derivs lex s₁).flatMap fun ⟨a, d₁⟩ ↦
      (I.derivs lex s₂).flatMap fun ⟨b, d₂⟩ ↦
        (I.binary n a b).map fun ⟨c, m⟩ ↦ ⟨c, .binary m d₁ d₂⟩

/-- Where a node admits at most one rule for given daughters and a word is at most one item, a
bare structure has at most one derivation. -/
theorem length_derivs_le_one {I : Interpreter L N} {lex : Lx → List (Σ a, W a)}
    (hu : ∀ n a, (I.unary n a).length ≤ 1) (hb : ∀ n l r, (I.binary n l r).length ≤ 1)
    (hl : ∀ x, (lex x).length ≤ 1) : ∀ s : Skeleton N Lx, (I.derivs lex s).length ≤ 1
  | .leaf x => by simpa [derivs] using hl x
  | .unary n s => by
    have ih := length_derivs_le_one hu hb hl s
    match h : I.derivs lex s, ih with
    | [], _ => simp [derivs, h]
    | [⟨a, d⟩], _ => simpa [derivs, h] using hu n a
  | .binary n s₁ s₂ => by
    have ih₁ := length_derivs_le_one hu hb hl s₁
    have ih₂ := length_derivs_le_one hu hb hl s₂
    match h₁ : I.derivs lex s₁, h₂ : I.derivs lex s₂, ih₁, ih₂ with
    | [], _, _, _ => simp [derivs, h₁]
    | [_], [], _, _ => simp [derivs, h₁, h₂]
    | [⟨a, d₁⟩], [⟨b, d₂⟩], _, _ => simpa [derivs, h₁, h₂] using hb n a b

/-- The values of the derivations over a bare structure, for a lexicon of typed items whose
values `ρ` gives. The derivations are found from the types alone. -/
def values (I : Interpreter L N) (M : L.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : Lx → List (Σ a, W a)) (s : Skeleton N Lx) : List (Σ a, D a) :=
  (I.derivs lex s).map fun ⟨a, d⟩ ↦ ⟨a, d.realize M ρ⟩

/-- The values of a leaf are the values of the items the word may be. -/
theorem values_leaf (I : Interpreter L N) (M : L.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : Lx → List (Σ a, W a)) (x : Lx) :
    I.values M ρ lex (.leaf x) = (lex x).map fun p ↦ ⟨p.1, ρ p.2⟩ := by
  simp [values, derivs, Function.comp_def]

/-- The values of a unary node are those of the rules it admits at the values of its
daughter. -/
theorem values_unary (I : Interpreter L N) (M : L.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : Lx → List (Σ a, W a)) (n : N) (s : Skeleton N Lx) :
    I.values M ρ lex (.unary n s) = (I.values M ρ lex s).flatMap fun d ↦
      (I.unary n d.1).map fun r ↦ ⟨r.1, M.funMap r.2 d.2⟩ := by
  simp [values, derivs, List.map_flatMap, List.flatMap_map, Function.comp_def]

/-- The values of a binary node are those of the rules it admits at the values of its
daughters. -/
theorem values_binary (I : Interpreter L N) (M : L.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : Lx → List (Σ a, W a)) (n : N) (s₁ s₂ : Skeleton N Lx) :
    I.values M ρ lex (.binary n s₁ s₂) = (I.values M ρ lex s₁).flatMap fun d₁ ↦
      (I.values M ρ lex s₂).flatMap fun d₂ ↦
        (I.binary n d₁.1 d₂.1).map fun m ↦ ⟨m.1, M.funMap m.2 (d₁.2, d₂.2)⟩ := by
  simp [values, derivs, List.map_flatMap, List.flatMap_map, Function.comp_def]

/-- A value of a binary node is the value of a rule the node admits, at values of its
daughters. -/
theorem mem_values_binary {I : Interpreter L N} {M : L.Structure D}
    {ρ : ∀ {a : T}, W a → D a} {lex : Lx → List (Σ a, W a)} {n : N} {s₁ s₂ : Skeleton N Lx}
    {d : Σ a, D a} :
    d ∈ I.values M ρ lex (.binary n s₁ s₂) ↔
      ∃ d₁ ∈ I.values M ρ lex s₁, ∃ d₂ ∈ I.values M ρ lex s₂,
      ∃ m ∈ I.binary n d₁.1 d₂.1, d = ⟨m.1, M.funMap m.2 (d₁.2, d₂.2)⟩ := by
  simp only [values, derivs, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨_, ⟨⟨a, e₁⟩, h₁, ⟨b, e₂⟩, h₂, ⟨u, m⟩, hm, rfl⟩, rfl⟩
    exact ⟨_, ⟨⟨a, e₁⟩, h₁, rfl⟩, _, ⟨⟨b, e₂⟩, h₂, rfl⟩, ⟨u, m⟩, hm, rfl⟩
  · rintro ⟨_, ⟨⟨a, e₁⟩, h₁, rfl⟩, _, ⟨⟨b, e₂⟩, h₂, rfl⟩, ⟨u, m⟩, hm, rfl⟩
    exact ⟨_, ⟨⟨a, e₁⟩, h₁, ⟨b, e₂⟩, h₂, ⟨u, m⟩, hm, rfl⟩, rfl⟩

end Interpreter
