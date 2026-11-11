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
says which rules a node admits by the types of its daughters, so that the
derivations of a syntactic object are found from the types alone. What a node makes of its
daughters' values is then an operation on lists of typed values, and a syntax folds its own
objects by these operations.

## Main definitions

* `ManySorted.Language.Deriv`: the derivations of a type over typed lexical items.
* `ManySorted.Language.LocallyFinite.unaryRules`, `binaryRules`: the rules that apply to given
  daughters, and `ManySorted.Language.motherTypes`, the types they give the mother.
* `Interpreter`: the rules a node admits by its daughters' types, and
  `Interpreter.typeDriven`, the interpreter that admits every rule that applies.
* `Interpreter.bindValues`, `Interpreter.binaryValues`: the values of the rules a node admits,
  at the values of its daughters.

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

/-- An interpreter for a language of rules: the rules a node admits. A binary node admits rules
by the types of its daughters. A binder admits them by its label and the type of its daughter,
since the type of one daughter does not say what binds it. A rule of one argument that no binder
admits, such as a type shift, is a step of a derivation that no node of a tree stands for. -/
structure Interpreter {T : Type u} (L : ManySorted.Language.{u, v} T) (N : Type v) where
  /-- The rules a binder labelled `n` over a daughter of type `a` admits. -/
  bind : N → (a : T) → List (Sigma (L.Unary a))
  /-- The binary rules a node over daughters of types `l` and `r` admits. -/
  binary : (l r : T) → List (Sigma (L.Binary l r))

namespace Interpreter

open ManySorted.Language

variable {T : Type u} {L : Language.{u, v} T} {N : Type v} {Lx : Type w} {W : T → Type w}
  {D : T → Type x}

/-- The type-driven interpreter of a language: a binary node admits every rule that applies to
the types of its daughters, and a binder admits none. -/
def typeDriven (L : Language.{u, v} T) [L.LocallyFinite] : Interpreter L N where
  bind _ _ := []
  binary := LocallyFinite.binaryRules

/-- The type-driven interpreter admits every binary rule of the language. -/
@[simp] theorem mem_binary_typeDriven [L.LocallyFinite] {l r : T}
    (m : Sigma (L.Binary l r)) : m ∈ (typeDriven L : Interpreter L N).binary l r :=
  LocallyFinite.mem_symbols m.2

/-- The values of the rules a binder labelled `n` admits, at the values of its daughter. -/
def bindValues (I : Interpreter L N) (M : L.Structure D) (n : N) (X : List (Sigma D)) :
    List (Sigma D) :=
  X.flatMap fun ⟨a, x⟩ ↦ (I.bind n a).map fun ⟨b, r⟩ ↦ ⟨b, M.funMap r x⟩

/-- The values of the binary rules a node admits, at the values of its daughters. -/
def binaryValues (I : Interpreter L N) (M : L.Structure D) (X Y : List (Sigma D)) :
    List (Sigma D) :=
  X.flatMap fun ⟨a, x⟩ ↦ Y.flatMap fun ⟨b, y⟩ ↦
    (I.binary a b).map fun ⟨c, m⟩ ↦ ⟨c, M.funMap m (x, y)⟩

variable {I : Interpreter L N} {M : L.Structure D} {n : N} {X Y : List (Sigma D)}
  {d : Sigma D}

/-- A value of a binder is the value of a rule it admits, at a value of its daughter. -/
theorem mem_bindValues :
    d ∈ I.bindValues M n X ↔ ∃ d₁ ∈ X, ∃ r ∈ I.bind n d₁.1, d = ⟨r.1, M.funMap r.2 d₁.2⟩ := by
  simp only [bindValues, List.mem_flatMap, List.mem_map, eq_comm]

/-- A value of a binary node is the value of a rule the node admits, at values of its
daughters. -/
theorem mem_binaryValues :
    d ∈ I.binaryValues M X Y ↔ ∃ d₁ ∈ X, ∃ d₂ ∈ Y, ∃ m ∈ I.binary d₁.1 d₂.1,
      d = ⟨m.1, M.funMap m.2 (d₁.2, d₂.2)⟩ := by
  simp only [binaryValues, List.mem_flatMap, List.mem_map, eq_comm]

/-- A binder that admits no rule has no value. -/
theorem bindValues_eq_nil (h : ∀ a, I.bind n a = []) : I.bindValues M n X = [] := by
  simp [bindValues, h]

/-- Where a binder admits at most one rule for a daughter, a daughter with at most one value
gives it at most one. -/
theorem length_bindValues_le_one (hu : ∀ a, (I.bind n a).length ≤ 1) (hX : X.length ≤ 1) :
    (I.bindValues M n X).length ≤ 1 := by
  match X, hX with
  | [], _ => simp [bindValues]
  | [⟨a, x⟩], _ => simpa [bindValues] using hu a

/-- Where a node admits at most one binary rule for given daughters, daughters with at most one
value each give it at most one. -/
theorem length_binaryValues_le_one (hb : ∀ a b, (I.binary a b).length ≤ 1)
    (hX : X.length ≤ 1) (hY : Y.length ≤ 1) : (I.binaryValues M X Y).length ≤ 1 := by
  match X, Y, hX, hY with
  | [], _, _, _ => simp [binaryValues]
  | [_], [], _, _ => simp [binaryValues]
  | [⟨a, x⟩], [⟨b, y⟩], _, _ => simpa [binaryValues] using hb a b

variable {D' : T → Type x} {M' : L.Structure D'} (h : ∀ a, D a → D' a)

/-- A map of domains that commutes with the unary rules commutes with the values of a
binder. -/
theorem map_bindValues
    (hh : ∀ {a b : T} (r : L.Unary a b) (x : D a), h b (M.funMap r x) = M'.funMap r (h a x)) :
    (I.bindValues M n X).map (fun d ↦ ⟨d.1, h d.1 d.2⟩) =
      I.bindValues M' n (X.map fun d ↦ ⟨d.1, h d.1 d.2⟩) := by
  simp [bindValues, List.map_flatMap, List.flatMap_map, Function.comp_def, hh]

/-- A map of domains that commutes with the binary rules commutes with the values of a binary
node. -/
theorem map_binaryValues
    (hh : ∀ {a b c : T} (m : L.Binary a b c) (x : D a) (y : D b),
      h c (M.funMap m (x, y)) = M'.funMap m (h a x, h b y)) :
    (I.binaryValues M X Y).map (fun d ↦ ⟨d.1, h d.1 d.2⟩) =
      I.binaryValues M' (X.map fun d ↦ ⟨d.1, h d.1 d.2⟩) (Y.map fun d ↦ ⟨d.1, h d.1 d.2⟩) := by
  simp [binaryValues, List.map_flatMap, List.flatMap_map, Function.comp_def, hh]

end Interpreter
