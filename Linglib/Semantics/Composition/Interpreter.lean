module

public import Linglib.Semantics.Composition.Basic

/-!
# Type-driven interpreters

One way a syntactic theory says which derivations its objects have is type-driven: an interpreter
says which rules a node admits by the types of its daughters, so that the derivations of a
syntactic object are found from the types alone. What a node makes of its daughters' values is
then an operation on lists of typed values, and a syntax folds its own objects by these
operations.

## Main definitions

* `Interpreter`: the rules a node admits, and `Interpreter.typeDriven`, the interpreter that
  admits every binary rule that applies.
* `Interpreter.bindValues`, `Interpreter.binaryValues`: the values of the rules a node admits,
  at the values of its daughters.

## References

* [klein-sag-1985]
* [heim-kratzer-1998]
-/

@[expose] public section

universe u v w x

open ManySorted

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
