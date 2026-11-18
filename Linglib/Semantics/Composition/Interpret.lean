module

public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.PredicateAbstraction
public import Linglib.Semantics.Composition.Rules

/-!
# Type-driven interpretation of a tree

Heim and Kratzer's interpretation of a tree, for any language of rules: at each node the rules
that apply to the types of its daughters, abstraction over its index at a binder, and at a trace
the value the assignment gives its index. A lexicon says what typed items each word may be, and
the meanings of a tree are functions of an assignment. [The meanings of a node come from those
of its daughters](##PhraseStructure.Tree.interpret_phrase_binary), and [a binder's are the
functions of the value its index is given](##PhraseStructure.Tree.interpret_bind).

## Main definitions

* `Interpreter.withAbstraction`: an interpreter that admits abstraction at an index.
* `PhraseStructure.Tree.derive`: the derivations of a tree over a language of rules with
  abstraction, its traces variables.
* `PhraseStructure.Tree.interpret`: their values, relative to an assignment.

## References

* [heim-kratzer-1998]
* [klein-sag-1985]
-/

@[expose] public section

namespace Interpreter

variable {B : Type} {L : ManySorted.Language.{0, 0} (Ty B)}

/-- An interpreter with predicate abstraction: a binder node admits abstraction over its index,
and a binary node admits what the interpreter admits. -/
def withAbstraction (I : Interpreter L ℕ) (Γ : ℕ → Ty B) :
    Interpreter (L.withAbstraction Γ) ℕ where
  bind n b := [⟨Γ n ⇒ b, ManySorted.Language.Sum.inr (PredicateAbstraction.index n b)⟩]
  binary l r := (I.binary l r).map fun ⟨u, m⟩ ↦ ⟨u, .inl m⟩

end Interpreter

open ManySorted Interpreter

namespace Interpreter

variable {B : Type}

/-- The leaves of a derivation of a tree: a typed item of a word, or a trace, of the type of its
index. -/
inductive Leaf (W : Ty B → Type) (Γ : ℕ → Ty B) : Ty B → Type
  /-- An item of a word. -/
  | word {a : Ty B} (x : W a) : Leaf W Γ a
  /-- A trace with index `n`. -/
  | trace (n : ℕ) : Leaf W Γ (Γ n)

variable {W : Ty B → Type} {Γ : ℕ → Ty B} {D : B → Type}

/-- The value of a leaf relative to an assignment: an item's value, and for a trace the value
the assignment gives its index. -/
def Leaf.val (ρ : ∀ {a : Ty B}, W a → (∀ n, (Γ n).Dom D) → a.Dom D) :
    {a : Ty B} → Leaf W Γ a → (∀ n, (Γ n).Dom D) → a.Dom D
  | _, .word x => ρ x
  | _, .trace n => fun g ↦ g n

/-- The leaves a word or a trace may be. -/
def Leaf.lex {Lx : Type} (lex : Lx → List (Sigma W)) (Γ : ℕ → Ty B) :
    Lx ⊕ ℕ → List (Σ a, Leaf W Γ a)
  | .inl w => (lex w).map fun ⟨a, x⟩ ↦ ⟨a, .word x⟩
  | .inr n => [⟨Γ n, .trace n⟩]

end Interpreter

namespace PhraseStructure.Tree

variable {C Lx : Type} {B : Type} {D : B → Type} {W : Ty B → Type}

/-- The derivations of a tree over a language of rules with abstraction over indices typed by
`Γ`: at each node the rules that apply to the types of its daughters, and at a binder
abstraction over its index. -/
def derive (L : Language.{0, 0} (Ty B)) [L.LocallyFinite] (Γ : ℕ → Ty B)
    (lex : Lx → List (Sigma W)) (t : Tree C Lx) :
    List (Σ a, (L.withAbstraction Γ).Deriv (Leaf W Γ) a) :=
  t.derivs ((typeDriven L).withAbstraction Γ) (Leaf.lex lex Γ)

/-- The meanings of a tree over a language of rules, at domains `D`, with abstraction over
indices typed by `Γ`, relative to an assignment of values to the indices: the values of its
derivations, an item's value being what `ρ` gives it. -/
def interpret (L : Language.{0, 0} (Ty B)) (D : B → Type) [L.LocallyFinite]
    [M : L.Structure (Ty.Dom D)] (Γ : ℕ → Ty B)
    (ρ : ∀ {a : Ty B}, W a → (∀ n, (Γ n).Dom D) → a.Dom D) (lex : Lx → List (Sigma W))
    (t : Tree C Lx) : List (Σ a : Ty B, (∀ n, (Γ n).Dom D) → a.Dom D) :=
  t.values ((typeDriven L).withAbstraction Γ)
    (Language.withAbstraction.structure (Assignments.total D Γ)) (Leaf.val ρ) (Leaf.lex lex Γ)

section Compositional

variable (L : Language.{0, 0} (Ty B)) [L.LocallyFinite] [M : L.Structure (Ty.Dom D)]
  (Γ : ℕ → Ty B) (ρ : ∀ {a : Ty B}, W a → (∀ n, (Γ n).Dom D) → a.Dom D)
  (lex : Lx → List (Sigma W))

theorem interpret_eq_map (t : Tree C Lx) :
    t.interpret L D Γ ρ lex = (t.derive L Γ lex).map fun ⟨a, d⟩ ↦
      ⟨a, d.realize (Language.withAbstraction.structure (Assignments.total D Γ))
        (Leaf.val ρ)⟩ := rfl

@[simp] theorem derive_terminal (c : C) (w : Lx) :
    (terminal c w).derive L Γ lex = (lex w).map fun ⟨a, x⟩ ↦ ⟨a, .leaf (.word x)⟩ := by
  simp [derive, derivs_terminal, Leaf.lex]

@[simp] theorem derive_trace (n : ℕ) (c : C) :
    (trace n c : Tree C Lx).derive L Γ lex = [⟨Γ n, .leaf (.trace n)⟩] := by
  simp [derive, derivs_trace, Leaf.lex]

@[simp] theorem derive_bind (n : ℕ) (c : C) (t : Tree C Lx) :
    (bind n c t).derive L Γ lex = (t.derive L Γ lex).map fun ⟨a, d⟩ ↦
      ⟨Γ n ⇒ a, .unary (Language.Sum.inr (PredicateAbstraction.index n a)) d⟩ := by
  simp [derive, derivs_bind, Interpreter.withAbstraction, typeDriven, List.map_eq_flatMap]

@[simp] theorem derive_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C Lx) :
    (phrase c k [t₁, t₂]).derive L Γ lex = (t₁.derive L Γ lex).flatMap fun ⟨a, d₁⟩ ↦
      (t₂.derive L Γ lex).flatMap fun ⟨b, d₂⟩ ↦
        (Language.LocallyFinite.binaryRules (L := L) a b).map fun ⟨u, f⟩ ↦
          ⟨u, .binary (Language.Sum.inl f) d₁ d₂⟩ := by
  simp [derive, derivs_phrase_binary, Interpreter.withAbstraction, typeDriven,
    Function.comp_def]

@[simp] theorem derive_phrase_unary (c : C) (k : PhraseKind) (t : Tree C Lx) :
    (phrase c k [t]).derive L Γ lex = t.derive L Γ lex := by
  simp [derive, derivs_phrase_unary]

/-- A word's meanings are the values of the items it may be. -/
@[simp] theorem interpret_terminal (c : C) (w : Lx) :
    (terminal c w).interpret L D Γ ρ lex = (lex w).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [interpret, Leaf.lex, Leaf.val, Function.comp_def]

/-- A trace means the value the assignment gives its index. -/
@[simp] theorem interpret_trace (n : ℕ) (c : C) :
    (trace n c : Tree C Lx).interpret L D Γ ρ lex = [⟨Γ n, fun g ↦ g n⟩] := by
  simp [interpret, Leaf.lex, Leaf.val]

/-- A binder's meanings are the functions of the value its index is given. -/
@[simp] theorem interpret_bind (n : ℕ) (c : C) (t : Tree C Lx) :
    (bind n c t).interpret L D Γ ρ lex = (t.interpret L D Γ ρ lex).map fun ⟨a, x⟩ ↦
      ⟨Γ n ⇒ a, fun g v ↦ x (Function.update g n v)⟩ := by
  simp [interpret, Interpreter.withAbstraction, typeDriven, Language.withAbstraction.structure,
    Assignments.total, List.map_eq_flatMap]

/-- The meanings of a binary node are those of the rules that apply to the types of its
daughters, at the meanings of its daughters. -/
@[simp] theorem interpret_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C Lx) :
    (phrase c k [t₁, t₂]).interpret L D Γ ρ lex =
      (t₁.interpret L D Γ ρ lex).flatMap fun ⟨a, x⟩ ↦
        (t₂.interpret L D Γ ρ lex).flatMap fun ⟨b, y⟩ ↦
          (Language.LocallyFinite.binaryRules (L := L) a b).map fun ⟨u, f⟩ ↦
            ⟨u, fun g ↦ M.funMap f (x g, y g)⟩ := by
  simp [interpret, Interpreter.withAbstraction, typeDriven, Language.withAbstraction.structure,
    Function.comp_def]

/-- A non-branching node has the meanings of its daughter. -/
@[simp] theorem interpret_phrase_unary (c : C) (k : PhraseKind) (t : Tree C Lx) :
    (phrase c k [t]).interpret L D Γ ρ lex = t.interpret L D Γ ρ lex := by
  simp [interpret]

end Compositional

end PhraseStructure.Tree
