module

public import Linglib.Semantics.Composition.Interpreter.Constituency
public import Linglib.Semantics.Composition.Interpreter.PredicateAbstraction
public import Linglib.Semantics.Composition.Interpreter.Rules

/-!
# Type-driven interpretation of a tree

The rules by which meanings combine are the symbols of a many-sorted language over the semantic
types: Functional Application and Predicate Modification are languages, and a grammar with both
is their sum. A constituency tree is interpreted by searching, at each node, for the symbols that
apply to the types of its daughters, with abstraction over an index at a binder. The meanings
of a tree are functions of an assignment, and [the meanings of a node come from those of its
daughters](##PhraseStructure.Tree.interpret_phrase_binary).

## Main definitions

* `Interpreter.application`, `Interpreter.predicateModification`: the rule sets as languages.
* `PhraseStructure.Tree.derive`: the derivations of a tree over a language with abstraction.
* `PhraseStructure.Tree.interpret`: their values, relative to an assignment.

## References

* [heim-kratzer-1998]
* [klein-sag-1985]
-/

@[expose] public section

open MSFirstOrder

namespace MSFirstOrder.Language

universe u v

variable {S : Type u} {L : Language.{u, v} S} {N Lx : Type} {W : S → Type}

/-- The derivations over a bare structure, given the symbols each node label admits for
arguments of a shape and the items each leaf may be. -/
def derivs (admits : N → (σ : Signature S) → List (Σ t, L.Functions σ t))
    (lex : Lx → List (Σ a, W a)) : Interpreter.Grammar.Skeleton N Lx → List (Σ a, L.Term W (.of a))
  | .leaf x => (lex x).map fun ⟨a, w⟩ ↦ ⟨a, .var w⟩
  | .unary n s => (derivs admits lex s).flatMap fun ⟨a, d⟩ ↦
      (admits n (.of a)).map fun ⟨b, f⟩ ↦ ⟨b, .func f d⟩
  | .binary n s₁ s₂ => (derivs admits lex s₁).flatMap fun ⟨a, d₁⟩ ↦
      (derivs admits lex s₂).flatMap fun ⟨b, d₂⟩ ↦
        (admits n (.prod (.of a) (.of b))).map fun ⟨c, f⟩ ↦ ⟨c, .func f (.prod d₁ d₂)⟩

end MSFirstOrder.Language

namespace Interpreter

variable {B : Type}

/-- Functional Application, as a language over the types. -/
@[reducible] def application : Language (Ty B) := .mk₂ (fun _ _ ↦ PEmpty) Application

/-- Predicate Modification, as a language over the types. -/
@[reducible] def predicateModification : Language (Ty B) :=
  .mk₂ (fun _ _ ↦ PEmpty) PredicateModification

/-- Abstraction over indices typed by `Γ`, as a language over the types. -/
@[reducible] def abstraction (Γ : ℕ → Ty B) : Language (Ty B) :=
  .mk₂ (PredicateAbstraction Γ) fun _ _ _ ↦ PEmpty

instance (D : B → Type) : (application (B := B)).Structure (Ty.Dom D) :=
  .mk₂ nofun (Application.eval D)

instance (D : B → Type) : (predicateModification (B := B)).Structure (Ty.Dom D) :=
  .mk₂ nofun (PredicateModification.eval D)

instance {S : Type} {L L' : Language S} {D : S → Type} [M : L.Structure D]
    [M' : L'.Structure D] : (L.sum L').Structure D := M.sum M'

instance [DecidableEq B] : (application (B := B)).LocallyFinite :=
  .mk₂ (fun _ ↦ []) (Grammar.LocallyFinite.binaryRules (G := Grammar.application)) nofun
    (Grammar.LocallyFinite.mem_binaryRules (G := Grammar.application))

instance [DecidableEq B] : (predicateModification (B := B)).LocallyFinite :=
  .mk₂ (fun _ ↦ []) (Grammar.LocallyFinite.binaryRules (G := Grammar.predicateModification))
    nofun (Grammar.LocallyFinite.mem_binaryRules (G := Grammar.predicateModification))

@[simp] theorem symbols_application [DecidableEq B] (l r : Ty B) :
    Language.LocallyFinite.symbols (L := application) (.prod (.of l) (.of r)) =
      Grammar.LocallyFinite.binaryRules (G := Grammar.application) l r := rfl

@[simp] theorem symbols_predicateModification [DecidableEq B] (l r : Ty B) :
    Language.LocallyFinite.symbols (L := predicateModification) (.prod (.of l) (.of r)) =
      Grammar.LocallyFinite.binaryRules (G := Grammar.predicateModification) l r := rfl

variable {Γ : ℕ → Ty B} {A : Type} {D : Ty B → Type}

/-- Abstraction relative to assignments: the abstract over an index is the function of the
value the assignment is modified to give it. -/
@[instance_reducible] def abstraction.structure (E : Assignments A D Γ) :
    (abstraction Γ).Structure fun a ↦ A → D a :=
  .mk₂ (fun | .index n _, body => fun g ↦ E.lam fun v ↦ body (E.set g n v)) nofun

/-- What a node admits in a language with abstraction: a binder, abstraction over its index;
any other node, the symbols of the language that apply. -/
def abstraction.admits (L : Language (Ty B)) [L.LocallyFinite] (Γ : ℕ → Ty B) :
    Node → (σ : Signature (Ty B)) → List (Σ u, (L.sum (abstraction Γ)).Functions σ u)
  | .index n, .of a => [⟨Γ n ⇒ a, Language.Sum.inr (PredicateAbstraction.index n a)⟩]
  | .index _, _ => []
  | _, σ => (Language.LocallyFinite.symbols (L := L) σ).map fun p ↦ ⟨p.1, .inl p.2⟩

end Interpreter

namespace PhraseStructure.Tree

open Interpreter

variable {C Lx : Type} {B : Type} {D : B → Type} {W : Ty B → Type}

/-- The derivations of a tree over a language with abstraction over indices typed by `Γ`: at
each node, the symbols that apply to the types of its daughters. -/
def derive (L : Language (Ty B)) [L.LocallyFinite] (Γ : ℕ → Ty B)
    (lex : Lx ⊕ ℕ → List (Σ a, W a)) (t : Tree C Lx) :
    List (Σ a, (L.sum (abstraction Γ)).Term W (.of a)) :=
  match t.skeleton fun _ ↦ false with
  | some s => Language.derivs (abstraction.admits L Γ) lex s
  | none => []

/-- The meanings of a tree over a language with abstraction over indices typed by `Γ`, relative
to an assignment of values to the indices: the values of its derivations. -/
def interpret (L : Language (Ty B)) (D : B → Type) [L.LocallyFinite]
    [M : L.Structure (Ty.Dom D)] (Γ : ℕ → Ty B)
    (ρ : ∀ {a : Ty B}, W a → (∀ n, (Γ n).Dom D) → a.Dom D)
    (lex : Lx ⊕ ℕ → List (Σ a, W a)) (t : Tree C Lx) :
    List (Σ a : Ty B, (∀ n, (Γ n).Dom D) → a.Dom D) :=
  (t.derive L Γ lex).map fun ⟨a, d⟩ ↦
    ⟨a, d.realize ((M.pi _).sum (abstraction.structure (Assignments.total D Γ))) ρ⟩

section Compositional

variable (L : Language (Ty B)) [L.LocallyFinite] [M : L.Structure (Ty.Dom D)] (Γ : ℕ → Ty B)
  (ρ : ∀ {a : Ty B}, W a → (∀ n, (Γ n).Dom D) → a.Dom D) (lex : Lx ⊕ ℕ → List (Σ a, W a))

@[simp] theorem derive_terminal (c : C) (w : Lx) :
    (terminal c w).derive L Γ lex = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, .var x⟩ := rfl

@[simp] theorem derive_trace (n : ℕ) (c : C) :
    (trace n c : Tree C Lx).derive L Γ lex =
      (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, .var x⟩ := rfl

@[simp] theorem derive_bind (n : ℕ) (c : C) (t : Tree C Lx) :
    (bind n c t).derive L Γ lex = (t.derive L Γ lex).map fun ⟨a, d⟩ ↦
      ⟨Γ n ⇒ a, .func (L := L.sum (abstraction Γ))
        (Language.Sum.inr (PredicateAbstraction.index n a)) d⟩ := by
  simp only [derive, skeleton]
  cases skeleton (fun _ ↦ false) t <;>
    simp [Language.derivs, abstraction.admits, List.map_eq_flatMap]

@[simp] theorem derive_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C Lx) :
    (phrase c k [t₁, t₂]).derive L Γ lex = (t₁.derive L Γ lex).flatMap fun ⟨a, d₁⟩ ↦
      (t₂.derive L Γ lex).flatMap fun ⟨b, d₂⟩ ↦
        (Language.LocallyFinite.symbols (L := L) (.prod (.of a) (.of b))).map fun ⟨u, f⟩ ↦
          ⟨u, .func (L := L.sum (abstraction Γ)) (Language.Sum.inl f) (.prod d₁ d₂)⟩ := by
  simp only [derive, skeleton]
  cases skeleton (fun _ ↦ false) t₁ <;> cases skeleton (fun _ ↦ false) t₂ <;>
    simp [Language.derivs, abstraction.admits, Function.comp_def]

@[simp] theorem derive_phrase_unary (c : C) (k : PhraseKind) (t : Tree C Lx) :
    (phrase c k [t]).derive L Γ lex = t.derive L Γ lex := by
  simp only [derive, skeleton]

/-- A word's meanings are the values of the items it may be. -/
@[simp] theorem interpret_terminal (c : C) (w : Lx) :
    (terminal c w).interpret L D Γ ρ lex = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [interpret, Language.Term.realize, Function.comp_def]

/-- A trace's meanings are the values of the items its index may be. -/
@[simp] theorem interpret_trace (n : ℕ) (c : C) :
    (trace n c : Tree C Lx).interpret L D Γ ρ lex = (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [interpret, Language.Term.realize, Function.comp_def]

/-- A binder's meanings are the functions of the value its index is given. -/
@[simp] theorem interpret_bind (n : ℕ) (c : C) (t : Tree C Lx) :
    (bind n c t).interpret L D Γ ρ lex = (t.interpret L D Γ ρ lex).map fun ⟨a, x⟩ ↦
      ⟨Γ n ⇒ a, fun g v ↦ x (Function.update g n v)⟩ := by
  simp [interpret, Language.Term.realize, Function.comp_def, abstraction.structure,
    Assignments.total]

/-- The meanings of a binary node are those of the symbols that apply to the types of its
daughters, at the meanings of its daughters. -/
@[simp] theorem interpret_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C Lx) :
    (phrase c k [t₁, t₂]).interpret L D Γ ρ lex = (t₁.interpret L D Γ ρ lex).flatMap fun ⟨a, x⟩ ↦
      (t₂.interpret L D Γ ρ lex).flatMap fun ⟨b, y⟩ ↦
        (Language.LocallyFinite.symbols (L := L) (.prod (.of a) (.of b))).map fun ⟨u, f⟩ ↦
          ⟨u, fun g ↦ M.funMap f (x g, y g)⟩ := by
  simp [interpret, Language.Term.realize, List.map_flatMap, List.flatMap_map, Function.comp_def,
    Signature.Interpret.app]

/-- A non-branching node has the meanings of its daughter. -/
@[simp] theorem interpret_phrase_unary (c : C) (k : PhraseKind) (t : Tree C Lx) :
    (phrase c k [t]).interpret L D Γ ρ lex = t.interpret L D Γ ρ lex := by
  simp [interpret]

end Compositional

end PhraseStructure.Tree
