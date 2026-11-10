module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Composition.Interpreter.Basic

/-!
# The bare structure of a constituency tree

A constituency tree gives the semantics its words in their constituency and order, the indices of
its moved phrases, and which of its nodes are islands. A terminal is a leaf, a trace a leaf that
is its index, a binder the index over its body, a non-branching node its daughter, and a binary
node a plain node or, at a category that is an island, an island.

## Main definitions

* `PhraseStructure.Tree.skeleton`: the bare structure of a tree.
* `PhraseStructure.Tree.derivs`, `PhraseStructure.Tree.values`: the derivations of a tree that an
  interpreter admits, and their values, with [the values of a node from those of its
  daughters](##PhraseStructure.Tree.values_phrase_binary).

## References

* [bumford-charlow-2026]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace PhraseStructure.Tree

open ManySorted ManySorted.Language Interpreter

variable {C L : Type}

/-- The bare structure of a tree, with the categories `island` holds of as islands: its leaves are
words and trace indices, and it has none if a phrase has no daughter or more than two. -/
def skeleton (island : C → Bool) : Tree C L → Option (Skeleton Node (L ⊕ ℕ))
  | .terminal _ w => some (.leaf (.inl w))
  | .trace n _ => some (.leaf (.inr n))
  | .bind n _ body => (skeleton island body).map (.unary (.index n))
  | .phrase _ _ (t :: []) => skeleton island t
  | .phrase c _ (t₁ :: t₂ :: []) => do
    let s₁ ← skeleton island t₁
    let s₂ ← skeleton island t₂
    pure (.binary (if island c then .island else .branch) s₁ s₂)
  | _ => none

variable {T : Type} {G : Language T} {W D : T → Type}

/-- The derivations of a tree that an interpreter admits, given the typed items a word or a
trace may be. -/
def derivs (I : Interpreter G Node) (lex : L ⊕ ℕ → List (Σ a, W a)) (t : Tree C L)
    (island : C → Bool := fun _ ↦ false) : List (Σ a, Deriv G W a) :=
  match t.skeleton island with
  | some s => I.derivs lex s
  | none => []

/-- The values of the derivations of a tree, for a lexicon of typed items whose values `ρ`
gives. -/
def values (I : Interpreter G Node) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → List (Σ a, W a)) (t : Tree C L) (island : C → Bool := fun _ ↦ false) :
    List (Σ a, D a) :=
  (t.derivs I lex island).map fun ⟨a, d⟩ ↦ ⟨a, d.realize M ρ⟩

/-! ### Values of a node from the values of its daughters -/

section Compositional

variable (I : Interpreter G Node) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
  (lex : L ⊕ ℕ → List (Σ a, W a)) (island : C → Bool)

theorem derivs_terminal (c : C) (w : L) :
    (terminal c w).derivs I lex island = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, .leaf x⟩ := rfl

theorem derivs_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).derivs I lex island =
      (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, .leaf x⟩ := rfl

theorem derivs_bind (n : ℕ) (c : C) (t : Tree C L) :
    (bind n c t).derivs I lex island = (t.derivs I lex island).flatMap fun ⟨a, d⟩ ↦
      (I.unary (.index n) a).map fun ⟨b, r⟩ ↦ ⟨b, .unary r d⟩ := by
  simp only [derivs, skeleton]
  cases skeleton island t <;> rfl

theorem derivs_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    (phrase c k [t₁, t₂]).derivs I lex island = (t₁.derivs I lex island).flatMap fun ⟨a, d₁⟩ ↦
      (t₂.derivs I lex island).flatMap fun ⟨b, d₂⟩ ↦
        (I.binary (if island c then .island else .branch) a b).map fun ⟨u, m⟩ ↦
          ⟨u, .binary m d₁ d₂⟩ := by
  simp only [derivs, skeleton]
  cases skeleton island t₁ <;> cases skeleton island t₂ <;> simp [Interpreter.derivs]

theorem derivs_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    (phrase c k [t]).derivs I lex island = t.derivs I lex island := by
  simp only [derivs, skeleton]

/-- A word's values are the values of the items it may be. -/
@[simp] theorem values_terminal (c : C) (w : L) :
    (terminal c w).values I M ρ lex island = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [values, derivs_terminal, Function.comp_def]

/-- A trace's values are the values of the items its index may be. -/
@[simp] theorem values_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).values I M ρ lex island =
      (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [values, derivs_trace, Function.comp_def]

/-- The values of a binder over an index are those of the unary rules its index admits, at the
values of its body. -/
@[simp] theorem values_bind (n : ℕ) (c : C) (t : Tree C L) :
    (bind n c t).values I M ρ lex island = (t.values I M ρ lex island).flatMap fun ⟨a, x⟩ ↦
      (I.unary (.index n) a).map fun ⟨b, r⟩ ↦ ⟨b, M.funMap r x⟩ := by
  simp [values, derivs_bind, List.map_flatMap, List.flatMap_map, Function.comp_def]

/-- The values of a binary node are those of the rules the node admits for its daughters'
types, at the values of its daughters. -/
@[simp] theorem values_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    (phrase c k [t₁, t₂]).values I M ρ lex island =
      (t₁.values I M ρ lex island).flatMap fun ⟨a, x⟩ ↦
        (t₂.values I M ρ lex island).flatMap fun ⟨b, y⟩ ↦
          (I.binary (if island c then .island else .branch) a b).map fun ⟨u, m⟩ ↦
            ⟨u, M.funMap m (x, y)⟩ := by
  simp [values, derivs_phrase_binary, List.map_flatMap, List.flatMap_map, Function.comp_def]

/-- A non-branching node has the values of its daughter. -/
@[simp] theorem values_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    (phrase c k [t]).values I M ρ lex island = t.values I M ρ lex island := by
  simp [values, derivs_phrase_unary]

end Compositional

end PhraseStructure.Tree
