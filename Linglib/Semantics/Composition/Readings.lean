module

public import Linglib.Semantics.Composition.Constituency
public import Mathlib.Data.Set.Image

/-!
# Readings over a lexicon of sets

A word may have infinitely many items, as a coordinator has one at every conjoinable type. What an
interpreter gives a tree is then a set, the readings of the tree, by the same fold as its values
over a lexicon of lists, and [the values are exactly the
readings](##PhraseStructure.Tree.mem_values_iff).

## Main definitions

* `Interpreter.unaryReadings`, `Interpreter.binaryReadings`: the readings of a node from the
  readings of its daughters.
* `PhraseStructure.Tree.readings`: the readings of a tree.

## References

* [partee-rooth-1983]
-/

@[expose] public section

universe u v w x

namespace Interpreter

open ManySorted ManySorted.Language

variable {T : Type u} {G : Language.{u, v} T} {N : Type v} {D : T → Type x}

/-- The readings of a unary node labelled `n` from those of its daughter: the values of the
rules the node admits. -/
def unaryReadings (I : Interpreter G N) (M : G.Structure D) (n : N) (X : Set (Sigma D)) :
    Set (Sigma D) :=
  {d | ∃ d₁ ∈ X, ∃ r ∈ I.unary n d₁.1, d = ⟨r.1, M.funMap r.2 d₁.2⟩}

/-- The readings of a binary node from those of its daughters: the values of the rules the node
admits. -/
def binaryReadings (I : Interpreter G N) (M : G.Structure D) (X Y : Set (Sigma D)) :
    Set (Sigma D) :=
  {d | ∃ d₁ ∈ X, ∃ d₂ ∈ Y, ∃ m ∈ I.binary d₁.1 d₂.1, d = ⟨m.1, M.funMap m.2 (d₁.2, d₂.2)⟩}

end Interpreter

namespace PhraseStructure.Tree

open ManySorted ManySorted.Language Interpreter

variable {C L : Type} {T : Type} {G : Language T} {W D : T → Type}

/-- What a label makes of the readings of its daughters, as `nodeValues` does of their values. -/
def nodeReadings (I : Interpreter G ℕ) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → Set (Sigma W)) :
    Label C L → List (Set (Sigma D)) → Set (Sigma D)
  | .terminal _ w, [] => (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex (.inl w)
  | .trace n _, [] => (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex (.inr n)
  | .bind n _, [X] => I.unaryReadings M n X
  | .phrase _ _, [X] => X
  | .phrase _ _, [X, Y] => I.binaryReadings M X Y
  | _, _ => ∅

/-- The readings of a tree when a word or a trace may be any of a set of items. -/
def readings (I : Interpreter G ℕ) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → Set (Sigma W)) (t : Tree C L) :
    Set (Sigma D) :=
  RoseTree.fold (nodeReadings I M ρ lex) t

variable (I : Interpreter G ℕ) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
  (lex : L ⊕ ℕ → Set (Sigma W))

/-- A word's readings are the values of the items it may be. -/
@[simp] theorem readings_terminal (c : C) (w : L) :
    (terminal c w).readings I M ρ lex = (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex (.inl w) := by
  simp [readings, nodeReadings]

/-- A trace's readings are the values of the items its index may be. -/
@[simp] theorem readings_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).readings I M ρ lex =
      (fun p ↦ ⟨p.1, ρ p.2⟩) '' lex (.inr n) := by
  simp [readings, nodeReadings]

/-- A non-branching node has the readings of its daughter. -/
@[simp] theorem readings_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    (phrase c k [t]).readings I M ρ lex = t.readings I M ρ lex := by
  simp [readings, nodeReadings]

variable {I M ρ lex}

/-- A reading of a binder is the value of a rule its index admits, at a reading of its body. -/
theorem mem_readings_bind {n : ℕ} {c : C} {t : Tree C L} {d : Sigma D} :
    d ∈ (bind n c t).readings I M ρ lex ↔
      ∃ d₁ ∈ t.readings I M ρ lex, ∃ r ∈ I.unary n d₁.1,
        d = ⟨r.1, M.funMap r.2 d₁.2⟩ := by
  simp [readings, nodeReadings, unaryReadings]

/-- A reading of a binary node is the value of a rule the node admits, at readings of its
daughters. -/
theorem mem_readings_phrase_binary {c : C} {k : PhraseKind} {t₁ t₂ : Tree C L} {d : Sigma D} :
    d ∈ (phrase c k [t₁, t₂]).readings I M ρ lex ↔
      ∃ d₁ ∈ t₁.readings I M ρ lex, ∃ d₂ ∈ t₂.readings I M ρ lex,
        ∃ m ∈ I.binary d₁.1 d₂.1,
          d = ⟨m.1, M.funMap m.2 (d₁.2, d₂.2)⟩ := by
  simp [readings, nodeReadings, binaryReadings]

/-- Under the type-driven interpreter, a reading of a binary node is the value of a rule of the
grammar at readings of its daughters. -/
theorem mem_readings_typeDriven_phrase_binary [G.LocallyFinite] {M : G.Structure D}
    {ρ : ∀ {a : T}, W a → D a} {lex : L ⊕ ℕ → Set (Sigma W)} {c : C}
    {k : PhraseKind} {t₁ t₂ : Tree C L} {d : Sigma D} :
    d ∈ (phrase c k [t₁, t₂]).readings (typeDriven G) M ρ lex ↔
      ∃ d₁ ∈ t₁.readings (typeDriven G) M ρ lex,
        ∃ d₂ ∈ t₂.readings (typeDriven G) M ρ lex,
          ∃ (u : T) (m : G.Binary d₁.1 d₂.1 u), d = ⟨u, M.funMap m (d₁.2, d₂.2)⟩ := by
  simp [mem_readings_phrase_binary, Sigma.exists]

/-- The values an interpreter finds over a lexicon of lists are the readings: what a label makes
of lists has the members of what it makes of their sets. -/
theorem mem_values_iff {lex : L ⊕ ℕ → List (Sigma W)} {d : Sigma D} (t : Tree C L) :
    d ∈ t.values I M ρ lex ↔ d ∈ t.readings I M ρ (fun x ↦ {p | p ∈ lex x}) := by
  rw [values_eq_fold]
  refine RoseTree.rel_fold (fun (X : List (Sigma D)) (S : Set (Sigma D)) ↦ ∀ d, d ∈ X ↔ d ∈ S)
    (fun l Xs Ss h ↦ ?_) t d
  match l, Xs, Ss, h with
  | .terminal _ w, [], [], _ => simp [nodeValues, nodeReadings, eq_comm]
  | .trace n _, [], [], _ => simp [nodeValues, nodeReadings, eq_comm]
  | .bind n _, [X], [S], .cons h .nil =>
    simp [nodeValues, nodeReadings, mem_unaryValues, unaryReadings, h]
  | .phrase _ _, [X], [S], .cons h .nil => exact h
  | .phrase _ _, [X, Y], [S, S'], .cons h (.cons h' .nil) =>
    simp [nodeValues, nodeReadings, mem_binaryValues, binaryReadings, h, h']
  | .terminal _ _, _ :: _, _ :: _, _ | .trace _ _, _ :: _, _ :: _, _ | .bind _ _, [], [], _
  | .bind _ _, _ :: _ :: _, _ :: _ :: _, _ | .phrase _ _, [], [], _
  | .phrase _ _, _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => simp [nodeValues, nodeReadings]

end PhraseStructure.Tree
