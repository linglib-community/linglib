module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Composition.Basic

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

/-- The daughters an interpreter reads under a label: a word or a trace has none, a binder one,
and a phrase one or two. -/
def Label.IsAtMostBinary : Label C L → List (Label C L) → Prop
  | .terminal _ _, ks | .trace _ _, ks => ks = []
  | .bind _ _, ks => ks.length = 1
  | .phrase _ _, ks => ks.length = 1 ∨ ks.length = 2

instance : ∀ (l : Label C L) (ks : List (Label C L)), Decidable (l.IsAtMostBinary ks)
  | .terminal _ _, ks | .trace _ _, ks => inferInstanceAs (Decidable (ks = []))
  | .bind _ _, ks => inferInstanceAs (Decidable (ks.length = 1))
  | .phrase _ _, ks => inferInstanceAs (Decidable (ks.length = 1 ∨ ks.length = 2))

variable {T : Type} {G : Language T} {W D : T → Type}

/-- What a label makes of the values of its daughters: a word and a trace are the items they may
be, a binder's index and a binary node admit rules, with the categories `island` holds of as
islands, and a non-branching node has the values of its daughter. A phrase with no daughter or
more than two has none. -/
def nodeValues (I : Interpreter G Node) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → List (Σ a, W a)) (island : C → Bool) :
    Label C L → List (List (Σ a, D a)) → List (Σ a, D a)
  | .terminal _ w, [] => (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩
  | .trace n _, [] => (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩
  | .bind n _, [X] => I.unaryValues M (.index n) X
  | .phrase _ _, [X] => X
  | .phrase c _, [X, Y] => I.binaryValues M (if island c then .island else .branch) X Y
  | _, _ => []

/-- The values an interpreter gives a tree in a structure, for a lexicon of typed items whose
values `ρ` gives: the fold of the tree by what each label makes of its daughters' values. -/
def values (I : Interpreter G Node) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → List (Σ a, W a)) (t : Tree C L) (island : C → Bool := fun _ ↦ false) :
    List (Σ a, D a) :=
  RoseTree.fold (nodeValues I M ρ lex island) t

/-- The derivations of a tree that an interpreter admits, given the typed items each word and
each trace may be: its values in the term algebra. -/
def derivs (I : Interpreter G Node) (lex : L ⊕ ℕ → List (Σ a, W a)) (t : Tree C L)
    (island : C → Bool := fun _ ↦ false) : List (Σ a, Deriv G W a) :=
  t.values I (Term.structure G W) Deriv.leaf lex island

/-- A tree is uninterpretable for an interpreter and a lexicon when each of its nodes has the
daughters an interpreter reads and the interpreter admits no derivation over it. A tree with a
phrase of no daughter or more than two has no derivations either, and is not thereby
uninterpretable. -/
structure Uninterpretable (I : Interpreter G Node) (lex : L ⊕ ℕ → List (Σ a, W a))
    (t : Tree C L) (island : C → Bool := fun _ ↦ false) : Prop where
  /-- Each node has the daughters an interpreter reads. -/
  licensed : t.Licensed Label.IsAtMostBinary
  /-- The interpreter admits no derivation over it. -/
  derivs_eq_nil : t.derivs I lex island = []

/-! ### Values of a node from the values of its daughters -/

section Compositional

variable (I : Interpreter G Node) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
  (lex : L ⊕ ℕ → List (Σ a, W a)) (island : C → Bool)

/-- A word's values are the values of the items it may be. -/
@[simp] theorem values_terminal (c : C) (w : L) :
    (terminal c w).values I M ρ lex island = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [values, nodeValues]

/-- A trace's values are the values of the items its index may be. -/
@[simp] theorem values_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).values I M ρ lex island =
      (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [values, nodeValues]

/-- The values of a binder over an index are those of the unary rules its index admits, at the
values of its body. -/
@[simp] theorem values_bind (n : ℕ) (c : C) (t : Tree C L) :
    (bind n c t).values I M ρ lex island = (t.values I M ρ lex island).flatMap fun ⟨a, x⟩ ↦
      (I.unary (.index n) a).map fun ⟨b, r⟩ ↦ ⟨b, M.funMap r x⟩ := by
  simp [values, nodeValues, unaryValues]

/-- The values of a binary node are those of the rules the node admits for its daughters'
types, at the values of its daughters. -/
@[simp] theorem values_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    (phrase c k [t₁, t₂]).values I M ρ lex island =
      (t₁.values I M ρ lex island).flatMap fun ⟨a, x⟩ ↦
        (t₂.values I M ρ lex island).flatMap fun ⟨b, y⟩ ↦
          (I.binary (if island c then .island else .branch) a b).map fun ⟨u, m⟩ ↦
            ⟨u, M.funMap m (x, y)⟩ := by
  simp [values, nodeValues, binaryValues]

/-- A non-branching node has the values of its daughter. -/
@[simp] theorem values_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    (phrase c k [t]).values I M ρ lex island = t.values I M ρ lex island := by
  simp [values, nodeValues]

theorem derivs_terminal (c : C) (w : L) :
    (terminal c w).derivs I lex island = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, .leaf x⟩ :=
  values_terminal ..

theorem derivs_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).derivs I lex island =
      (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, .leaf x⟩ :=
  values_trace ..

theorem derivs_bind (n : ℕ) (c : C) (t : Tree C L) :
    (bind n c t).derivs I lex island = (t.derivs I lex island).flatMap fun ⟨a, d⟩ ↦
      (I.unary (.index n) a).map fun ⟨b, r⟩ ↦ ⟨b, .unary r d⟩ :=
  values_bind ..

theorem derivs_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    (phrase c k [t₁, t₂]).derivs I lex island = (t₁.derivs I lex island).flatMap fun ⟨a, d₁⟩ ↦
      (t₂.derivs I lex island).flatMap fun ⟨b, d₂⟩ ↦
        (I.binary (if island c then .island else .branch) a b).map fun ⟨u, m⟩ ↦
          ⟨u, .binary m d₁ d₂⟩ :=
  values_phrase_binary ..

theorem derivs_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    (phrase c k [t]).derivs I lex island = t.derivs I lex island :=
  values_phrase_unary ..

/-- What a label makes of its daughters' values commutes with a map of domains that commutes
with the rules and takes the values of the items to their values. -/
theorem map_nodeValues {D' : T → Type} {M' : G.Structure D'} {ρ' : ∀ {a : T}, W a → D' a}
    (h : ∀ a, D a → D' a)
    (hu : ∀ {a b : T} (r : G.Unary a b) (x : D a), h b (M.funMap r x) = M'.funMap r (h a x))
    (hb : ∀ {a b c : T} (m : G.Binary a b c) (x : D a) (y : D b),
      h c (M.funMap m (x, y)) = M'.funMap m (h a x, h b y))
    (hρ : ∀ {a : T} (x : W a), h a (ρ x) = ρ' x) (l : Label C L)
    (Xs : List (List (Σ a, D a))) :
    (nodeValues I M ρ lex island l Xs).map (fun d ↦ ⟨d.1, h d.1 d.2⟩) =
      nodeValues I M' ρ' lex island l (Xs.map (List.map fun d ↦ ⟨d.1, h d.1 d.2⟩)) := by
  match l, Xs with
  | .terminal _ w, [] => simp [nodeValues, Function.comp_def, hρ]
  | .trace n _, [] => simp [nodeValues, Function.comp_def, hρ]
  | .bind n _, [X] => exact map_unaryValues h hu
  | .phrase _ _, [X] => rfl
  | .phrase c _, [X, Y] => exact map_binaryValues h hb
  | .terminal _ _, _ :: _ | .trace _ _, _ :: _ | .bind _ _, [] | .bind _ _, _ :: _ :: _
  | .phrase _ _, [] | .phrase _ _, _ :: _ :: _ :: _ => rfl

/-- The values of a tree are the values of its derivations. -/
theorem values_eq_map_derivs (t : Tree C L) :
    t.values I M ρ lex island =
      (t.derivs I lex island).map fun d ↦ ⟨d.1, d.2.realize M ρ⟩ :=
  (RoseTree.fold_hom
    (List.map fun d : Σ a, Deriv G W a ↦ (⟨d.1, d.2.realize M ρ⟩ : Σ a, D a))
    (fun l Xs ↦ map_nodeValues I (Term.structure G W) Deriv.leaf lex island
      (fun _ d ↦ d.realize M ρ) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ ↦ rfl) l Xs) t).symm

end Compositional

theorem Uninterpretable.values_eq_nil {I : Interpreter G Node} {lex : L ⊕ ℕ → List (Σ a, W a)}
    {t : Tree C L} {island : C → Bool} (h : t.Uninterpretable I lex island) (M : G.Structure D)
    (ρ : ∀ {a : T}, W a → D a) : t.values I M ρ lex island = [] := by
  simp [values_eq_map_derivs, h.derivs_eq_nil]

end PhraseStructure.Tree
