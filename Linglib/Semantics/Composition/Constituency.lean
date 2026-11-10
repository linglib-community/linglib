module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Composition.Basic

/-!
# The interpretation of a constituency tree

A constituency tree gives the semantics its words in their constituency and order, the indices of
its moved phrases. Its derivations are its fold by what each label makes of its daughters': a
word and a trace are the items they may be, a binder's index and a binary node admit rules, and
a non-branching node has what its daughter has. [Its values
in a structure are the same fold there](##PhraseStructure.Tree.values_eq_fold), and where a node
admits at most one rule [it has at most one](##PhraseStructure.Tree.length_values_le_one).

## Main definitions

* `PhraseStructure.Tree.nodeValues`: what a label makes of the values of its daughters.
* `PhraseStructure.Tree.derivs`, `PhraseStructure.Tree.values`: the derivations of a tree that an
  interpreter admits, and their values, with [the values of a node from those of its
  daughters](##PhraseStructure.Tree.values_phrase_binary).
* `PhraseStructure.Tree.Uninterpretable`: a tree an interpreter reads and admits no derivation
  over.

## Implementation notes

Values are defined as the values of the derivations and not as the fold in the structure. The
derivations of a tree are closed terms, and over a model with variables in it the fold in the
model is much slower to check.

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
be, a binder's index and a binary node admit rules, and a non-branching node has the values of
its daughter. A phrase with no daughter or
more than two has none. -/
def nodeValues (I : Interpreter G ℕ) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → List (Sigma W)) :
    Label C L → List (List (Sigma D)) → List (Sigma D)
  | .terminal _ w, [] => (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩
  | .trace n _, [] => (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩
  | .bind n _, [X] => I.unaryValues M n X
  | .phrase _ _, [X] => X
  | .phrase _ _, [X, Y] => I.binaryValues M X Y
  | _, _ => []

/-- The derivations of a tree that an interpreter admits, given the typed items each word and
each trace may be: the fold of the tree by what each label makes of its daughters' derivations,
which are their values in the term algebra. -/
def derivs (I : Interpreter G ℕ) (lex : L ⊕ ℕ → List (Sigma W)) (t : Tree C L)
    : List (Sigma (Deriv G W)) :=
  RoseTree.fold (nodeValues I (Term.structure G W) Deriv.leaf lex) t

/-- The values of the derivations of a tree, for a lexicon of typed items whose values `ρ`
gives. -/
def values (I : Interpreter G ℕ) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
    (lex : L ⊕ ℕ → List (Sigma W)) (t : Tree C L) :
    List (Sigma D) :=
  (t.derivs I lex).map fun ⟨a, d⟩ ↦ ⟨a, d.realize M ρ⟩

/-- A tree is uninterpretable for an interpreter and a lexicon when each of its nodes has the
daughters an interpreter reads and the interpreter admits no derivation over it. A tree with a
phrase of no daughter or more than two has no derivations either, and is not thereby
uninterpretable. -/
structure Uninterpretable (I : Interpreter G ℕ) (lex : L ⊕ ℕ → List (Sigma W))
    (t : Tree C L) : Prop where
  /-- Each node has the daughters an interpreter reads. -/
  licensed : t.Licensed Label.IsAtMostBinary
  /-- The interpreter admits no derivation over it. -/
  derivs_eq_nil : t.derivs I lex = []

/-! ### Values of a node from the values of its daughters -/

section Compositional

variable (I : Interpreter G ℕ) (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a)
  (lex : L ⊕ ℕ → List (Sigma W))

/-- What a label makes of its daughters' values commutes with a map of domains that commutes
with the rules and takes the values of the items to their values. -/
theorem map_nodeValues {D' : T → Type} {M' : G.Structure D'} {ρ' : ∀ {a : T}, W a → D' a}
    (h : ∀ a, D a → D' a)
    (hu : ∀ {a b : T} (r : G.Unary a b) (x : D a), h b (M.funMap r x) = M'.funMap r (h a x))
    (hb : ∀ {a b c : T} (m : G.Binary a b c) (x : D a) (y : D b),
      h c (M.funMap m (x, y)) = M'.funMap m (h a x, h b y))
    (hρ : ∀ {a : T} (x : W a), h a (ρ x) = ρ' x) (l : Label C L)
    (Xs : List (List (Sigma D))) :
    (nodeValues I M ρ lex l Xs).map (fun d ↦ ⟨d.1, h d.1 d.2⟩) =
      nodeValues I M' ρ' lex l (Xs.map (List.map fun d ↦ ⟨d.1, h d.1 d.2⟩)) := by
  match l, Xs with
  | .terminal _ w, [] => simp [nodeValues, Function.comp_def, hρ]
  | .trace n _, [] => simp [nodeValues, Function.comp_def, hρ]
  | .bind n _, [X] => exact map_unaryValues h hu
  | .phrase _ _, [X] => rfl
  | .phrase _ _, [X, Y] => exact map_binaryValues h hb
  | .terminal _ _, _ :: _ | .trace _ _, _ :: _ | .bind _ _, [] | .bind _ _, _ :: _ :: _
  | .phrase _ _, [] | .phrase _ _, _ :: _ :: _ :: _ => rfl

theorem values_eq_map_derivs (t : Tree C L) :
    t.values I M ρ lex =
      (t.derivs I lex).map fun d ↦ ⟨d.1, d.2.realize M ρ⟩ := rfl

/-- The values of a tree are its fold by what each label makes of its daughters' values:
taking values commutes with the rules. -/
theorem values_eq_fold (t : Tree C L) :
    t.values I M ρ lex = RoseTree.fold (nodeValues I M ρ lex) t :=
  RoseTree.fold_hom
    (List.map fun d : Sigma (Deriv G W) ↦ (⟨d.1, d.2.realize M ρ⟩ : Sigma D))
    (fun l Xs ↦ map_nodeValues I (Term.structure G W) Deriv.leaf lex
      (fun _ d ↦ d.realize M ρ) (fun _ _ ↦ rfl) (fun _ _ _ ↦ rfl) (fun _ ↦ rfl) l Xs) t

/-- The derivations of a tree are its values in the term algebra. -/
theorem derivs_eq_values (t : Tree C L) :
    t.derivs I lex = t.values I (Term.structure G W) Deriv.leaf lex :=
  (values_eq_fold ..).symm

/-- A word's values are the values of the items it may be. -/
@[simp] theorem values_terminal (c : C) (w : L) :
    (terminal c w).values I M ρ lex = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [values_eq_fold, nodeValues]

/-- A trace's values are the values of the items its index may be. -/
@[simp] theorem values_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).values I M ρ lex =
      (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, ρ x⟩ := by
  simp [values_eq_fold, nodeValues]

/-- The values of a binder over an index are those of the unary rules its index admits, at the
values of its body. -/
@[simp] theorem values_bind (n : ℕ) (c : C) (t : Tree C L) :
    (bind n c t).values I M ρ lex = (t.values I M ρ lex).flatMap fun ⟨a, x⟩ ↦
      (I.unary n a).map fun ⟨b, r⟩ ↦ ⟨b, M.funMap r x⟩ := by
  simp [values_eq_fold, nodeValues, unaryValues]

/-- The values of a binary node are those of the rules the node admits for its daughters'
types, at the values of its daughters. -/
@[simp] theorem values_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    (phrase c k [t₁, t₂]).values I M ρ lex =
      (t₁.values I M ρ lex).flatMap fun ⟨a, x⟩ ↦
        (t₂.values I M ρ lex).flatMap fun ⟨b, y⟩ ↦
          (I.binary a b).map fun ⟨u, m⟩ ↦
            ⟨u, M.funMap m (x, y)⟩ := by
  simp [values_eq_fold, nodeValues, binaryValues]

/-- A non-branching node has the values of its daughter. -/
@[simp] theorem values_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    (phrase c k [t]).values I M ρ lex = t.values I M ρ lex := by
  simp [values_eq_fold, nodeValues]

theorem derivs_terminal (c : C) (w : L) :
    (terminal c w).derivs I lex = (lex (.inl w)).map fun ⟨a, x⟩ ↦ ⟨a, .leaf x⟩ := by
  simp [derivs, nodeValues]

theorem derivs_trace (n : ℕ) (c : C) :
    (trace n c : Tree C L).derivs I lex =
      (lex (.inr n)).map fun ⟨a, x⟩ ↦ ⟨a, .leaf x⟩ := by
  simp [derivs, nodeValues]

theorem derivs_bind (n : ℕ) (c : C) (t : Tree C L) :
    (bind n c t).derivs I lex = (t.derivs I lex).flatMap fun ⟨a, d⟩ ↦
      (I.unary n a).map fun ⟨b, r⟩ ↦ ⟨b, .unary r d⟩ := by
  simp [derivs, nodeValues, unaryValues]
  rfl

theorem derivs_phrase_binary (c : C) (k : PhraseKind) (t₁ t₂ : Tree C L) :
    (phrase c k [t₁, t₂]).derivs I lex = (t₁.derivs I lex).flatMap fun ⟨a, d₁⟩ ↦
      (t₂.derivs I lex).flatMap fun ⟨b, d₂⟩ ↦
        (I.binary a b).map fun ⟨u, m⟩ ↦
          ⟨u, .binary m d₁ d₂⟩ := by
  simp [derivs, nodeValues, binaryValues]
  rfl

theorem derivs_phrase_unary (c : C) (k : PhraseKind) (t : Tree C L) :
    (phrase c k [t]).derivs I lex = t.derivs I lex := by
  simp [derivs, nodeValues]

end Compositional

variable {I : Interpreter G ℕ} {M : G.Structure D} {ρ : ∀ {a : T}, W a → D a}
  {lex : L ⊕ ℕ → List (Sigma W)}

/-- Where a node admits at most one rule for given daughters and a word is at most one item, a
tree has at most one value: interpretation is a function. -/
theorem length_values_le_one (hu : ∀ n a, (I.unary n a).length ≤ 1)
    (hb : ∀ a b, (I.binary a b).length ≤ 1) (hl : ∀ x, (lex x).length ≤ 1) (t : Tree C L) :
    (t.values I M ρ lex).length ≤ 1 := by
  rw [values_eq_fold]
  refine RoseTree.rel_fold (g := nodeValues I M ρ lex)
    (fun (X _ : List (Sigma D)) ↦ X.length ≤ 1) (fun l Xs Ys h ↦ ?_) t
  match l, Xs, Ys, h with
  | .terminal _ w, [], [], _ => simpa [nodeValues] using hl _
  | .trace n _, [], [], _ => simpa [nodeValues] using hl _
  | .bind n _, [X], [_], .cons hX .nil => exact length_unaryValues_le_one (hu _) hX
  | .phrase _ _, [X], [_], .cons hX .nil => exact hX
  | .phrase _ _, [X, Y], [_, _], .cons hX (.cons hY .nil) =>
    exact length_binaryValues_le_one hb hX hY
  | .terminal _ _, _ :: _, _ :: _, _ | .trace _ _, _ :: _, _ :: _, _ | .bind _ _, [], [], _
  | .bind _ _, _ :: _ :: _, _ :: _ :: _, _ | .phrase _ _, [], [], _
  | .phrase _ _, _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => exact Nat.zero_le _


theorem Uninterpretable.values_eq_nil {t : Tree C L} (h : t.Uninterpretable I lex)
    (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a) : t.values I M ρ lex = [] := by
  simp [values, h.derivs_eq_nil]

end PhraseStructure.Tree
