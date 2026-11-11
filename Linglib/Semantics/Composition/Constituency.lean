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
  | .bind n _, [X] => I.bindValues M n X
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
  | .bind n _, [X] => exact map_bindValues h hu
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

/-- The values of a binder over an index are those of the rules its index admits, at the
values of its body. -/
@[simp] theorem values_bind (n : ℕ) (c : C) (t : Tree C L) :
    (bind n c t).values I M ρ lex = (t.values I M ρ lex).flatMap fun ⟨a, x⟩ ↦
      (I.bind n a).map fun ⟨b, r⟩ ↦ ⟨b, M.funMap r x⟩ := by
  simp [values_eq_fold, nodeValues, bindValues]

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
      (I.bind n a).map fun ⟨b, r⟩ ↦ ⟨b, .unary r d⟩ := by
  simp [derivs, nodeValues, bindValues]
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

/-! ### Relations between the values of two interpreters

Two interpreters may differ in their rules, their types and their domains. A relation between
their lists of values that holds at the words, and that binders and binary nodes preserve, holds
of the values of every tree. -/

section Rel

variable {T' : Type} {G' : Language T'} {W' D' : T' → Type} {I : Interpreter G ℕ}
  {J : Interpreter G' ℕ} {M : G.Structure D} {M' : G'.Structure D'} {ρ : ∀ {a : T}, W a → D a}
  {ρ' : ∀ {a : T'}, W' a → D' a} {lex : L ⊕ ℕ → List (Sigma W)}
  {lex' : L ⊕ ℕ → List (Sigma W')} (R : List (Sigma D) → List (Sigma D') → Prop)

/-- A relation between lists of values that holds of the items of each word and each trace, and
that binders and binary nodes preserve, is preserved by every label. -/
theorem nodeValues_rel (hnil : R [] [])
    (hlex : ∀ x, R ((lex x).map fun ⟨a, w⟩ ↦ ⟨a, ρ w⟩) ((lex' x).map fun ⟨a, w⟩ ↦ ⟨a, ρ' w⟩))
    (hbind : ∀ n X Y, R X Y → R (I.bindValues M n X) (J.bindValues M' n Y))
    (hbinary : ∀ X₁ Y₁ X₂ Y₂, R X₁ Y₁ → R X₂ Y₂ →
      R (I.binaryValues M X₁ X₂) (J.binaryValues M' Y₁ Y₂))
    (l : Label C L) {Xs : List (List (Sigma D))} {Ys : List (List (Sigma D'))}
    (h : List.Forall₂ R Xs Ys) :
    R (nodeValues I M ρ lex l Xs) (nodeValues J M' ρ' lex' l Ys) := by
  match l, Xs, Ys, h with
  | .terminal _ w, [], [], _ => exact hlex _
  | .trace n _, [], [], _ => exact hlex _
  | .bind n _, [X], [Y], .cons h .nil => exact hbind n X Y h
  | .phrase _ _, [X], [Y], .cons h .nil => exact h
  | .phrase _ _, [X₁, X₂], [Y₁, Y₂], .cons h₁ (.cons h₂ .nil) => exact hbinary _ _ _ _ h₁ h₂
  | .terminal _ _, _ :: _, _ :: _, _ | .trace _ _, _ :: _, _ :: _, _ | .bind _ _, [], [], _
  | .bind _ _, _ :: _ :: _, _ :: _ :: _, _ | .phrase _ _, [], [], _
  | .phrase _ _, _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => exact hnil

/-- A relation between lists of values that holds of the items of each word and each trace, and
that binders and binary nodes preserve, holds of the values of a tree. -/
theorem values_rel (hnil : R [] [])
    (hlex : ∀ x, R ((lex x).map fun ⟨a, w⟩ ↦ ⟨a, ρ w⟩) ((lex' x).map fun ⟨a, w⟩ ↦ ⟨a, ρ' w⟩))
    (hbind : ∀ n X Y, R X Y → R (I.bindValues M n X) (J.bindValues M' n Y))
    (hbinary : ∀ X₁ Y₁ X₂ Y₂, R X₁ Y₁ → R X₂ Y₂ →
      R (I.binaryValues M X₁ X₂) (J.binaryValues M' Y₁ Y₂))
    (t : Tree C L) : R (t.values I M ρ lex) (t.values J M' ρ' lex') := by
  rw [values_eq_fold, values_eq_fold]
  exact RoseTree.rel_fold R (fun l _ _ h ↦ nodeValues_rel R hnil hlex hbind hbinary l h) t

end Rel

variable {I : Interpreter G ℕ} {M : G.Structure D} {ρ : ∀ {a : T}, W a → D a}
  {lex : L ⊕ ℕ → List (Sigma W)}

/-- Where a node admits at most one rule for given daughters and a word is at most one item, a
tree has at most one value: interpretation is a function. -/
theorem length_values_le_one (hu : ∀ n a, (I.bind n a).length ≤ 1)
    (hb : ∀ a b, (I.binary a b).length ≤ 1) (hl : ∀ x, (lex x).length ≤ 1) (t : Tree C L) :
    (t.values I M ρ lex).length ≤ 1 :=
  values_rel (J := I) (M' := M) (ρ' := ρ) (lex' := lex) (fun X _ ↦ X.length ≤ 1)
    (Nat.zero_le _) (fun x ↦ by simpa using hl x)
    (fun _ _ _ hX ↦ length_bindValues_le_one (hu _) hX)
    (fun _ _ _ _ hX hY ↦ length_binaryValues_le_one hb hX hY) t

theorem Uninterpretable.values_eq_nil {t : Tree C L} (h : t.Uninterpretable I lex)
    (M : G.Structure D) (ρ : ∀ {a : T}, W a → D a) : t.values I M ρ lex = [] := by
  simp [values, h.derivs_eq_nil]

/-- Two interpreters that agree along a map of types give a tree the same values. The second
interprets at the image `ι a` what the first interprets at `a`, the values of the first at `a`
being values of the second at `ι a`. Where, on the types satisfying `Q`, the items of each word
and the values of the rules each node admits correspond, and the rules of the first keep to
those types, the values of a tree by the second are its values by the first, retyped. -/
theorem values_eq_map_of_types {T' : Type} {G' : Language T'} {W' D' : T' → Type} (ι : T → T')
    (Q : T → Prop) {I : Interpreter G ℕ} {J : Interpreter G' ℕ}
    {M : G.Structure fun a ↦ D' (ι a)} {M' : G'.Structure D'}
    {ρ : ∀ {a : T}, W a → D' (ι a)} {ρ' : ∀ {a : T'}, W' a → D' a}
    {lex : L ⊕ ℕ → List (Sigma W)} {lex' : L ⊕ ℕ → List (Sigma W')}
    (hlex : ∀ x, (lex' x).map (fun p ↦ (⟨p.1, ρ' p.2⟩ : Sigma D')) =
      (lex x).map fun p ↦ ⟨ι p.1, ρ p.2⟩)
    (hQ : ∀ x, ∀ p ∈ lex x, Q p.1)
    (hu : ∀ (n : ℕ) (a : T), Q a → ∀ x : D' (ι a),
      (J.bind n (ι a)).map (fun r ↦ (⟨r.1, M'.funMap r.2 x⟩ : Sigma D')) =
        (I.bind n a).map fun r ↦ ⟨ι r.1, M.funMap (σ := .of a) r.2 x⟩)
    (hQu : ∀ (n : ℕ) (a : T), Q a → ∀ r ∈ I.bind n a, Q r.1)
    (hb : ∀ a b : T, Q a → Q b → ∀ (x : D' (ι a)) (y : D' (ι b)),
      (J.binary (ι a) (ι b)).map (fun m ↦ (⟨m.1, M'.funMap m.2 (x, y)⟩ : Sigma D')) =
        (I.binary a b).map fun m ↦ ⟨ι m.1, M.funMap (σ := .prod (.of a) (.of b)) m.2 (x, y)⟩)
    (hQb : ∀ a b : T, Q a → Q b → ∀ m ∈ I.binary a b, Q m.1) (t : Tree C L) :
    t.values J M' ρ' lex' = (t.values I M ρ lex).map fun d ↦ ⟨ι d.1, d.2⟩ := by
  refine (values_rel
    (fun (X : List (Sigma D')) (Y : List (Sigma fun a ↦ D' (ι a))) ↦
      X = Y.map (fun d ↦ ⟨ι d.1, d.2⟩) ∧ ∀ d ∈ Y, Q d.1)
    ⟨rfl, fun _ hd ↦ nomatch hd⟩ (fun x ↦ ⟨?_, fun d hd ↦ ?_⟩) ?_ ?_ t).1
  · exact (hlex x).trans (by rw [List.map_map]; rfl)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact hQ x p hp
  · rintro n _ Y ⟨rfl, hY⟩
    refine ⟨?_, fun d hd ↦ ?_⟩
    · simp only [bindValues, List.flatMap_map, List.map_flatMap]
      exact List.flatMap_congr fun d hd ↦ by rw [hu n d.1 (hY d hd) d.2, List.map_map]; rfl
    · obtain ⟨d₁, h₁, r, hr, rfl⟩ := mem_bindValues.1 hd
      exact hQu n d₁.1 (hY d₁ h₁) r hr
  · rintro _ Y₁ _ Y₂ ⟨rfl, h₁⟩ ⟨rfl, h₂⟩
    refine ⟨?_, fun d hd ↦ ?_⟩
    · simp only [binaryValues, List.flatMap_map, List.map_flatMap]
      exact List.flatMap_congr fun d₁ hd₁ ↦ List.flatMap_congr fun d₂ hd₂ ↦ by
        rw [hb d₁.1 d₂.1 (h₁ d₁ hd₁) (h₂ d₂ hd₂) d₁.2 d₂.2, List.map_map]; rfl
    · obtain ⟨d₁, hd₁, d₂, hd₂, m, hm, rfl⟩ := mem_binaryValues.1 hd
      exact hQb d₁.1 d₂.1 (h₁ d₁ hd₁) (h₂ d₂ hd₂) m hm

end PhraseStructure.Tree
