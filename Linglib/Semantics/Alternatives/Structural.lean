module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Data.Finset.Basic
public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Composition.WithAlternatives

/-!
# Structural alternatives

The *structural alternatives* of a parse tree are the trees obtainable from it by deletion,
contraction, and substitution of a constituent by a same-category item of the substitution
source, the lexicon together with the tree's own subtrees. A tree is *at most as complex* as
another if these operations reach it from the other (definition (19)), and the structural
alternatives of a tree are the trees at most as complex as it (definition (20)). Structural
alternatives are one source of alternatives for the competition relations of `Competition`.

## Main definitions

* `substitutionSource` — the lexicon together with the subtrees of the host.
* `StructuralOp`, `atMostAsComplex`, `equalComplexity` — one operation, its reflexive-transitive
  closure as a preorder, and the equal-complexity equivalence.
* `structuralAlternatives` — the trees at most as complex as the host over its source.
* `withAlternatives` — the Hamblin composition of a tree over a lexicon, a `WithAlternatives`
  value.

## Main results

* `category_preservation`, `phrase_preservation`, `subtree_preservation` — the operations
  create no category, no phrase of a category and no subtree property absent from the host and
  the source; `phrase_preservation` is what excludes the symmetric alternatives.
* `horn_alternatives_are_structural` — substituting a same-category lexical item throughout a tree
  is a chain of substitutions, so Horn-scale alternatives are structural alternatives.
* `alternatives_withAlternatives_subset` — the Hamblin composition of `WithAlternatives`, with each
  terminal evoking its same-category lexical items, generates only structural alternatives;
  deletion and contraction, which act on the whole tree, lie outside any pointwise composition.

## Implementation notes

`atMostAsComplex` is reachability, not an operation count, so `equalComplexity`, mutual
reachability, is coarser than the paper's equal complexity. The `inBind` constructor extends
the operations into the body of a binder, which the paper's trees lack.

## References

* [katzir-2007]
* [fox-katzir-2011]
-/

@[expose] public section

namespace PhraseStructure.Tree

variable {C W : Type*}

/-- The substitution source of `φ` (the paper's definition (41)) is the lexicon together with
the subtrees of `φ`, so that a complex constituent of `φ` can replace a simpler one
elsewhere in it. -/
def substitutionSource (lex : Finset (Tree C W)) (φ : Tree C W) : Set (Tree C W) :=
  ↑lex ∪ {t | t ∈ φ.subtrees}

theorem forall_mem_substitutionSource {lex : Finset (Tree C W)} {φ : Tree C W}
    {P : Tree C W → Prop} :
    (∀ t ∈ substitutionSource lex φ, P t) ↔ (∀ t ∈ lex, P t) ∧ ∀ t ∈ φ.subtrees, P t := by
  simp only [substitutionSource, Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, or_imp,
    forall_and]

/-- A structural operation on parse trees substitutes a constituent by a same-category item of the
source, deletes a child of a phrase, contracts a phrase to one of its same-category children, or
applies one of these inside a child of a phrase or a binder body. A phrase is a node or an
adjunction structure. -/
inductive StructuralOp (source : Set (Tree C W)) : Tree C W → Tree C W → Prop where
  /-- Substitute a tree by a same-category item of the source. -/
  | subst {φ ψ : Tree C W} (h_cat : ψ.cat = φ.cat) (h_src : ψ ∈ source) : StructuralOp source φ ψ
  /-- Delete the `i`-th child of a phrase. -/
  | delete {l : Tree.Label C W} {cs : List (Tree C W)} (i : Fin cs.length)
    (hl : l.IsPhrase := by trivial) :
    StructuralOp source (RoseTree.node l cs) (RoseTree.node l (cs.eraseIdx i))
  /-- Contract a phrase to one of its same-category children. -/
  | contract {l : Tree.Label C W} {cs : List (Tree C W)} {child : Tree C W} (h_mem : child ∈ cs)
    (h_cat : child.cat = l.cat) (hl : l.IsPhrase := by trivial) :
    StructuralOp source (RoseTree.node l cs) child
  /-- Apply an operation inside one child of a phrase. -/
  | inChild {l : Tree.Label C W} {cs : List (Tree C W)} (i : Fin cs.length) {ψ_child : Tree C W}
    (h_step : StructuralOp source (cs.get i) ψ_child) (hl : l.IsPhrase := by trivial) :
    StructuralOp source (RoseTree.node l cs) (RoseTree.node l (cs.set i ψ_child))
  /-- Apply an operation inside a binder body. -/
  | inBind {n : Nat} {cat : C} {body body' : Tree C W} (h_step : StructuralOp source body body') :
    StructuralOp source (.bind n cat body) (.bind n cat body')

/-- `ψ` is at most as complex as `φ` when a chain of structural operations over the source
leads from `φ` to `ψ`, the paper's definition (19) as a reachability preorder. -/
def atMostAsComplex (source : Set (Tree C W)) (ψ φ : Tree C W) : Prop :=
  Relation.ReflTransGen (StructuralOp source) φ ψ

instance (source : Set (Tree C W)) : IsPreorder (Tree C W) (atMostAsComplex source) where
  refl _ := Relation.ReflTransGen.refl
  trans _ _ _ h₁ h₂ := h₂.trans h₁

/-- Two trees are of equal complexity when each is at most as complex as the other. -/
def equalComplexity (source : Set (Tree C W)) : Tree C W → Tree C W → Prop :=
  AntisymmRel (atMostAsComplex source)

theorem equalComplexity.equivalence (source : Set (Tree C W)) :
    Equivalence (equalComplexity source) :=
  (AntisymmRel.setoid (Tree C W) (atMostAsComplex source)).iseqv

theorem equalComplexity_terminal_subst {source : Set (Tree C W)} {cat : C} {oldW newW : W}
    (h_old : Tree.terminal cat oldW ∈ source) (h_new : Tree.terminal cat newW ∈ source) :
    equalComplexity source (.terminal cat oldW) (.terminal cat newW) :=
  ⟨Relation.ReflTransGen.single (StructuralOp.subst rfl h_old),
   Relation.ReflTransGen.single (StructuralOp.subst rfl h_new)⟩

/-- The structural alternatives of `φ`, the paper's definition (20), are the trees at most as
complex as `φ` over its substitution source. -/
def structuralAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) : Set (Tree C W) :=
  {ψ | atMostAsComplex (substitutionSource lex φ) ψ φ}

theorem self_mem_structuralAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) :
    φ ∈ structuralAlternatives lex φ :=
  Relation.ReflTransGen.refl

/-! ### Category and subtree preservation -/

private theorem structuralOp_preserves_no_cat (source : Set (Tree C W)) (c : C) (φ ψ : Tree C W)
    (h_source : ∀ s ∈ source, c ∉ s.cats) (h_φ : c ∉ φ.cats) (h_step : StructuralOp source φ ψ) :
    c ∉ ψ.cats := by
  induction h_step with
  | subst _ h_src => exact h_source _ h_src
  | @delete l cs i =>
    rw [Tree.mem_cats_rose] at h_φ ⊢; push Not at h_φ ⊢
    exact ⟨h_φ.1, fun t ht ↦ h_φ.2 t ((List.eraseIdx_sublist cs i).subset ht)⟩
  | @contract l cs child h_mem _ =>
    rw [Tree.mem_cats_rose] at h_φ; push Not at h_φ; exact h_φ.2 child h_mem
  | @inChild l cs i ψ_child _ _ ih =>
    rw [Tree.mem_cats_rose] at h_φ ⊢; push Not at h_φ ⊢
    have hih := ih (h_φ.2 (cs.get i) (List.get_mem cs i))
    refine ⟨h_φ.1, fun t ht ↦ ?_⟩
    rcases List.mem_or_eq_of_mem_set ht with ht' | rfl
    · exact h_φ.2 t ht'
    · exact hih
  | @inBind n cat body body' _ ih =>
    rw [Tree.mem_cats_bind] at h_φ ⊢; push Not at h_φ ⊢
    exact ⟨h_φ.1, ih h_φ.2⟩

/-- No tree reachable by structural operations contains a category absent from the source and
the host. -/
theorem category_preservation (source : Set (Tree C W)) (c : C) (φ ψ : Tree C W)
    (h_source : ∀ s ∈ source, c ∉ s.cats) (h_φ : c ∉ φ.cats)
    (h_reach : atMostAsComplex source ψ φ) : c ∉ ψ.cats := by
  unfold atMostAsComplex at h_reach
  induction h_reach with
  | refl => exact h_φ
  | tail _ h_last ih =>
    exact structuralOp_preserves_no_cat source c _ _ h_source ih h_last

private theorem structuralOp_preserves_free (source : Set (Tree C W))
    (Bad : Tree C W → Prop) (h_source : ∀ s ∈ source, ∀ t ∈ s.subtrees, ¬ Bad t)
    (h_delete : ∀ (l : Tree.Label C W) (cs : List (Tree C W)) (i : Fin cs.length), l.IsPhrase →
      ¬ Bad (RoseTree.node l cs) → ¬ Bad (RoseTree.node l (cs.eraseIdx i)))
    (h_set : ∀ (l : Tree.Label C W) (cs : List (Tree C W)) (i : Fin cs.length) (ψ : Tree C W),
      l.IsPhrase → ¬ Bad (RoseTree.node l cs) → ¬ Bad (RoseTree.node l (cs.set i ψ)))
    (h_bind : ∀ (n : ℕ) (cat : C) (body body' : Tree C W),
      ¬ Bad (.bind n cat body) → ¬ Bad (.bind n cat body'))
    {φ ψ : Tree C W} (h_φ : ∀ t ∈ φ.subtrees, ¬ Bad t) (h_step : StructuralOp source φ ψ) :
    ∀ t ∈ ψ.subtrees, ¬ Bad t := by
  induction h_step with
  | subst _ h_src => exact h_source _ h_src
  | @delete l cs i hl =>
    rw [RoseTree.subtrees_node] at h_φ ⊢
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h_delete l cs i hl (h_φ _ (List.mem_cons_self ..))
    · obtain ⟨c, hc, htc⟩ := List.mem_flatMap.mp ht
      exact h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨c, (List.eraseIdx_sublist cs i).subset hc, htc⟩))
  | @contract l cs child h_mem _ =>
    rw [RoseTree.subtrees_node] at h_φ
    exact fun t ht ↦ h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, h_mem, ht⟩))
  | @inChild l cs i ψ_child _ hl ih =>
    rw [RoseTree.subtrees_node] at h_φ ⊢
    have hih := ih fun t ht ↦
      h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨cs.get i, List.get_mem cs i, ht⟩))
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h_set l cs i ψ_child hl (h_φ _ (List.mem_cons_self ..))
    · obtain ⟨c, hc, htc⟩ := List.mem_flatMap.mp ht
      rcases List.mem_or_eq_of_mem_set hc with hc | rfl
      · exact h_φ t (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, htc⟩))
      · exact hih t htc
  | @inBind n cat body body' _ ih =>
    rw [Tree.subtrees_bind] at h_φ ⊢
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h_bind n cat body body' (h_φ _ (List.mem_cons_self ..))
    · exact ih (fun t ht ↦ h_φ t (List.mem_cons_of_mem _ ht)) t ht

/-- Let `Bad` be a subtree property that the host and the source items lack, and that no node
acquires by losing a child, by having a child replaced, or by a change of its binder's body. Then
no structural alternative of the host has `Bad`. -/
theorem subtree_preservation (source : Set (Tree C W)) (Bad : Tree C W → Prop)
    (h_source : ∀ s ∈ source, ∀ t ∈ s.subtrees, ¬ Bad t)
    (h_delete : ∀ (l : Tree.Label C W) (cs : List (Tree C W)) (i : Fin cs.length), l.IsPhrase →
      ¬ Bad (RoseTree.node l cs) → ¬ Bad (RoseTree.node l (cs.eraseIdx i)))
    (h_set : ∀ (l : Tree.Label C W) (cs : List (Tree C W)) (i : Fin cs.length) (ψ : Tree C W),
      l.IsPhrase → ¬ Bad (RoseTree.node l cs) → ¬ Bad (RoseTree.node l (cs.set i ψ)))
    (h_bind : ∀ (n : ℕ) (cat : C) (body body' : Tree C W),
      ¬ Bad (.bind n cat body) → ¬ Bad (.bind n cat body'))
    {φ ψ : Tree C W} (h_φ : ∀ t ∈ φ.subtrees, ¬ Bad t) (h_reach : atMostAsComplex source ψ φ) :
    ∀ t ∈ ψ.subtrees, ¬ Bad t := by
  unfold atMostAsComplex at h_reach
  induction h_reach with
  | refl => exact h_φ
  | tail _ h_last ih =>
    exact structuralOp_preserves_free source Bad h_source h_delete h_set h_bind ih h_last

/-- If neither the host nor any source item has a phrase (a node or adjunction structure) of
category `c`, no structural alternative has one. -/
theorem phrase_preservation (source : Set (Tree C W)) (c : C)
    (h_source : ∀ s ∈ source, ∀ t ∈ s.subtrees, ¬ (t.value.IsPhrase ∧ Tree.cat t = c))
    {φ ψ : Tree C W} (h_φ : ∀ t ∈ φ.subtrees, ¬ (t.value.IsPhrase ∧ Tree.cat t = c))
    (h_reach : atMostAsComplex source ψ φ) :
    ∀ t ∈ ψ.subtrees, ¬ (t.value.IsPhrase ∧ Tree.cat t = c) :=
  subtree_preservation source (fun t ↦ t.value.IsPhrase ∧ Tree.cat t = c) h_source
    (fun _ _ _ _ ↦ id) (fun _ _ _ _ _ ↦ id) (fun _ _ _ _ _ h ↦ h.1.elim) h_φ h_reach

/-! ### Horn scales are structural alternatives -/

private theorem lift_at_position {source : Set (Tree C W)}
    {l : Tree.Label C W} (hl : l.IsPhrase) (cs : List (Tree C W))
    (i : Nat) (hi : i < cs.length) (ψ : Tree C W)
    (h : Relation.ReflTransGen (StructuralOp source) cs[i] ψ) :
    Relation.ReflTransGen (StructuralOp source)
      (RoseTree.node l cs) (RoseTree.node l (cs.set i ψ)) := by
  induction h with
  | refl => rw [List.set_getElem_self hi]
  | @tail b d _ hbd ih =>
    apply ih.trans
    apply Relation.ReflTransGen.single
    have hlen : i < (cs.set i b).length := by rw [List.length_set]; exact hi
    rw [show cs.set i d = (cs.set i b).set i d from (List.set_set ..).symm]
    refine StructuralOp.inChild ⟨i, hlen⟩ ?_ hl
    have hget : (cs.set i b).get ⟨i, hlen⟩ = b := List.getElem_set_self ..
    rw [hget]; exact hbd

private theorem lift_bind {source : Set (Tree C W)}
    {n : Nat} {cat : C} {body body' : Tree C W}
    (h : Relation.ReflTransGen (StructuralOp source) body body') :
    Relation.ReflTransGen (StructuralOp source) (.bind n cat body) (.bind n cat body') :=
  Relation.ReflTransGen.lift (fun t ↦ Tree.bind n cat t)
    (fun _ _ h ↦ StructuralOp.inBind h) body body' h

private theorem pointwise_reachable {source : Set (Tree C W)} {l : Tree.Label C W}
    (hl : l.IsPhrase) {cs cs' : List (Tree C W)} (hlen : cs'.length = cs.length)
    (hf : ∀ (i : Nat) (hi : i < cs.length),
      Relation.ReflTransGen (StructuralOp source) cs[i] (cs'[i]'(hlen ▸ hi))) :
    Relation.ReflTransGen (StructuralOp source) (RoseTree.node l cs) (RoseTree.node l cs') := by
  suffices h : ∀ k (hk : k ≤ cs.length),
    Relation.ReflTransGen (StructuralOp source)
      (RoseTree.node l cs) (RoseTree.node l (List.take k cs' ++ List.drop k cs)) by
    have h' := h cs.length le_rfl
    rw [List.take_of_length_le (by omega), List.drop_length, List.append_nil] at h'
    exact h'
  intro k
  induction k with
  | zero => intro _; simp; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro hk
    have hk' : k < cs.length := by omega
    apply Relation.ReflTransGen.trans (ih (by omega))
    have htk_len : (List.take k cs').length = k := by simp [List.length_take]; omega
    have hmid_k : (List.take k cs' ++ List.drop k cs)[k]'(by simp [List.length_take]; omega)
        = cs[k] := by
      rw [List.getElem_append_right (by omega)]
      simp [htk_len, List.getElem_drop]
    suffices heq : List.take (k + 1) cs' ++ List.drop (k + 1) cs =
        (List.take k cs' ++ List.drop k cs).set k (cs'[k]'(by omega)) by
      rw [heq]
      apply lift_at_position hl _ k (by simp [List.length_take]; omega)
      rw [hmid_k]; exact hf k hk'
    have htk1_len : (List.take (k + 1) cs').length = k + 1 := by simp [List.length_take]; omega
    apply List.ext_getElem
    · simp [List.length_set, List.length_take, List.length_drop]; omega
    · intro i hi1 hi2
      by_cases hik : i = k
      · subst hik
        rw [List.getElem_set_self, List.getElem_append_left (by omega)]
        simp [List.getElem_take]
      · rw [List.getElem_set_ne (Ne.symm hik)]
        by_cases hilt : i < k
        · rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
          simp [List.getElem_take]
        · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
          simp [htk1_len, htk_len, List.getElem_drop]
          congr 1; omega

private theorem mapChildren_reachable {source : Set (Tree C W)}
    {l : Tree.Label C W} (hl : l.IsPhrase) {cs : List (Tree C W)} {f : Tree C W → Tree C W}
    (hf : ∀ (i : Nat) (hi : i < cs.length),
      Relation.ReflTransGen (StructuralOp source) cs[i] (f cs[i])) :
    Relation.ReflTransGen (StructuralOp source)
      (RoseTree.node l cs) (RoseTree.node l (cs.map f)) :=
  pointwise_reachable hl (by simp) fun i hi ↦ by rw [List.getElem_map]; exact hf i hi

private theorem leafSubst_reachable [DecidableEq C] [DecidableEq W] {source : Set (Tree C W)}
    (α β : W) (c : C) (h_β : Tree.terminal c β ∈ source) (φ : Tree C W) (hφ : φ.IsWellFormed) :
    Relation.ReflTransGen (StructuralOp source) φ (φ.leafSubst α β c) := by
  induction φ using Tree.rec' with
  | terminal c' w =>
    rw [Tree.leafSubst_terminal]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact .single (StructuralOp.subst rfl h_β)
    · exact .refl
  | node c' cs ih =>
    rw [Tree.leafSubst_node]
    exact mapChildren_reachable (l := .node c') trivial fun i hi ↦
      ih _ (List.getElem_mem hi) (RoseTree.Licensed.of_mem hφ (List.getElem_mem hi))
  | adjoin c' cs ih =>
    rw [Tree.leafSubst_adjoin]
    exact mapChildren_reachable (l := .segment c') trivial fun i hi ↦
      ih _ (List.getElem_mem hi) (RoseTree.Licensed.of_mem hφ (List.getElem_mem hi))
  | trace n c' => exact .refl
  | bind n c' body ih =>
    rw [Tree.leafSubst_bind]
    exact lift_bind (ih (RoseTree.Licensed.of_mem hφ List.mem_cons_self))
  | junk l cs h _ => exact absurd (RoseTree.licensed_node_iff.mp hφ).1 h

/-- Substituting a same-category lexical item for a leaf throughout a well-formed tree gives a
structural alternative, so Horn-scale alternatives are structural alternatives. -/
theorem horn_alternatives_are_structural [DecidableEq C] [DecidableEq W]
    (lex : Finset (Tree C W)) (φ : Tree C W) (α β : W) (c : C) (h_β : Tree.terminal c β ∈ lex)
    (hφ : φ.IsWellFormed) :
    φ.leafSubst α β c ∈ structuralAlternatives lex φ :=
  leafSubst_reachable α β c (Set.mem_union_left _ (Finset.mem_coe.2 h_β)) φ hφ

/-! ### Hamblin composition stays within the substitution fragment

The composition engine of `WithAlternatives` computes alternatives pointwise from the parts:
`withAlternatives lex φ` gives each terminal the same-category items of the lexicon as
alternatives and composes the constructors through the applicative. Every alternative it evokes is
a chain of substitutions at the leaves, hence a structural alternative
(`alternatives_withAlternatives_subset`); deletion and contraction lie outside the compositional
fragment, so the converse fails. -/

/-- In the Hamblin composition of a tree over a lexicon a terminal evokes itself and the
same-category items of the lexicon, and the constructors compose pointwise. -/
def withAlternatives (lex : Finset (Tree C W)) : Tree C W → WithAlternatives (Tree C W)
  | t@(.terminal c _) => ⟨t, insert t {s | s ∈ lex ∧ s.cat = c}⟩
  | .node c cs => Tree.node c <$> list lex cs
  | .adjoin c cs => Tree.adjoin c <$> list lex cs
  | t@(.trace _ _) => pure t
  | .bind n c body => Tree.bind n c <$> withAlternatives lex body
  | t => pure t
where
  /-- The pointwise composition of a list of children. -/
  list (lex : Finset (Tree C W)) :
      List (Tree C W) → WithAlternatives (List (Tree C W))
  | [] => pure []
  | t :: ts => (· :: ·) <$> withAlternatives lex t <*> list lex ts

theorem withAlternatives_node_of_not_licenses (lex : Finset (Tree C W)) {l : Tree.Label C W}
    {cs : List (Tree C W)}
    (h : ¬ Tree.Label.Licenses l (cs.map RoseTree.value)) :
    withAlternatives lex (RoseTree.node l cs) = pure (RoseTree.node l cs) := by
  cases l with
  | terminal c w => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | node c => exact absurd trivial h
  | segment c => exact absurd trivial h
  | trace n c => cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  | bind n c =>
    rcases cs with _ | ⟨t, _ | ⟨u, cs⟩⟩
    · rfl
    · exact absurd rfl h
    · rfl

theorem ordinary_withAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) :
    (withAlternatives lex φ).ordinary = φ := by
  induction φ using Tree.rec' with
  | terminal c w => rfl
  | node c cs ih =>
    simp only [withAlternatives, WithAlternatives.ordinary_map]
    congr 1
    induction cs with
    | nil => rfl
    | cons t ts ihts =>
      simp only [withAlternatives.list, WithAlternatives.ordinary_seq,
        WithAlternatives.ordinary_map, ih t List.mem_cons_self,
        ihts fun s hs ↦ ih s (List.mem_cons_of_mem _ hs)]
  | adjoin c cs ih =>
    simp only [withAlternatives, WithAlternatives.ordinary_map]
    congr 1
    induction cs with
    | nil => rfl
    | cons t ts ihts =>
      simp only [withAlternatives.list, WithAlternatives.ordinary_seq,
        WithAlternatives.ordinary_map, ih t List.mem_cons_self,
        ihts fun s hs ↦ ih s (List.mem_cons_of_mem _ hs)]
  | trace n c => rfl
  | bind n c body ih => simp only [withAlternatives, WithAlternatives.ordinary_map, ih]
  | junk l cs h _ => rw [withAlternatives_node_of_not_licenses lex h]; rfl

theorem wellFormed_withAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) :
    (withAlternatives lex φ).WellFormed := by
  induction φ using Tree.rec' with
  | terminal c w => exact Set.mem_insert _ _
  | node c cs ih =>
    refine WithAlternatives.WellFormed.map ?_
    induction cs with
    | nil => exact WithAlternatives.WellFormed.unfeatured _
    | cons t ts ihts =>
      exact WithAlternatives.mem_alternatives_seq.2
        ⟨_, WithAlternatives.mem_alternatives_map.2 ⟨_, ih t List.mem_cons_self, rfl⟩, _,
          ihts fun s hs ↦ ih s (List.mem_cons_of_mem _ hs), rfl⟩
  | adjoin c cs ih =>
    refine WithAlternatives.WellFormed.map ?_
    induction cs with
    | nil => exact WithAlternatives.WellFormed.unfeatured _
    | cons t ts ihts =>
      exact WithAlternatives.mem_alternatives_seq.2
        ⟨_, WithAlternatives.mem_alternatives_map.2 ⟨_, ih t List.mem_cons_self, rfl⟩, _,
          ihts fun s hs ↦ ih s (List.mem_cons_of_mem _ hs), rfl⟩
  | trace n c => exact WithAlternatives.WellFormed.unfeatured _
  | bind n c body ih => exact ih.map
  | junk l cs h _ =>
    rw [withAlternatives_node_of_not_licenses lex h]; exact WithAlternatives.WellFormed.unfeatured _

theorem reachable_of_mem_withAlternatives {source : Set (Tree C W)} (lex : Finset (Tree C W))
    (hlex : ↑lex ⊆ source) (φ : Tree C W) :
    ∀ ψ ∈ (withAlternatives lex φ).alternatives,
      Relation.ReflTransGen (StructuralOp source) φ ψ := by
  induction φ using Tree.rec' with
  | terminal c w =>
    intro ψ hψ
    rcases hψ with rfl | ⟨hlex', hcat⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (StructuralOp.subst hcat (hlex (Finset.mem_coe.2 hlex')))
  | node c cs ih =>
    intro ψ hψ
    obtain ⟨cs', hcs', rfl⟩ := WithAlternatives.mem_alternatives_map.1 hψ
    clear hψ
    have h : List.Forall₂ (Relation.ReflTransGen (StructuralOp source)) cs cs' := by
      induction cs generalizing cs' with
      | nil =>
        have h : cs' ∈ ({[]} : Set (List (Tree C W))) := by
          simpa [withAlternatives.list, WithAlternatives.alternatives_pure] using hcs'
        obtain rfl := Set.mem_singleton_iff.1 h
        exact List.Forall₂.nil
      | cons t ts ihts =>
        obtain ⟨g, hg, bs, hbs, rfl⟩ := WithAlternatives.mem_alternatives_seq.1 hcs'
        obtain ⟨b, hb, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hg
        exact List.Forall₂.cons (ih t List.mem_cons_self b hb)
          (ihts (fun s hs ↦ ih s (List.mem_cons_of_mem _ hs)) bs hbs)
    exact pointwise_reachable (l := .node c) trivial h.length_eq.symm fun i hi ↦
      h.get hi (h.length_eq ▸ hi)
  | adjoin c cs ih =>
    intro ψ hψ
    obtain ⟨cs', hcs', rfl⟩ := WithAlternatives.mem_alternatives_map.1 hψ
    clear hψ
    have h : List.Forall₂ (Relation.ReflTransGen (StructuralOp source)) cs cs' := by
      induction cs generalizing cs' with
      | nil =>
        have h : cs' ∈ ({[]} : Set (List (Tree C W))) := by
          simpa [withAlternatives.list, WithAlternatives.alternatives_pure] using hcs'
        obtain rfl := Set.mem_singleton_iff.1 h
        exact List.Forall₂.nil
      | cons t ts ihts =>
        obtain ⟨g, hg, bs, hbs, rfl⟩ := WithAlternatives.mem_alternatives_seq.1 hcs'
        obtain ⟨b, hb, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hg
        exact List.Forall₂.cons (ih t List.mem_cons_self b hb)
          (ihts (fun s hs ↦ ih s (List.mem_cons_of_mem _ hs)) bs hbs)
    exact pointwise_reachable (l := .segment c) trivial h.length_eq.symm fun i hi ↦
      h.get hi (h.length_eq ▸ hi)
  | trace n c =>
    intro ψ hψ
    have h : ψ ∈ ({Tree.trace n c} : Set (Tree C W)) := by
      simpa [withAlternatives, WithAlternatives.alternatives_pure] using hψ
    obtain rfl := Set.mem_singleton_iff.1 h
    exact Relation.ReflTransGen.refl
  | bind n c body ih =>
    intro ψ hψ
    obtain ⟨body', hb, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hψ
    exact lift_bind (ih body' hb)
  | junk l cs hj _ =>
    intro ψ hψ
    rw [withAlternatives_node_of_not_licenses lex hj] at hψ
    have h : ψ ∈ ({RoseTree.node l cs} : Set (Tree C W)) := by
      simpa [WithAlternatives.alternatives_pure] using hψ
    obtain rfl := Set.mem_singleton_iff.1 h
    exact Relation.ReflTransGen.refl

/-- In the compositional fragment, the alternatives the Hamblin engine evokes from the lexicon are
structural alternatives. -/
theorem alternatives_withAlternatives_subset (lex : Finset (Tree C W)) (φ : Tree C W) :
    (withAlternatives lex φ).alternatives ⊆ structuralAlternatives lex φ :=
  reachable_of_mem_withAlternatives lex Set.subset_union_left φ

end PhraseStructure.Tree
