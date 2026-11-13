module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Data.Finset.Basic
public import Linglib.Core.Data.RoseTree.Rewrite
public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Alternatives.WithAlternatives

/-!
# Structural alternatives

The *structural alternatives* of a parse tree are the trees obtainable from it by deletion,
contraction, and substitution of a constituent by a same-category item of the substitution
source, the lexicon together with the tree's own subtrees. A tree is *at most as complex* as
another if these operations reach it from the other (definition (19)), and the structural
alternatives of a tree are the trees at most as complex as it (definition (20)). Structural
alternatives are one source of alternatives for presuppositional strengthening and the
conversational principles.

## Main definitions

* `substitutionSource` — the lexicon together with the subtrees of the host.
* `StructuralOp`, `atMostAsComplex`, `equalComplexity` — one operation at a constituent, the
  chains of operations at any constituent as a preorder, and the equal-complexity equivalence.
* `structuralAlternatives` — the trees at most as complex as the host over its source.
* `Substitutes`, `substitutionAlternatives` — replacement alone, of any category.
* `withAlternatives` — the Hamblin composition of a tree over a lexicon, a `WithAlternatives`
  value.

## Main results

* `licensed_of_atMostAsComplex` — the operations leave a tree licensed by any relation that survives
  deleting a daughter and replacing one by another of its category; `phrase_preservation`, no phrase
  of a category absent from the host and the source, is what excludes the symmetric alternatives.
* `atMostAsComplex.numNodes_le` — over a source of terminals, complexity bounds size.
* `horn_alternatives_are_structural` — substituting a same-category lexical item throughout a tree
  is a chain of substitutions, so Horn-scale alternatives are structural alternatives.
* `alternatives_withAlternatives_subset` — the Hamblin composition of `WithAlternatives`, with each
  terminal evoking its same-category lexical items, generates only structural alternatives;
  deletion and contraction, which act on the whole tree, lie outside any pointwise composition.

## Implementation notes

`atMostAsComplex` is the paper's (19), reachability by finitely many operations, over a source
given as an argument. Over `substitutionSource`, which holds the tree itself, it bounds no size: a
tree with a same-category constituent can replace that constituent by the whole. The paper draws
the replacements that make `ψ` at most as complex as `φ` from the substitution source of `φ`, so
its equal complexity uses each tree's own source for one direction, where `equalComplexity` uses
one source for both. An operation applies at any constituent, the body of a binder, which the
paper's trees lack, included.

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

/-- A structural operation on a parse tree substitutes it by a same-category item of the source,
deletes one of its children, or contracts it to one of its same-category children, the last two
when it is a phrase, a projection or an adjunction structure. `RoseTree.Rewrites` applies an
operation at any constituent. -/
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

/-- `ψ` is at most as complex as `φ` when a chain of structural operations over the source
leads from `φ` to `ψ`, the paper's definition (19) as a reachability preorder. -/
def atMostAsComplex (source : Set (Tree C W)) (ψ φ : Tree C W) : Prop :=
  Relation.ReflTransGen (RoseTree.Rewrites (StructuralOp source)) φ ψ

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
  ⟨Relation.ReflTransGen.single (.here (StructuralOp.subst rfl h_old)),
   Relation.ReflTransGen.single (.here (StructuralOp.subst rfl h_new))⟩

/-- The structural alternatives of `φ`, the paper's definition (20), are the trees at most as
complex as `φ` over its substitution source. -/
def structuralAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) : Set (Tree C W) :=
  {ψ | atMostAsComplex (substitutionSource lex φ) ψ φ}

theorem self_mem_structuralAlternatives (lex : Finset (Tree C W)) (φ : Tree C W) :
    φ ∈ structuralAlternatives lex φ :=
  Relation.ReflTransGen.refl

/-! ### Substitution alone

[fox-katzir-2011] simplify the complexity relation to successive replacement of a sub-constituent
by an element of the substitution source, of any category, without deletion or contraction. The
relation makes no use of the labels, so it is stated for every rose tree. -/

section Substitutes

variable {α : Type*}

/-- One replacement of a sub-constituent with an element of the substitution source. -/
def Substitutes (source : Set (RoseTree α)) : RoseTree α → RoseTree α → Prop :=
  RoseTree.Rewrites fun _ s ↦ s ∈ source

/-- What successive replacements from the source derive from `φ`. -/
def substitutionAlternatives (source : Set (RoseTree α)) (φ : RoseTree α) : Set (RoseTree α) :=
  {ψ | Relation.ReflTransGen (Substitutes source) φ ψ}

theorem self_mem_substitutionAlternatives (source : Set (RoseTree α)) (φ : RoseTree α) :
    φ ∈ substitutionAlternatives source φ :=
  Relation.ReflTransGen.refl

theorem subset_substitutionAlternatives (source : Set (RoseTree α)) (φ : RoseTree α) :
    source ⊆ substitutionAlternatives source φ :=
  fun _ h ↦ .single (.here h)

end Substitutes

/-! ### Preservation -/

/-- An operation preserves the category of the tree it acts on. -/
theorem StructuralOp.cat_eq {source : Set (Tree C W)} {φ ψ : Tree C W}
    (h : StructuralOp source φ ψ) : Tree.cat ψ = Tree.cat φ := by
  cases h with
  | subst hc _ => exact hc
  | delete _ _ => rfl
  | contract _ hc _ => exact hc

theorem cat_eq_of_rewrites {source : Set (Tree C W)} {φ ψ : Tree C W}
    (h : RoseTree.Rewrites (StructuralOp source) φ ψ) : Tree.cat ψ = Tree.cat φ := by
  cases h with
  | here h => exact h.cat_eq
  | child => rfl

/-- At most as complex a tree has the same category. -/
theorem atMostAsComplex.cat_eq {source : Set (Tree C W)} {φ ψ : Tree C W}
    (h : atMostAsComplex source ψ φ) : Tree.cat ψ = Tree.cat φ := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact (cat_eq_of_rewrites h).trans ih

section Licensed

variable {source : Set (Tree C W)} {R : Tree.Label C W → List (Tree.Label C W) → Prop}

private theorem licensed_of_op {K : C → Prop} (hK : ∀ l ks, R l ks → K (Label.cat l))
    (h_source : ∀ s ∈ source, K (Tree.cat s) → s.Licensed R)
    (h_delete : ∀ l ks i, l.IsPhrase → R l ks → R l (ks.eraseIdx i))
    (h_set : ∀ l ks₁ k k' ks₂, Label.cat k' = Label.cat k → R l (ks₁ ++ k :: ks₂) →
      R l (ks₁ ++ k' :: ks₂))
    {φ ψ : Tree C W} (h : RoseTree.Rewrites (StructuralOp source) φ ψ) (hφ : φ.Licensed R) :
    ψ.Licensed R := by
  induction h with
  | @here x _ h =>
    cases h with
    | subst hc hs =>
      obtain ⟨l, cs⟩ := x
      exact h_source _ hs (hc ▸ hK _ _ hφ.rel_root)
    | @delete l cs i hl =>
      obtain ⟨hr, hc⟩ := RoseTree.licensed_node_iff.1 hφ
      refine RoseTree.licensed_node_iff.2
        ⟨?_, fun c hm ↦ hc c ((List.eraseIdx_sublist cs i).subset hm)⟩
      simpa only [List.eraseIdx_eq_take_drop_succ, List.map_append, List.map_take, List.map_drop]
        using h_delete l _ i hl hr
    | contract hmem _ _ => exact (RoseTree.licensed_node_iff.1 hφ).2 _ hmem
  | @child a l₁ c c' l₂ hstep ih =>
    obtain ⟨hr, hc⟩ := RoseTree.licensed_node_iff.1 hφ
    refine RoseTree.licensed_node_iff.2 ⟨?_, fun x hm ↦ ?_⟩
    · simpa using h_set a (l₁.map RoseTree.value) c.value c'.value (l₂.map RoseTree.value)
        (by simpa [Tree.cat] using cat_eq_of_rewrites hstep) (by simpa using hr)
    · rcases List.mem_append.1 hm with h | h
      · exact hc x (by simp [h])
      · rcases List.mem_cons.1 h with rfl | h
        · exact ih (hc c (by simp))
        · exact hc x (by simp [h])

/-- A tree no more complex than a licensed tree is licensed, when the local trees survive deleting
a daughter and replacing one by another of its category, and the source items are licensed whose
category `K` admits, `K` holding of the category of every node `R` licenses: no other item can
replace a constituent. -/
theorem licensed_of_atMostAsComplex_of_cat {K : C → Prop}
    (hK : ∀ l ks, R l ks → K (Label.cat l))
    (h_source : ∀ s ∈ source, K (Tree.cat s) → s.Licensed R)
    (h_delete : ∀ l ks i, l.IsPhrase → R l ks → R l (ks.eraseIdx i))
    (h_set : ∀ l ks₁ k k' ks₂, Label.cat k' = Label.cat k → R l (ks₁ ++ k :: ks₂) →
      R l (ks₁ ++ k' :: ks₂))
    {φ ψ : Tree C W} (hφ : φ.Licensed R) (h : atMostAsComplex source ψ φ) : ψ.Licensed R := by
  induction h with
  | refl => exact hφ
  | tail _ h ih => exact licensed_of_op hK h_source h_delete h_set h ih

/-- A tree no more complex than a licensed tree over a licensed source is licensed, when the local
trees survive deleting a daughter and replacing one by another of its category. -/
theorem licensed_of_atMostAsComplex (h_source : ∀ s ∈ source, s.Licensed R)
    (h_delete : ∀ l ks i, l.IsPhrase → R l ks → R l (ks.eraseIdx i))
    (h_set : ∀ l ks₁ k k' ks₂, Label.cat k' = Label.cat k → R l (ks₁ ++ k :: ks₂) →
      R l (ks₁ ++ k' :: ks₂))
    {φ ψ : Tree C W} (hφ : φ.Licensed R) (h : atMostAsComplex source ψ φ) : ψ.Licensed R :=
  licensed_of_atMostAsComplex_of_cat (K := fun _ ↦ True) (fun _ _ _ ↦ trivial)
    (fun s hs _ ↦ h_source s hs) h_delete h_set hφ h

end Licensed

/-- If neither the host nor any source item has a phrase (a node or adjunction structure) of
category `c`, no structural alternative has one. -/
theorem phrase_preservation (source : Set (Tree C W)) (c : C)
    (h_source : ∀ s ∈ source, ∀ t ∈ s.subtrees, ¬ (t.value.IsPhrase ∧ Tree.cat t = c))
    {φ ψ : Tree C W} (h_φ : ∀ t ∈ φ.subtrees, ¬ (t.value.IsPhrase ∧ Tree.cat t = c))
    (h_reach : atMostAsComplex source ψ φ) :
    ∀ t ∈ ψ.subtrees, ¬ (t.value.IsPhrase ∧ Tree.cat t = c) := by
  have key {t : Tree C W} : t.Licensed (fun l _ ↦ ¬ (l.IsPhrase ∧ l.cat = c)) ↔
      ∀ s ∈ t.subtrees, ¬ (s.value.IsPhrase ∧ Tree.cat s = c) :=
    RoseTree.licensed_iff_forall_mem_subtrees
  exact key.1 (licensed_of_atMostAsComplex (fun s hs ↦ key.2 (h_source s hs))
    (fun _ _ _ _ ↦ id) (fun _ _ _ _ _ _ ↦ id) (key.2 h_φ) h_reach)

/-- Over a source of terminals, at most as complex a tree has no more nodes: the plain notion of
complexity bounds size, where a source holding the tree itself does not. -/
theorem atMostAsComplex.numNodes_le {source : Set (Tree C W)}
    (hs : ∀ t ∈ source, RoseTree.numNodes t = 1) {φ ψ : Tree C W}
    (h : atMostAsComplex source ψ φ) : RoseTree.numNodes ψ ≤ RoseTree.numNodes φ := by
  have step {φ ψ : Tree C W} (h : RoseTree.Rewrites (StructuralOp source) φ ψ) :
      RoseTree.numNodes ψ ≤ RoseTree.numNodes φ := by
    induction h with
    | here h =>
      cases h with
      | subst _ hsrc => rw [hs _ hsrc]; exact RoseTree.numNodes_pos _
      | @delete l cs i =>
        simp only [RoseTree.numNodes_node]
        exact Nat.succ_le_succ
          (((List.eraseIdx_sublist cs i).map _).sum_le_sum fun _ _ ↦ Nat.zero_le _)
      | @contract l cs child hmem _ =>
        rw [RoseTree.numNodes_node]
        have := List.single_le_sum (l := cs.map RoseTree.numNodes) (fun _ _ ↦ Nat.zero_le _) _
          (List.mem_map_of_mem hmem)
        omega
    | child a l₁ l₂ _ ih =>
      simp only [RoseTree.numNodes_node, List.map_append, List.map_cons, List.sum_append,
        List.sum_cons]
      omega
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact (step h).trans ih

/-! ### Horn scales are structural alternatives -/

private theorem leafSubst_reachable [DecidableEq C] [DecidableEq W] {source : Set (Tree C W)}
    (α β : W) (c : C) (h_β : Tree.terminal c β ∈ source) (φ : Tree C W) (hφ : φ.IsWellFormed) :
    Relation.ReflTransGen (RoseTree.Rewrites (StructuralOp source)) φ (φ.leafSubst α β c) := by
  induction φ using Tree.rec' with
  | terminal c' w =>
    rw [Tree.leafSubst_terminal]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact .single (.here (StructuralOp.subst rfl h_β))
    · exact .refl
  | phrase c' k cs ih =>
    rw [Tree.leafSubst_phrase]
    exact RoseTree.reflTransGen_rewrites_node _ [] (List.forall₂_map_right_iff.2
      (List.forall₂_same.2 fun t ht ↦ ih t ht (RoseTree.Licensed.of_mem hφ ht)))
  | trace n c' => exact .refl
  | bind n c' body ih =>
    rw [Tree.leafSubst_bind]
    exact RoseTree.reflTransGen_rewrites_node _ []
      (.cons (ih (RoseTree.Licensed.of_mem hφ List.mem_cons_self)) .nil)
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
  | .phrase c k cs => Tree.phrase c k <$> list lex cs
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
  | phrase c k => exact absurd trivial h
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
  | phrase c k cs ih =>
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
  | phrase c k cs ih =>
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
      Relation.ReflTransGen (RoseTree.Rewrites (StructuralOp source)) φ ψ := by
  induction φ using Tree.rec' with
  | terminal c w =>
    intro ψ hψ
    rcases hψ with rfl | ⟨hlex', hcat⟩
    · exact Relation.ReflTransGen.refl
    · exact .single (.here (StructuralOp.subst hcat (hlex (Finset.mem_coe.2 hlex'))))
  | phrase c k cs ih =>
    intro ψ hψ
    obtain ⟨cs', hcs', rfl⟩ := WithAlternatives.mem_alternatives_map.1 hψ
    clear hψ
    have h : List.Forall₂ (Relation.ReflTransGen (RoseTree.Rewrites (StructuralOp source)))
        cs cs' := by
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
    exact RoseTree.reflTransGen_rewrites_node _ [] h
  | trace n c =>
    intro ψ hψ
    have h : ψ ∈ ({Tree.trace n c} : Set (Tree C W)) := by
      simpa [withAlternatives, WithAlternatives.alternatives_pure] using hψ
    obtain rfl := Set.mem_singleton_iff.1 h
    exact Relation.ReflTransGen.refl
  | bind n c body ih =>
    intro ψ hψ
    obtain ⟨body', hb, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hψ
    exact RoseTree.reflTransGen_rewrites_node _ [] (.cons (ih body' hb) .nil)
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
