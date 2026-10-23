module

public import Linglib.Core.Data.UnorderedTree.Leaves
public import Mathlib.Logic.Relation
public import Linglib.Core.Algebra.Order.Group.Multiset
public import Linglib.Core.Data.UnorderedTree.FilterMap
public import Linglib.Core.Data.UnorderedTree.DecEq
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Basic

/-!
# Senturia and Marcolli (2025): The Algebraic Structure of Morphosyntax

This file formalizes the Distributed Morphology operations of [senturia-marcolli-2025], which
models morphology inside the Merge algebra of [marcolli-chomsky-berwick-2025]. A morphological
object is built by the same free non-associative commutative magma as a syntactic object, with
features in place of lexical items, and differs from it only in labeling: an internal vertex
carries the union of its children's feature bundles (Definition 2.1), so a bundle is derived
from the tree (`bundle`, `bundle_fuse`). A morphosyntactic tree inserts morphological objects
at the leaves of a syntactic tree under the syntax-morphology feature correspondence
(Definitions 2.4 and 3.4; `FeatureCorrespondence`, `Morphosyntactic`, `Matched`), and
forgetting the inserted morphology is the morphism of algebras over the Merge operad of
Definition 3.9 (`toSyntactic`).

On this carrier the four operations reduce to two. Fusion is the magma product itself
(Definition 5.2, `fuse`), which is why it is the one operation available inside syntax.
Fission restricts the tree vertex-wise along a partition of its bundle with a copied residue
(Definition 5.6, `restrict`) and duplicates exactly that residue (`msFeatures_fissionSite_copy`).
Impoverishment keeps one fission output and obliteration empties an insertion (Propositions
5.13 and 5.20), so both derive from fission (Proposition 5.21). Fission followed by fusion
restores the bundle but not the tree (`bundle_fuse_restrict`, `fuse_restrict_ne`, the paper's
Example 5.7). Closing the site relations under congruence gives the post-syntactic and
Distributed Morphology semigroups of Definition 6.1 as rewrite relations (`PostSyntactic`,
`Derivation`): along the first the total feature set is invariant while the boundary between
syntax and morphology moves one leaf at a time (`PostSyntactic.toFinset_msFeatures_eq`,
`Step.numLeaves_fuse`, `Step.numLeaves_fiss`); along the second the feature set can only
shrink (`Derivation.toFinset_msFeatures_subset`).

## Implementation notes

* Morphological objects are unordered trees over `F ⊕ Unit`, features at the leaves and bare
  structural vertices elsewhere. `IsMorphological` does not constrain arity, so the theorems
  cover the paper's binary objects and the non-branching extended objects of Definition 2.8
  alike. Restriction keeps a structural vertex whose leaves all vanish as a childless vertex
  where the quotient of Definition 5.6 removes it; both carry the empty bundle.
* A morphosyntactic tree is kept in labeled form, each syntactic leaf carrying its datum and
  the inserted object, `none` for the empty insertion of Remark 5.12; this carries the same
  data as splicing the object below the leaf.
* The operations are stated as transformations of morphosyntactic trees, the first of the
  paper's two equivalent perspectives; the semigroups act on trees rather than on the assembly
  operations of Definition 4.2.

## TODO

The workspace Hopf algebra with obliteration via the coproduct, and the colored correspondence
between the syntactic and morphosyntactic algebras over the Merge operad (Theorem 3.16).

## References

* [senturia-marcolli-2025]
* [marcolli-chomsky-berwick-2025]
* [hewett-2023]
-/

@[expose] public section

namespace SenturiaMarcolli2025

open RoseTree

variable {F : Type*} [DecidableEq F]

/-! ### Morphological objects and the derived bundle labeling

A morphological object is a nonplanar tree with single features at the
leaves and bare structural vertices elsewhere — the alphabet `F ⊕ Unit`,
exactly the carrier shape of syntactic objects with features in place of
the lexical items. Definition 2.1 of [senturia-marcolli-2025] labels
each internal vertex with the union of its children's bundles, so every
vertex label is determined by the leaves below it; `bundle` is the
root's. -/

/-- Features occur only at leaves: internal vertices are structural.
Arity is not constrained, so the predicate covers the paper's binary
objects and the non-branching extended objects of Definition 2.8 that
restriction produces. -/
inductive IsMorphological : RoseTree (F ⊕ Unit) → Prop
  | leaf (x : F ⊕ Unit) : IsMorphological (.node x [])
  | node {cs : List (RoseTree (F ⊕ Unit))} (hne : cs ≠ [])
      (h : ∀ c ∈ cs, IsMorphological c) : IsMorphological (.node (.inr ()) cs)

/-- The multiset of leaf features of a planar tree. -/
def leafFeatures (t : RoseTree (F ⊕ Unit)) : Multiset F :=
  t.leaves.filterMap Sum.getLeft?

/-- The feature bundle of a morphological object: the set of features at
its leaves, the root label of [senturia-marcolli-2025] Definition 2.1. -/
def bundle (S : UnorderedTree (F ⊕ Unit)) : Finset F :=
  (S.leaves.filterMap Sum.getLeft?).toFinset

@[simp] theorem bundle_mk (t : RoseTree (F ⊕ Unit)) :
    bundle (UnorderedTree.mk t) = (leafFeatures t).toFinset := rfl

@[simp] theorem bundle_leaf (f : F) :
    bundle (UnorderedTree.leaf (.inl f)) = {f} := by
  rw [show bundle (UnorderedTree.leaf (.inl f)) = ({f} : Multiset F).toFinset from rfl]
  exact Multiset.toFinset_singleton f

@[simp] theorem bundle_leaf_inr :
    bundle (UnorderedTree.leaf (.inr () : F ⊕ Unit)) = ∅ := rfl

/-- The multiset of leaf features of a morphological object; `bundle` is
its underlying set. Fission with an overlapping partition duplicates
features, which only the multiset records. -/
def features (S : UnorderedTree (F ⊕ Unit)) : Multiset F :=
  S.leaves.filterMap Sum.getLeft?

omit [DecidableEq F] in
@[simp] theorem features_mk (t : RoseTree (F ⊕ Unit)) :
    features (UnorderedTree.mk t) = leafFeatures t := rfl

theorem bundle_eq_toFinset_features (S : UnorderedTree (F ⊕ Unit)) :
    bundle S = (features S).toFinset := rfl

omit [DecidableEq F] in
theorem leafFeatures_node_inr (cs : List (RoseTree (F ⊕ Unit))) :
    leafFeatures (.node (.inr ()) cs) = (cs.map leafFeatures).sum := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    rw [leafFeatures, leaves_node_cons, ← Multiset.coe_filterMapAddMonoidHom, map_list_sum,
      List.map_map]
    rfl

/-! ### Fusion

Fusion merges the bundles at two adjacent leaves of the syntactic tree
into one ([senturia-marcolli-2025] §5.1, Swahili negation *si-* fusing
NEG with first-singular agreement). On morphological objects it is the
magma operation itself — grafting under a fresh structural root — which
is why fusion is the one DM operation available inside syntax. -/

/-- Fusion of two morphological objects: the magma product, grafting
both under a structural root ([senturia-marcolli-2025] Definition 5.2). -/
noncomputable def fuse (S₁ S₂ : UnorderedTree (F ⊕ Unit)) : UnorderedTree (F ⊕ Unit) :=
  UnorderedTree.node (.inr ()) {S₁, S₂}

theorem bundle_fuse (S₁ S₂ : UnorderedTree (F ⊕ Unit)) :
    bundle (fuse S₁ S₂) = bundle S₁ ∪ bundle S₂ := by
  refine Quotient.inductionOn₂ S₁ S₂ fun p q ↦ ?_
  show bundle (UnorderedTree.node (.inr ()) {UnorderedTree.mk p, UnorderedTree.mk q}) = _
  rw [UnorderedTree.node_pair_mk]
  simp only [bundle_mk, leafFeatures_node_inr, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Multiset.toFinset_add]
  rfl

omit [DecidableEq F] in
theorem features_fuse (S₁ S₂ : UnorderedTree (F ⊕ Unit)) :
    features (fuse S₁ S₂) = features S₁ + features S₂ := by
  refine Quotient.inductionOn₂ S₁ S₂ fun p q ↦ ?_
  show features (UnorderedTree.node (.inr ()) {UnorderedTree.mk p, UnorderedTree.mk q}) = _
  rw [UnorderedTree.node_pair_mk]
  simp only [features_mk, leafFeatures_node_inr, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rfl

/-! ### Fission

Fission splits one bundle into two along a partition `B ∖ A = B₁ ⊔ B₂`,
with the residue `A` copied into both outputs ([senturia-marcolli-2025]
§5.2; the discontinuous agreement of Ṣanʕānī Arabic after [hewett-2023],
where person and number of a single head surface as prefix and suffix).
Each output is the input
tree restricted vertex-wise to the kept features: leaves outside the
kept set are deleted, structural vertices stay, and vanished subtrees
may leave non-branching structural vertices behind — the extended
morphological objects. -/

/-- Keep a leaf feature iff it lies in `C`; structural vertices always
survive. -/
def keep (C : Finset F) : F ⊕ Unit → Option (F ⊕ Unit)
  | .inl f => if f ∈ C then some (.inl f) else none
  | .inr _ => some (.inr ())

/-- Restriction of a morphological object to the features in `C`: the
construction of a single fission output ([senturia-marcolli-2025]
Definition 5.6, with `C = Bᵢ ∪ A`). `none` only for a single leaf
outside `C`. -/
def restrict (C : Finset F) (S : UnorderedTree (F ⊕ Unit)) :
    Option (UnorderedTree (F ⊕ Unit)) :=
  S.filterMap (keep C)

private theorem sum_leafFeatures_filterMap (C : Finset F)
    (cs : List (RoseTree (F ⊕ Unit)))
    (ih : ∀ c ∈ cs, ((c.filterMap (keep C)).elim 0 leafFeatures)
      = (leafFeatures c).filter (· ∈ C)) :
    ((cs.filterMap (RoseTree.filterMap (keep C))).map leafFeatures).sum
      = ((cs.map leafFeatures).sum).filter (· ∈ C) := by
  induction cs with
  | nil => simp
  | cons c cs ihcs =>
    have hc := ih c (List.mem_cons_self ..)
    have hrest := ihcs fun d hd ↦ ih d (List.mem_cons_of_mem _ hd)
    cases hcc : RoseTree.filterMap (keep C) c with
    | none =>
      rw [hcc, Option.elim_none] at hc
      rw [List.filterMap_cons_none hcc]
      simp only [List.map_cons, List.sum_cons, Multiset.filter_add, ← hc,
        hrest, zero_add]
    | some c' =>
      rw [hcc, Option.elim_some] at hc
      rw [List.filterMap_cons_some hcc]
      simp only [List.map_cons, List.sum_cons, Multiset.filter_add, ← hc, hrest]

private theorem leafFeatures_filterMap_keep (C : Finset F)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t) :
    ((t.filterMap (keep C)).elim 0 leafFeatures)
      = (leafFeatures t).filter (· ∈ C) := by
  induction ht with
  | leaf x =>
    cases x with
    | inl f =>
      have e : Multiset.filterMap Sum.getLeft? ({Sum.inl f} : Multiset (F ⊕ Unit))
          = ({f} : Multiset F) := rfl
      by_cases hf : f ∈ C <;>
        simp [keep, hf, leafFeatures, e, Multiset.filter_singleton]
    | inr u =>
      have e : Multiset.filterMap Sum.getLeft? ({Sum.inr u} : Multiset (F ⊕ Unit))
          = (0 : Multiset F) := rfl
      simp [keep, leafFeatures, e]
  | @node cs hne h ih =>
    rw [RoseTree.filterMap_node, keep, Option.map_some, Option.elim_some, leafFeatures_node_inr,
      leafFeatures_node_inr]
    exact sum_leafFeatures_filterMap C cs ih

/-- The bundle of a fission output is the input bundle restricted to the kept features, at the root
([senturia-marcolli-2025] Definition 5.6). -/
theorem bundle_restrict {C : Finset F} {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) {S' : UnorderedTree (F ⊕ Unit)}
    (h : restrict C (UnorderedTree.mk t) = some S') :
    bundle S' = bundle (UnorderedTree.mk t) ∩ C := by
  rw [restrict, UnorderedTree.filterMap_mk] at h
  cases hc : t.filterMap (keep C) with
  | none => rw [hc, Option.map_none] at h; exact absurd h (by simp)
  | some t' =>
    rw [hc, Option.map_some, Option.some.injEq] at h
    subst h
    have key := leafFeatures_filterMap_keep C ht
    rw [hc, Option.elim_some] at key
    rw [bundle_mk, bundle_mk, key, Multiset.toFinset_filter,
      Finset.filter_mem_eq_inter]

theorem features_restrict (C : Finset F) {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) :
    (restrict C (UnorderedTree.mk t)).elim 0 features
      = (features (UnorderedTree.mk t)).filter (· ∈ C) := by
  rw [restrict, UnorderedTree.filterMap_mk]
  have key := leafFeatures_filterMap_keep C ht
  cases hc : t.filterMap (keep C) with
  | none => rw [hc, Option.elim_none] at key; simpa using key
  | some t' => rw [hc, Option.elim_some] at key; simpa using key

theorem restrict_copies_shared {A C₁ C₂ : Finset F}
    (h₁ : A ⊆ C₁) (h₂ : A ⊆ C₂) {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) {S₁' S₂' : UnorderedTree (F ⊕ Unit)}
    (e₁ : restrict C₁ (UnorderedTree.mk t) = some S₁')
    (e₂ : restrict C₂ (UnorderedTree.mk t) = some S₂') :
    A ∩ bundle (UnorderedTree.mk t) ⊆ bundle S₁' ∩ bundle S₂' := by
  rw [bundle_restrict ht e₁, bundle_restrict ht e₂]
  intro f hf
  simp only [Finset.mem_inter] at hf ⊢
  exact ⟨⟨hf.2, h₁ hf.1⟩, hf.2, h₂ hf.1⟩

/-! ### Impoverishment as fission plus fusion

[senturia-marcolli-2025] Propositions 5.20–5.21: impoverishment and
obliteration are not independent operations. Discarding a subbundle is
keeping one fission output (`bundle_restrict` with the kept part as
`C`); the trace-maintaining variant fissions and refuses at the same
vertex, restoring the bundle without restoring the tree. Obliteration
replaces a whole morphological object by the unit of the workspace
algebra, which lives in the second slice. -/

theorem bundle_fuse_restrict {C₁ C₂ : Finset F} {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t) (hcover : bundle (UnorderedTree.mk t) ⊆ C₁ ∪ C₂)
    {S₁' S₂' : UnorderedTree (F ⊕ Unit)}
    (e₁ : restrict C₁ (UnorderedTree.mk t) = some S₁')
    (e₂ : restrict C₂ (UnorderedTree.mk t) = some S₂') :
    bundle (fuse S₁' S₂') = bundle (UnorderedTree.mk t) := by
  rw [bundle_fuse, bundle_restrict ht e₁, bundle_restrict ht e₂,
    ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hcover]

/-! ### The tree is not restored

Fission at a partition whose residue is copied into both outputs, then
fusion, restores the bundle but not the tree: the copied feature now
occupies a leaf on each side, so the composite has strictly more leaves.
The witness is [senturia-marcolli-2025] Example 5.7: `[φ, α, β, γ]` with
kept sets `[φ, γ]` and `[φ, α, β]`. -/

inductive Feat where
  | phi | alpha | beta | gamma
  deriving DecidableEq, Repr

def exTree : RoseTree (Feat ⊕ Unit) :=
  .node (.inr ()) [.node (.inr ()) [.node (.inl .phi) [], .node (.inl .alpha) []],
    .node (.inr ()) [.node (.inl .beta) [], .node (.inl .gamma) []]]

theorem fuse_restrict_ne (S₁' S₂' : UnorderedTree (Feat ⊕ Unit))
    (e₁ : restrict {.phi, .gamma} (UnorderedTree.mk exTree) = some S₁')
    (e₂ : restrict {.phi, .alpha, .beta} (UnorderedTree.mk exTree) = some S₂') :
    fuse S₁' S₂' ≠ UnorderedTree.mk exTree := by
  have c₁ : exTree.filterMap (keep {.phi, .gamma})
      = some (.node (.inr ()) [.node (.inr ()) [.node (.inl .phi) []],
          .node (.inr ()) [.node (.inl .gamma) []]]) := by decide
  have c₂ : exTree.filterMap (keep {.phi, .alpha, .beta})
      = some (.node (.inr ()) [.node (.inr ()) [.node (.inl .phi) [],
          .node (.inl .alpha) []], .node (.inr ()) [.node (.inl .beta) []]]) := by
    decide
  rw [restrict, UnorderedTree.filterMap_mk, c₁, Option.map_some,
    Option.some.injEq] at e₁
  rw [restrict, UnorderedTree.filterMap_mk, c₂, Option.map_some,
    Option.some.injEq] at e₂
  subst e₁ e₂
  rw [fuse, UnorderedTree.node_pair_mk]
  intro hcontra
  have := congrArg UnorderedTree.numLeaves hcontra
  rw [UnorderedTree.numLeaves_mk, UnorderedTree.numLeaves_mk] at this
  exact absurd this (by decide)

/-! ### The syntax-morphology correspondence and morphosyntactic trees

A morphosyntactic tree inserts morphological objects at the leaves of a
syntactic tree, constrained by a matching rule between the bundle at the
root of the inserted object and the syntactic datum at the leaf
([senturia-marcolli-2025] Definitions 2.4 and 3.4). We keep the
insertion as a leaf label — syntactic datum paired with the inserted
object — which carries the same data as splicing the object below the
leaf. -/

/-- The syntax-morphology feature correspondence: which feature bundles
can be matched with which lexical items and syntactic features
([senturia-marcolli-2025] Definition 2.4). Matching is multivalued in
both directions, but every syntactic datum carries some bundle. -/
structure FeatureCorrespondence (F Λ : Type*) [DecidableEq F] where
  /-- `matching B lex` iff the bundle `B` can decorate a leaf carrying
  the syntactic datum `lex`. -/
  matching : Finset F → Λ → Prop
  /-- Every syntactic datum carries some bundle. -/
  matching_surjective : ∀ lex : Λ, ∃ B, matching B lex

/-- A morphosyntactic tree in labeled form: each syntactic leaf carries
its datum together with the inserted morphological object, `none` where
morphology was obliterated ([senturia-marcolli-2025] Definition 3.4; the
empty insertion is Remark 5.12). -/
abbrev Morphosyntactic (F Λ : Type*) :=
  UnorderedTree ((Λ × Option (UnorderedTree (F ⊕ Unit))) ⊕ Unit)

variable {Λ : Type*}

/-- A leaf of a morphosyntactic tree: a syntactic datum with an optional
morphological insertion. -/
def insertion (lex : Λ) (mo : Option (UnorderedTree (F ⊕ Unit))) :
    Morphosyntactic F Λ :=
  UnorderedTree.leaf (.inl (lex, mo))

/-- The forgetful projection to the syntactic tree: drop the inserted
morphology. This is [senturia-marcolli-2025] Definition 3.9's morphism
of algebras over the Merge operad, in labeled form. -/
def toSyntactic : Morphosyntactic F Λ → UnorderedTree (Λ ⊕ Unit) :=
  UnorderedTree.map (Sum.map Prod.fst id)

omit [DecidableEq F] in
@[simp] theorem toSyntactic_insertion (lex : Λ)
    (mo : Option (UnorderedTree (F ⊕ Unit))) :
    toSyntactic (insertion lex mo) = UnorderedTree.leaf (.inl lex) :=
  UnorderedTree.map_leaf _ _

/-- The feature content of one leaf label. -/
def insertionFeatures : (Λ × Option (UnorderedTree (F ⊕ Unit))) ⊕ Unit → Multiset F
  | .inl (_, some S) => features S
  | .inl (_, none) => 0
  | .inr _ => 0

omit [DecidableEq F] in
@[simp] theorem insertionFeatures_inl (lex : Λ)
    (mo : Option (UnorderedTree (F ⊕ Unit))) :
    insertionFeatures (.inl (lex, mo)) = mo.elim 0 features := by
  cases mo <;> rfl

/-- The total feature content of a morphosyntactic tree: everything its
inserted morphological objects carry, with multiplicity. -/
def msFeatures (T : Morphosyntactic F Λ) : Multiset F :=
  (T.leaves.map insertionFeatures).sum

omit [DecidableEq F] in
@[simp] theorem msFeatures_insertion (lex : Λ)
    (mo : Option (UnorderedTree (F ⊕ Unit))) :
    msFeatures (insertion lex mo) = mo.elim 0 features := by
  simp [msFeatures, insertion]

/-- Every inserted morphological object matches its leaf's syntactic
datum. -/
def Matched (Γ : FeatureCorrespondence F Λ) (T : Morphosyntactic F Λ) : Prop :=
  ∀ lex S, .inl (lex, some S) ∈ T.leaves → Γ.matching (bundle S) lex

theorem matched_insertion_iff (Γ : FeatureCorrespondence F Λ) (lex : Λ)
    (S : UnorderedTree (F ⊕ Unit)) :
    Matched Γ (insertion lex (some S)) ↔ Γ.matching (bundle S) lex := by
  constructor
  · exact fun h ↦ h lex S (by simp [insertion])
  · intro h lex' S' hmem
    simp only [insertion, UnorderedTree.leaves_leaf, Multiset.mem_singleton,
      Sum.inl.injEq, Prod.mk.injEq, Option.some.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    exact h

/-! ### The DM operations at their application site

The four DM operations transform the assembly of a morphosyntactic tree
at one site ([senturia-marcolli-2025] §5–§6). Fusion turns a syntactic
cherry over two insertions into a single insertion of the magma product;
fission turns one insertion into a cherry over its two restrictions.
Under `toSyntactic` the first collapses a cherry and the second grows
one — the movable syntax-morphology boundary — while `msFeatures`
records what happens to the feature content. -/

private theorem leaves_node_pair_leaf {α : Type*} (a x y : α) :
    (UnorderedTree.node a {UnorderedTree.leaf x, UnorderedTree.leaf y}).leaves = {x, y} := by
  simp [UnorderedTree.leaves_node_cons]

/-- The application site of fusion: a syntactic cherry with insertions
at both leaves. -/
noncomputable def fusionSite (lex₁ lex₂ : Λ) (S₁ S₂ : UnorderedTree (F ⊕ Unit)) :
    Morphosyntactic F Λ :=
  UnorderedTree.node (.inr ()) {insertion lex₁ (some S₁), insertion lex₂ (some S₂)}

/-- The application site of fission on `S` along the kept sets `C₁, C₂`:
a syntactic cherry whose leaves carry the two restrictions; an empty
restriction is an empty insertion. -/
noncomputable def fissionSite (lex₁ lex₂ : Λ) (C₁ C₂ : Finset F)
    (S : UnorderedTree (F ⊕ Unit)) : Morphosyntactic F Λ :=
  UnorderedTree.node (.inr ())
    {insertion lex₁ (restrict C₁ S), insertion lex₂ (restrict C₂ S)}

omit [DecidableEq F] in
theorem msFeatures_fusionSite (lex₁ lex₂ : Λ) (S₁ S₂ : UnorderedTree (F ⊕ Unit)) :
    msFeatures (fusionSite lex₁ lex₂ S₁ S₂) = features S₁ + features S₂ := by
  rw [msFeatures, fusionSite, insertion, insertion, leaves_node_pair_leaf]
  simp

omit [DecidableEq F] in
/-- Fusion preserves the total feature content at the site ([senturia-marcolli-2025] Definition
5.2). -/
theorem msFeatures_fuse (lexHead lex₁ lex₂ : Λ)
    (S₁ S₂ : UnorderedTree (F ⊕ Unit)) :
    msFeatures (insertion lexHead (some (fuse S₁ S₂)))
      = msFeatures (fusionSite lex₁ lex₂ S₁ S₂) := by
  rw [msFeatures_insertion, Option.elim_some, features_fuse,
    msFeatures_fusionSite]

omit [DecidableEq F] in
theorem toSyntactic_fusionSite (lex₁ lex₂ : Λ) (S₁ S₂ : UnorderedTree (F ⊕ Unit)) :
    toSyntactic (fusionSite lex₁ lex₂ S₁ S₂)
      = UnorderedTree.node (.inr ())
          {UnorderedTree.leaf (.inl lex₁), UnorderedTree.leaf (.inl lex₂)} := by
  simp only [fusionSite, toSyntactic, UnorderedTree.map_node, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, insertion, UnorderedTree.map_leaf, Sum.map_inl,
    Sum.map_inr, id]

/-- The fused site is matched iff the union of the two bundles matches the projecting datum
([senturia-marcolli-2025], after Definition 5.2). -/
theorem matched_fused_iff (Γ : FeatureCorrespondence F Λ) (lexHead : Λ)
    (S₁ S₂ : UnorderedTree (F ⊕ Unit)) :
    Matched Γ (insertion lexHead (some (fuse S₁ S₂)))
      ↔ Γ.matching (bundle S₁ ∪ bundle S₂) lexHead := by
  rw [matched_insertion_iff, bundle_fuse]

theorem msFeatures_fissionSite (lex₁ lex₂ : Λ) (C₁ C₂ : Finset F)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t) :
    msFeatures (fissionSite lex₁ lex₂ C₁ C₂ (UnorderedTree.mk t))
      = (features (UnorderedTree.mk t)).filter (· ∈ C₁)
        + (features (UnorderedTree.mk t)).filter (· ∈ C₂) := by
  rw [msFeatures, fissionSite, insertion, insertion, leaves_node_pair_leaf]
  simp [features_restrict _ ht]

/-- Fission along a disjoint cover of the bundle preserves the feature
multiset: the boundary moves down (`toSyntactic` grows a cherry) with no
change in feature content. An overlapping partition instead duplicates
the shared residue (`restrict_copies_shared`), which is how the copied
features of discontinuous agreement come to be pronounced twice. -/
theorem msFeatures_fission_partition (lex₁ lex₂ : Λ) {C₁ C₂ : Finset F}
    (hdisj : Disjoint C₁ C₂) {t : RoseTree (F ⊕ Unit)}
    (ht : IsMorphological t)
    (hcover : ∀ f ∈ features (UnorderedTree.mk t), f ∈ C₁ ∪ C₂) :
    msFeatures (fissionSite lex₁ lex₂ C₁ C₂ (UnorderedTree.mk t))
      = features (UnorderedTree.mk t) := by
  rw [msFeatures_fissionSite _ _ _ _ ht, Multiset.filter_add_filter]
  have h₁ : (features (UnorderedTree.mk t)).filter (fun f ↦ f ∈ C₁ ∨ f ∈ C₂)
      = features (UnorderedTree.mk t) :=
    Multiset.filter_eq_self.mpr fun f hf ↦ by
      simpa [Finset.mem_union] using hcover f hf
  have h₂ : (features (UnorderedTree.mk t)).filter (fun f ↦ f ∈ C₁ ∧ f ∈ C₂)
      = 0 :=
    Multiset.filter_eq_nil.mpr fun f _ hf ↦
      Finset.disjoint_left.mp hdisj hf.1 hf.2
  rw [h₁, h₂, add_zero]

/-- Impoverishment at a leaf only removes features: keeping one fission
output ([senturia-marcolli-2025] Proposition 5.20, first case) bounds
the feature content by the original. -/
theorem msFeatures_impoverish_le (lex : Λ) (kept : Finset F)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t) :
    msFeatures (insertion lex (restrict kept (UnorderedTree.mk t)))
      ≤ msFeatures (insertion lex (some (UnorderedTree.mk t))) := by
  rw [msFeatures_insertion, msFeatures_insertion, Option.elim_some,
    features_restrict _ ht]
  exact Multiset.filter_le _ _

omit [DecidableEq F] in
/-- Obliteration leaves the syntactic tree unchanged ([senturia-marcolli-2025] Proposition 5.13). -/
theorem toSyntactic_obliterate (lex : Λ) (S : UnorderedTree (F ⊕ Unit)) :
    toSyntactic (insertion lex none : Morphosyntactic F Λ)
      = toSyntactic (insertion lex (some S)) := by
  rw [toSyntactic_insertion, toSyntactic_insertion]

omit [DecidableEq F] in
@[simp] theorem msFeatures_obliterate (lex : Λ) :
    msFeatures (insertion lex none : Morphosyntactic F Λ) = 0 := by
  rw [msFeatures_insertion, Option.elim_none]

/-! ### One-step transformations and the post-syntactic semigroup

The DM operations act anywhere in a morphosyntactic tree: a step applies
a site transformation at the root of some subtree. Compositions of such
steps form [senturia-marcolli-2025] Definition 6.1's semigroups — the
post-syntactic semigroup generated by fusion and fission, and the full
Distributed Morphology semigroup adding impoverishment and obliteration.
Their action is the movable syntax-morphology boundary: `PostSyntactic`
preserves the total feature set exactly, and `Derivation` can only
shrink it. -/

/-- Close a site relation under congruence: apply it at the root or
inside one subtree. -/
inductive Step (R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop) :
    Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | here {T T'} : R T T' → Step R T T'
  | congr {x} {cs : Multiset (Morphosyntactic F Λ)} {T T'} : Step R T T' →
      Step R (UnorderedTree.node x (T ::ₘ cs)) (UnorderedTree.node x (T' ::ₘ cs))

/-- The fusion site relation: a syntactic cherry over two insertions
rewrites to a single insertion of the magma product, projecting one of
the two data. -/
inductive FuseAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lexHead lex₁ lex₂ : Λ) (S₁ S₂ : UnorderedTree (F ⊕ Unit))
      (hhead : lexHead = lex₁ ∨ lexHead = lex₂) :
      FuseAt (fusionSite lex₁ lex₂ S₁ S₂) (insertion lexHead (some (fuse S₁ S₂)))

/-- The fission site relation: an insertion rewrites to a syntactic
cherry over the two restrictions determined by a partition
`B ∖ A = B₁ ⊔ B₂` of its bundle with copied residue `A`
([senturia-marcolli-2025] Definition 5.6). -/
inductive FissAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lex lex₁ lex₂ : Λ) (A B₁ B₂ : Finset F) {t : RoseTree (F ⊕ Unit)}
      (ht : IsMorphological t) (hlex : lex = lex₁ ∨ lex = lex₂)
      (h₁ : Disjoint A B₁) (h₂ : Disjoint A B₂) (h₁₂ : Disjoint B₁ B₂)
      (hcover : ∀ f ∈ features (UnorderedTree.mk t), f ∈ A ∪ B₁ ∪ B₂) :
      FissAt (insertion lex (some (UnorderedTree.mk t)))
        (fissionSite lex₁ lex₂ (B₁ ∪ A) (B₂ ∪ A) (UnorderedTree.mk t))

/-- The impoverishment site relation: the insertion is replaced by one
of its fission outputs. -/
inductive ImpovAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lex : Λ) (kept : Finset F) {t : RoseTree (F ⊕ Unit)}
      (ht : IsMorphological t) :
      ImpovAt (insertion lex (some (UnorderedTree.mk t)))
        (insertion lex (restrict kept (UnorderedTree.mk t)))

/-- The obliteration site relation: the insertion is emptied, the
syntactic leaf and its datum staying in place. -/
inductive OblitAt : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop
  | mk (lex : Λ) (mo : Option (UnorderedTree (F ⊕ Unit))) :
      OblitAt (insertion lex mo) (insertion lex none)

theorem msFeatures_fissionSite_copy (lex₁ lex₂ : Λ) {A B₁ B₂ : Finset F}
    (h₁ : Disjoint A B₁) (h₂ : Disjoint A B₂) (h₁₂ : Disjoint B₁ B₂)
    {t : RoseTree (F ⊕ Unit)} (ht : IsMorphological t)
    (hcover : ∀ f ∈ features (UnorderedTree.mk t), f ∈ A ∪ B₁ ∪ B₂) :
    msFeatures (fissionSite lex₁ lex₂ (B₁ ∪ A) (B₂ ∪ A) (UnorderedTree.mk t))
      = features (UnorderedTree.mk t)
        + (features (UnorderedTree.mk t)).filter (· ∈ A) := by
  rw [msFeatures_fissionSite _ _ _ _ ht]
  refine Multiset.ext.mpr fun f ↦ ?_
  have hcnt : f ∉ A → f ∉ B₁ → f ∉ B₂ →
      Multiset.count f (features (UnorderedTree.mk t)) = 0 := by
    intro nA nB₁ nB₂
    refine Multiset.count_eq_zero.mpr fun hf ↦ ?_
    rcases Finset.mem_union.mp (hcover f hf) with h | h
    · rcases Finset.mem_union.mp h with h | h
      exacts [nA h, nB₁ h]
    · exact nB₂ h
  simp only [Multiset.count_add, Multiset.count_filter, Finset.mem_union]
  by_cases hfA : f ∈ A
  · have nB₁ : f ∉ B₁ := fun hf ↦ Finset.disjoint_left.mp h₁ hfA hf
    have nB₂ : f ∉ B₂ := fun hf ↦ Finset.disjoint_left.mp h₂ hfA hf
    simp [hfA, nB₁, nB₂]
  · by_cases hfB₁ : f ∈ B₁
    · have nB₂ : f ∉ B₂ := fun hf ↦ Finset.disjoint_left.mp h₁₂ hfB₁ hf
      simp [hfA, hfB₁, nB₂]
    · by_cases hfB₂ : f ∈ B₂
      · simp [hfA, hfB₁, hfB₂]
      · have h0 := hcnt hfA hfB₁ hfB₂
        simp only [features_mk] at h0
        simp [hfA, hfB₁, hfB₂, h0]

/-! ### Feature bookkeeping along the semigroups -/

omit [DecidableEq F] in
private theorem msFeatures_node_cons (x : (Λ × Option (UnorderedTree (F ⊕ Unit))) ⊕ Unit)
    (T : Morphosyntactic F Λ) (cs : Multiset (Morphosyntactic F Λ)) :
    msFeatures (UnorderedTree.node x (T ::ₘ cs))
      = msFeatures T
        + (((cs.map UnorderedTree.leaves).sum).map insertionFeatures).sum := by
  rw [msFeatures, UnorderedTree.leaves_node_cons, Multiset.map_add,
    Multiset.sum_add, msFeatures]

omit [DecidableEq F] in
private theorem numLeaves_node_cons (x : (Λ × Option (UnorderedTree (F ⊕ Unit))) ⊕ Unit)
    (T : Morphosyntactic F Λ) (cs : Multiset (Morphosyntactic F Λ)) :
    (UnorderedTree.node x (T ::ₘ cs)).numLeaves
      = T.numLeaves + Multiset.card ((cs.map UnorderedTree.leaves).sum) := by
  rw [← UnorderedTree.card_leaves, UnorderedTree.leaves_node_cons, Multiset.card_add,
    UnorderedTree.card_leaves]

omit [DecidableEq F] in
theorem FuseAt.msFeatures_eq {T T' : Morphosyntactic F Λ} (h : FuseAt T T') :
    msFeatures T' = msFeatures T := by
  cases h with
  | mk lexHead lex₁ lex₂ S₁ S₂ hhead => exact msFeatures_fuse ..

theorem FissAt.toFinset_msFeatures_eq {T T' : Morphosyntactic F Λ}
    (h : FissAt T T') :
    (msFeatures T').toFinset = (msFeatures T).toFinset := by
  cases h with
  | mk lex lex₁ lex₂ A B₁ B₂ ht hlex h₁ h₂ h₁₂ hcover =>
    rw [msFeatures_fissionSite_copy _ _ h₁ h₂ h₁₂ ht hcover,
      msFeatures_insertion, Option.elim_some, Multiset.toFinset_add,
      Multiset.toFinset_filter]
    exact Finset.union_eq_left.mpr (Finset.filter_subset _ _)

theorem ImpovAt.msFeatures_le {T T' : Morphosyntactic F Λ} (h : ImpovAt T T') :
    msFeatures T' ≤ msFeatures T := by
  cases h with
  | mk lex kept ht => exact msFeatures_impoverish_le _ _ ht

omit [DecidableEq F] in
theorem OblitAt.msFeatures_le {T T' : Morphosyntactic F Λ} (h : OblitAt T T') :
    msFeatures T' ≤ msFeatures T := by
  cases h with
  | mk lex mo =>
    rw [msFeatures_insertion, msFeatures_insertion, Option.elim_none]
    exact Multiset.zero_le _

omit [DecidableEq F] in
theorem Step.msFeatures_eq {R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop}
    (hR : ∀ {T T' : Morphosyntactic F Λ}, R T T' → msFeatures T' = msFeatures T)
    {T T' : Morphosyntactic F Λ} (h : Step R T T') :
    msFeatures T' = msFeatures T := by
  induction h with
  | here h => exact hR h
  | congr _ ih => rw [msFeatures_node_cons, msFeatures_node_cons, ih]

omit [DecidableEq F] in
theorem Step.msFeatures_le {R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop}
    (hR : ∀ {T T' : Morphosyntactic F Λ}, R T T' → msFeatures T' ≤ msFeatures T)
    {T T' : Morphosyntactic F Λ} (h : Step R T T') :
    msFeatures T' ≤ msFeatures T := by
  induction h with
  | here h => exact hR h
  | congr _ ih =>
    rw [msFeatures_node_cons, msFeatures_node_cons]
    exact add_le_add ih le_rfl

theorem Step.toFinset_msFeatures_eq
    {R : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop}
    (hR : ∀ {T T' : Morphosyntactic F Λ}, R T T' →
      (msFeatures T').toFinset = (msFeatures T).toFinset)
    {T T' : Morphosyntactic F Λ} (h : Step R T T') :
    (msFeatures T').toFinset = (msFeatures T).toFinset := by
  induction h with
  | here h => exact hR h
  | congr _ ih =>
    rw [msFeatures_node_cons, msFeatures_node_cons, Multiset.toFinset_add,
      Multiset.toFinset_add, ih]

omit [DecidableEq F] in
theorem Step.numLeaves_fuse {T T' : Morphosyntactic F Λ}
    (h : Step FuseAt T T') : T'.numLeaves + 1 = T.numLeaves := by
  induction h with
  | here h =>
    cases h with
    | mk lexHead lex₁ lex₂ S₁ S₂ hhead =>
      rw [show (insertion lexHead (some (fuse S₁ S₂)) : Morphosyntactic F Λ).numLeaves
          = 1 from rfl, ← UnorderedTree.card_leaves, fusionSite, insertion, insertion,
        leaves_node_pair_leaf]
      rfl
  | congr _ ih => rw [numLeaves_node_cons, numLeaves_node_cons]; omega

theorem Step.numLeaves_fiss {T T' : Morphosyntactic F Λ}
    (h : Step FissAt T T') : T.numLeaves + 1 = T'.numLeaves := by
  induction h with
  | here h =>
    cases h with
    | mk lex lex₁ lex₂ A B₁ B₂ ht hlex h₁ h₂ h₁₂ hcover =>
      rw [show (insertion lex (some (UnorderedTree.mk _)) : Morphosyntactic F Λ).numLeaves
          = 1 from rfl, ← UnorderedTree.card_leaves, fissionSite, insertion, insertion,
        leaves_node_pair_leaf]
      rfl
  | congr _ ih => rw [numLeaves_node_cons, numLeaves_node_cons]; omega

/-! ### The two semigroups and the movable boundary -/

/-- The post-syntactic semigroup: compositions of fusion and fission
steps ([senturia-marcolli-2025] Definition 6.1). -/
def PostSyntactic : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop :=
  Relation.ReflTransGen fun T T' ↦ Step FuseAt T T' ∨ Step FissAt T T'

/-- A derivation of the full Distributed Morphology semigroup:
post-syntactic steps together with impoverishment and obliteration
([senturia-marcolli-2025] Definition 6.1). -/
def Derivation : Morphosyntactic F Λ → Morphosyntactic F Λ → Prop :=
  Relation.ReflTransGen fun T T' ↦
    (Step FuseAt T T' ∨ Step FissAt T T') ∨
      (Step ImpovAt T T' ∨ Step OblitAt T T')

theorem PostSyntactic.toFinset_msFeatures_eq {T T' : Morphosyntactic F Λ}
    (h : PostSyntactic T T') :
    (msFeatures T').toFinset = (msFeatures T).toFinset := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
    rcases step with hf | hs
    · rw [Step.msFeatures_eq (fun h ↦ h.msFeatures_eq) hf, ih]
    · rw [Step.toFinset_msFeatures_eq (fun h ↦ h.toFinset_msFeatures_eq) hs, ih]

theorem Derivation.toFinset_msFeatures_subset {T T' : Morphosyntactic F Λ}
    (h : Derivation T T') :
    (msFeatures T').toFinset ⊆ (msFeatures T).toFinset := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ step ih =>
    refine Finset.Subset.trans ?_ ih
    rcases step with (hf | hs) | (hi | ho)
    · rw [Step.msFeatures_eq (fun h ↦ h.msFeatures_eq) hf]
    · rw [Step.toFinset_msFeatures_eq (fun h ↦ h.toFinset_msFeatures_eq) hs]
    · exact Multiset.toFinset_subset.mpr
        (Multiset.subset_of_le (Step.msFeatures_le (fun h ↦ h.msFeatures_le) hi))
    · exact Multiset.toFinset_subset.mpr
        (Multiset.subset_of_le (Step.msFeatures_le (fun h ↦ h.msFeatures_le) ho))

/-! ### The economy of bivalent features

[senturia-marcolli-2025] Remark 2.3: with `n` feature categories and
three valuations (+, −, unvalued), the bivalent inventory has `n + 3`
generating objects against the `3 n` features a privative encoding
needs, strictly fewer for more than one category. -/

theorem bivalent_economy {n : ℕ} (h : 1 < n) : n + 3 < 3 * n := by omega

end SenturiaMarcolli2025
