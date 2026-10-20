/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Relation
public import Linglib.Core.Data.UnorderedTree.Count
public import Linglib.Core.Data.UnorderedTree.Subtree
public import Linglib.Syntax.Minimalist.SyntacticObject.Basic

/-!
# Terms, containment, and c-command

This file develops the theory of terms of syntactic objects: containment as a closure of the
daughter relation, the multisets of terms and accessible terms that enumerate it, and
sisterhood and c-command relative to a root. Containment lowers the vertex count, which makes it
a well-founded strict order and decides it.

## Main definitions

* `SyntacticObject.ImmediatelyContains`: `x` immediately contains `y` when `y` is a
  root daughter of `x`.
* `SyntacticObject.Contains`: the transitive closure of immediate containment.
* `SyntacticObject.ContainsOrEq`: the reflexive transitive closure of immediate
  containment.
* `SyntacticObject.terms`: the terms of an object, itself included, one per vertex.
* `SyntacticObject.accessibleTerms`: the terms at the non-root vertices, the
  accessible terms of Marcolli, Chomsky and Berwick.
* `SyntacticObject.Sisters`: `x` and `y` are sisters in `root` when they are
  distinct daughters of one term of `root`.
* `SyntacticObject.CCommands`: `x` c-commands `y` in `root` when a sister of `x`
  reflexively contains `y`, after Reinhart.
* `SyntacticObject.AsymmCCommands`: c-command in one direction only.
* `SyntacticObject.cCommandDomain`: the c-command domain of `x` in `root`, the terms it
  c-commands.

## Main results

* `SyntacticObject.mem_terms`, `mem_accessibleTerms`: the terms of `x` are the
  objects it reflexively contains, and the accessible terms those it strictly contains.
* `SyntacticObject.wellFounded_flip_contains`: the proper term relation is
  well-founded.
* `SyntacticObject.card_accessibleTerms`: one accessible term per edge.

## Implementation notes

Syntactic objects are values, not occurrences: a term sitting at two vertices is one object of
multiplicity two in `terms`, and containment and c-command relate values, so the two
daughters of `merge x x` are not sisters.

## References

* [marcolli-chomsky-berwick-2025], Definition 1.2.2
* [reinhart-1976]
-/

@[expose] public section

namespace Minimalist

open Relation UnorderedTree

namespace SyntacticObject

variable {x y z l r : SyntacticObject}

/-! ### Immediate containment -/

/-- `y` is one of `x`'s root daughters. -/
def ImmediatelyContains (x y : SyntacticObject) : Prop := y.val ∈ children x.val

instance (x y : SyntacticObject) : Decidable (ImmediatelyContains x y) :=
  inferInstanceAs (Decidable (_ ∈ _))

@[simp] theorem immediatelyContains_leaf (tok : LexicalItem.Token) (y : SyntacticObject) :
    ¬ ImmediatelyContains (leaf tok) y := by
  simp [ImmediatelyContains]

@[simp] theorem immediatelyContains_trace (y : SyntacticObject) :
    ¬ ImmediatelyContains trace y := by
  simp [ImmediatelyContains]

@[simp] theorem immediatelyContains_traceOf (tok : LexicalItem.Token) (y : SyntacticObject) :
    ¬ ImmediatelyContains (traceOf tok) y := by
  simp [ImmediatelyContains]

@[simp] theorem immediatelyContains_merge (l r y : SyntacticObject) :
    ImmediatelyContains (merge l r) y ↔ y = l ∨ y = r := by
  simp only [ImmediatelyContains, merge_val, children_node, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton]
  exact or_congr Subtype.val_inj Subtype.val_inj

/-! ### Containment -/

/-- Containment, the transitive closure of immediate containment. -/
def Contains : SyntacticObject → SyntacticObject → Prop := TransGen ImmediatelyContains

/-- Reflexive containment, the reflexive transitive closure of immediate containment. -/
def ContainsOrEq : SyntacticObject → SyntacticObject → Prop := ReflTransGen ImmediatelyContains

theorem ImmediatelyContains.Contains (h : ImmediatelyContains x y) : Contains x y :=
  TransGen.single h

theorem Contains.trans (hxy : Contains x y) (hyz : Contains y z) : Contains x z :=
  TransGen.trans hxy hyz

instance : IsPreorder SyntacticObject ContainsOrEq :=
  inferInstanceAs (IsPreorder _ (ReflTransGen _))

theorem containsOrEq_iff_eq_or_contains : ContainsOrEq x y ↔ y = x ∨ Contains x y :=
  reflTransGen_iff_eq_or_transGen

theorem contains_iff_exists_immediatelyContains :
    Contains x y ↔ ∃ z, ImmediatelyContains x z ∧ ContainsOrEq z y :=
  TransGen.head'_iff

@[simp] theorem contains_leaf (tok : LexicalItem.Token) (y : SyntacticObject) :
    ¬ Contains (leaf tok) y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_trace (y : SyntacticObject) : ¬ Contains trace y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_traceOf (tok : LexicalItem.Token) (y : SyntacticObject) :
    ¬ Contains (traceOf tok) y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_merge :
    Contains (merge l r) y ↔ ContainsOrEq l y ∨ ContainsOrEq r y := by
  simp [contains_iff_exists_immediatelyContains, or_and_right, exists_or]

@[simp] theorem containsOrEq_leaf (tok : LexicalItem.Token) :
    ContainsOrEq (leaf tok) y ↔ y = leaf tok :=
  reflTransGen_iff_eq (immediatelyContains_leaf tok)

@[simp] theorem containsOrEq_trace : ContainsOrEq trace y ↔ y = trace :=
  reflTransGen_iff_eq immediatelyContains_trace

@[simp] theorem containsOrEq_traceOf (tok : LexicalItem.Token) :
    ContainsOrEq (traceOf tok) y ↔ y = traceOf tok :=
  reflTransGen_iff_eq (immediatelyContains_traceOf tok)

@[simp] theorem containsOrEq_merge :
    ContainsOrEq (merge l r) y ↔ y = merge l r ∨ ContainsOrEq l y ∨ ContainsOrEq r y := by
  rw [containsOrEq_iff_eq_or_contains, contains_merge]

/-! ### The vertex count grades containment -/

theorem numNodes_lt_of_immediatelyContains (h : ImmediatelyContains x y) :
    y.val.numNodes < x.val.numNodes := by
  obtain ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ := exists_form x <;> simp at h
  obtain rfl | rfl := h <;> simp <;> omega

theorem numNodes_lt_of_contains (h : Contains x y) : y.val.numNodes < x.val.numNodes :=
  transGen_minimal (r' := InvImage (· > ·) fun s : SyntacticObject ↦ s.val.numNodes)
    (fun _ _ ↦ numNodes_lt_of_immediatelyContains) x y h

/-- Being a proper term is well-founded: an object has finitely many terms. -/
theorem wellFounded_flip_contains : WellFounded (flip Contains) :=
  Subrelation.wf (fun h ↦ numNodes_lt_of_contains h)
    (InvImage.wf (fun s : SyntacticObject ↦ s.val.numNodes) wellFounded_lt)

instance : IsStrictOrder SyntacticObject Contains where
  irrefl _ h := lt_irrefl _ (numNodes_lt_of_contains h)
  trans _ _ _ := TransGen.trans

theorem contains_irrefl (x : SyntacticObject) : ¬ Contains x x := irrefl x

end SyntacticObject

/-! ### Terms -/

/-- The subtrees of a syntactic object are its terms, hence syntactic objects. -/
theorem isSyntacticObject_of_mem_subtrees (s : SyntacticObject) :
    ∀ m ∈ UnorderedTree.subtrees s.val, IsSyntacticObject m := by
  induction s using SyntacticObject.ind with
  | leaf tok =>
    simp only [SyntacticObject.leaf_val, mem_subtrees_leaf, forall_eq]
    exact (SyntacticObject.leaf tok).2
  | trace =>
    simp only [SyntacticObject.trace_val, mem_subtrees_leaf, forall_eq]
    exact SyntacticObject.trace.2
  | traceOf tok =>
    simp only [SyntacticObject.traceOf_val, mem_subtrees_leaf, forall_eq]
    exact (SyntacticObject.traceOf tok).2
  | merge l r ihl ihr =>
    simp only [SyntacticObject.merge_val, mem_subtrees_node_pair]
    rintro m (rfl | h | h)
    exacts [(SyntacticObject.merge l r).2, ihl m h, ihr m h]

namespace SyntacticObject

variable {x y l r : SyntacticObject}

/-- The terms of a syntactic object, itself included. -/
def terms (s : SyntacticObject) : Multiset SyntacticObject :=
  (UnorderedTree.subtrees s.val).pmap Subtype.mk (isSyntacticObject_of_mem_subtrees s)

@[simp] theorem map_val_terms (s : SyntacticObject) :
    s.terms.map Subtype.val = UnorderedTree.subtrees s.val := by
  simp [terms, Multiset.map_pmap, Multiset.pmap_eq_map]

@[simp] theorem terms_leaf (tok : LexicalItem.Token) : (leaf tok).terms = {leaf tok} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, leaf_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_trace : trace.terms = {trace} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, trace_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_traceOf (tok : LexicalItem.Token) : (traceOf tok).terms = {traceOf tok} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, traceOf_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_merge (l r : SyntacticObject) :
    (merge l r).terms = merge l r ::ₘ (l.terms + r.terms) :=
  Multiset.map_injective Subtype.val_injective <| by
    simp only [Multiset.map_cons, Multiset.map_add, map_val_terms, merge_val,
      UnorderedTree.subtrees_node_pair]

/-- The terms of `x` are the objects it reflexively contains. -/
@[simp] theorem mem_terms : y ∈ x.terms ↔ ContainsOrEq x y := by
  induction x using ind with
  | leaf tok => simp
  | trace => simp
  | traceOf tok => simp
  | merge l r ihl ihr => simp [ihl, ihr]

theorem self_mem_terms (s : SyntacticObject) : s ∈ s.terms :=
  mem_terms.2 ReflTransGen.refl

theorem terms_subset_terms (h : ContainsOrEq x y) : y.terms ⊆ x.terms :=
  fun _ hz ↦ mem_terms.2 (ReflTransGen.trans h (mem_terms.1 hz))

/-- The daughters of a term are terms. -/
theorem mem_terms_of_merge_mem_terms {s : SyntacticObject} (h : merge l r ∈ s.terms) :
    l ∈ s.terms ∧ r ∈ s.terms :=
  ⟨terms_subset_terms (mem_terms.1 h) (mem_terms.2 (.single ((immediatelyContains_merge _ _ _).2
      (.inl rfl)))),
    terms_subset_terms (mem_terms.1 h) (mem_terms.2 (.single ((immediatelyContains_merge _ _ _).2
      (.inr rfl))))⟩

/-- One term per vertex. -/
theorem card_terms (s : SyntacticObject) : s.terms.card = s.val.numNodes := by
  rw [terms, Multiset.card_pmap, UnorderedTree.card_subtrees]

instance (x y : SyntacticObject) : Decidable (ContainsOrEq x y) :=
  decidable_of_iff _ mem_terms

/-! ### Accessible terms -/

/-- The accessible terms, the terms at the non-root vertices. -/
def accessibleTerms (s : SyntacticObject) : Multiset SyntacticObject := s.terms.erase s

theorem cons_accessibleTerms (s : SyntacticObject) : s ::ₘ s.accessibleTerms = s.terms :=
  Multiset.cons_erase (self_mem_terms s)

@[simp] theorem accessibleTerms_leaf (tok : LexicalItem.Token) :
    (leaf tok).accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_trace : trace.accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_traceOf (tok : LexicalItem.Token) :
    (traceOf tok).accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_merge (l r : SyntacticObject) :
    (merge l r).accessibleTerms = l.terms + r.terms := by
  simp [accessibleTerms]

/-- The accessible terms of `x` are the objects it contains. -/
@[simp] theorem mem_accessibleTerms : y ∈ x.accessibleTerms ↔ Contains x y := by
  induction x using ind with
  | leaf tok => simp
  | trace => simp
  | traceOf tok => simp
  | merge l r _ _ => simp

/-- One accessible term per edge. -/
theorem card_accessibleTerms (s : SyntacticObject) :
    s.accessibleTerms.card = s.val.numEdges := by
  rw [accessibleTerms, Multiset.card_erase_of_mem (self_mem_terms s), card_terms]; rfl

instance (x y : SyntacticObject) : Decidable (Contains x y) :=
  decidable_of_iff _ mem_accessibleTerms

/-! ### C-command -/

variable {root : SyntacticObject}

/-- `x` and `y` are sisters in `root` when they are distinct daughters of some term of
`root`. -/
def Sisters (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.terms, ImmediatelyContains z x ∧ ImmediatelyContains z y ∧ x ≠ y

instance (root x y : SyntacticObject) : Decidable (Sisters root x y) :=
  Multiset.decidableExistsMultiset

theorem Sisters.symm (h : Sisters root x y) : Sisters root y x :=
  let ⟨z, hz, hx, hy, hne⟩ := h; ⟨z, hz, hy, hx, hne.symm⟩

theorem Sisters.mem_left (h : Sisters root x y) : x ∈ root.terms :=
  let ⟨_, hz, hx, _, _⟩ := h; mem_terms.2 (ReflTransGen.tail (mem_terms.1 hz) hx)

theorem Sisters.mem_right (h : Sisters root x y) : y ∈ root.terms :=
  h.symm.mem_left

/-- `x` c-commands `y` in `root` when a sister of `x` contains or equals `y`. -/
def CCommands (root x y : SyntacticObject) : Prop :=
  ∃ z ∈ root.terms, Sisters root x z ∧ ContainsOrEq z y

instance (root x y : SyntacticObject) : Decidable (CCommands root x y) :=
  Multiset.decidableExistsMultiset

/-- Sisters c-command each other. -/
theorem Sisters.cCommands (h : Sisters root x y) : CCommands root x y :=
  ⟨y, h.mem_right, h, ReflTransGen.refl⟩

/-- A c-commanded object is a term of the root. -/
theorem CCommands.mem_terms (h : CCommands root x y) : y ∈ root.terms :=
  let ⟨_, hz, _, hzy⟩ := h
  terms_subset_terms (SyntacticObject.mem_terms.1 hz) (SyntacticObject.mem_terms.2 hzy)

/-- A c-commanding object is a term of the root. -/
theorem CCommands.left_mem_terms (h : CCommands root x y) : x ∈ root.terms :=
  let ⟨_, _, hs, _⟩ := h
  hs.mem_left

/-- The c-command domain of `x` in `root`, the search space of a probe sitting at `x`. -/
def cCommandDomain (root x : SyntacticObject) : Multiset SyntacticObject :=
  root.terms.filter (CCommands root x)

@[simp] theorem mem_cCommandDomain : y ∈ cCommandDomain root x ↔ CCommands root x y :=
  Multiset.mem_filter.trans (and_iff_right_of_imp CCommands.mem_terms)

/-- `x` c-commands `y` in `root` and `y` does not c-command `x`. -/
def AsymmCCommands (root x y : SyntacticObject) : Prop :=
  CCommands root x y ∧ ¬ CCommands root y x

instance (root x y : SyntacticObject) : Decidable (AsymmCCommands root x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Sisters never asymmetrically c-command each other. -/
theorem Sisters.not_asymmCCommands (h : Sisters root x y) :
    ¬ AsymmCCommands root x y :=
  fun h' ↦ h'.2 (Sisters.cCommands h.symm)

end SyntacticObject


end Minimalist
