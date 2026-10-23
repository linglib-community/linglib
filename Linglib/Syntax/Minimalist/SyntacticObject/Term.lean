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
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

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

variable {L : Type}

open Relation UnorderedTree

namespace SyntacticObject

variable {x y z l r : SyntacticObject L}

/-! ### Immediate containment -/

/-- `y` is one of `x`'s root daughters. -/
def ImmediatelyContains (x y : SyntacticObject L) : Prop := y.val ∈ children x.val

instance [DecidableEq L] (x y : SyntacticObject L) : Decidable (ImmediatelyContains x y) :=
  inferInstanceAs (Decidable (_ ∈ _))

@[simp] theorem immediatelyContains_leaf (tok : L) (y : SyntacticObject L) :
    ¬ ImmediatelyContains (leaf tok) y := by
  simp [ImmediatelyContains]

@[simp] theorem immediatelyContains_trace (y : SyntacticObject L) :
    ¬ ImmediatelyContains trace y := by
  simp [ImmediatelyContains]

@[simp] theorem immediatelyContains_traceOf (tok : L) (y : SyntacticObject L) :
    ¬ ImmediatelyContains (traceOf tok) y := by
  simp [ImmediatelyContains]

@[simp] theorem immediatelyContains_merge (l r y : SyntacticObject L) :
    ImmediatelyContains (merge l r) y ↔ y = l ∨ y = r := by
  simp only [ImmediatelyContains, merge_val, children_node, Multiset.insert_eq_cons,
    Multiset.mem_cons, Multiset.mem_singleton]
  exact or_congr Subtype.val_inj Subtype.val_inj

/-! ### Containment -/

/-- Containment, the transitive closure of immediate containment. -/
def Contains : SyntacticObject L → SyntacticObject L → Prop := TransGen ImmediatelyContains

/-- Reflexive containment, the reflexive transitive closure of immediate containment. -/
def ContainsOrEq : SyntacticObject L → SyntacticObject L → Prop := ReflTransGen ImmediatelyContains

theorem ImmediatelyContains.Contains (h : ImmediatelyContains x y) : Contains x y :=
  TransGen.single h

theorem Contains.trans (hxy : Contains x y) (hyz : Contains y z) : Contains x z :=
  TransGen.trans hxy hyz

instance : IsPreorder (SyntacticObject L) ContainsOrEq :=
  inferInstanceAs (IsPreorder _ (ReflTransGen _))

theorem containsOrEq_iff_eq_or_contains : ContainsOrEq x y ↔ y = x ∨ Contains x y :=
  reflTransGen_iff_eq_or_transGen

theorem contains_iff_exists_immediatelyContains :
    Contains x y ↔ ∃ z, ImmediatelyContains x z ∧ ContainsOrEq z y :=
  TransGen.head'_iff

@[simp] theorem contains_leaf (tok : L) (y : SyntacticObject L) :
    ¬ Contains (leaf tok) y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_trace (y : SyntacticObject L) : ¬ Contains trace y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_traceOf (tok : L) (y : SyntacticObject L) :
    ¬ Contains (traceOf tok) y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_merge :
    Contains (merge l r) y ↔ ContainsOrEq l y ∨ ContainsOrEq r y := by
  simp [contains_iff_exists_immediatelyContains, or_and_right, exists_or]

@[simp] theorem containsOrEq_leaf (tok : L) :
    ContainsOrEq (leaf tok) y ↔ y = leaf tok :=
  reflTransGen_iff_eq (immediatelyContains_leaf tok)

@[simp] theorem containsOrEq_trace : ContainsOrEq trace y ↔ y = trace :=
  reflTransGen_iff_eq immediatelyContains_trace

@[simp] theorem containsOrEq_traceOf (tok : L) :
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
  transGen_minimal (r' := InvImage (· > ·) fun s : SyntacticObject L ↦ s.val.numNodes)
    (fun _ _ ↦ numNodes_lt_of_immediatelyContains) x y h

theorem wellFounded_flip_contains : WellFounded (flip (Contains (L := L))) :=
  Subrelation.wf (fun h ↦ numNodes_lt_of_contains h)
    (InvImage.wf (fun s : SyntacticObject L ↦ s.val.numNodes) wellFounded_lt)

instance : IsStrictOrder (SyntacticObject L) Contains where
  irrefl _ h := lt_irrefl _ (numNodes_lt_of_contains h)
  trans _ _ _ := TransGen.trans

theorem contains_irrefl (x : SyntacticObject L) : ¬ Contains x x := irrefl x

end SyntacticObject

/-! ### Terms -/

theorem isSyntacticObject_of_mem_subtrees (s : SyntacticObject L) :
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

variable {x y l r : SyntacticObject L}

/-- The terms of a syntactic object, itself included. -/
def terms (s : SyntacticObject L) : Multiset (SyntacticObject L) :=
  (UnorderedTree.subtrees s.val).pmap Subtype.mk (isSyntacticObject_of_mem_subtrees s)

@[simp] theorem map_val_terms (s : SyntacticObject L) :
    s.terms.map Subtype.val = UnorderedTree.subtrees s.val := by
  simp [terms, Multiset.map_pmap, Multiset.pmap_eq_map]

@[simp] theorem terms_leaf (tok : L) : (leaf tok).terms = {leaf tok} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, leaf_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_trace : (trace : SyntacticObject L).terms = {trace} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, trace_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_traceOf (tok : L) : (traceOf tok).terms = {traceOf tok} :=
  Multiset.map_injective Subtype.val_injective <| by
    rw [Multiset.map_singleton, map_val_terms, traceOf_val, UnorderedTree.subtrees_leaf]

@[simp] theorem terms_merge (l r : SyntacticObject L) :
    (merge l r).terms = merge l r ::ₘ (l.terms + r.terms) :=
  Multiset.map_injective Subtype.val_injective <| by
    simp only [Multiset.map_cons, Multiset.map_add, map_val_terms, merge_val,
      UnorderedTree.subtrees_node_pair]

@[simp] theorem mem_terms : y ∈ x.terms ↔ ContainsOrEq x y := by
  induction x using ind with
  | leaf tok => simp
  | trace => simp
  | traceOf tok => simp
  | merge l r ihl ihr => simp [ihl, ihr]

theorem self_mem_terms (s : SyntacticObject L) : s ∈ s.terms :=
  mem_terms.2 ReflTransGen.refl

theorem val_mem_subtrees {S U : SyntacticObject L} : S.val ∈ U.val.subtrees ↔ S ∈ U.terms := by
  rw [← map_val_terms, Multiset.mem_map_of_injective Subtype.val_injective]

theorem mem_terms_merge_right (u C : SyntacticObject L) : C ∈ (merge u C).terms := by
  rw [terms_merge]
  exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr (self_mem_terms C)))

theorem terms_subset_terms (h : ContainsOrEq x y) : y.terms ⊆ x.terms :=
  fun _ hz ↦ mem_terms.2 (ReflTransGen.trans h (mem_terms.1 hz))

theorem mem_terms_of_merge_mem_terms {s : SyntacticObject L} (h : merge l r ∈ s.terms) :
    l ∈ s.terms ∧ r ∈ s.terms :=
  ⟨terms_subset_terms (mem_terms.1 h) (mem_terms.2 (.single ((immediatelyContains_merge _ _ _).2
      (.inl rfl)))),
    terms_subset_terms (mem_terms.1 h) (mem_terms.2 (.single ((immediatelyContains_merge _ _ _).2
      (.inr rfl))))⟩

theorem card_terms (s : SyntacticObject L) : s.terms.card = s.val.numNodes := by
  rw [terms, Multiset.card_pmap, UnorderedTree.card_subtrees]

instance [DecidableEq L] (x y : SyntacticObject L) : Decidable (ContainsOrEq x y) :=
  decidable_of_iff _ mem_terms

/-! ### Accessible terms -/

section AccessibleTerms

variable [DecidableEq L]

/-- The accessible terms, the terms at the non-root vertices. -/
def accessibleTerms (s : SyntacticObject L) : Multiset (SyntacticObject L) := s.terms.erase s

theorem cons_accessibleTerms (s : SyntacticObject L) : s ::ₘ s.accessibleTerms = s.terms :=
  Multiset.cons_erase (self_mem_terms s)

@[simp] theorem accessibleTerms_leaf (tok : L) :
    (leaf tok).accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_trace : (trace : SyntacticObject L).accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_traceOf (tok : L) :
    (traceOf tok).accessibleTerms = 0 := by
  simp [accessibleTerms]

@[simp] theorem accessibleTerms_merge (l r : SyntacticObject L) :
    (merge l r).accessibleTerms = l.terms + r.terms := by
  simp [accessibleTerms]

@[simp] theorem mem_accessibleTerms : y ∈ x.accessibleTerms ↔ Contains x y := by
  induction x using ind with
  | leaf tok => simp
  | trace => simp
  | traceOf tok => simp
  | merge l r _ _ => simp

theorem card_accessibleTerms (s : SyntacticObject L) :
    s.accessibleTerms.card = s.val.numEdges := by
  rw [accessibleTerms, Multiset.card_erase_of_mem (self_mem_terms s), card_terms]; rfl

instance (x y : SyntacticObject L) : Decidable (Contains x y) :=
  decidable_of_iff _ mem_accessibleTerms

end AccessibleTerms

/-! ### C-command -/

variable {root : SyntacticObject L}

/-- `x` and `y` are sisters in `root` when they are distinct daughters of some term of
`root`. -/
def Sisters (root x y : SyntacticObject L) : Prop :=
  ∃ z ∈ root.terms, ImmediatelyContains z x ∧ ImmediatelyContains z y ∧ x ≠ y

instance [DecidableEq L] (root x y : SyntacticObject L) : Decidable (Sisters root x y) :=
  Multiset.decidableExistsMultiset

theorem Sisters.symm (h : Sisters root x y) : Sisters root y x :=
  let ⟨z, hz, hx, hy, hne⟩ := h; ⟨z, hz, hy, hx, hne.symm⟩

theorem Sisters.mem_left (h : Sisters root x y) : x ∈ root.terms :=
  let ⟨_, hz, hx, _, _⟩ := h; mem_terms.2 (ReflTransGen.tail (mem_terms.1 hz) hx)

theorem Sisters.mem_right (h : Sisters root x y) : y ∈ root.terms :=
  h.symm.mem_left

/-- `x` c-commands `y` in `root` when a sister of `x` contains or equals `y`. -/
def CCommands (root x y : SyntacticObject L) : Prop :=
  ∃ z ∈ root.terms, Sisters root x z ∧ ContainsOrEq z y

instance [DecidableEq L] (root x y : SyntacticObject L) : Decidable (CCommands root x y) :=
  Multiset.decidableExistsMultiset

theorem Sisters.cCommands (h : Sisters root x y) : CCommands root x y :=
  ⟨y, h.mem_right, h, ReflTransGen.refl⟩

theorem CCommands.mem_terms (h : CCommands root x y) : y ∈ root.terms :=
  let ⟨_, hz, _, hzy⟩ := h
  terms_subset_terms (SyntacticObject.mem_terms.1 hz) (SyntacticObject.mem_terms.2 hzy)

theorem CCommands.left_mem_terms (h : CCommands root x y) : x ∈ root.terms :=
  let ⟨_, _, hs, _⟩ := h
  hs.mem_left

theorem CCommands.mono {root' : SyntacticObject L} (h : CCommands root x y)
    (hsub : root.terms ⊆ root'.terms) : CCommands root' x y :=
  let ⟨z, hz, ⟨w, hw, hwx, hwz, hxz⟩, hzy⟩ := h
  ⟨z, hsub hz, ⟨w, hsub hw, hwx, hwz, hxz⟩, hzy⟩

theorem cCommands_merge_left (hlr : l ≠ r) (hy : y ∈ r.terms) : CCommands (merge l r) l y :=
  ⟨r, mem_terms.2 (.single ((immediatelyContains_merge _ _ _).2 (.inr rfl))),
    ⟨merge l r, self_mem_terms _, (immediatelyContains_merge _ _ _).2 (.inl rfl),
      (immediatelyContains_merge _ _ _).2 (.inr rfl), hlr⟩, mem_terms.1 hy⟩

theorem Sisters.of_merge {x z : SyntacticObject L} (h : Sisters (merge l r) x z) :
    Sisters l x z ∨ Sisters r x z ∨ x = l ∧ z = r ∨ x = r ∧ z = l := by
  obtain ⟨w, hw, hwx, hwz, hxz⟩ := h
  rw [terms_merge, Multiset.mem_cons, Multiset.mem_add] at hw
  rcases hw with rfl | hw | hw
  · rw [immediatelyContains_merge] at hwx hwz
    rcases hwx with rfl | rfl <;> rcases hwz with rfl | rfl
    · exact absurd rfl hxz
    · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
    · exact .inr (.inr (.inr ⟨rfl, rfl⟩))
    · exact absurd rfl hxz
  · exact .inl ⟨w, hw, hwx, hwz, hxz⟩
  · exact .inr (.inl ⟨w, hw, hwx, hwz, hxz⟩)

/-- The c-command domain of `x` in `root`, the search space of a probe sitting at `x`. -/
def cCommandDomain [DecidableEq L] (root x : SyntacticObject L) :
    Multiset (SyntacticObject L) :=
  root.terms.filter (CCommands root x)

@[simp] theorem mem_cCommandDomain [DecidableEq L] :
    y ∈ cCommandDomain root x ↔ CCommands root x y :=
  Multiset.mem_filter.trans (and_iff_right_of_imp CCommands.mem_terms)

/-- `x` c-commands `y` in `root` and `y` does not c-command `x`. -/
def AsymmCCommands (root x y : SyntacticObject L) : Prop :=
  CCommands root x y ∧ ¬ CCommands root y x

instance [DecidableEq L] (root x y : SyntacticObject L) : Decidable (AsymmCCommands root x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Sisters.not_asymmCCommands (h : Sisters root x y) :
    ¬ AsymmCCommands root x y :=
  fun h' ↦ h'.2 (Sisters.cCommands h.symm)

/-! ### Pronounced tokens of terms -/

theorem mem_yield_iff {s : SyntacticObject L} {tok : L} :
    tok ∈ s.yield ↔ leaf tok ∈ s.terms := by
  induction s using ind with
  | leaf a => simp
  | trace => simp
  | traceOf a => simp
  | merge l r ihl ihr => simp [ihl, ihr, leaf_ne_merge]

theorem yield_le_of_mem_terms {s u : SyntacticObject L} (h : u ∈ s.terms) : u.yield ≤ s.yield := by
  induction s using ind with
  | leaf a => rw [terms_leaf, Multiset.mem_singleton] at h; rw [h]
  | trace => rw [terms_trace, Multiset.mem_singleton] at h; rw [h]
  | traceOf a => rw [terms_traceOf, Multiset.mem_singleton] at h; rw [h]
  | merge l r ihl ihr =>
    rw [terms_merge, Multiset.mem_cons, Multiset.mem_add] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · exact (ihl h).trans (by rw [yield_merge]; exact Multiset.le_add_right _ _)
    · exact (ihr h).trans (by rw [yield_merge]; exact Multiset.le_add_left _ _)

end SyntacticObject


end Minimalist
