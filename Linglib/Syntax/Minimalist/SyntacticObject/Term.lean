/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Relation
public import Linglib.Core.Data.UnorderedTree.Leaves
public import Linglib.Core.Data.UnorderedTree.Subtree
public import Linglib.Syntax.Minimalist.SyntacticObject.Tree
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Terms, containment, and c-command

This file develops the theory of terms of syntactic objects: containment as a closure of the
daughter relation, the multiset of terms that enumerates it, and sisterhood and c-command
relative to a root. Containment lowers the vertex count, which makes it
a well-founded strict order and decides it.

## Main definitions

* `SyntacticObject.ImmediatelyContains`: `x` immediately contains `y` when `y` is a
  root daughter of `x`.
* `SyntacticObject.Contains`: the transitive closure of immediate containment.
* `SyntacticObject.ContainsOrEq`: the reflexive transitive closure of immediate
  containment.
* `SyntacticObject.terms`: the terms of an object, itself included, one per vertex.
* `SyntacticObject.Sisters`: `x` and `y` are sisters in `root` when they are
  distinct daughters of one term of `root`.
* `SyntacticObject.CCommands`: `x` c-commands `y` in `root` when a sister of `x`
  reflexively contains `y`, after Reinhart.

## Main results

* `SyntacticObject.mem_terms`: the terms of `x` are the objects it reflexively contains.
* `SyntacticObject.wellFounded_flip_contains`: the proper term relation is
  well-founded.
* `SyntacticObject.cCommands_map_iff`: an injective relabelling preserves and reflects
  c-command.

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

variable {L ι : Type}

open Relation UnorderedTree

namespace SyntacticObject

/-! ### Containment and terms, on any leaves -/

section Leaves

variable {α : Type} {x y z l r : SyntacticObject α}

/-- `y` is one of `x`'s root daughters. -/
def ImmediatelyContains (x y : SyntacticObject α) : Prop := ∃ z, x = y * z

@[simp] theorem immediatelyContains_of (a : α) (y : SyntacticObject α) :
    ¬ ImmediatelyContains (FreeCommMagma.of a) y :=
  fun ⟨z, h⟩ ↦ FreeCommMagma.of_ne_mul a y z h

@[simp] theorem immediatelyContains_mul : ImmediatelyContains (l * r) y ↔ y = l ∨ y = r := by
  refine ⟨fun ⟨z, h⟩ ↦ ?_, ?_⟩
  · rcases FreeCommMagma.mul_eq_mul_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
    · exact .inl h.symm
    · exact .inr h.symm
  · rintro (rfl | rfl)
    · exact ⟨r, rfl⟩
    · exact ⟨l, mul_comm l y⟩

/-- Containment, the transitive closure of immediate containment. -/
def Contains : SyntacticObject α → SyntacticObject α → Prop := TransGen ImmediatelyContains

/-- Reflexive containment, the reflexive transitive closure of immediate containment. -/
def ContainsOrEq : SyntacticObject α → SyntacticObject α → Prop := ReflTransGen ImmediatelyContains

theorem ImmediatelyContains.Contains (h : ImmediatelyContains x y) : Contains x y :=
  TransGen.single h

theorem Contains.trans (hxy : Contains x y) (hyz : Contains y z) : Contains x z :=
  TransGen.trans hxy hyz

instance : IsPreorder (SyntacticObject α) ContainsOrEq :=
  inferInstanceAs (IsPreorder _ (ReflTransGen _))

theorem containsOrEq_iff_eq_or_contains : ContainsOrEq x y ↔ y = x ∨ Contains x y :=
  reflTransGen_iff_eq_or_transGen

theorem contains_iff_exists_immediatelyContains :
    Contains x y ↔ ∃ z, ImmediatelyContains x z ∧ ContainsOrEq z y :=
  TransGen.head'_iff

@[simp] theorem contains_of (a : α) (y : SyntacticObject α) :
    ¬ Contains (FreeCommMagma.of a) y := by
  simp [contains_iff_exists_immediatelyContains]

@[simp] theorem contains_mul : Contains (l * r) y ↔ ContainsOrEq l y ∨ ContainsOrEq r y := by
  simp [contains_iff_exists_immediatelyContains, or_and_right, exists_or]

@[simp] theorem containsOrEq_of (a : α) :
    ContainsOrEq (FreeCommMagma.of a) y ↔ y = FreeCommMagma.of a :=
  reflTransGen_iff_eq (immediatelyContains_of a)

@[simp] theorem containsOrEq_mul :
    ContainsOrEq (l * r) y ↔ y = l * r ∨ ContainsOrEq l y ∨ ContainsOrEq r y := by
  rw [containsOrEq_iff_eq_or_contains, contains_mul]

/-- The terms of an object, one per vertex of its tree: the object itself and the terms of its
daughters. -/
def terms : SyntacticObject α → Multiset (SyntacticObject α) :=
  FreeCommMagma.elim (fun x ↦ {FreeCommMagma.of x}) (fun l r a b ↦ (l * r) ::ₘ (a + b))
    fun l r a b ↦ by rw [mul_comm, add_comm]

@[simp] theorem terms_of (a : α) :
    terms (FreeCommMagma.of a : SyntacticObject α) = {FreeCommMagma.of a} := rfl

@[simp] theorem terms_mul (l r : SyntacticObject α) :
    (l * r).terms = (l * r) ::ₘ (l.terms + r.terms) :=
  FreeCommMagma.elim_mul _ _ _ l r

/-- The terms of `x` are the objects it reflexively contains. -/
@[simp] theorem mem_terms : y ∈ x.terms ↔ ContainsOrEq x y := by
  induction x using FreeCommMagma.inductionOn with
  | of a => simp
  | mul l r ihl ihr => simp [ihl, ihr]

theorem self_mem_terms (s : SyntacticObject α) : s ∈ s.terms :=
  mem_terms.2 ReflTransGen.refl

theorem terms_subset_terms (h : ContainsOrEq x y) : y.terms ⊆ x.terms :=
  fun _ hz ↦ mem_terms.2 (ReflTransGen.trans h (mem_terms.1 hz))

instance [DecidableEq α] (x y : SyntacticObject α) : Decidable (ImmediatelyContains x y) :=
  @decidable_of_iff _ (∃ z ∈ x.terms, x = y * z)
    ⟨fun ⟨z, _, h⟩ ↦ ⟨z, h⟩, fun ⟨z, h⟩ ↦
      ⟨z, mem_terms.2 (h ▸ containsOrEq_mul.2 (.inr (.inr ReflTransGen.refl))), h⟩⟩
    Multiset.decidableExistsMultiset

instance [DecidableEq α] (x y : SyntacticObject α) : Decidable (ContainsOrEq x y) :=
  decidable_of_iff _ mem_terms

theorem containsOrEq_refl (x : SyntacticObject α) : ContainsOrEq x x := ReflTransGen.refl

theorem ContainsOrEq.trans (hxy : ContainsOrEq x y) (hyz : ContainsOrEq y z) : ContainsOrEq x z :=
  ReflTransGen.trans hxy hyz

/-! ### Leaves -/

/-- The leaves of an object, with multiplicity. -/
def leaves : SyntacticObject α → Multiset α :=
  FreeCommMagma.elim (fun a ↦ {a}) (fun _ _ a b ↦ a + b) fun _ _ a b ↦ add_comm a b

@[simp] theorem leaves_of (a : α) : leaves (FreeCommMagma.of a : SyntacticObject α) = {a} := rfl

@[simp] theorem leaves_mul (l r : SyntacticObject α) : (l * r).leaves = l.leaves + r.leaves :=
  FreeCommMagma.elim_mul _ _ _ l r

theorem card_leaves_pos (x : SyntacticObject α) : 0 < x.leaves.card := by
  induction x using FreeCommMagma.inductionOn with
  | of a => simp
  | mul l r ihl _ => rw [leaves_mul, Multiset.card_add]; omega

theorem ImmediatelyContains.card_leaves_lt (h : ImmediatelyContains x y) :
    y.leaves.card < x.leaves.card := by
  obtain ⟨z, rfl⟩ := h
  rw [leaves_mul, Multiset.card_add]
  have := card_leaves_pos z
  omega

/-- A proper term of an object has fewer leaves. -/
theorem Contains.card_leaves_lt (h : Contains x y) : y.leaves.card < x.leaves.card := by
  induction h with
  | single h => exact h.card_leaves_lt
  | tail _ h ih => exact h.card_leaves_lt.trans ih

/-- The leaves of a term are among the leaves of the object. -/
theorem leaves_le_of_mem_terms (h : y ∈ x.terms) : y.leaves ≤ x.leaves := by
  induction x using FreeCommMagma.inductionOn with
  | of a =>
    rw [terms_of, Multiset.mem_singleton] at h
    rw [h]
  | mul l r ihl ihr =>
    rw [terms_mul, Multiset.mem_cons, Multiset.mem_add] at h
    rw [leaves_mul]
    rcases h with rfl | h | h
    · rw [leaves_mul]
    · exact (ihl h).trans (Multiset.le_add_right _ _)
    · exact (ihr h).trans (Multiset.le_add_left _ _)

theorem contains_irrefl (x : SyntacticObject α) : ¬ Contains x x :=
  fun h ↦ lt_irrefl _ h.card_leaves_lt

/-- Being a proper term is well-founded: an object has finitely many terms. -/
theorem wellFounded_flip_contains : WellFounded (flip (Contains (α := α))) :=
  Subrelation.wf (fun h ↦ Contains.card_leaves_lt h)
    (InvImage.wf (fun s : SyntacticObject α ↦ s.leaves.card) wellFounded_lt)

instance : IsStrictOrder (SyntacticObject α) Contains where
  irrefl := contains_irrefl
  trans _ _ _ := TransGen.trans

theorem contains_iff_containsOrEq_and_ne : Contains x y ↔ ContainsOrEq x y ∧ y ≠ x :=
  ⟨fun h ↦ ⟨h.to_reflTransGen, fun hyx ↦ contains_irrefl x (hyx ▸ h)⟩,
    fun ⟨h, hne⟩ ↦ (containsOrEq_iff_eq_or_contains.1 h).resolve_left hne⟩

instance [DecidableEq α] (x y : SyntacticObject α) : Decidable (Contains x y) :=
  decidable_of_iff _ contains_iff_containsOrEq_and_ne.symm

end Leaves

variable {x y z l r : SyntacticObject (SyntacticObject.Leaf L ι)}

/-! ### At leaves with traces -/

@[simp] theorem immediatelyContains_leaf (tok : L)
    (y : SyntacticObject (SyntacticObject.Leaf L ι)) : ¬ ImmediatelyContains (leaf tok) y :=
  immediatelyContains_of _ y

@[simp] theorem immediatelyContains_trace (y : SyntacticObject (SyntacticObject.Leaf L ι)) :
    ¬ ImmediatelyContains trace y :=
  immediatelyContains_of _ y

@[simp] theorem immediatelyContains_labelledTrace (i : ι)
    (y : SyntacticObject (SyntacticObject.Leaf L ι)) :
    ¬ ImmediatelyContains (labelledTrace i) y :=
  immediatelyContains_of _ y

@[simp] theorem immediatelyContains_merge (l r y : SyntacticObject (SyntacticObject.Leaf L ι)) :
    ImmediatelyContains (merge l r) y ↔ y = l ∨ y = r :=
  immediatelyContains_mul

/-- Immediate containment is membership among the children of the object's tree. -/
theorem immediatelyContains_iff_mem_children {α : Type} {x y : SyntacticObject α} :
    ImmediatelyContains x y ↔ y.toUnorderedTree ∈ children x.toUnorderedTree := by
  induction x using FreeCommMagma.inductionOn with
  | of a => simp
  | mul l r _ _ =>
    simp only [immediatelyContains_mul, toUnorderedTree_mul, children_node,
      Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    exact (or_congr toUnorderedTree_inj toUnorderedTree_inj).symm

@[simp] theorem contains_leaf (tok : L) (y : SyntacticObject (SyntacticObject.Leaf L ι)) :
    ¬ Contains (leaf tok) y :=
  contains_of _ y

@[simp] theorem contains_trace (y : SyntacticObject (SyntacticObject.Leaf L ι)) :
    ¬ Contains trace y :=
  contains_of _ y

@[simp] theorem contains_labelledTrace (i : ι) (y : SyntacticObject (SyntacticObject.Leaf L ι)) :
    ¬ Contains (labelledTrace i) y :=
  contains_of _ y

@[simp] theorem contains_merge :
    Contains (merge l r) y ↔ ContainsOrEq l y ∨ ContainsOrEq r y :=
  contains_mul

@[simp] theorem containsOrEq_leaf (tok : L) : ContainsOrEq (leaf tok) y ↔ y = leaf tok :=
  containsOrEq_of _

@[simp] theorem containsOrEq_trace : ContainsOrEq trace y ↔ y = trace :=
  containsOrEq_of _

@[simp] theorem containsOrEq_labelledTrace (i : ι) :
    ContainsOrEq (labelledTrace i) y ↔ y = labelledTrace i :=
  containsOrEq_of _

@[simp] theorem containsOrEq_merge :
    ContainsOrEq (merge l r) y ↔ y = merge l r ∨ ContainsOrEq l y ∨ ContainsOrEq r y :=
  containsOrEq_mul

@[simp] theorem terms_leaf (tok : L) :
    (leaf tok : SyntacticObject (SyntacticObject.Leaf L ι)).terms = {leaf tok} := rfl

@[simp] theorem terms_trace :
    (trace : SyntacticObject (SyntacticObject.Leaf L ι)).terms = {trace} := rfl

@[simp] theorem terms_labelledTrace (i : ι) :
    (labelledTrace i : SyntacticObject (SyntacticObject.Leaf L ι)).terms = {labelledTrace i} := rfl

@[simp] theorem terms_merge (l r : SyntacticObject (SyntacticObject.Leaf L ι)) :
    (merge l r).terms = merge l r ::ₘ (l.terms + r.terms) :=
  terms_mul l r

/-! ### The vertex count grades containment -/

theorem numNodes_lt_of_immediatelyContains (h : ImmediatelyContains x y) :
    y.toUnorderedTree.numNodes < x.toUnorderedTree.numNodes := by
  obtain ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ := exists_form x <;> simp at h
  obtain rfl | rfl := h <;> simp <;> omega

theorem numNodes_lt_of_contains (h : Contains x y) :
    y.toUnorderedTree.numNodes < x.toUnorderedTree.numNodes :=
  transGen_minimal
      (r' := InvImage (· > ·) fun s : SyntacticObject (SyntacticObject.Leaf L ι) ↦
      s.toUnorderedTree.numNodes)
    (fun _ _ ↦ numNodes_lt_of_immediatelyContains) x y h

end SyntacticObject

/-! ### Terms -/

namespace SyntacticObject

variable {x y l r : SyntacticObject (SyntacticObject.Leaf L ι)}

@[simp] theorem map_toUnorderedTree_terms {α : Type} (s : SyntacticObject α) :
    s.terms.map toUnorderedTree = UnorderedTree.subtrees s.toUnorderedTree := by
  induction s using FreeCommMagma.inductionOn with
  | of a => rw [terms_of, Multiset.map_singleton, toUnorderedTree_of, UnorderedTree.subtrees_leaf]
  | mul l r ihl ihr =>
    rw [terms_mul, Multiset.map_cons, Multiset.map_add, ihl, ihr, toUnorderedTree_mul,
      UnorderedTree.subtrees_node_pair]

theorem toUnorderedTree_mem_subtrees {α : Type} {S U : SyntacticObject α} :
    S.toUnorderedTree ∈ U.toUnorderedTree.subtrees ↔ S ∈ U.terms := by
  rw [← map_toUnorderedTree_terms, Multiset.mem_map_of_injective toUnorderedTree_injective]

theorem mem_terms_merge_right (u C : SyntacticObject (SyntacticObject.Leaf L ι)) : C ∈
    (merge u C).terms := by
  rw [terms_merge]
  exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr (self_mem_terms C)))

/-- The terms of a term, one per vertex, are among the terms of the object. -/
theorem terms_le_terms (h : y ∈ x.terms) : y.terms ≤ x.terms := by
  induction x using ind with
  | leaf a => rw [terms_leaf, Multiset.mem_singleton] at h; rw [h]
  | trace => rw [terms_trace, Multiset.mem_singleton] at h; rw [h]
  | traceOf a => rw [terms_labelledTrace, Multiset.mem_singleton] at h; rw [h]
  | merge l r ihl ihr =>
    rw [terms_merge, Multiset.mem_cons, Multiset.mem_add] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · rw [terms_merge]
      exact ((ihl h).trans (Multiset.le_add_right _ _)).trans (Multiset.le_cons_self _ _)
    · rw [terms_merge]
      exact ((ihr h).trans (Multiset.le_add_left _ _)).trans (Multiset.le_cons_self _ _)

theorem mem_terms_antisymm (h₁ : x ∈ y.terms) (h₂ : y ∈ x.terms) : x = y := by
  rcases containsOrEq_iff_eq_or_contains.1 (mem_terms.1 h₁) with h | h
  · exact h
  rcases containsOrEq_iff_eq_or_contains.1 (mem_terms.1 h₂) with h' | h'
  · exact h'.symm
  · exact absurd (h.trans h') (contains_irrefl y)

theorem mem_terms_of_merge_mem_terms {s : SyntacticObject (SyntacticObject.Leaf L ι)}
    (h : merge l r ∈ s.terms) :
    l ∈ s.terms ∧ r ∈ s.terms :=
  ⟨terms_subset_terms (mem_terms.1 h) (mem_terms.2 (.single ((immediatelyContains_merge _ _ _).2
      (.inl rfl)))),
    terms_subset_terms (mem_terms.1 h) (mem_terms.2 (.single ((immediatelyContains_merge _ _ _).2
      (.inr rfl))))⟩

theorem count_self_terms [DecidableEq L] [DecidableEq ι]
    (s : SyntacticObject (SyntacticObject.Leaf L ι)) :
    s.terms.count s = 1 := by
  rcases exists_form s with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩
  iterate 3 simp
  have hl : merge l r ∉ l.terms := fun h ↦ contains_irrefl (merge l r)
    (TransGen.trans_left (contains_merge.2 (.inl ReflTransGen.refl)) (mem_terms.1 h))
  have hr : merge l r ∉ r.terms := fun h ↦ contains_irrefl (merge l r)
    (TransGen.trans_left (contains_merge.2 (.inr ReflTransGen.refl)) (mem_terms.1 h))
  rw [terms_merge, Multiset.count_cons_self, Multiset.count_add, Multiset.count_eq_zero.2 hl,
    Multiset.count_eq_zero.2 hr]

/-- Merging a term with an object adds one occurrence of it. -/
theorem count_terms_merge_left [DecidableEq L] [DecidableEq ι]
    (u C : SyntacticObject (SyntacticObject.Leaf L ι)) :
    (merge u C).terms.count u = C.terms.count u + 1 := by
  have hne : u ≠ merge u C := fun h ↦ (numNodes_lt_of_contains
    (contains_merge.2 (.inl ReflTransGen.refl) : Contains (merge u C) u)).ne
      (congrArg (·.toUnorderedTree.numNodes) h)
  rw [terms_merge, Multiset.count_cons_of_ne hne, Multiset.count_add, count_self_terms, add_comm]

theorem card_terms (s : SyntacticObject (SyntacticObject.Leaf L ι)) : s.terms.card =
    s.toUnorderedTree.numNodes := by
  rw [← UnorderedTree.card_subtrees, ← map_toUnorderedTree_terms, Multiset.card_map]


/-! ### C-command -/

section CCommand

variable {α : Type} {root x y l r : SyntacticObject α}

/-- `x` and `y` are sisters in `root` when they are distinct daughters of some term of
`root`. -/
def Sisters (root x y : SyntacticObject α) : Prop :=
  ∃ z ∈ root.terms, ImmediatelyContains z x ∧ ImmediatelyContains z y ∧ x ≠ y

instance [DecidableEq α] (root x y : SyntacticObject α) :
    Decidable (Sisters root x y) :=
  Multiset.decidableExistsMultiset

theorem Sisters.symm (h : Sisters root x y) : Sisters root y x :=
  let ⟨z, hz, hx, hy, hne⟩ := h; ⟨z, hz, hy, hx, hne.symm⟩

theorem Sisters.mem_left (h : Sisters root x y) : x ∈ root.terms :=
  let ⟨_, hz, hx, _, _⟩ := h; mem_terms.2 (ReflTransGen.tail (mem_terms.1 hz) hx)

theorem Sisters.mem_right (h : Sisters root x y) : y ∈ root.terms :=
  h.symm.mem_left

/-- `x` c-commands `y` in `root` when a sister of `x` contains or equals `y`. -/
def CCommands (root x y : SyntacticObject α) : Prop :=
  ∃ z ∈ root.terms, Sisters root x z ∧ ContainsOrEq z y

instance [DecidableEq α] (root x y : SyntacticObject α) :
    Decidable (CCommands root x y) :=
  Multiset.decidableExistsMultiset

theorem Sisters.cCommands (h : Sisters root x y) : CCommands root x y :=
  ⟨y, h.mem_right, h, ReflTransGen.refl⟩

/-- A c-commanded object is a term of the root. -/
theorem CCommands.mem_terms (h : CCommands root x y) : y ∈ root.terms :=
  let ⟨_, hz, _, hzy⟩ := h
  terms_subset_terms (SyntacticObject.mem_terms.1 hz) (SyntacticObject.mem_terms.2 hzy)

theorem CCommands.left_mem_terms (h : CCommands root x y) : x ∈ root.terms :=
  let ⟨_, _, hs, _⟩ := h
  hs.mem_left

theorem CCommands.mono {root' : SyntacticObject α} (h : CCommands root x y)
    (hsub : root.terms ⊆ root'.terms) : CCommands root' x y :=
  let ⟨z, hz, ⟨w, hw, hwx, hwz, hxz⟩, hzy⟩ := h
  ⟨z, hsub hz, ⟨w, hsub hw, hwx, hwz, hxz⟩, hzy⟩

theorem cCommands_merge_left (hlr : l ≠ r) (hy : y ∈ r.terms) : CCommands (l * r) l y :=
  ⟨r, mem_terms.2 (.single (immediatelyContains_mul.2 (.inr rfl))),
    ⟨l * r, self_mem_terms _, immediatelyContains_mul.2 (.inl rfl),
      immediatelyContains_mul.2 (.inr rfl), hlr⟩, mem_terms.1 hy⟩

theorem Sisters.of_merge {x z : SyntacticObject α}
    (h : Sisters (l * r) x z) :
    Sisters l x z ∨ Sisters r x z ∨ x = l ∧ z = r ∨ x = r ∧ z = l := by
  obtain ⟨w, hw, hwx, hwz, hxz⟩ := h
  rw [terms_mul, Multiset.mem_cons, Multiset.mem_add] at hw
  rcases hw with rfl | hw | hw
  · rw [immediatelyContains_mul] at hwx hwz
    rcases hwx with rfl | rfl <;> rcases hwz with rfl | rfl
    · exact absurd rfl hxz
    · exact .inr (.inr (.inl ⟨rfl, rfl⟩))
    · exact .inr (.inr (.inr ⟨rfl, rfl⟩))
    · exact absurd rfl hxz
  · exact .inl ⟨w, hw, hwx, hwz, hxz⟩
  · exact .inr (.inl ⟨w, hw, hwx, hwz, hxz⟩)

/-- Once `β` has moved, leaving the remnant `R`, nothing but `R` and the terms of `β` c-commands a
term found only in `β`: the sister of anything else lies inside `R`. -/
theorem not_cCommands_merge_of_notMem_terms {β R x y : SyntacticObject α}
    (hx : x ∉ β.terms)
    (hR : x ≠ R) (hy : y ∉ R.terms) : ¬ CCommands (β * R) x y := by
  rintro ⟨z, -, hs, hzy⟩
  rcases Sisters.of_merge hs with h | h | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact hx h.mem_left
  · exact hy (terms_subset_terms (mem_terms.1 h.mem_right) (mem_terms.2 hzy))
  · exact hx (self_mem_terms _)
  · exact hR rfl

end CCommand

/-! ### Pronounced tokens of terms -/

theorem mem_yield_iff {s : SyntacticObject (SyntacticObject.Leaf L ι)} {tok : L} :
    tok ∈ s.yield ↔ leaf tok ∈ s.terms := by
  induction s using ind with
  | leaf a => simp
  | trace => simp
  | traceOf a => simp
  | merge l r ihl ihr => simp [ihl, ihr, leaf_ne_merge]

theorem yield_le_of_mem_terms {s u : SyntacticObject (SyntacticObject.Leaf L ι)} (h : u ∈ s.terms) :
    u.yield ≤ s.yield := by
  induction s using ind with
  | leaf a => rw [terms_leaf, Multiset.mem_singleton] at h; rw [h]
  | trace => rw [terms_trace, Multiset.mem_singleton] at h; rw [h]
  | traceOf a => rw [terms_labelledTrace, Multiset.mem_singleton] at h; rw [h]
  | merge l r ihl ihr =>
    rw [terms_merge, Multiset.mem_cons, Multiset.mem_add] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · exact (ihl h).trans (by rw [yield_merge]; exact Multiset.le_add_right _ _)
    · exact (ihr h).trans (by rw [yield_merge]; exact Multiset.le_add_left _ _)

/-! ### Relabelling -/

section Map

variable {L' : Type} {f : L → L'} {x y root : SyntacticObject (SyntacticObject.Leaf L L)}

theorem terms_map (f : L → L') (s : SyntacticObject (SyntacticObject.Leaf L L)) :
    (s.map f).terms = s.terms.map (map f) := by
  induction s using ind with
  | leaf a => simp
  | trace => simp
  | traceOf a => simp
  | merge l r ihl ihr => simp [ihl, ihr]

theorem immediatelyContains_map_iff (hf : Function.Injective f) :
    ImmediatelyContains (x.map f) (y.map f) ↔ ImmediatelyContains x y := by
  rcases x.exists_form with ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [(map_injective hf).eq_iff]

theorem containsOrEq_map_iff (hf : Function.Injective f) :
    ContainsOrEq (x.map f) (y.map f) ↔ ContainsOrEq x y := by
  rw [← mem_terms, ← mem_terms, terms_map, Multiset.mem_map_of_injective (map_injective hf)]

theorem contains_map_iff (hf : Function.Injective f) :
    Contains (x.map f) (y.map f) ↔ Contains x y := by
  rw [contains_iff_containsOrEq_and_ne, contains_iff_containsOrEq_and_ne,
    containsOrEq_map_iff hf, (map_injective hf).ne_iff]

theorem sisters_map_iff (hf : Function.Injective f) :
    Sisters (root.map f) (x.map f) (y.map f) ↔ Sisters root x y := by
  simp only [Sisters, terms_map, Multiset.mem_map, exists_exists_and_eq_and,
    immediatelyContains_map_iff hf, (map_injective hf).ne_iff]

theorem cCommands_map_iff (hf : Function.Injective f) :
    CCommands (root.map f) (x.map f) (y.map f) ↔ CCommands root x y := by
  simp only [CCommands, terms_map, Multiset.mem_map, exists_exists_and_eq_and,
    sisters_map_iff hf, containsOrEq_map_iff hf]

end Map

end SyntacticObject


end Minimalist
