/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Syntax.Minimalist.SyntacticObject.Replace

/-!
# Linearized objects with their lower copies marked

Under the copy theory a moved constituent leaves a copy of itself, and externalization pronounces
only the highest. A linearized syntactic object with its lower copies marked carries both:
forgetting the marks gives the copy object, and contracting each marked subtree to the trace leaf of
its mark gives the object externalization reads, its traces silent. Marking the outermost copies of
a term mirrors replacing them in the contraction, and a c-command between pronounced leaves of the
contraction holds in the copy object.

## Main definitions

* `Minimalist.CopyMark`, `Minimalist.LinearizedSyntacticObject.Marked`: marks and marked objects.
* `Minimalist.LinearizedSyntacticObject.Marked.unmark`, `contract`: the copy object and its
  contraction.
* `Minimalist.LinearizedSyntacticObject.Marked.mark`, `find?`: marking the lower copies of a term,
  and the occurrence of a term outside the lower copies.

## Main results

* `Minimalist.LinearizedSyntacticObject.Marked.contract_mark`: marking contracts to replacement.
* `Minimalist.LinearizedSyntacticObject.Marked.map_contract_find?`: the occurrence found contracts
  to the occurrence found in the contraction.

## Implementation notes

* The contraction has the shape of the contraction quotient of Marcolli, Chomsky and Berwick, but
  plays a different role. Their account sends that quotient to the semantic interface and its
  deletion to externalization; here externalization reads the contraction, and binding at LF reads
  the copy object, as Collins argues it must.

## References

* [marcolli-chomsky-berwick-2025], Definitions 1.2.4–1.2.6 and §1.8
* [collins-2026]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject

/-- The mark on a vertex of a linearized copy object: `some l` on the root of a lower copy, `l` the
label of the trace that stands for it, and `none` elsewhere. -/
abbrev CopyMark : Type := Option (Option LexicalItem.Token)

/-- A linearized syntactic object with its lower copies marked, the datum externalization reads. The
copy object itself is a syntactic object, order and marks forgotten. -/
def LinearizedSyntacticObject.Marked : Type :=
  {t : RoseTree (CopyMark × Vertex) // IsSyntacticObject (UnorderedTree.mk (t.map Prod.snd))}

instance : DecidableEq LinearizedSyntacticObject.Marked := Subtype.instDecidableEq

namespace LinearizedSyntacticObject.Marked

/-! ### Contraction -/

/-- The contraction of a marked tree: each marked subtree becomes the trace leaf of its mark. -/
def contractTree : RoseTree (CopyMark × Vertex) → RoseTree Vertex :=
  fold fun v cs ↦ v.1.elim (.node v.2 cs) fun l ↦ .node (.inr l) []

@[simp] theorem contractTree_some (l : Option LexicalItem.Token) (a : Vertex)
    (cs : List (RoseTree (CopyMark × Vertex))) :
    contractTree (.node (some l, a) cs) = .node (.inr l) [] := by
  simp [contractTree, fold_node]

@[simp] theorem contractTree_none (a : Vertex) (cs : List (RoseTree (CopyMark × Vertex))) :
    contractTree (.node (none, a) cs) = .node a (cs.map contractTree) := by
  simp [contractTree, fold_node]

theorem isSyntacticObject_contractTree {t : RoseTree (CopyMark × Vertex)}
    (h : IsSyntacticObject (UnorderedTree.mk (t.map Prod.snd))) :
    IsSyntacticObject (UnorderedTree.mk (contractTree t)) := by
  induction t with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [isSyntacticObject_mk, map_node, licensed_node_iff] at h
    cases k with
    | some l => exact isSyntacticObject_mk_leaf (by simp)
    | none =>
      rw [contractTree_none, isSyntacticObject_mk, licensed_node_iff]
      refine ⟨(Vertex.licenses_iff_of_card_eq (by simp)).1 h.1, fun c hc ↦ ?_⟩
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact ih c' hc' (h.2 _ (List.mem_map_of_mem hc'))

variable (t : Marked)

/-- The copy object, the marks forgotten. -/
def unmark : LinearizedSyntacticObject := ⟨t.val.map Prod.snd, t.2⟩

/-- The contraction: each lower copy becomes the trace that stands for it, the form externalization
reads. It has the shape of the contraction quotient $T/^c F$ of [marcolli-chomsky-berwick-2025]
(Definition 1.2.4), though the book sends that quotient to the Conceptual-Intensional interface and
its deletion $T/^d F$ to externalization (pp. 33, 82). -/
def contract : LinearizedSyntacticObject := ⟨contractTree t.val, isSyntacticObject_contractTree t.2⟩

/-! ### Linearized objects without lower copies -/

theorem map_snd_map (s : RoseTree Vertex) :
    (s.map ((none, ·) : Vertex → CopyMark × Vertex)).map Prod.snd = s := by
  rw [← comp_map]
  exact id_map s

/-- A linearized object with no lower copy. -/
def ofLinearized (p : LinearizedSyntacticObject) : Marked :=
  ⟨p.val.map ((none, ·)), by rw [map_snd_map]; exact p.2⟩

theorem contractTree_map (s : RoseTree Vertex) :
    contractTree (s.map ((none, ·))) = s := by
  induction s with
  | node a cs ih =>
    rw [map_node, contractTree_none, List.map_map]
    exact congrArg _ ((List.map_congr_left ih).trans (List.map_id cs))

@[simp] theorem unmark_ofLinearized (p : LinearizedSyntacticObject) : (ofLinearized p).unmark = p :=
  Subtype.ext (map_snd_map p.val)

@[simp] theorem contract_ofLinearized (p : LinearizedSyntacticObject) :
    (ofLinearized p).contract = p :=
  Subtype.ext (contractTree_map p.val)

/-! ### Merge -/

/-- Merge, the new daughter `d` on edge `e`. -/
def attach (e : Edge) (d : Marked) : Marked :=
  match e with
  | .left => ⟨.node (none, Vertex.bare) [d.val, t.val], by
      simpa using (isSyntacticObject_mk_merge _ _).2 ⟨d.2, t.2⟩⟩
  | .right => ⟨.node (none, Vertex.bare) [t.val, d.val], by
      simpa using (isSyntacticObject_mk_merge _ _).2 ⟨t.2, d.2⟩⟩

variable {t}

@[simp] theorem unmark_attach (e : Edge) (d : Marked) :
    (t.attach e d).unmark = t.unmark.attach e d.unmark := by
  cases e <;> exact Subtype.ext (by simp [attach, unmark, LinearizedSyntacticObject.attach,
    LinearizedSyntacticObject.merge])

@[simp] theorem contract_attach (e : Edge) (d : Marked) :
    (t.attach e d).contract = t.contract.attach e d.contract := by
  cases e <;> exact Subtype.ext (by simp [attach, contract, LinearizedSyntacticObject.attach,
    LinearizedSyntacticObject.merge])

/-! ### Marking lower copies -/

section Mark

variable (m : SyntacticObject) (l : Option LexicalItem.Token)

/-- The tree with its root marked as a lower copy whose trace carries `l`. -/
def setMark : RoseTree (CopyMark × Vertex) → RoseTree (CopyMark × Vertex)
  | .node (_, a) cs => .node (some l, a) cs

/-- Mark every outermost subtree whose contraction is `m` as a lower copy whose trace carries `l`:
`replaceIf` on the contraction. -/
def markTree : RoseTree (CopyMark × Vertex) → RoseTree (CopyMark × Vertex) :=
  modifyIf (fun s ↦ UnorderedTree.mk (contractTree s) = m.val) (setMark l)

theorem markTree_node (v : CopyMark × Vertex) (cs : List (RoseTree (CopyMark × Vertex))) :
    markTree m l (.node v cs) =
      if UnorderedTree.mk (contractTree (.node v cs)) = m.val then setMark l (.node v cs)
      else .node v (cs.map (markTree m l)) :=
  modifyIf_node _ _ v cs

theorem map_snd_markTree (s : RoseTree (CopyMark × Vertex)) :
    (markTree m l s).map Prod.snd = s.map Prod.snd := by
  induction s with
  | node v cs ih =>
    rw [markTree_node]
    split_ifs
    · simp [setMark]
    · rw [map_node, map_node, List.map_map]
      exact congrArg _ (List.map_congr_left ih)

theorem contractTree_markTree (s : RoseTree (CopyMark × Vertex)) :
    contractTree (markTree m l s) =
      replaceIf (UnorderedTree.mk · = m.val) (.node (.inr l) []) (contractTree s) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [markTree_node]
    rcases k with _ | l' <;> split_ifs with h
    · rw [setMark, contractTree_some, contractTree_none, replaceIf_node,
        ite_eq_left (by simpa using h)]
    · rw [contractTree_none, contractTree_none, replaceIf_node, ite_eq_right (by simpa using h),
        List.map_map, List.map_map]
      exact congrArg _ (List.map_congr_left ih)
    · rw [setMark, contractTree_some, contractTree_some, replaceIf_node,
        ite_eq_left (by simpa using h)]
    · rw [contractTree_some, contractTree_some, replaceIf_node, ite_eq_right (by simpa using h),
        List.map_nil]

end Mark

/-- Mark every outermost copy of `m` as a lower copy whose trace carries `l`. -/
def mark (t : Marked) (m : SyntacticObject) (l : Option LexicalItem.Token) : Marked :=
  ⟨markTree m l t.val, by rw [map_snd_markTree]; exact t.2⟩

@[simp] theorem unmark_mark (m : SyntacticObject) (l : Option LexicalItem.Token) :
    (t.mark m l).unmark = t.unmark :=
  Subtype.ext (map_snd_markTree m l t.val)

/-- Marking the copies of `m` with its trace contracts to replacing `m` by its trace. -/
theorem contract_mark (m : SyntacticObject) (τ : SyntacticObject → Option LexicalItem.Token) :
    (t.mark m (τ m)).contract = t.contract.replace m (m.traceLinearized τ) :=
  Subtype.ext (by
    change contractTree (markTree m (τ m) t.val) =
      replaceIf _ (m.traceLinearized τ).val (contractTree t.val)
    rw [traceLinearized_val]
    exact contractTree_markTree m (τ m) t.val)

/-! ### Occurrences -/

/-- The subtrees outside the lower copies, in preorder, a lower copy itself included: the subtrees
whose contractions are the subtrees of the contraction. -/
abbrev outerSubtrees (s : RoseTree (CopyMark × Vertex)) : List (RoseTree (CopyMark × Vertex)) :=
  s.subtreesUntil (·.value.1.isSome)

theorem map_contractTree_outerSubtrees (s : RoseTree (CopyMark × Vertex)) :
    (outerSubtrees s).map contractTree = (contractTree s).subtrees := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rcases k with _ | l
    · rw [outerSubtrees, subtreesUntil_node, ite_eq_right (by simp), contractTree_none,
        subtrees_node, List.map_cons, contractTree_none, List.map_flatMap, List.flatMap_map]
      exact congrArg _ (List.flatMap_congr ih)
    · simp [subtreesUntil_node]

/-- The leftmost, outermost subtree outside the lower copies whose contraction is `target`. -/
def find? (t : Marked) (target : SyntacticObject) : Option Marked :=
  ((outerSubtrees t.val).find? fun s ↦ UnorderedTree.mk (contractTree s) = target.val).pmap
    (p := (· ∈ outerSubtrees t.val))
    (fun s hs ↦ ⟨s, (isSyntacticObject_mk _).2
      (((isSyntacticObject_mk _).1 t.2).of_isSubtree ((isSubtree_of_mem_subtreesUntil hs).map _))⟩)
    fun _ h ↦ List.mem_of_find?_eq_some h

theorem mem_terms_of_find? {target : SyntacticObject} {s : Marked} (h : t.find? target = some s) :
    s.unmark.toSyntacticObject ∈ t.unmark.toSyntacticObject.terms := by
  obtain ⟨r, hr, -, rfl⟩ := Option.pmap_eq_some_iff.1 h
  exact LinearizedSyntacticObject.mem_terms_toSyntacticObject.2
    ⟨_, mem_subtrees.2 ((isSubtree_of_mem_subtreesUntil hr).map _), rfl⟩

theorem mk_contractTree_of_find? {target : SyntacticObject} {s : Marked}
    (h : t.find? target = some s) : UnorderedTree.mk (contractTree s.val) = target.val := by
  obtain ⟨r, -, hr, rfl⟩ := Option.pmap_eq_some_iff.1 h
  simpa using List.find?_some hr

/-- The occurrence found contracts to the occurrence found in the contraction. -/
theorem map_contract_find? (target : SyntacticObject) :
    (t.find? target).map contract = t.contract.find? target := by
  apply Option.map_injective Subtype.val_injective
  rw [Option.map_map, find?, LinearizedSyntacticObject.find?, Option.map_pmap, Option.map_pmap]
  simp only [Function.comp_apply, contract, Option.pmap_eq_map]
  rw [← map_contractTree_outerSubtrees, List.find?_map]
  simp [Function.comp_def]

/-! ### Leaves -/

theorem exists_val_eq_of_unmark_eq_leaf {t : Marked} {x : LexicalItem.Token}
    (h : t.unmark.toSyntacticObject = SyntacticObject.leaf x) :
    ∃ k, t.val = .node (k, .inl (some x)) [] := by
  obtain ⟨⟨⟨k, a⟩, cs⟩, ht⟩ := t
  have hv := congrArg Subtype.val h
  simp only [unmark, LinearizedSyntacticObject.toSyntacticObject_val, map_node,
    SyntacticObject.leaf_val, UnorderedTree.leaf, UnorderedTree.mk_node_eq_mk_node_iff] at hv
  obtain ⟨rfl, hcs⟩ := hv
  have hc : cs = [] := by simpa using congrArg Multiset.card hcs
  subst hc
  exact ⟨k, rfl⟩

theorem contract_eq_leaf_of_unmark_eq_leaf {t : Marked} {x : LexicalItem.Token}
    (h : t.unmark.toSyntacticObject = SyntacticObject.leaf x)
    (hx : x ∈ t.contract.toSyntacticObject.yield) :
    t.contract.toSyntacticObject = SyntacticObject.leaf x := by
  obtain ⟨k, hk⟩ := exists_val_eq_of_unmark_eq_leaf h
  rcases k with _ | l
  · exact Subtype.ext (by simp [contract, hk, SyntacticObject.leaf_val])
  · simp [LinearizedSyntacticObject.yield_toSyntacticObject, contract, hk] at hx

theorem eq_leaf_of_find? {t s : Marked} {target : SyntacticObject} {x : LexicalItem.Token}
    (h : t.find? target = some s) (ht : target.val.value.isLeft)
    (hs : s.unmark.toSyntacticObject = SyntacticObject.leaf x) :
    target = SyntacticObject.leaf x := by
  have hc := mk_contractTree_of_find? h
  obtain ⟨k, hk⟩ := exists_val_eq_of_unmark_eq_leaf hs
  rw [hk] at hc
  rcases k with _ | l
  · exact Subtype.ext (by rw [← hc, contractTree_none, SyntacticObject.leaf_val]; rfl)
  · rw [← hc, contractTree_some] at ht
    simp at ht

end LinearizedSyntacticObject.Marked

end Minimalist
