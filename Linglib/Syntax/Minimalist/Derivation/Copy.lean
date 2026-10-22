/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Monadic
public import Linglib.Syntax.Minimalist.Linearization.Replay

/-!
# Derivations with copies

Under the copy theory Internal Merge merges a copy of the mover and leaves the mover in place. The
copy object a derivation builds is a syntactic object, on which Internal Merge is Merge with one of
the object's own terms, and the terms of each stage are terms of every later one. Externalization
reads the planar copy object with its lower copies marked: their contraction (Definition 1.2.4 of
the algebraic account of Merge) is the replay with traces, which pronounces each token once.

## Main definitions

* `Minimalist.Derivation.copyObject?`: the copy object, a syntactic object.
* `Minimalist.PlanarSyntacticObject.Marked`, `Minimalist.Derivation.replayWithCopies?`: the planar
  copy object with its lower copies marked, the datum externalization reads; `unmark` and
  `contract` read off the copy object and its contraction.

## Main results

* `Minimalist.Derivation.copyObject?_append_em`, `copyObject?_append_im`: External Merge merges the
  copy object with an item from outside, Internal Merge with one of its own terms.
* `Minimalist.Derivation.terms_subset_copyObject?_append`: preservation of terms.
* `Minimalist.Derivation.map_contract_replayWithCopies?`: contracting the lower copies gives the
  replay with traces.
* `Minimalist.Derivation.coe_surfaceTokens`: chain reduction, each merged token pronounced once.

## TODO

* Steps name their movers in the replay with traces, so a remnant mover carries traces and the copy
  object depends on the trace encoder `τ`. Name movers independently of traces, or prove the copy
  object independent of `τ` when no token is merged twice.
* The lower copies as an admissible cut of the copy object, the one its contraction contracts.

## References

* [marcolli-chomsky-berwick-2025], Definitions 1.2.4–1.2.6 and §1.8
* [nunes-2004]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject

/-- The mark on a vertex of a planar copy object: `some l` on the root of a lower copy, `l` the
label of the trace that stands for it, and `none` elsewhere. -/
abbrev CopyMark : Type := Option (Option LexicalItem.Token)

/-- A planar syntactic object with its lower copies marked, the datum externalization reads. The
copy object itself is a syntactic object, order and marks forgotten. -/
def PlanarSyntacticObject.Marked : Type :=
  {t : RoseTree (CopyMark × Vertex) // IsSyntacticObject (UnorderedTree.mk (t.map Prod.snd))}

instance : DecidableEq PlanarSyntacticObject.Marked := Subtype.instDecidableEq

namespace PlanarSyntacticObject.Marked

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
def unmark : PlanarSyntacticObject := ⟨t.val.map Prod.snd, t.2⟩

/-- The contraction: each lower copy becomes the trace that stands for it, the form
externalization reads ([marcolli-chomsky-berwick-2025] Definition 1.2.4). -/
def contract : PlanarSyntacticObject := ⟨contractTree t.val, isSyntacticObject_contractTree t.2⟩

/-! ### Planar objects without lower copies -/

theorem map_snd_map (s : RoseTree Vertex) :
    (s.map ((none, ·) : Vertex → CopyMark × Vertex)).map Prod.snd = s := by
  rw [← comp_map]
  exact id_map s

/-- A planar object with no lower copy. -/
def ofPlanar (p : PlanarSyntacticObject) : Marked :=
  ⟨p.val.map ((none, ·)), by rw [map_snd_map]; exact p.2⟩

theorem contractTree_map (s : RoseTree Vertex) :
    contractTree (s.map ((none, ·))) = s := by
  induction s with
  | node a cs ih =>
    rw [map_node, contractTree_none, List.map_map]
    exact congrArg _ ((List.map_congr_left ih).trans (List.map_id cs))

@[simp] theorem unmark_ofPlanar (p : PlanarSyntacticObject) : (ofPlanar p).unmark = p :=
  Subtype.ext (map_snd_map p.val)

@[simp] theorem contract_ofPlanar (p : PlanarSyntacticObject) : (ofPlanar p).contract = p :=
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
  cases e <;> exact Subtype.ext (by simp [attach, unmark, PlanarSyntacticObject.attach,
    PlanarSyntacticObject.merge])

@[simp] theorem contract_attach (e : Edge) (d : Marked) :
    (t.attach e d).contract = t.contract.attach e d.contract := by
  cases e <;> exact Subtype.ext (by simp [attach, contract, PlanarSyntacticObject.attach,
    PlanarSyntacticObject.merge])

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

/-- Marking changes no vertex of the copy object. -/
theorem map_snd_markTree (s : RoseTree (CopyMark × Vertex)) :
    (markTree m l s).map Prod.snd = s.map Prod.snd := by
  induction s with
  | node v cs ih =>
    rw [markTree_node]
    split_ifs
    · simp [setMark]
    · rw [map_node, map_node, List.map_map]
      exact congrArg _ (List.map_congr_left ih)

/-- Marking the copies of `m` contracts to replacing `m` in the contraction. -/
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

/-- Marking a lower copy leaves the copy object as it was. -/
@[simp] theorem unmark_mark (m : SyntacticObject) (l : Option LexicalItem.Token) :
    (t.mark m l).unmark = t.unmark :=
  Subtype.ext (map_snd_markTree m l t.val)

/-- Marking the copies of `m` with its trace contracts to replacing `m` by its trace. -/
theorem contract_mark (m : SyntacticObject) (τ : SyntacticObject → Option LexicalItem.Token) :
    (t.mark m (τ m)).contract = t.contract.replace m (m.tracePlanar τ) :=
  Subtype.ext (by
    change contractTree (markTree m (τ m) t.val) =
      replaceIf _ (m.tracePlanar τ).val (contractTree t.val)
    rw [tracePlanar_val]
    exact contractTree_markTree m (τ m) t.val)

/-! ### Occurrences -/

mutual
/-- The subtrees outside the lower copies, in preorder, a lower copy itself included: the subtrees
whose contractions are the subtrees of the contraction. -/
def outerSubtrees :
    RoseTree (CopyMark × Vertex) →
      List (RoseTree (CopyMark × Vertex))
  | .node (some l, a) cs => [.node (some l, a) cs]
  | .node (none, a) cs => .node (none, a) cs :: outerSubtreesList cs
/-- `outerSubtrees` of the trees of a list. -/
def outerSubtreesList :
    List (RoseTree (CopyMark × Vertex)) →
      List (RoseTree (CopyMark × Vertex))
  | [] => []
  | c :: cs => outerSubtrees c ++ outerSubtreesList cs
end

theorem outerSubtreesList_eq (cs : List (RoseTree (CopyMark × Vertex))) :
    outerSubtreesList cs = cs.flatMap outerSubtrees := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [outerSubtreesList, ih, List.flatMap_cons]

theorem map_contractTree_outerSubtrees (s : RoseTree (CopyMark × Vertex)) :
    (outerSubtrees s).map contractTree = (contractTree s).subtrees := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rcases k with _ | l
    · rw [outerSubtrees, outerSubtreesList_eq, contractTree_none, subtrees_node, List.map_cons,
        contractTree_none, List.map_flatMap, List.flatMap_map]
      exact congrArg _ (List.flatMap_congr ih)
    · simp [outerSubtrees]

theorem isSubtree_of_mem_outerSubtrees {r s : RoseTree (CopyMark × Vertex)}
    (h : r ∈ outerSubtrees s) : IsSubtree r s := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rcases k with _ | l
    · rw [outerSubtrees, outerSubtreesList_eq, List.mem_cons, List.mem_flatMap] at h
      rcases h with rfl | ⟨c, hc, hr⟩
      · exact .refl _
      · exact (ih c hc hr).trans (.of_mem_children hc)
    · rw [outerSubtrees, List.mem_singleton] at h
      exact h ▸ .refl _

/-- The leftmost, outermost subtree outside the lower copies whose contraction is `target`. -/
def find? (t : Marked) (target : SyntacticObject) : Option Marked :=
  ((outerSubtrees t.val).find? fun s ↦ UnorderedTree.mk (contractTree s) = target.val).pmap
    (p := (· ∈ outerSubtrees t.val))
    (fun s hs ↦ ⟨s, (isSyntacticObject_mk _).2
      (((isSyntacticObject_mk _).1 t.2).of_isSubtree ((isSubtree_of_mem_outerSubtrees hs).map _))⟩)
    fun _ h ↦ List.mem_of_find?_eq_some h

/-- The occurrence found is a term of the copy object. -/
theorem mem_terms_of_find? {target : SyntacticObject} {s : Marked} (h : t.find? target = some s) :
    s.unmark.toSyntacticObject ∈ t.unmark.toSyntacticObject.terms := by
  obtain ⟨r, hr, -, rfl⟩ := Option.pmap_eq_some_iff.1 h
  exact PlanarSyntacticObject.mem_terms_toSyntacticObject.2
    ⟨_, mem_subtrees.2 ((isSubtree_of_mem_outerSubtrees hr).map _), rfl⟩

/-- The occurrence found contracts to the target. -/
theorem mk_contractTree_of_find? {target : SyntacticObject} {s : Marked}
    (h : t.find? target = some s) : UnorderedTree.mk (contractTree s.val) = target.val := by
  obtain ⟨r, -, hr, rfl⟩ := Option.pmap_eq_some_iff.1 h
  simpa using List.find?_some hr

/-- The occurrence found contracts to the occurrence found in the contraction. -/
theorem map_contract_find? (target : SyntacticObject) :
    (t.find? target).map contract = t.contract.find? target := by
  apply Option.map_injective Subtype.val_injective
  rw [Option.map_map, find?, PlanarSyntacticObject.find?, Option.map_pmap, Option.map_pmap]
  simp only [Function.comp_apply, contract, Option.pmap_eq_map]
  rw [← map_contractTree_outerSubtrees, List.find?_map]
  simp [Function.comp_def]

/-! ### Leaves -/

/-- A marked object whose copy object is a lexical leaf is that leaf, perhaps marked. -/
theorem exists_val_eq_of_unmark_eq_leaf {t : Marked} {x : LexicalItem.Token}
    (h : t.unmark.toSyntacticObject = SyntacticObject.leaf x) :
    ∃ k, t.val = .node (k, .inl (some x)) [] := by
  obtain ⟨⟨⟨k, a⟩, cs⟩, ht⟩ := t
  have hv := congrArg Subtype.val h
  simp only [unmark, PlanarSyntacticObject.toSyntacticObject_val, map_node,
    SyntacticObject.leaf_val, UnorderedTree.leaf, UnorderedTree.mk_node_eq_mk_node_iff] at hv
  obtain ⟨rfl, hcs⟩ := hv
  have hc : cs = [] := by simpa using congrArg Multiset.card hcs
  subst hc
  exact ⟨k, rfl⟩

/-- A copy object that is a lexical leaf contracts to that leaf when the leaf is pronounced. -/
theorem contract_eq_leaf_of_unmark_eq_leaf {t : Marked} {x : LexicalItem.Token}
    (h : t.unmark.toSyntacticObject = SyntacticObject.leaf x)
    (hx : x ∈ t.contract.toSyntacticObject.yield) :
    t.contract.toSyntacticObject = SyntacticObject.leaf x := by
  obtain ⟨k, hk⟩ := exists_val_eq_of_unmark_eq_leaf h
  rcases k with _ | l
  · exact Subtype.ext (by simp [contract, hk, SyntacticObject.leaf_val])
  · simp [PlanarSyntacticObject.yield_toSyntacticObject, contract, hk] at hx

/-- An occurrence found whose copy is a lexical leaf is that leaf, when the target is no trace. -/
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

/-! ### C-command in the contraction and in the copy object -/

/-- A subtree contracting to a lexical leaf is that leaf, unmarked. -/
theorem eq_of_mk_contractTree_eq_leaf {r : RoseTree (CopyMark × Vertex)} {x : LexicalItem.Token}
    (h : UnorderedTree.mk (contractTree r) = (SyntacticObject.leaf x).val) :
    r = .node (none, .inl (some x)) [] := by
  obtain ⟨⟨k, a⟩, cs⟩ := r
  rcases k with _ | l
  · rw [contractTree_none, SyntacticObject.leaf_val, UnorderedTree.leaf,
      UnorderedTree.mk_node_eq_mk_node_iff] at h
    obtain ⟨rfl, hcs⟩ := h
    have hc : cs = [] := by simpa using congrArg Multiset.card hcs
    rw [hc]
  · rw [contractTree_some, SyntacticObject.leaf_val, UnorderedTree.leaf,
      UnorderedTree.mk_node_eq_mk_node_iff] at h
    exact absurd h.1 (by simp)

private theorem isSyntacticObject_of_isSubtree {t : Marked} {r : RoseTree (CopyMark × Vertex)}
    (hr : IsSubtree r t.val) : IsSyntacticObject (UnorderedTree.mk (r.map Prod.snd)) :=
  (isSyntacticObject_mk _).2 (((isSyntacticObject_mk _).1 t.2).of_isSubtree (hr.map _))

private theorem mem_terms_unmark {t : Marked} {r : RoseTree (CopyMark × Vertex)}
    (hr : IsSubtree r t.val) :
    (⟨_, isSyntacticObject_of_isSubtree hr⟩ : SyntacticObject) ∈ t.unmark.toSyntacticObject.terms :=
  PlanarSyntacticObject.mem_terms_toSyntacticObject.2 ⟨_, mem_subtrees.2 (hr.map _), rfl⟩

/-- A c-command between two pronounced leaves of the contraction holds between the same leaves of
the copy object, the contraction changing nothing outside the lower copies. -/
theorem cCommands_unmark_of_cCommands_contract {t : Marked} {x y : LexicalItem.Token}
    (hxy : x ≠ y) (h : t.contract.toSyntacticObject.CCommands ↑x ↑y) :
    t.unmark.toSyntacticObject.CCommands ↑x ↑y := by
  obtain ⟨z, -, ⟨w, hw, hwx, hwz, hxz⟩, hzy⟩ := h
  obtain ⟨q, hq, hqw⟩ := PlanarSyntacticObject.mem_terms_toSyntacticObject.1 hw
  rw [show t.contract.val = contractTree t.val from rfl, ← map_contractTree_outerSubtrees] at hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
  have hrt := isSubtree_of_mem_outerSubtrees hr
  obtain ⟨⟨k, a⟩, rs⟩ := r
  rcases k with _ | l
  swap
  · simp [ImmediatelyContains, ← hqw] at hwx
  simp only [ImmediatelyContains, ← hqw, contractTree_none, UnorderedTree.children_mk,
    Multiset.mem_coe, List.mem_map] at hwx hwz
  obtain ⟨ci, hci, hix⟩ := hwx
  obtain ⟨ri, hri, rfl⟩ := List.mem_map.1 (show ci ∈ rs.map contractTree from hci)
  obtain rfl := eq_of_mk_contractTree_eq_leaf hix
  obtain ⟨cj, hcj, hjz⟩ := hwz
  obtain ⟨rj, hrj, rfl⟩ := List.mem_map.1 (show cj ∈ rs.map contractTree from hcj)
  -- `y` is a pronounced leaf of `rj`
  have hy : ∃ r' ∈ outerSubtrees rj, r' = .node (none, .inl (some y)) [] := by
    have := (val_mem_subtrees.2 (mem_terms.2 hzy))
    rw [← hjz, UnorderedTree.subtrees_mk, unorderedSubtrees_eq_map, Multiset.mem_coe,
      List.mem_map, ← map_contractTree_outerSubtrees] at this
    obtain ⟨q', hq', hq'y⟩ := this
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hq'
    exact ⟨r', hr', eq_of_mk_contractTree_eq_leaf hq'y⟩
  obtain ⟨r', hr', rfl⟩ := hy
  have hjt : IsSubtree rj t.val := (IsSubtree.of_mem_children hrj).trans hrt
  set zc : SyntacticObject := ⟨_, isSyntacticObject_of_isSubtree hjt⟩
  have hzcy : SyntacticObject.leaf y ∈ zc.terms :=
    val_mem_subtrees.1 (by
      rw [UnorderedTree.subtrees_mk, unorderedSubtrees_eq_map, Multiset.mem_coe]
      exact List.mem_map.2 ⟨_, mem_subtrees.2 ((isSubtree_of_mem_outerSubtrees hr').map _), rfl⟩)
  refine ⟨zc, mem_terms_unmark hjt, ⟨_, mem_terms_unmark hrt, ?_, ?_, fun he ↦ ?_⟩,
    mem_terms.1 hzcy⟩
  · simp only [ImmediatelyContains, map_node, UnorderedTree.children_mk, Multiset.mem_coe,
      List.mem_map]
    exact ⟨_, show _ ∈ rs.map (map Prod.snd) from List.mem_map_of_mem hri, rfl⟩
  · simp only [ImmediatelyContains, map_node, UnorderedTree.children_mk, Multiset.mem_coe,
      List.mem_map]
    exact ⟨_, show _ ∈ rs.map (map Prod.snd) from List.mem_map_of_mem hrj, rfl⟩
  · rw [← he, terms_leaf, Multiset.mem_singleton, leaf_inj] at hzcy
    exact hxy hzcy.symm

end PlanarSyntacticObject.Marked

/-! ### The replay with copies -/

open Derivation (Cfg)
open PlanarSyntacticObject (Marked)

/-- A step on a marked configuration, `Step.replay?` keeping the copies. Internal Merge merges a
copy of the leftmost outermost occurrence of the mover and marks the occurrences it leaves as
lower copies, each with the trace of the mover's head under `τ`; an extraction stacks the copy. -/
def Step.replayWithCopies? (step : Step) (c : Cfg Marked)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option (Cfg Marked) :=
  match step, c with
  | .em side item, ⟨p, st⟩ => item.toPlanarLeaf?.map fun i ↦ ⟨p.attach side (.ofPlanar i), st⟩
  | .im mover side, ⟨p, st⟩ =>
      (p.find? mover).map fun s ↦ ⟨(p.mark mover (τ mover)).attach side s, st⟩
  | .extract mover, ⟨p, st⟩ => (p.find? mover).map fun s ↦ ⟨p.mark mover (τ mover), s :: st⟩
  | .remerge side, ⟨p, m :: st⟩ => some ⟨p.attach side m, st⟩
  | .remerge _, ⟨_, []⟩ => none

/-- The derivation's marked configuration under the trace encoder `τ`, `none` exactly when
`Derivation.replay?` is. -/
def Derivation.replayWithCopies? (d : Derivation)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option (Cfg Marked) :=
  d.initial.toPlanarLeaf?.bind fun p ↦
    d.steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) ⟨.ofPlanar p, []⟩

variable {τ : SyntacticObject → Option LexicalItem.Token}

/-- Contracting the copies of a step with copies gives the step with traces. -/
theorem Step.map_contract_replayWithCopies? (step : Step) (c : Cfg Marked) :
    (step.replayWithCopies? c τ).map (Cfg.map Marked.contract) =
      step.replay? (c.map Marked.contract) τ := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item =>
    simp only [Step.replayWithCopies?, Step.replay?, Option.map_map]
    congr 1
    funext i
    simp [Cfg.map]
  | im mover side =>
    simp only [Step.replayWithCopies?, Step.replay?, Cfg.map]
    rw [← Marked.map_contract_find?, Option.map_map, Option.map_map]
    congr 1
    funext s
    simp [Cfg.map, Marked.contract_mark]
  | extract mover =>
    simp only [Step.replayWithCopies?, Step.replay?, Cfg.map]
    rw [← Marked.map_contract_find?, Option.map_map, Option.map_map]
    congr 1
    funext s
    simp [Cfg.map, Marked.contract_mark]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩ <;> simp [Step.replayWithCopies?, Step.replay?, Cfg.map]

/-- Contracting the copies of the replay with copies gives the replay with traces. -/
theorem Derivation.map_contract_replayWithCopies? (d : Derivation) :
    (d.replayWithCopies? τ).map (Cfg.map Marked.contract) = d.replay? τ := by
  rw [replayWithCopies?, replay?, Option.map_bind]
  congr 1
  funext p
  rw [Function.comp_apply, List.map_foldlM (g := fun c (step : Step) ↦ step.replay? c τ)
    (fun c step ↦ Step.map_contract_replayWithCopies? step c)]
  simp [Cfg.map]

/-- The externalized object is the contraction of the copy object. -/
theorem Derivation.externalize?_eq_map_replayWithCopies? (d : Derivation) :
    d.externalize? τ = (d.replayWithCopies? τ).map (·.current.contract) := by
  rw [externalize?, ← d.map_contract_replayWithCopies?, Option.map_map]
  rfl

/-- The replay with copies fails exactly when the replay with traces does. -/
theorem Derivation.isSome_replayWithCopies? (d : Derivation) :
    (d.replayWithCopies? τ).isSome = (d.replay? τ).isSome := by
  rw [← d.map_contract_replayWithCopies?, Option.isSome_map]

/-- Internal Merge with copies merges a copy of a subtree of the copy object onto the object
unchanged: Extension and No Tampering. -/
theorem Step.unmark_replayWithCopies?_im {mover : SyntacticObject} {side : Edge}
    {c c' : Cfg Marked} (h : (Step.im mover side).replayWithCopies? c τ = some c') :
    ∃ s : Marked, IsSubtree s.unmark.val c.current.unmark.val ∧
      c'.current.unmark = c.current.unmark.attach side s.unmark := by
  obtain ⟨p, st⟩ := c
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨s, ?_, by simp⟩
  obtain ⟨r, hr, -, rfl⟩ := Option.pmap_eq_some_iff.1 hs
  exact (Marked.isSubtree_of_mem_outerSubtrees hr).map _

/-! ### The copy object -/

/-- The derivation's copy object, the syntactic object with every copy in place and neither order
nor marks: the form the semantic interface receives. -/
def Derivation.copyObject? (d : Derivation)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option SyntacticObject :=
  (d.replayWithCopies? τ).map (·.current.unmark.toSyntacticObject)

theorem Derivation.replayWithCopies?_append (d : Derivation) (steps : List Step) :
    (d.append steps).replayWithCopies? τ = (d.replayWithCopies? τ).bind fun c ↦
      steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) c := by
  simp only [replayWithCopies?, append, List.foldlM_append, Option.bind_assoc]
  rfl

/-- External Merge merges the copy object with the item. -/
theorem Step.toSyntacticObject_replayWithCopies?_em {side : Edge} {item : SyntacticObject}
    {c c' : Cfg Marked} (h : (Step.em side item).replayWithCopies? c τ = some c') :
    c'.current.unmark.toSyntacticObject = merge item c.current.unmark.toSyntacticObject := by
  obtain ⟨p, st⟩ := c
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
  simp [SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hi]

/-- Internal Merge merges the copy object with one of its own terms. -/
theorem Step.toSyntacticObject_replayWithCopies?_im {mover : SyntacticObject} {side : Edge}
    {c c' : Cfg Marked} (h : (Step.im mover side).replayWithCopies? c τ = some c') :
    ∃ u ∈ c.current.unmark.toSyntacticObject.terms,
      c'.current.unmark.toSyntacticObject = merge u c.current.unmark.toSyntacticObject := by
  obtain ⟨s, hs, he⟩ := Step.unmark_replayWithCopies?_im h
  refine ⟨s.unmark.toSyntacticObject, ?_,
    by rw [he, PlanarSyntacticObject.toSyntacticObject_attach]⟩
  exact PlanarSyntacticObject.mem_terms_toSyntacticObject.2 ⟨_, mem_subtrees.2 hs, rfl⟩

private theorem mem_terms_merge_right (u C : SyntacticObject) : C ∈ (merge u C).terms := by
  rw [terms_merge]
  exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr (self_mem_terms C)))

/-- Each step keeps the copy object as a term of the next. -/
theorem Step.mem_terms_replayWithCopies? {step : Step} {c c' : Cfg Marked}
    (h : step.replayWithCopies? c τ = some c') :
    c.current.unmark.toSyntacticObject ∈ c'.current.unmark.toSyntacticObject.terms := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item =>
    rw [Step.toSyntacticObject_replayWithCopies?_em h]
    exact mem_terms_merge_right _ _
  | im mover side =>
    obtain ⟨u, -, hu⟩ := Step.toSyntacticObject_replayWithCopies?_im h
    rw [hu]
    exact mem_terms_merge_right _ _
  | extract mover =>
    obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Marked.unmark_mark]
    exact self_mem_terms _
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp only [Marked.unmark_attach, PlanarSyntacticObject.toSyntacticObject_attach]
      exact mem_terms_merge_right _ _

private theorem mem_terms_foldlM_replayWithCopies? :
    ∀ {steps : List Step} {c c' : Cfg Marked},
      steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) c = some c' →
        c.current.unmark.toSyntacticObject ∈ c'.current.unmark.toSyntacticObject.terms
  | [], _, _, h => by obtain rfl := Option.some.inj h; exact self_mem_terms _
  | step :: steps, _, _, h => by
    obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    exact terms_subset_terms (mem_terms.1 (mem_terms_foldlM_replayWithCopies? h))
      (Step.mem_terms_replayWithCopies? h₁)

/-- Preservation of terms: the terms of the copy object at a stage are terms of the copy object at
every later stage. -/
theorem Derivation.terms_subset_copyObject?_append {d : Derivation} {steps : List Step}
    {C' : SyntacticObject} (h : (d.append steps).copyObject? τ = some C') :
    ∃ C ∈ d.copyObject? τ, C.terms ⊆ C'.terms := by
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 h
  rw [replayWithCopies?_append] at hc'
  obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some_iff.1 hc'
  exact ⟨_, Option.map_eq_some_iff.2 ⟨c, hc, rfl⟩,
    terms_subset_terms (mem_terms.1 (mem_terms_foldlM_replayWithCopies? hc'))⟩

/-- External Merge merges the copy object with the item, a leaf from outside. -/
theorem Derivation.copyObject?_append_em (d : Derivation) (side : Edge) (item : SyntacticObject) :
    (d.append [.em side item]).copyObject? τ =
      (d.copyObject? τ).bind fun C ↦ item.toPlanarLeaf?.map fun _ ↦ merge item C := by
  simp only [copyObject?, replayWithCopies?_append, Option.map_bind, Option.bind_map]
  congr 1
  funext c
  rcases h : item.toPlanarLeaf? with _ | i
  · simp [Step.replayWithCopies?, h]
  · simp [Step.replayWithCopies?, h, SyntacticObject.toSyntacticObject_of_toPlanarLeaf? h]

/-- Internal Merge merges the copy object with one of its own terms, so Internal and External
Merge are one operation, differing in where its object comes from. -/
theorem Derivation.copyObject?_append_im {d : Derivation} {mover : SyntacticObject} {side : Edge}
    {C' : SyntacticObject} (h : (d.append [.im mover side]).copyObject? τ = some C') :
    ∃ C ∈ d.copyObject? τ, ∃ u ∈ C.terms, C' = merge u C := by
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 h
  rw [replayWithCopies?_append] at hc'
  obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some_iff.1 hc'
  exact ⟨_, Option.map_eq_some_iff.2 ⟨c, hc, rfl⟩,
    Step.toSyntacticObject_replayWithCopies?_im (by simpa using hc')⟩

/-! ### Pronunciation -/

/-- The pronounced tokens of a configuration, its object's and those of the copies on its stack. -/
private def cfgYield (c : Cfg PlanarSyntacticObject) : Multiset LexicalItem.Token :=
  c.current.toSyntacticObject.yield + (c.stack.map (·.toSyntacticObject.yield)).sum

private theorem Step.cfgYield_replay? {step : Step} {c c' : Cfg PlanarSyntacticObject}
    (hc : (cfgYield c + (step.items.map SyntacticObject.yield).sum).Nodup)
    (h : step.replay? c τ = some c') :
    cfgYield c' = cfgYield c + (step.items.map SyntacticObject.yield).sum := by
  obtain ⟨p, st⟩ := c
  have hp : p.toSyntacticObject.yield.Nodup :=
    Multiset.nodup_of_le ((Multiset.le_add_right _ _).trans (Multiset.le_add_right _ _)) hc
  cases step with
  | em side item =>
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [← SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hi]
    simp only [cfgYield, Step.items, Multiset.map_singleton, Multiset.sum_singleton,
      PlanarSyntacticObject.yield_attach]
    abel
  | im mover side =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [cfgYield, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero,
      PlanarSyntacticObject.yield_attach]
    rw [add_comm s.toSyntacticObject.yield, PlanarSyntacticObject.yield_replace_add_yield τ hp hs]
  | extract mover =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [cfgYield, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero, List.map_cons,
      List.sum_cons]
    rw [← add_assoc, PlanarSyntacticObject.yield_replace_add_yield τ hp hs]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp only [cfgYield, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero,
        List.map_cons, List.sum_cons, PlanarSyntacticObject.yield_attach]
      abel

private theorem cfgYield_foldlM_replay? : ∀ {steps : List Step} {c c' : Cfg PlanarSyntacticObject},
    steps.foldlM (fun c step ↦ step.replay? c τ) c = some c' →
    (cfgYield c + ((Step.itemsList steps).map SyntacticObject.yield).sum).Nodup →
    cfgYield c' = cfgYield c + ((Step.itemsList steps).map SyntacticObject.yield).sum
  | [], _, _, h, _ => by obtain rfl := Option.some.inj h; simp
  | step :: steps, c, _, h, hn => by
    obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    rw [Step.itemsList_cons, Multiset.map_add, Multiset.sum_add, ← add_assoc] at hn ⊢
    have e₁ := Step.cfgYield_replay? (Multiset.nodup_of_le (Multiset.le_add_right _ _) hn) h₁
    rw [← e₁] at hn ⊢
    exact cfgYield_foldlM_replay? h hn

/-- When no token is merged twice, a derivation pronounces each token it merges once, in its
object or in a copy left on the stack, however many copies its movements leave. -/
theorem Derivation.yield_replay? {d : Derivation} {c : Cfg PlanarSyntacticObject}
    (hd : d.lexTokens.Nodup) (h : d.replay? τ = some c) :
    c.current.toSyntacticObject.yield + (c.stack.map (·.toSyntacticObject.yield)).sum =
      d.lexTokens := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  have h0 : cfgYield ⟨p, []⟩ = d.initial.yield := by
    simp [cfgYield, SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hp]
  have := cfgYield_foldlM_replay? h (by rwa [h0])
  rwa [h0] at this

/-- Chain reduction ([nunes-2004]): when no token is merged twice and no extracted copy is left on
the stack, a derivation pronounces every token it merges exactly once. -/
theorem Derivation.coe_surfaceTokens {d : Derivation} (hd : d.lexTokens.Nodup)
    (h : d.replay?.map (·.stack) = some []) : (d.surfaceTokens : Multiset _) = d.lexTokens := by
  obtain ⟨c, hc, hst⟩ := Option.map_eq_some_iff.1 h
  have := d.yield_replay? hd hc
  rw [hst, List.map_nil, List.sum_nil, add_zero] at this
  rw [surfaceTokens, externalize?, hc, Option.map_some, Option.map_some, Option.getD_some,
    PlanarSyntacticObject.coe_yield, this]

/-! ### Inclusiveness -/

namespace SyntacticObject

/-- A token is pronounced in an object exactly when its leaf is a term. -/
theorem mem_yield_iff {s : SyntacticObject} {tok : LexicalItem.Token} :
    tok ∈ s.yield ↔ leaf tok ∈ s.terms := by
  induction s using ind with
  | leaf a => simp
  | trace => simp
  | traceOf a => simp
  | merge l r ihl ihr => simp [ihl, ihr, leaf_ne_merge]

/-- A term pronounces no more than its object. -/
theorem yield_le_of_mem_terms {s u : SyntacticObject} (h : u ∈ s.terms) : u.yield ≤ s.yield := by
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

/-- The tokens a configuration's copy object and stacked copies pronounce. -/
private def cfgCopyYield (c : Cfg Marked) : Multiset LexicalItem.Token :=
  c.current.unmark.toSyntacticObject.yield + (c.stack.map (·.unmark.toSyntacticObject.yield)).sum

private theorem Step.mem_cfgCopyYield {step : Step} {c c' : Cfg Marked}
    (h : step.replayWithCopies? c τ = some c') {tok : LexicalItem.Token}
    (ht : tok ∈ cfgCopyYield c') :
    tok ∈ cfgCopyYield c ∨ tok ∈ (step.items.map SyntacticObject.yield).sum := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item =>
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [← SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hi]
    simp only [cfgCopyYield, Marked.unmark_attach, Marked.unmark_ofPlanar,
      PlanarSyntacticObject.yield_attach, Step.items, Multiset.map_singleton,
      Multiset.sum_singleton, Multiset.mem_add] at ht ⊢
    tauto
  | im mover side =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    have hle := SyntacticObject.yield_le_of_mem_terms (Marked.mem_terms_of_find? hs)
    simp only [cfgCopyYield, Marked.unmark_attach, Marked.unmark_mark,
      PlanarSyntacticObject.yield_attach, Multiset.mem_add] at ht ⊢
    rcases ht with (ht | ht) | ht
    · exact .inl (.inl (Multiset.mem_of_le hle ht))
    · exact .inl (.inl ht)
    · exact .inl (.inr ht)
  | extract mover =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    have hle := SyntacticObject.yield_le_of_mem_terms (Marked.mem_terms_of_find? hs)
    simp only [cfgCopyYield, Marked.unmark_mark, List.map_cons, List.sum_cons,
      Multiset.mem_add] at ht ⊢
    rcases ht with ht | ht | ht
    · exact .inl (.inl ht)
    · exact .inl (.inl (Multiset.mem_of_le hle ht))
    · exact .inl (.inr ht)
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp only [cfgCopyYield, Marked.unmark_attach, PlanarSyntacticObject.yield_attach,
        List.map_cons, List.sum_cons, Multiset.mem_add] at ht ⊢
      tauto

private theorem mem_cfgCopyYield_foldlM : ∀ {steps : List Step} {c c' : Cfg Marked},
    steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) c = some c' →
    ∀ tok ∈ cfgCopyYield c',
      tok ∈ cfgCopyYield c ∨ tok ∈ ((Step.itemsList steps).map SyntacticObject.yield).sum
  | [], _, _, h, _, ht => by obtain rfl := Option.some.inj h; exact .inl ht
  | step :: steps, _, _, h, tok, ht => by
    obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    rw [Step.itemsList_cons, Multiset.map_add, Multiset.sum_add, Multiset.mem_add]
    rcases mem_cfgCopyYield_foldlM h tok ht with ht | ht
    · rcases Step.mem_cfgCopyYield h₁ ht with ht | ht
      · exact .inl ht
      · exact .inr (.inl ht)
    · exact .inr (.inr ht)

/-- Inclusiveness: the copy object pronounces only tokens the derivation merges. -/
theorem Derivation.mem_lexTokens_of_mem_yield_copyObject? {d : Derivation} {C : SyntacticObject}
    {tok : LexicalItem.Token} (h : d.copyObject? τ = some C) (ht : tok ∈ C.yield) :
    tok ∈ d.lexTokens := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨p, hp, hc⟩ := Option.bind_eq_some_iff.1 hc
  rcases mem_cfgCopyYield_foldlM hc tok (Multiset.mem_add.2 (.inl ht)) with ht | ht
  · simpa [cfgCopyYield, lexTokens, SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hp] using
      Multiset.mem_add.2 (.inl ht)
  · exact Multiset.mem_add.2 (.inr ht)

/-- A derivation of Merge steps leaves nothing on the stack. -/
theorem Derivation.stack_eq_nil_of_replay? {d : Derivation} {c : Cfg PlanarSyntacticObject}
    (hm : ∀ step ∈ d.steps, step.IsMerge) (h : d.replay? τ = some c) : c.stack = [] := by
  obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
  have key : ∀ (steps : List Step) (c₀ c : Cfg PlanarSyntacticObject),
      (∀ step ∈ steps, step.IsMerge) → c₀.stack = [] →
        steps.foldlM (fun c step ↦ step.replay? c τ) c₀ = some c → c.stack = [] := by
    intro steps
    induction steps with
    | nil => intro c₀ c _ h₀ h; obtain rfl := Option.some.inj h; exact h₀
    | cons step steps ih =>
      intro c₀ c hm h₀ h
      obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
      refine ih c₁ c (fun s hs ↦ hm s (List.mem_cons_of_mem _ hs)) ?_ h
      obtain ⟨p₀, st₀⟩ := c₀
      cases h₀
      have := hm step List.mem_cons_self
      cases step with
      | em side item => obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 h₁; rfl
      | im mover side => obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 h₁; rfl
      | extract mover => exact this.elim
      | remerge side => exact this.elim
  exact key _ _ _ hm rfl h

/-- In a derivation of Merge steps with no token merged twice, every token merged is pronounced in
its object. -/
theorem Derivation.mem_yield_of_mem_lexTokens {d : Derivation} {c : Cfg PlanarSyntacticObject}
    (hd : d.lexTokens.Nodup) (hm : ∀ step ∈ d.steps, step.IsMerge) (h : d.replay? τ = some c)
    {tok : LexicalItem.Token} (ht : tok ∈ d.lexTokens) :
    tok ∈ c.current.toSyntacticObject.yield := by
  have := d.yield_replay? hd h
  rw [stack_eq_nil_of_replay? hm h, List.map_nil, List.sum_nil, add_zero] at this
  rwa [this]

/-- Chain reduction needs the tokens fresh: raising a token merged twice replaces both occurrences
by its trace, so one of the two goes unpronounced. -/
example :
    let a : LexicalItem.Token := ⟨.of .D [], 0⟩
    let b : LexicalItem.Token := ⟨.of .V [.D], 1⟩
    let d : Derivation := ⟨a, [.em .left b, .em .left a, .im a]⟩
    (d.surfaceTokens : Multiset _) ≠ d.lexTokens := by
  decide

end Minimalist
