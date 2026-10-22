/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Monadic
public import Linglib.Core.Order.TreePath
public import Linglib.Syntax.Minimalist.Linearization.Replay

/-!
# Derivations with copies

Under the copy theory Internal Merge merges a copy of the mover and leaves the mover in place; the
trace of the planar replay is the contraction of that lower copy to a leaf (Definition 1.2.4 of the
algebraic account of Merge), the form externalization reads. The replay with copies marks each
lower copy with the label of its trace, so that contracting the marks gives the replay with traces
step by step, a remnant carrying the marks of what left it. On the copy object Internal Merge
leaves the object as it was and merges a copy of one of its subtrees: Extension and No Tampering.

## Main definitions

* `Minimalist.PlanarSyntacticObject.Marked`: a planar syntactic object with its lower copies
  marked; `unmark`, `contract` and `lowerCopies` read off the copy object, its contraction and the
  positions contracted.
* `Minimalist.Step.replayWithCopies?`, `Minimalist.Derivation.replayWithCopies?`: the replay with
  copies.

## Main results

* `Minimalist.Derivation.map_contract_replayWithCopies?`: contracting the copies gives the replay
  with traces.
* `Minimalist.Step.unmark_replayWithCopies?_im`: Internal Merge with copies merges a copy of a
  subtree of the object onto the object unchanged.

## References

* [marcolli-chomsky-berwick-2025], Definitions 1.2.4–1.2.6 and §1.8
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject

/-- A planar syntactic object with its lower copies marked: the root of each lower copy carries
`some l`, `l` the label of the trace that stands for it, and every other vertex `none`. -/
def PlanarSyntacticObject.Marked : Type :=
  {t : RoseTree (Option (Option LexicalItem.Token) × Vertex) //
    IsSyntacticObject (UnorderedTree.mk (t.map Prod.snd))}

instance : DecidableEq PlanarSyntacticObject.Marked := Subtype.instDecidableEq

namespace PlanarSyntacticObject.Marked

/-! ### Contraction -/

mutual
/-- The contraction of a marked tree: each marked subtree becomes the trace leaf of its mark. -/
def contractTree : RoseTree (Option (Option LexicalItem.Token) × Vertex) → RoseTree Vertex
  | .node (some l, _) _ => .node (.inr l) []
  | .node (none, a) cs => .node a (contractList cs)
/-- `contractTree` on each tree of a list. -/
def contractList :
    List (RoseTree (Option (Option LexicalItem.Token) × Vertex)) → List (RoseTree Vertex)
  | [] => []
  | c :: cs => contractTree c :: contractList cs
end

theorem contractList_eq (cs : List (RoseTree (Option (Option LexicalItem.Token) × Vertex))) :
    contractList cs = cs.map contractTree := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [contractList, ih, List.map_cons]

@[simp] theorem contractTree_some (l : Option LexicalItem.Token) (a : Vertex)
    (cs : List (RoseTree (Option (Option LexicalItem.Token) × Vertex))) :
    contractTree (.node (some l, a) cs) = .node (.inr l) [] := by
  rw [contractTree]

@[simp] theorem contractTree_none (a : Vertex)
    (cs : List (RoseTree (Option (Option LexicalItem.Token) × Vertex))) :
    contractTree (.node (none, a) cs) = .node a (cs.map contractTree) := by
  rw [contractTree, contractList_eq]

theorem isSyntacticObject_contractTree {t : RoseTree (Option (Option LexicalItem.Token) × Vertex)}
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
    (s.map ((none, ·) : Vertex → Option (Option LexicalItem.Token) × Vertex)).map Prod.snd = s := by
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

mutual
/-- Mark every outermost subtree whose contraction is `m` as a lower copy whose trace carries `l`,
testing each subtree before its children: `replaceIf` on the contraction. -/
def markTree :
    RoseTree (Option (Option LexicalItem.Token) × Vertex) →
      RoseTree (Option (Option LexicalItem.Token) × Vertex)
  | .node (k, a) cs =>
      if UnorderedTree.mk (contractTree (.node (k, a) cs)) = m.val then .node (some l, a) cs
      else match k with
        | some l' => .node (some l', a) cs
        | none => .node (none, a) (markList cs)
/-- `markTree` on each tree of a list. -/
def markList :
    List (RoseTree (Option (Option LexicalItem.Token) × Vertex)) →
      List (RoseTree (Option (Option LexicalItem.Token) × Vertex))
  | [] => []
  | c :: cs => markTree c :: markList cs
end

theorem markList_eq (cs : List (RoseTree (Option (Option LexicalItem.Token) × Vertex))) :
    markList m l cs = cs.map (markTree m l) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [markList, ih, List.map_cons]

theorem markTree_node (k : Option (Option LexicalItem.Token)) (a : Vertex)
    (cs : List (RoseTree (Option (Option LexicalItem.Token) × Vertex))) :
    markTree m l (.node (k, a) cs) =
      if UnorderedTree.mk (contractTree (.node (k, a) cs)) = m.val then .node (some l, a) cs
      else match k with
        | some l' => .node (some l', a) cs
        | none => .node (none, a) (cs.map (markTree m l)) := by
  simp only [markTree, markList_eq]

/-- Marking changes no vertex of the copy object. -/
theorem map_snd_markTree (s : RoseTree (Option (Option LexicalItem.Token) × Vertex)) :
    (markTree m l s).map Prod.snd = s.map Prod.snd := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [markTree_node]
    split_ifs
    · simp
    · rcases k with _ | l'
      · rw [map_node, map_node, List.map_map]
        exact congrArg _ (List.map_congr_left ih)
      · rfl

/-- Marking the copies of `m` contracts to replacing `m` in the contraction. -/
theorem contractTree_markTree (s : RoseTree (Option (Option LexicalItem.Token) × Vertex)) :
    contractTree (markTree m l s) =
      replaceIf (UnorderedTree.mk · = m.val) (.node (.inr l) []) (contractTree s) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [markTree_node]
    rcases k with _ | l' <;> split_ifs with h
    · rw [contractTree_some, contractTree_none, replaceIf_node, ite_eq_left (by simpa using h)]
    · rw [contractTree_none, contractTree_none, replaceIf_node, ite_eq_right (by simpa using h),
        List.map_map, List.map_map]
      exact congrArg _ (List.map_congr_left ih)
    · rw [contractTree_some, contractTree_some, replaceIf_node, ite_eq_left (by simpa using h)]
    · rw [contractTree_some, replaceIf_node, ite_eq_right (by simpa using h), List.map_nil]

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
    RoseTree (Option (Option LexicalItem.Token) × Vertex) →
      List (RoseTree (Option (Option LexicalItem.Token) × Vertex))
  | .node (some l, a) cs => [.node (some l, a) cs]
  | .node (none, a) cs => .node (none, a) cs :: outerSubtreesList cs
/-- `outerSubtrees` of the trees of a list. -/
def outerSubtreesList :
    List (RoseTree (Option (Option LexicalItem.Token) × Vertex)) →
      List (RoseTree (Option (Option LexicalItem.Token) × Vertex))
  | [] => []
  | c :: cs => outerSubtrees c ++ outerSubtreesList cs
end

theorem outerSubtreesList_eq (cs : List (RoseTree (Option (Option LexicalItem.Token) × Vertex))) :
    outerSubtreesList cs = cs.flatMap outerSubtrees := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [outerSubtreesList, ih, List.flatMap_cons]

theorem map_contractTree_outerSubtrees (s : RoseTree (Option (Option LexicalItem.Token) × Vertex)) :
    (outerSubtrees s).map contractTree = (contractTree s).subtrees := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rcases k with _ | l
    · rw [outerSubtrees, outerSubtreesList_eq, contractTree_none, subtrees_node, List.map_cons,
        contractTree_none, List.map_flatMap, List.flatMap_map]
      exact congrArg _ (List.flatMap_congr ih)
    · simp [outerSubtrees]

theorem isSubtree_of_mem_outerSubtrees {r s : RoseTree (Option (Option LexicalItem.Token) × Vertex)}
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

/-- The occurrence found contracts to the occurrence found in the contraction. -/
theorem map_contract_find? (target : SyntacticObject) :
    (t.find? target).map contract = t.contract.find? target := by
  apply Option.map_injective Subtype.val_injective
  rw [Option.map_map, find?, PlanarSyntacticObject.find?, Option.map_pmap, Option.map_pmap]
  simp only [Function.comp_apply, contract, Option.pmap_eq_map]
  rw [← map_contractTree_outerSubtrees, List.find?_map]
  simp [Function.comp_def]

/-! ### Lower copies -/

mutual
/-- The addresses of the outermost marked subtrees, in preorder. -/
def lowerCopyAddrs : RoseTree (Option (Option LexicalItem.Token) × Vertex) → List (List ℕ)
  | .node (some _, _) _ => [[]]
  | .node (none, _) cs => lowerCopyAddrsList 0 cs
/-- `lowerCopyAddrs` of the trees of a list, those of the `i`-th prefixed by `i`. -/
def lowerCopyAddrsList :
    ℕ → List (RoseTree (Option (Option LexicalItem.Token) × Vertex)) → List (List ℕ)
  | _, [] => []
  | i, c :: cs => (lowerCopyAddrs c).map (i :: ·) ++ lowerCopyAddrsList (i + 1) cs
end

/-- The positions of the lower copies, left to right, each outermost: the cut the contraction
contracts ([marcolli-chomsky-berwick-2025] Definition 1.2.6). -/
def lowerCopies (t : Marked) : List Core.Order.TreePath := (lowerCopyAddrs t.val).map .mk

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
theorem Derivation.map_contract_current_replayWithCopies? (d : Derivation) :
    (d.replayWithCopies? τ).map (·.current.contract) = d.externalize? τ := by
  rw [externalize?, ← d.map_contract_replayWithCopies?, Option.map_map]
  rfl

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

end Minimalist
