/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.ToTree
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.Deletion

/-!
# Readings as cuts of the copy object

This file relates the readings of a marked object to the coproducts on trees. A reading cuts a
forest from the copy object: the lower copies of the chains read high, each leaving its trace, and
the higher copies of the chains read low, each leaving nothing, with the unary vertex that leaves
contracted. With [no chain read low](##mem_traceCuts_contract) the reading is a term of the
coproduct $\Delta^c$, and with [every chain read low](##mem_deletionCuts_lf) a term of the deletion
coproduct $\Delta^d$. A reading with chains of both kinds is [a cut under a policy of its
own](##exists_mem_rootCuts_lf), which `leaveNothing` follows on some trees and `leaveTrace` on the
rest.

## Implementation notes

* `Δ^c` labels a trace by a function of the tree it cuts, where a replay gives a lower copy the mark
  of its mover's contraction at that step, so `MarkedBy` is a hypothesis on the object.

## TODO

* Prove `MarkedBy` of `termTrace selHead` for the objects a replay reaches, under conditions on the
  moved heads.
* Characterize `cutForest` by the positions it cuts.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.PlanarSyntacticObject.Marked

open RoseTree SyntacticObject ConnesKreimer

/-- A copy's part in a reading as a cut of the copy object: the forest it cuts, and what stays. A
lower copy of a chain read high is cut and leaves its trace. A higher copy of a chain read low is
cut and leaves nothing, so that its mother goes unary. -/
def readCut (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low] :
    RoseTree (CopyMark × Vertex) → Multiset (RoseTree Vertex) × List (RoseTree Vertex) :=
  reading low (fun r l ↦ ({r.map Prod.snd}, [.node (.inr l) []]))
    (fun v bs ↦ ((bs.map Prod.fst).sum, [.node v (bs.flatMap Prod.snd)]))
    (fun _ b ↦ b)
    fun x v b ↦ (x.map Prod.snd ::ₘ b.1, [.node v b.2])

section Mem

variable {α : Type*} {e : RoseTree α → Option (List (RoseTree α))}

private theorem mem_childCuts_self {t : RoseTree α} {r : List (RoseTree α)} (h : e t = some r) :
    (({t} : Multiset (RoseTree α)), r) ∈ childCuts e t := by
  rw [childCuts_eq_some e t r h]
  exact Multiset.mem_cons_self _ _

private theorem mem_childCuts_of_mem {t : RoseTree α} {p : Multiset (RoseTree α) × RoseTree α}
    (h : p ∈ rootCuts e t) : (p.1, [p.2]) ∈ childCuts e t := by
  rw [childCuts_eq]
  exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨p, h, rfl⟩))

private theorem mem_childrenCuts_cons {t : RoseTree α} {ts : List (RoseTree α)}
    {a b : Multiset (RoseTree α) × List (RoseTree α)} (ha : a ∈ childCuts e t)
    (hb : b ∈ childrenCuts e ts) :
    (a.1 + b.1, a.2 ++ b.2) ∈ childrenCuts e (t :: ts) := by
  rw [childrenCuts_cons]
  exact Multiset.mem_map.2 ⟨(a, b), Multiset.mem_product.2 ⟨ha, hb⟩, rfl⟩

private theorem mem_rootCuts_node {a : α} {cs : List (RoseTree α)}
    {p : Multiset (RoseTree α) × List (RoseTree α)} (h : p ∈ childrenCuts e cs) :
    (p.1, RoseTree.node a p.2) ∈ rootCuts e (.node a cs) := by
  rw [rootCuts_node]
  exact Multiset.mem_map.2 ⟨p, h, rfl⟩

private theorem mem_childrenCuts_pair {x y : RoseTree α}
    {a b : Multiset (RoseTree α) × List (RoseTree α)}
    (ha : a ∈ childCuts e x) (hb : b ∈ childCuts e y) :
    (a.1 + b.1, a.2 ++ b.2) ∈ childrenCuts e [x, y] := by
  have h := mem_childrenCuts_cons ha (mem_childrenCuts_cons hb
    (by rw [childrenCuts_nil]; exact Multiset.mem_singleton_self _))
  simpa using h

private theorem mem_childrenCuts_map {β : Type*}
    {f : β → Multiset (RoseTree α) × List (RoseTree α)} {g : β → RoseTree α} (cs : List β)
    (h : ∀ c ∈ cs, f c ∈ childCuts e (g c)) :
    (((cs.map f).map Prod.fst).sum, (cs.map f).flatMap Prod.snd) ∈
      childrenCuts e (cs.map g) := by
  induction cs with
  | nil => rw [List.map_nil, childrenCuts_nil]; exact Multiset.mem_singleton_self _
  | cons c cs ih =>
    have := mem_childrenCuts_cons (h c (by simp)) (ih fun d hd ↦ h d (by simp [hd]))
    simpa using this

end Mem

variable (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
  (e : RoseTree Vertex → Option (List (RoseTree Vertex)))

theorem readCut_some (l : Option LexicalItem.Token) (a : Vertex)
    (cs : List (RoseTree (CopyMark × Vertex))) :
    readCut low (.node (some l, a) cs) =
      if low (.node (some l, a) cs) then readCut low (.node (none, a) cs)
      else ({(RoseTree.node (some l, a) cs).map Prod.snd}, [.node (.inr l) []]) :=
  reading_some ..

/-- An unmarked node reads as a node over its daughters, or as a daughter with the other cut. -/
private theorem readCut_none_cases (a : Vertex) (cs : List (RoseTree (CopyMark × Vertex))) :
    (readCut low (.node (none, a) cs) =
        (((cs.map (readCut low)).map Prod.fst).sum,
          [.node a ((cs.map (readCut low)).flatMap Prod.snd)]) ∧
      lfBy low (.node (none, a) cs) = .node a (cs.map (lfBy low))) ∨
    ∃ x y, (cs = [x, y] ∨ cs = [y, x]) ∧ low x ∧
      readCut low (.node (none, a) cs) =
        (x.map Prod.snd ::ₘ (readCut low y).1, [.node a (readCut low y).2]) ∧
      lfBy low (.node (none, a) cs) = lfBy low y := by
  by_cases hlen : cs.length = 2
  · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
    have hcut := reading_pair low (fun r l ↦ (({r.map Prod.snd} : Multiset (RoseTree Vertex)),
        [RoseTree.node (.inr l) []]))
      (fun v bs ↦ ((bs.map Prod.fst).sum, [RoseTree.node v (bs.flatMap Prod.snd)]))
      (fun _ b ↦ b) (fun x v b ↦ (x.map Prod.snd ::ₘ b.1, [RoseTree.node v b.2])) (fun _ _ ↦ rfl) a
      u v
    rw [lfBy_pair]
    change readCut low _ = _ at hcut
    rw [hcut]
    split_ifs with h1 h2 h3 h4
    · exact .inr ⟨u, v, .inl rfl, h2, rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨v, u, .inr rfl, h4, rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inl ⟨rfl, rfl⟩
  · exact .inl ⟨reading_of_length_ne _ _ _ _ _ a hlen, lfBy_of_length_ne _ a hlen⟩

/-- An unmarked node reads as one cut of the copy object, with its root as the root of the trunk. -/
private theorem exists_mem_rootCuts_none {a : Vertex}
    {cs : List (RoseTree (CopyMark × Vertex))}
    (ih : ∀ c ∈ cs, readCut low c ∈ childCuts e (c.map Prod.snd))
    (hl : ∀ c ∈ cs, low c → e (c.map Prod.snd) = some []) :
    ∃ T, (readCut low (.node (none, a) cs)).2 = [T] ∧
      ((readCut low (.node (none, a) cs)).1, T) ∈
        rootCuts e (.node a (cs.map (·.map Prod.snd))) := by
  rcases readCut_none_cases low a cs with ⟨h, -⟩ | ⟨x, y, hc, hx, h, -⟩
  · rw [h]
    exact ⟨_, rfl, mem_rootCuts_node
      (mem_childrenCuts_map (f := readCut low) (g := (·.map Prod.snd)) cs ih)⟩
  · rw [h]
    refine ⟨_, rfl, ?_⟩
    have hxm : x ∈ cs := by rcases hc with rfl | rfl <;> simp
    have hym : y ∈ cs := by rcases hc with rfl | rfl <;> simp
    have ax := mem_childCuts_self (hl x hxm hx)
    have ay := ih y hym
    rcases hc with rfl | rfl
    · simpa using mem_rootCuts_node (a := a) (mem_childrenCuts_pair ax ay)
    · have h := mem_rootCuts_node (a := a) (mem_childrenCuts_pair ay ax)
      simp only [List.append_nil] at h
      rwa [Multiset.add_comm, Multiset.singleton_add] at h

private theorem subtrees_subset {v : CopyMark × Vertex} {cs : List (RoseTree (CopyMark × Vertex))}
    {c : RoseTree (CopyMark × Vertex)} (hc : c ∈ cs) {r : RoseTree (CopyMark × Vertex)}
    (hr : r ∈ c.subtrees) : r ∈ (RoseTree.node v cs).subtrees :=
  mem_subtrees.2 ((mem_subtrees.1 hr).trans (.of_mem_children hc))

variable {low e} {s : RoseTree (CopyMark × Vertex)}

/-- A copy's part in a reading is one of the choices a cut has at it, when the policy cuts a lower
copy of a chain read high leaving its trace and a copy of a chain read low leaving nothing. -/
theorem readCut_mem_childCuts
    (hh : ∀ r ∈ s.subtrees, ∀ l, r.value.1 = some l → ¬ low r →
      e (r.map Prod.snd) = some [.node (.inr l) []])
    (hl : ∀ r ∈ s.subtrees, low r → e (r.map Prod.snd) = some []) :
    readCut low s ∈ childCuts e (s.map Prod.snd) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    have ih' : ∀ c ∈ cs, readCut low c ∈ childCuts e (c.map Prod.snd) := fun c hc ↦
      ih c hc (fun r hr ↦ hh r (subtrees_subset hc hr)) fun r hr ↦ hl r (subtrees_subset hc hr)
    have hl' : ∀ c ∈ cs, low c → e (c.map Prod.snd) = some [] := fun c hc ↦
      hl c (subtrees_subset hc (self_mem_subtrees c))
    obtain ⟨T, hT, hm⟩ := exists_mem_rootCuts_none low e (a := a) ih' hl'
    have hnone : readCut low (.node (none, a) cs) ∈
        childCuts e (RoseTree.node a (cs.map (·.map Prod.snd))) := by
      have := mem_childCuts_of_mem hm
      rwa [← hT] at this
    rcases k with _ | l
    · simpa [map_node] using hnone
    · rw [readCut_some]
      split_ifs with hlow
      · simpa [map_node] using hnone
      · exact mem_childCuts_self (hh _ (self_mem_subtrees _) l rfl hlow)

/-- A tree whose root is not a lower copy of a chain read high reads as one cut of it, with what
stays in place a single tree. -/
theorem exists_mem_rootCuts_readCut (hroot : ∀ l, s.value.1 = some l → low s)
    (hh : ∀ r ∈ s.subtrees, ∀ l, r.value.1 = some l → ¬ low r →
      e (r.map Prod.snd) = some [.node (.inr l) []])
    (hl : ∀ r ∈ s.subtrees, low r → e (r.map Prod.snd) = some []) :
    ∃ T, (readCut low s).2 = [T] ∧ ((readCut low s).1, T) ∈ rootCuts e (s.map Prod.snd) := by
  obtain ⟨⟨k, a⟩, cs⟩ := s
  have ih' : ∀ c ∈ cs, readCut low c ∈ childCuts e (c.map Prod.snd) := fun c hc ↦
    readCut_mem_childCuts (fun r hr ↦ hh r (subtrees_subset hc hr))
      fun r hr ↦ hl r (subtrees_subset hc hr)
  have hl' : ∀ c ∈ cs, low c → e (c.map Prod.snd) = some [] := fun c hc ↦
    hl c (subtrees_subset hc (self_mem_subtrees c))
  have hnone := exists_mem_rootCuts_none low e (a := a) ih' hl'
  rcases k with _ | l
  · simpa [map_node] using hnone
  · rw [readCut_some, ite_eq_left (hroot l rfl)]
    simpa [map_node] using hnone

/-- The trunk of a reading, its unary vertices contracted, is the object the reading gives. -/
theorem map_contractUnary_readCut (hs : IsSyntacticObject (UnorderedTree.mk (s.map Prod.snd))) :
    (readCut low s).2.map contractUnary = [lfBy low s] := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [map_node] at hs
    have hlen := length_eq_zero_or_two hs
    rw [isSyntacticObject_mk, licensed_node_iff] at hs
    have ih' : ∀ c ∈ cs, (readCut low c).2.map contractUnary = [lfBy low c] := fun c hc ↦
      ih c hc (hs.2 _ (List.mem_map_of_mem hc))
    have hnone : (readCut low (.node (none, a) cs)).2.map contractUnary =
        [lfBy low (.node (none, a) cs)] := by
      rcases readCut_none_cases low a cs with ⟨h, hf⟩ | ⟨x, y, hc, hx, h, hf⟩
      · rw [h, hf]
        rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩
        · simp
        · simp at hlen
        · obtain ⟨Tx, hTx, hx⟩ := List.map_eq_singleton_iff.1 (ih' x (by simp))
          obtain ⟨Ty, hTy, hy⟩ := List.map_eq_singleton_iff.1 (ih' y (by simp))
          simp [hTx, hTy, hx, hy]
        · simp at hlen
      · obtain ⟨Ty, hTy, hy⟩ := List.map_eq_singleton_iff.1
          (ih' y (by rcases hc with rfl | rfl <;> simp))
        simp [h, hf, hTy, hy]
    rcases k with _ | l
    · exact hnone
    · rw [readCut_some, lfBy_some]
      split_ifs
      · exact hnone
      · simp

/-- With no chain read low, the trunk of a reading is the contraction. -/
theorem readCut_readLow_empty (s : RoseTree (CopyMark × Vertex)) :
    (readCut (ReadLow ∅) s).2 = [contractTree s] := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rcases k with _ | l
    · rcases readCut_none_cases (ReadLow ∅) a cs with ⟨h, -⟩ | ⟨x, y, -, hx, -⟩
      · have key : ∀ ds : List (RoseTree (CopyMark × Vertex)),
            (∀ d ∈ ds, (readCut (ReadLow ∅) d).2 = [contractTree d]) →
              (ds.map (readCut (ReadLow ∅))).flatMap Prod.snd = ds.map contractTree := by
          intro ds hds
          induction ds with
          | nil => rfl
          | cons d ds ihd =>
            simp [hds d (by simp), ihd fun c hc ↦ hds c (by simp [hc])]
        rw [h, contractTree_none, key cs ih]
      · exact absurd hx (not_readLow_empty x)
    · rw [readCut_some, ite_eq_right (not_readLow_empty _), contractTree_some]

/-! ### Readings and the coproducts -/

variable (τ : UnorderedTree Vertex → Option LexicalItem.Token)

/-- Every lower copy of `s` is a tree of the copy object with a root that is not a trace, and has
`τ` of its term as its mark. -/
def MarkedBy (s : RoseTree (CopyMark × Vertex)) : Prop :=
  ∀ r ∈ s.subtrees, r.value.1.isSome → r.value.2.isLeft ∧ r.value.1 = some (τ (termOf r))

instance : DecidablePred (MarkedBy τ) := fun _ ↦ inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A trace encoder on syntactic objects as one on terms, with no label off them. -/
def termTrace (σ : SyntacticObject → Option LexicalItem.Token) (u : UnorderedTree Vertex) :
    Option LexicalItem.Token :=
  if h : IsSyntacticObject u then σ (SyntacticObject.ofUnorderedTree u h) else none

/-- The policy of a reading: a copy of a chain read low leaves nothing when it is cut, as under
`leaveNothing`, and any other subtree its trace, as under `leaveTrace`. -/
def extractReading (low : Finset SyntacticObject) (τ : RoseTree Vertex → Option LexicalItem.Token) :
    RoseTree Vertex → Option (List (RoseTree Vertex)) := fun r ↦
  if ∃ m ∈ low, m.toUnorderedTree = UnorderedTree.mk r then leaveNothing r else leaveTrace τ r

variable {τ} (t : Marked) (low : Finset SyntacticObject)

/-- The trees a reading cuts from the copy object: the lower copies of the chains read high, and
the higher copies of the chains read low, each outermost. -/
def cutForest : Multiset (RoseTree Vertex) := (readCut (ReadLow low) t.val).1

private theorem leaveTrace_map_snd {r : RoseTree (CopyMark × Vertex)} {l : Option LexicalItem.Token}
    (hτ : r.value.2.isLeft ∧ r.value.1 = some (τ (termOf r))) (hl : r.value.1 = some l) :
    leaveTrace (τ ∘ UnorderedTree.mk) (r.map Prod.snd) = some [.node (.inr l) []] := by
  obtain ⟨⟨k, a⟩, cs⟩ := r
  obtain ⟨ha, hk⟩ := hτ
  obtain rfl : τ (termOf (.node (k, a) cs)) = l := Option.some.inj (hk.symm.trans hl)
  rcases a with a | b
  · rw [map_node]
    dsimp only
    rw [leaveTrace_inl, termOf, map_node]
    rfl
  · exact absurd ha (by simp [value])

private theorem extractReading_of_not_low {low : Finset SyntacticObject}
    {τ : RoseTree Vertex → Option LexicalItem.Token} {r : RoseTree (CopyMark × Vertex)}
    (h : ¬ ReadLow low r) :
    extractReading low τ (r.map Prod.snd) = leaveTrace τ (r.map Prod.snd) :=
  ite_eq_right h

private theorem extractReading_of_low {low : Finset SyntacticObject}
    {τ : RoseTree Vertex → Option LexicalItem.Token} {r : RoseTree (CopyMark × Vertex)}
    (h : ReadLow low r) : extractReading low τ (r.map Prod.snd) = some [] :=
  ite_eq_left h

/-- A reading gives a cut of the copy object under its policy, its unary vertices contracted. -/
theorem exists_mem_rootCuts_lf (hroot : t.val.value.1 = none) (hτ : MarkedBy τ t.val) :
    ∃ T, (t.cutForest low, T) ∈
        rootCuts (extractReading low (τ ∘ UnorderedTree.mk)) t.unmark.toRoseTree ∧
      contractUnary T = (t.lf low).toRoseTree := by
  simp only [toRoseTree_unmark, toRoseTree_lf]
  obtain ⟨T, hT, hm⟩ := exists_mem_rootCuts_readCut (low := ReadLow low)
    (e := extractReading low (τ ∘ UnorderedTree.mk)) (s := t.val)
    (fun l hl ↦ by simp [hroot] at hl)
    (fun r hr l hl hn ↦ (extractReading_of_not_low hn).trans
      (leaveTrace_map_snd (hτ r hr (by simp [hl])) hl))
    (fun r _ hr ↦ extractReading_of_low hr)
  refine ⟨T, hm, ?_⟩
  have h := map_contractUnary_readCut (low := ReadLow low) t.2
  rw [hT] at h
  exact (by simpa using h : contractUnary T = lfBy (ReadLow low) t.val)

/-- With no chain read low, a reading is the contraction, a term of the coproduct `Δ^c`: the lower
copies are an admissible cut of the copy object. -/
theorem mem_traceCuts_contract (hroot : t.val.value.1 = none) (hτ : MarkedBy τ t.val) :
    ((t.cutForest ∅).map UnorderedTree.mk, UnorderedTree.mk t.contract.toRoseTree) ∈
      traceCuts τ (UnorderedTree.mk t.unmark.toRoseTree) := by
  rw [toRoseTree_contract, toRoseTree_unmark]
  obtain ⟨T, hT, hm⟩ := exists_mem_rootCuts_readCut (low := ReadLow ∅)
    (e := leaveTrace (τ ∘ UnorderedTree.mk)) (s := t.val)
    (fun l hl ↦ by simp [hroot] at hl)
    (fun r hr l hl _ ↦ leaveTrace_map_snd (hτ r hr (by simp [hl])) hl)
    (fun r _ hr ↦ absurd hr (not_readLow_empty r))
  obtain rfl : T = contractTree t.val := by
    have := readCut_readLow_empty t.val
    rw [hT] at this
    simpa using this
  rw [traceCuts_mk]
  exact Multiset.mem_map.2 ⟨_, hm, rfl⟩

/-- With every chain read low, a reading is the trunk of an admissible cut of the copy object with
its unary vertices contracted, the higher copies being the crown. -/
theorem exists_mem_admissibleCuts_lf
    (hlow : ∀ r ∈ t.val.subtrees, r.value.1.isSome → ReadLow low r) :
    ∃ T, ((t.cutForest low).map UnorderedTree.mk, T) ∈
        admissibleCuts (UnorderedTree.mk t.unmark.toRoseTree) ∧
      T.contractUnary = UnorderedTree.mk (t.lf low).toRoseTree := by
  rw [toRoseTree_lf, toRoseTree_unmark]
  obtain ⟨T, hT, hm⟩ := exists_mem_rootCuts_readCut (low := ReadLow low) (e := leaveNothing)
    (s := t.val)
    (fun l hl ↦ hlow _ (self_mem_subtrees _) (by simp [hl]))
    (fun r hr l hl hn ↦ absurd (hlow r hr (by simp [hl])) hn)
    (fun _ _ _ ↦ rfl)
  have h := map_contractUnary_readCut (low := ReadLow low) t.2
  rw [hT, List.map_singleton, List.cons.injEq] at h
  rw [admissibleCuts_mk]
  refine ⟨UnorderedTree.mk T, Multiset.mem_map.2 ⟨_, hm, rfl⟩, ?_⟩
  rw [UnorderedTree.contractUnary_mk]
  exact congrArg UnorderedTree.mk h.1

/-- With every chain read low, a reading with no bare leaf is a term of the deletion coproduct
`Δ^d`: the higher copies are an admissible cut of the copy object, and the reading is the
remainder. -/
theorem mem_deletionCuts_lf (hlow : ∀ r ∈ t.val.subtrees, r.value.1.isSome → ReadLow low r)
    (hlf : ∀ a ∈ (UnorderedTree.mk (t.lf low).toRoseTree).leaves, a ≠ Vertex.bare) :
    ((t.cutForest low).map UnorderedTree.mk, some (UnorderedTree.mk (t.lf low).toRoseTree)) ∈
      deletionCuts Vertex.bare (UnorderedTree.mk t.unmark.toRoseTree) := by
  obtain ⟨T, hT, hc⟩ := exists_mem_admissibleCuts_lf t low hlow
  refine Multiset.mem_map.2 ⟨_, hT, ?_⟩
  rw [← hc, UnorderedTree.leaves_contractUnary] at hlf
  rw [deletionQuotient_eq_some _ hlf, hc]

end Minimalist.PlanarSyntacticObject.Marked
