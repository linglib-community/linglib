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
contracted. With [no chain read low](##mem_cutSummandsCN_contract) the reading is a term of the
coproduct $\Delta^c$, and with [every chain read low](##mem_cutSummandsDN_lf) a term of the deletion
coproduct $\Delta^d$. A reading with chains of both kinds is [a cut under a policy of its
own](##exists_mem_cutSummandsG_lf), which `pruning` follows on some trees and `extractC` on the
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

namespace Minimalist.LinearizedSyntacticObject.Marked

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

private theorem mem_augActionG_self {t : RoseTree α} {r : List (RoseTree α)} (h : e t = some r) :
    (({t} : Multiset (RoseTree α)), r) ∈ augActionG e t := by
  rw [augActionG_eq_some e t r h]
  exact Multiset.mem_cons_self _ _

private theorem mem_augActionG_of_mem {t : RoseTree α} {p : Multiset (RoseTree α) × RoseTree α}
    (h : p ∈ cutSummandsG e t) : (p.1, [p.2]) ∈ augActionG e t := by
  rw [augActionG_eq]
  exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨p, h, rfl⟩))

private theorem mem_cutListSummandsG_cons {t : RoseTree α} {ts : List (RoseTree α)}
    {a b : Multiset (RoseTree α) × List (RoseTree α)} (ha : a ∈ augActionG e t)
    (hb : b ∈ cutListSummandsG e ts) :
    (a.1 + b.1, a.2 ++ b.2) ∈ cutListSummandsG e (t :: ts) := by
  rw [cutListSummandsG_cons]
  exact Multiset.mem_map.2 ⟨(a, b), Multiset.mem_product.2 ⟨ha, hb⟩, rfl⟩

private theorem mem_cutSummandsG_node {a : α} {cs : List (RoseTree α)}
    {p : Multiset (RoseTree α) × List (RoseTree α)} (h : p ∈ cutListSummandsG e cs) :
    (p.1, RoseTree.node a p.2) ∈ cutSummandsG e (.node a cs) := by
  rw [cutSummandsG_node]
  exact Multiset.mem_map.2 ⟨p, h, rfl⟩

private theorem mem_cutListSummandsG_pair {x y : RoseTree α}
    {a b : Multiset (RoseTree α) × List (RoseTree α)}
    (ha : a ∈ augActionG e x) (hb : b ∈ augActionG e y) :
    (a.1 + b.1, a.2 ++ b.2) ∈ cutListSummandsG e [x, y] := by
  have h := mem_cutListSummandsG_cons ha (mem_cutListSummandsG_cons hb
    (by rw [cutListSummandsG_nil]; exact Multiset.mem_singleton_self _))
  simpa using h

private theorem mem_cutListSummandsG_map {β : Type*}
    {f : β → Multiset (RoseTree α) × List (RoseTree α)} {g : β → RoseTree α} (cs : List β)
    (h : ∀ c ∈ cs, f c ∈ augActionG e (g c)) :
    (((cs.map f).map Prod.fst).sum, (cs.map f).flatMap Prod.snd) ∈
      cutListSummandsG e (cs.map g) := by
  induction cs with
  | nil => rw [List.map_nil, cutListSummandsG_nil]; exact Multiset.mem_singleton_self _
  | cons c cs ih =>
    have := mem_cutListSummandsG_cons (h c (by simp)) (ih fun d hd ↦ h d (by simp [hd]))
    simpa using this

end Mem

variable (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
  (e : RoseTree Vertex → Option (List (RoseTree Vertex)))

private theorem map_fst_pair {β : Type*} (f : RoseTree (CopyMark × Vertex) → β)
    (cs : List (RoseTree (CopyMark × Vertex))) :
    (cs.map fun c ↦ (c, f c)).map Prod.fst = cs := by
  simp [Function.comp_def]

/-- A lower copy of a chain read high is cut whole, and leaves its trace. -/
theorem readCut_of_not_low {l : Option LexicalItem.Token} {a : Vertex}
    {cs : List (RoseTree (CopyMark × Vertex))} (h : ¬ low (.node (some l, a) cs)) :
    readCut low (.node (some l, a) cs) =
      ({(RoseTree.node (some l, a) cs).map Prod.snd}, [.node (.inr l) []]) := by
  simp only [readCut]
  rw [reading_node]
  simp only [readStep, map_fst_pair, h, ↓reduceIte]

/-- A lower copy of a chain read low reads as if it were not one. -/
theorem readCut_of_low {l : Option LexicalItem.Token} {a : Vertex}
    {cs : List (RoseTree (CopyMark × Vertex))} (h : low (.node (some l, a) cs)) :
    readCut low (.node (some l, a) cs) = readCut low (.node (none, a) cs) := by
  simp only [readCut]
  rw [reading_node, reading_node]
  simp only [readStep, map_fst_pair, h, ↓reduceIte]

private theorem lfBy_of_not_low {l : Option LexicalItem.Token} {a : Vertex}
    {cs : List (RoseTree (CopyMark × Vertex))} (h : ¬ low (.node (some l, a) cs)) :
    lfBy low (.node (some l, a) cs) = .node (.inr l) [] := by
  simp only [lfBy]
  rw [reading_node]
  simp only [readStep, map_fst_pair, h, ↓reduceIte]

private theorem lfBy_of_low {l : Option LexicalItem.Token} {a : Vertex}
    {cs : List (RoseTree (CopyMark × Vertex))} (h : low (.node (some l, a) cs)) :
    lfBy low (.node (some l, a) cs) = lfBy low (.node (none, a) cs) := by
  simp only [lfBy]
  rw [reading_node, reading_node]
  simp only [readStep, map_fst_pair, h, ↓reduceIte]

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
  simp only [readCut, lfBy]
  rw [reading_node, reading_node]
  simp only [readStep]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩
  · simp
  · simp
  · simp only [List.map]
    cases h1 : lowerCopy? x y with
    | some l =>
      by_cases hx : low x
      · exact .inr ⟨x, y, .inl rfl, hx, by simp [hx], by simp [hx]⟩
      · exact .inl ⟨by simp [hx], by simp [hx]⟩
    | none =>
      cases h2 : lowerCopy? y x with
      | some l =>
        by_cases hy : low y
        · exact .inr ⟨y, x, .inr rfl, hy, by simp [hy], by simp [hy]⟩
        · exact .inl ⟨by simp [hy], by simp [hy]⟩
      | none => exact .inl ⟨by simp, by simp⟩
  · simp [Function.comp_def]

/-- An unmarked node reads as one cut of the copy object, with its root as the root of the trunk. -/
private theorem exists_mem_cutSummandsG_none {a : Vertex}
    {cs : List (RoseTree (CopyMark × Vertex))}
    (ih : ∀ c ∈ cs, readCut low c ∈ augActionG e (c.map Prod.snd))
    (hl : ∀ c ∈ cs, low c → e (c.map Prod.snd) = some []) :
    ∃ T, (readCut low (.node (none, a) cs)).2 = [T] ∧
      ((readCut low (.node (none, a) cs)).1, T) ∈
        cutSummandsG e (.node a (cs.map (·.map Prod.snd))) := by
  rcases readCut_none_cases low a cs with ⟨h, -⟩ | ⟨x, y, hc, hx, h, -⟩
  · rw [h]
    exact ⟨_, rfl, mem_cutSummandsG_node
      (mem_cutListSummandsG_map (f := readCut low) (g := (·.map Prod.snd)) cs ih)⟩
  · rw [h]
    refine ⟨_, rfl, ?_⟩
    have hxm : x ∈ cs := by rcases hc with rfl | rfl <;> simp
    have hym : y ∈ cs := by rcases hc with rfl | rfl <;> simp
    have ax := mem_augActionG_self (hl x hxm hx)
    have ay := ih y hym
    rcases hc with rfl | rfl
    · simpa using mem_cutSummandsG_node (a := a) (mem_cutListSummandsG_pair ax ay)
    · have h := mem_cutSummandsG_node (a := a) (mem_cutListSummandsG_pair ay ax)
      simp only [List.append_nil] at h
      rwa [Multiset.add_comm, Multiset.singleton_add] at h

private theorem subtrees_subset {v : CopyMark × Vertex} {cs : List (RoseTree (CopyMark × Vertex))}
    {c : RoseTree (CopyMark × Vertex)} (hc : c ∈ cs) {r : RoseTree (CopyMark × Vertex)}
    (hr : r ∈ c.subtrees) : r ∈ (RoseTree.node v cs).subtrees := by
  simp only [subtrees_node, List.mem_cons, List.mem_flatMap]
  exact .inr ⟨c, hc, hr⟩

variable {low e} {s : RoseTree (CopyMark × Vertex)}

/-- A copy's part in a reading is one of the choices a cut has at it, when the policy cuts a lower
copy of a chain read high leaving its trace and a copy of a chain read low leaving nothing. -/
theorem readCut_mem_augActionG
    (hh : ∀ r ∈ s.subtrees, ∀ l, r.value.1 = some l → ¬ low r →
      e (r.map Prod.snd) = some [.node (.inr l) []])
    (hl : ∀ r ∈ s.subtrees, low r → e (r.map Prod.snd) = some []) :
    readCut low s ∈ augActionG e (s.map Prod.snd) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    have ih' : ∀ c ∈ cs, readCut low c ∈ augActionG e (c.map Prod.snd) := fun c hc ↦
      ih c hc (fun r hr ↦ hh r (subtrees_subset hc hr)) fun r hr ↦ hl r (subtrees_subset hc hr)
    have hl' : ∀ c ∈ cs, low c → e (c.map Prod.snd) = some [] := fun c hc ↦
      hl c (subtrees_subset hc (self_mem_subtrees c))
    obtain ⟨T, hT, hm⟩ := exists_mem_cutSummandsG_none low e (a := a) ih' hl'
    have hnone : readCut low (.node (none, a) cs) ∈
        augActionG e (RoseTree.node a (cs.map (·.map Prod.snd))) := by
      have := mem_augActionG_of_mem hm
      rwa [← hT] at this
    rcases k with _ | l
    · simpa [map_node] using hnone
    · by_cases hlow : low (.node (some l, a) cs)
      · rw [readCut_of_low low hlow]
        simpa [map_node] using hnone
      · rw [readCut_of_not_low low hlow]
        exact mem_augActionG_self (hh _ (self_mem_subtrees _) l rfl hlow)

/-- A tree whose root is not a lower copy of a chain read high reads as one cut of it, with what
stays in place a single tree. -/
theorem exists_mem_cutSummandsG_readCut (hroot : ∀ l, s.value.1 = some l → low s)
    (hh : ∀ r ∈ s.subtrees, ∀ l, r.value.1 = some l → ¬ low r →
      e (r.map Prod.snd) = some [.node (.inr l) []])
    (hl : ∀ r ∈ s.subtrees, low r → e (r.map Prod.snd) = some []) :
    ∃ T, (readCut low s).2 = [T] ∧ ((readCut low s).1, T) ∈ cutSummandsG e (s.map Prod.snd) := by
  obtain ⟨⟨k, a⟩, cs⟩ := s
  have ih' : ∀ c ∈ cs, readCut low c ∈ augActionG e (c.map Prod.snd) := fun c hc ↦
    readCut_mem_augActionG (fun r hr ↦ hh r (subtrees_subset hc hr))
      fun r hr ↦ hl r (subtrees_subset hc hr)
  have hl' : ∀ c ∈ cs, low c → e (c.map Prod.snd) = some [] := fun c hc ↦
    hl c (subtrees_subset hc (self_mem_subtrees c))
  have hnone := exists_mem_cutSummandsG_none low e (a := a) ih' hl'
  rcases k with _ | l
  · simpa [map_node] using hnone
  · rw [readCut_of_low low (hroot l rfl)]
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
    · by_cases hlow : low (.node (some l, a) cs)
      · rw [readCut_of_low low hlow, lfBy_of_low low hlow]
        exact hnone
      · rw [readCut_of_not_low low hlow, lfBy_of_not_low low hlow]
        simp

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
    · rw [readCut_of_not_low _ (not_readLow_empty _), contractTree_some]

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
  if h : IsSyntacticObject u then σ ⟨u, h⟩ else none

/-- The policy of a reading: a copy of a chain read low leaves nothing when it is cut, as under
`pruning`, and any other subtree its trace, as under `extractC`. -/
def extractReading (low : Finset SyntacticObject) (τ : RoseTree Vertex → Option LexicalItem.Token) :
    RoseTree Vertex → Option (List (RoseTree Vertex)) := fun r ↦
  if ∃ m ∈ low, m.val = UnorderedTree.mk r then pruning r else extractC τ r

variable {τ} (t : Marked) (low : Finset SyntacticObject)

/-- The trees a reading cuts from the copy object: the lower copies of the chains read high, and
the higher copies of the chains read low, each outermost. -/
def cutForest : Multiset (RoseTree Vertex) := (readCut (ReadLow low) t.val).1

private theorem extractC_map_snd {r : RoseTree (CopyMark × Vertex)} {l : Option LexicalItem.Token}
    (hτ : r.value.2.isLeft ∧ r.value.1 = some (τ (termOf r))) (hl : r.value.1 = some l) :
    extractC (τ ∘ UnorderedTree.mk) (r.map Prod.snd) = some [.node (.inr l) []] := by
  obtain ⟨⟨k, a⟩, cs⟩ := r
  obtain ⟨ha, hk⟩ := hτ
  obtain rfl : τ (termOf (.node (k, a) cs)) = l := Option.some.inj (hk.symm.trans hl)
  rcases a with a | b
  · rw [map_node]
    dsimp only
    rw [extractC_inl, termOf, map_node]
    rfl
  · exact absurd ha (by simp [value])

private theorem extractReading_of_not_low {low : Finset SyntacticObject}
    {τ : RoseTree Vertex → Option LexicalItem.Token} {r : RoseTree (CopyMark × Vertex)}
    (h : ¬ ReadLow low r) :
    extractReading low τ (r.map Prod.snd) = extractC τ (r.map Prod.snd) :=
  ite_eq_right h

private theorem extractReading_of_low {low : Finset SyntacticObject}
    {τ : RoseTree Vertex → Option LexicalItem.Token} {r : RoseTree (CopyMark × Vertex)}
    (h : ReadLow low r) : extractReading low τ (r.map Prod.snd) = some [] :=
  ite_eq_left h

/-- A reading gives a cut of the copy object under its policy, its unary vertices contracted. -/
theorem exists_mem_cutSummandsG_lf (hroot : t.val.value.1 = none) (hτ : MarkedBy τ t.val) :
    ∃ T, (t.cutForest low, T) ∈
        cutSummandsG (extractReading low (τ ∘ UnorderedTree.mk)) t.unmark.val ∧
      contractUnary T = (t.lf low).val := by
  obtain ⟨T, hT, hm⟩ := exists_mem_cutSummandsG_readCut (low := ReadLow low)
    (e := extractReading low (τ ∘ UnorderedTree.mk)) (s := t.val)
    (fun l hl ↦ by simp [hroot] at hl)
    (fun r hr l hl hn ↦ (extractReading_of_not_low hn).trans
      (extractC_map_snd (hτ r hr (by simp [hl])) hl))
    (fun r _ hr ↦ extractReading_of_low hr)
  refine ⟨T, hm, ?_⟩
  have h := map_contractUnary_readCut (low := ReadLow low) t.2
  rw [hT] at h
  exact (by simpa using h : contractUnary T = lfBy (ReadLow low) t.val)

/-- With no chain read low, a reading is the contraction, a term of the coproduct `Δ^c`: the lower
copies are an admissible cut of the copy object. -/
theorem mem_cutSummandsCN_contract (hroot : t.val.value.1 = none) (hτ : MarkedBy τ t.val) :
    ((t.cutForest ∅).map UnorderedTree.mk, UnorderedTree.mk t.contract.val) ∈
      cutSummandsCN τ (UnorderedTree.mk t.unmark.val) := by
  obtain ⟨T, hT, hm⟩ := exists_mem_cutSummandsG_readCut (low := ReadLow ∅)
    (e := extractC (τ ∘ UnorderedTree.mk)) (s := t.val)
    (fun l hl ↦ by simp [hroot] at hl)
    (fun r hr l hl _ ↦ extractC_map_snd (hτ r hr (by simp [hl])) hl)
    (fun r _ hr ↦ absurd hr (not_readLow_empty r))
  obtain rfl : T = contractTree t.val := by
    have := readCut_readLow_empty t.val
    rw [hT] at this
    simpa using this
  rw [cutSummandsCN_mk]
  exact Multiset.mem_map.2 ⟨_, hm, rfl⟩

/-- With every chain read low, a reading is a term of the deletion coproduct `Δ^d`: the higher
copies are an admissible cut of the copy object. -/
theorem mem_cutSummandsDN_lf (hlow : ∀ r ∈ t.val.subtrees, r.value.1.isSome → ReadLow low r) :
    ((t.cutForest low).map UnorderedTree.mk, UnorderedTree.mk (t.lf low).val) ∈
      cutSummandsDN (UnorderedTree.mk t.unmark.val) := by
  obtain ⟨T, hT, hm⟩ := exists_mem_cutSummandsG_readCut (low := ReadLow low) (e := pruning)
    (s := t.val)
    (fun l hl ↦ hlow _ (self_mem_subtrees _) (by simp [hl]))
    (fun r hr l hl hn ↦ absurd (hlow r hr (by simp [hl])) hn)
    (fun _ _ _ ↦ rfl)
  have h := map_contractUnary_readCut (low := ReadLow low) t.2
  rw [hT, List.map_singleton, List.cons.injEq] at h
  rw [cutSummandsDN, cutSummandsN_mk, Multiset.map_map]
  refine Multiset.mem_map.2 ⟨_, hm, ?_⟩
  simp only [Function.comp_apply, projSummand, UnorderedTree.contractUnary_mk]
  exact congrArg₂ Prod.mk rfl (congrArg UnorderedTree.mk h.1)

end Minimalist.LinearizedSyntacticObject.Marked
