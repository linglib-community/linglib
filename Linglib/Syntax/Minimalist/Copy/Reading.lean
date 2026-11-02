/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Marked
public import Linglib.Syntax.Minimalist.SyntacticObject.TokenCCommand

/-!
# The readings of a marked object

This file defines what a linearized object with its lower copies marked gives to the semantic
interface. A reading is the finite set of chains read low, a chain being named by its term in the
copy object. A chain read high keeps its higher copy, and its lower copies contract to traces. A
chain read low keeps its lowest copy, and its higher copies are deleted. With no chain read low the
result [is the contraction](##lf_empty). A reading [binds only where the copy object
does](##cCommands_unmark_of_cCommands_lf), unless it deletes a copy whose sister is a copy of it.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.Marked.reading`: the recursion over a marked tree that every
  reading's objects are built by.
* `Minimalist.LinearizedSyntacticObject.Marked.lf`: the object a reading gives.
* `Minimalist.LinearizedSyntacticObject.Marked.carrying`: the chains with a lower copy holding a
  token.

## Implementation notes

* A movement node is found by search: a binary node one of whose daughters has the term of a marked
  subtree of the other. Recording it would put on the object a datum externalization never reads.

## References

* [marcolli-chomsky-berwick-2025]
* [collins-2026]
-/

@[expose] public section

namespace Minimalist.LinearizedSyntacticObject.Marked

open RoseTree SyntacticObject

/-- The term of the copy object a tree is a copy of, its marks forgotten. Marking leaves it
unchanged, so it names a chain at every stage of a derivation. -/
def termOf (r : RoseTree (CopyMark × Vertex)) : UnorderedTree Vertex :=
  UnorderedTree.mk (r.map Prod.snd)

/-- The mark of a lower copy of `x` in `y`: a marked subtree of `y` with the term of `x`. -/
def lowerCopy? (x y : RoseTree (CopyMark × Vertex)) : Option (Option LexicalItem.Token) :=
  y.subtrees.findSome? fun r ↦ r.value.1.bind fun l ↦ if termOf r = termOf x then some l else none

/-- The chain of the copy `r` is read low in the reading `low`. -/
def ReadLow (low : Finset SyntacticObject) (r : RoseTree (CopyMark × Vertex)) : Prop :=
  ∃ m ∈ low, m.val = termOf r

instance (low : Finset SyntacticObject) : DecidablePred (ReadLow low) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ low, _))

@[simp] theorem not_readLow_empty (r : RoseTree (CopyMark × Vertex)) : ¬ ReadLow ∅ r := by
  simp [ReadLow]

section Reading

variable {β : Type*} (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
  (tr : RoseTree (CopyMark × Vertex) → Option LexicalItem.Token → β) (nd : Vertex → List β → β)
  (wrap : Option LexicalItem.Token → β → β) (del : RoseTree (CopyMark × Vertex) → Vertex → β → β)

/-- A node with its daughters, each paired with what it reads as. A copy of a chain read low is
deleted at its movement node by `del`, which receives that copy and what the other daughter reads
as, and `wrap` goes around the other daughter of a copy of a chain read high. A marked copy reads as
`tr` of itself and its mark if its chain is read high. -/
def readStep (v : CopyMark × Vertex) (cs : List (RoseTree (CopyMark × Vertex) × β)) :
    RoseTree (CopyMark × Vertex) × β :=
  let raw := RoseTree.node v (cs.map Prod.fst)
  let plain : β :=
    match cs with
    | [x, y] =>
      match lowerCopy? x.1 y.1, lowerCopy? y.1 x.1 with
      | some l, _ => if low x.1 then del x.1 v.2 y.2 else nd v.2 [x.2, wrap l y.2]
      | _, some l => if low y.1 then del y.1 v.2 x.2 else nd v.2 [wrap l x.2, y.2]
      | none, none => nd v.2 [x.2, y.2]
    | _ => nd v.2 (cs.map Prod.snd)
  (raw, match v.1 with
    | some l => if low raw then plain else tr raw l
    | none => plain)

/-- What a marked tree reads as, under `readStep`. -/
def reading (t : RoseTree (CopyMark × Vertex)) : β :=
  (fold (readStep low tr nd wrap del) t).2

theorem fold_readStep (t : RoseTree (CopyMark × Vertex)) :
    fold (readStep low tr nd wrap del) t = (t, reading low tr nd wrap del t) := by
  refine Prod.ext ?_ rfl
  induction t with
  | node v cs ih =>
    simp only [fold_node, readStep, List.map_map]
    congr 1
    exact (List.map_congr_left ih).trans (List.map_id' _)

theorem reading_node (v : CopyMark × Vertex) (cs : List (RoseTree (CopyMark × Vertex))) :
    reading low tr nd wrap del (.node v cs) =
      (readStep low tr nd wrap del v (cs.map fun c ↦ (c, reading low tr nd wrap del c))).2 := by
  rw [reading, fold_node]
  congr 2
  exact List.map_congr_left fun c _ ↦ fold_readStep low tr nd wrap del c

/-- A lower copy reads as `tr` if its chain is read high, and otherwise as if it were not one. -/
theorem reading_some (l : Option LexicalItem.Token) (a : Vertex)
    (cs : List (RoseTree (CopyMark × Vertex))) :
    reading low tr nd wrap del (.node (some l, a) cs) =
      if low (.node (some l, a) cs) then reading low tr nd wrap del (.node (none, a) cs)
      else tr (.node (some l, a) cs) l := by
  rw [reading_node, reading_node]
  simp [readStep, List.map_map, Function.comp_def]

theorem reading_of_length_ne (a : Vertex) {cs : List (RoseTree (CopyMark × Vertex))}
    (hc : cs.length ≠ 2) :
    reading low tr nd wrap del (.node (none, a) cs) =
      nd a (cs.map (reading low tr nd wrap del)) := by
  rw [reading_node]
  rcases cs with _ | ⟨u, _ | ⟨v, _ | ⟨w, ws⟩⟩⟩
  · simp [readStep]
  · simp [readStep]
  · simp at hc
  · simp [readStep, List.map_map, Function.comp_def]

/-- A binary node, when `wrap` does nothing: a daughter that has a lower copy in the other is
deleted if its chain is read low. -/
theorem reading_pair (hw : ∀ l b, wrap l b = b) (a : Vertex) (u v : RoseTree (CopyMark × Vertex)) :
    reading low tr nd wrap del (.node (none, a) [u, v]) =
      if (lowerCopy? u v).isSome then
        if low u then del u a (reading low tr nd wrap del v)
        else nd a [reading low tr nd wrap del u, reading low tr nd wrap del v]
      else if (lowerCopy? v u).isSome then
        if low v then del v a (reading low tr nd wrap del u)
        else nd a [reading low tr nd wrap del u, reading low tr nd wrap del v]
      else nd a [reading low tr nd wrap del u, reading low tr nd wrap del v] := by
  rw [reading_node]
  simp only [readStep, List.map]
  rcases lowerCopy? u v with _ | l <;> rcases lowerCopy? v u with _ | l' <;> simp [hw]

end Reading

theorem isSome_lowerCopy?_iff {u v : RoseTree (CopyMark × Vertex)} :
    (lowerCopy? u v).isSome ↔ ∃ r ∈ v.subtrees, r.value.1.isSome ∧ termOf r = termOf u := by
  rw [lowerCopy?, List.findSome?_isSome_iff]
  refine exists_congr fun r ↦ and_congr_right fun _ ↦ ?_
  rcases r.value.1 with _ | l <;> by_cases h : termOf r = termOf u <;> simp [h]

/-- The object a test of copies gives, as a tree of vertices. -/
def lfBy (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low] :
    RoseTree (CopyMark × Vertex) → RoseTree Vertex :=
  reading low (fun _ l ↦ .node (.inr l) []) .node (fun _ y ↦ y) fun _ _ y ↦ y

/-- The object a reading gives, as a tree of vertices. -/
abbrev lfTree (low : Finset SyntacticObject) : RoseTree (CopyMark × Vertex) → RoseTree Vertex :=
  lfBy (ReadLow low)

section Equations

variable (P : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred P]

theorem lfBy_some (l : Option LexicalItem.Token) (a : Vertex)
    (cs : List (RoseTree (CopyMark × Vertex))) :
    lfBy P (.node (some l, a) cs) =
      if P (.node (some l, a) cs) then lfBy P (.node (none, a) cs) else .node (.inr l) [] :=
  reading_some ..

theorem lfBy_of_length_ne (a : Vertex) {cs : List (RoseTree (CopyMark × Vertex))}
    (hc : cs.length ≠ 2) : lfBy P (.node (none, a) cs) = .node a (cs.map (lfBy P)) :=
  reading_of_length_ne _ _ _ _ _ a hc

theorem lfBy_pair (a : Vertex) (u v : RoseTree (CopyMark × Vertex)) :
    lfBy P (.node (none, a) [u, v]) =
      if (lowerCopy? u v).isSome then
        if P u then lfBy P v else .node a [lfBy P u, lfBy P v]
      else if (lowerCopy? v u).isSome then
        if P v then lfBy P u else .node a [lfBy P u, lfBy P v]
      else .node a [lfBy P u, lfBy P v] :=
  reading_pair _ _ _ _ _ (fun _ _ ↦ rfl) a u v

@[simp] theorem lfBy_leaf (a : Vertex) : lfBy P (.node (none, a) []) = .node a [] :=
  lfBy_of_length_ne P a (by simp)

end Equations

/-- The object a test gives at a node is a trace, the node with its daughters' objects, or a
daughter's object. -/
theorem lfBy_node_cases (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low] (k :
    CopyMark)
    (a : Vertex) (cs : List (RoseTree (CopyMark × Vertex))) :
    (∃ l, lfBy low (.node (k, a) cs) = .node (.inr l) []) ∨
      lfBy low (.node (k, a) cs) = .node a (cs.map (lfBy low)) ∨
      ∃ c ∈ cs, lfBy low (.node (k, a) cs) = lfBy low c := by
  unfold lfBy
  rw [reading_node]
  simp only [readStep]
  rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases k <;> simp only [List.map] <;>
    (try split) <;> (try split) <;> (try split_ifs) <;> simp_all

theorem isSyntacticObject_lfBy (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
    {t : RoseTree (CopyMark × Vertex)} (h : IsSyntacticObject (UnorderedTree.mk (t.map Prod.snd))) :
    IsSyntacticObject (UnorderedTree.mk (lfBy low t)) := by
  induction t with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [isSyntacticObject_mk, map_node, licensed_node_iff] at h
    rcases lfBy_node_cases low k a cs with ⟨l, hl⟩ | hn | ⟨c, hc, hl⟩
    · rw [hl]
      exact isSyntacticObject_mk_leaf (by simp)
    · rw [hn, isSyntacticObject_mk, licensed_node_iff]
      refine ⟨(Vertex.licenses_iff_of_card_eq (by simp)).1 h.1, fun c hc ↦ ?_⟩
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
      exact ih c' hc' (h.2 _ (List.mem_map_of_mem hc'))
    · rw [hl]
      exact ih c hc (h.2 _ (List.mem_map_of_mem hc))

/-- The object a reading gives: each chain in `low` keeps its lowest copy, and every other its
highest, its lower copies contracted. -/
def lf (t : Marked) (low : Finset SyntacticObject) : LinearizedSyntacticObject :=
  ⟨lfTree low t.val, isSyntacticObject_lfBy _ t.2⟩

/-- The chains with a lower copy holding `y`. -/
def carrying (t : Marked) (y : LexicalItem.Token) : Finset SyntacticObject :=
  ((t.val.subtrees.filter fun r ↦
      r.value.1.isSome ∧ Sum.inl (some y) ∈ (r.map Prod.snd).leaves).filterMap fun r ↦
    if h : IsSyntacticObject (termOf r) then some ⟨termOf r, h⟩ else none).toFinset

/-! ### The contraction -/

theorem lfTree_empty (t : RoseTree (CopyMark × Vertex)) : lfTree ∅ t = contractTree t := by
  induction t with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    simp only [lfTree, lfBy] at ih ⊢
    rw [reading_node]
    simp only [readStep]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;> cases k <;> simp only [List.map] <;>
      (try split) <;> (try split) <;> simp_all [contractTree_none, contractTree_some]

/-- With no chain read low, a reading gives the contraction. -/
@[simp] theorem lf_empty (t : Marked) : t.lf ∅ = t.contract :=
  Subtype.ext (lfTree_empty t.val)

/-! ### Objects with no lower copy -/

theorem lowerCopy?_map_none (x : RoseTree (CopyMark × Vertex)) (s : RoseTree Vertex) :
    lowerCopy? x (s.map ((none, ·) : Vertex → CopyMark × Vertex)) = none := by
  refine List.findSome?_eq_none_iff.2 fun r hr ↦ ?_
  rw [subtrees_map] at hr
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hr
  cases q
  simp

theorem lfBy_map_none (low : RoseTree (CopyMark × Vertex) → Prop) [DecidablePred low]
    (s : RoseTree Vertex) : lfBy low (s.map ((none, ·) : Vertex → CopyMark × Vertex)) = s := by
  induction s with
  | node a cs ih =>
    simp only [lfBy] at ih ⊢
    rw [map_node, reading_node]
    simp only [readStep, List.map_map]
    rcases cs with _ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩ <;>
      simp_all [lowerCopy?_map_none, Function.comp_def]
    exact (List.map_congr_left ih.2.2.2).trans (List.map_id' _)

/-- An object with no lower copy gives itself under every reading. -/
@[simp] theorem lf_ofLinearized (p : LinearizedSyntacticObject) (low : Finset SyntacticObject) :
    (ofLinearized p).lf low = p :=
  Subtype.ext (lfBy_map_none _ p.val)

/-! ### Binding at a reading is binding at the copy object -/

section Binding

variable {P : RoseTree (CopyMark × Vertex) → Prop} [DecidablePred P]
  {x y w : LexicalItem.Token} {s : RoseTree (CopyMark × Vertex)}

/-- A reading holds only what the copy object does. -/
theorem holds_of_holds_lfBy (h : Holds w (lfBy P s)) : Holds w (s.map Prod.snd) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [map_node]
    rcases lfBy_node_cases P k a cs with ⟨l, hl⟩ | hl | ⟨c, hc, hl⟩
    · rw [hl, holds_leaf] at h
      simp at h
    · rw [hl] at h
      rcases cs with _ | ⟨c₀, cs⟩
      · simpa using h
      · obtain ⟨c, hc, hyc⟩ := exists_mem_of_holds_map (by simp) h
        exact holds_node_of_mem (List.mem_map_of_mem hc) (ih c hc hyc)
    · rw [hl] at h
      exact holds_node_of_mem (List.mem_map_of_mem hc) (ih c hc h)

/-- A token is a daughter in a reading only where it is one in the copy object, when no copy the
test deletes has a sister that is a copy of it. -/
theorem map_snd_eq_leaf_of_lfBy_eq
    (hP : ∀ r ∈ s.subtrees, ∀ k a u v, r = .node (k, a) [u, v] → P u ∨ P v → termOf u ≠ termOf v)
    (h : lfBy P s = .node (.inl (some w)) []) : s.map Prod.snd = .node (.inl (some w)) [] := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    have hn : lfBy P (.node (none, a) cs) = .node (.inl (some w)) [] →
        (RoseTree.node (k, a) cs).map Prod.snd = .node (.inl (some w)) [] := by
      intro he
      have hch : ∀ c ∈ cs, lfBy P c = .node (.inl (some w)) [] →
          c.map Prod.snd = .node (.inl (some w)) [] := fun c hc ↦
        ih c hc fun r hr ↦ hP r (mem_subtrees.2 ((mem_subtrees.1 hr).trans (.of_mem_children hc)))
      have hdel : ∀ {u z : RoseTree (CopyMark × Vertex)}, u ∈ cs → z ∈ cs → P u →
          termOf u ≠ termOf z → (lowerCopy? u z).isSome → lfBy P z = .node (.inl (some w)) [] →
          False := by
        intro u z _ hz _ hne hl hle
        obtain ⟨r, hr, -, ht⟩ := isSome_lowerCopy?_iff.1 hl
        have hzl := hch z hz hle
        obtain ⟨⟨k', a'⟩, ds⟩ := z
        rw [map_node, RoseTree.node.injEq, List.map_eq_nil_iff] at hzl
        obtain ⟨-, rfl⟩ := hzl
        simp only [subtrees_node, List.flatMap_nil, List.mem_singleton] at hr
        subst hr
        exact hne ht.symm
      by_cases hlen : cs.length = 2
      · obtain ⟨u, z, rfl⟩ := List.length_eq_two.1 hlen
        have hd := hP _ (self_mem_subtrees _) k a u z rfl
        rw [lfBy_pair] at he
        split_ifs at he with h1 h2 h3 h4 <;> try simp at he
        · exact (hdel (by simp) (by simp) h2 (hd (.inl h2)) h1 he).elim
        · exact (hdel (by simp) (by simp) h4 (hd (.inr h4)).symm h3 he).elim
      · rw [lfBy_of_length_ne _ _ hlen] at he
        simp only [RoseTree.node.injEq, List.map_eq_nil_iff] at he
        obtain ⟨rfl, rfl⟩ := he
        simp
    cases k with
    | none => exact hn h
    | some l =>
      rw [lfBy_some] at h
      split_ifs at h with hp
      · exact hn h
      · simp at h

/-- A token c-commanding another in a reading does so in the copy object, when no copy the test
deletes has a sister that is a copy of it. -/
theorem tokenCCommands_of_tokenCCommands_lfBy
    (hP : ∀ r ∈ s.subtrees, ∀ k a u v, r = .node (k, a) [u, v] → P u ∨ P v → termOf u ≠ termOf v)
    (h : TokenCCommands x y (lfBy P s)) : TokenCCommands x y (s.map Prod.snd) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [map_node]
    have hn : TokenCCommands x y (lfBy P (.node (none, a) cs)) →
        TokenCCommands x y (.node a (cs.map (RoseTree.map Prod.snd))) := by
      intro hc
      by_cases hlen : cs.length = 2
      · obtain ⟨u, z, rfl⟩ := List.length_eq_two.1 hlen
        have hsub : ∀ c ∈ [u, z], ∀ r ∈ c.subtrees, ∀ k a u' v', r = .node (k, a) [u', v'] →
            P u' ∨ P v' → termOf u' ≠ termOf v' := fun c hc r hr ↦
          hP r (mem_subtrees.2 ((mem_subtrees.1 hr).trans (.of_mem_children hc)))
        have hu := ih u (by simp) (hsub u (by simp))
        have hz := ih z (by simp) (hsub z (by simp))
        have hnode : TokenCCommands x y (.node a [lfBy P u, lfBy P z]) →
            TokenCCommands x y (.node a [u.map Prod.snd, z.map Prod.snd]) := fun hc' ↦ by
          rw [tokenCCommands_pair_iff] at hc' ⊢
          rcases hc' with h' | h' | ⟨hl, hy⟩ | ⟨hl, hy⟩
          · exact .inl (hu h')
          · exact .inr (.inl (hz h'))
          · exact .inr (.inr (.inl ⟨map_snd_eq_leaf_of_lfBy_eq (hsub u (by simp)) hl,
              holds_of_holds_lfBy hy⟩))
          · exact .inr (.inr (.inr ⟨map_snd_eq_leaf_of_lfBy_eq (hsub z (by simp)) hl,
              holds_of_holds_lfBy hy⟩))
        rw [lfBy_pair] at hc
        simp only [List.map_cons, List.map_nil]
        split_ifs at hc with h1 h2 h3 h4
        · exact .inr (hz hc)
        · exact hnode hc
        · exact .inl (hu hc)
        · exact hnode hc
        · exact hnode hc
      · rw [lfBy_of_length_ne _ _ hlen] at hc
        exact absurd hc (not_tokenCCommands_of_length_ne (by simpa using hlen))
    cases k with
    | none => exact hn h
    | some l =>
      rw [lfBy_some] at h
      split_ifs at h with hp
      · exact hn h
      · exact absurd h (not_tokenCCommands_of_length_ne (by simp))

/-- Binding at a reading is binding at the copy object, when no copy the reading deletes has a
sister that is a copy of it. -/
theorem cCommands_unmark_of_cCommands_lf {t : Marked} {low : Finset SyntacticObject} (hxy : x ≠ y)
    (hlow : ∀ r ∈ t.val.subtrees, ∀ k a u v, r = .node (k, a) [u, v] →
      ReadLow low u ∨ ReadLow low v → termOf u ≠ termOf v)
    (h : (t.lf low).toSyntacticObject.CCommands ↑x ↑y) :
    t.unmark.toSyntacticObject.CCommands ↑x ↑y :=
  (cCommands_iff_tokenCCommands hxy _).2 (tokenCCommands_of_tokenCCommands_lfBy hlow
    ((cCommands_iff_tokenCCommands hxy _).1 h))

/-- A c-command between two pronounced leaves of the contraction holds between the same leaves of
the copy object, the contraction changing nothing outside the lower copies. -/
theorem cCommands_unmark_of_cCommands_contract {t : Marked} (hxy : x ≠ y)
    (h : t.contract.toSyntacticObject.CCommands ↑x ↑y) :
    t.unmark.toSyntacticObject.CCommands ↑x ↑y :=
  cCommands_unmark_of_cCommands_lf (low := ∅) hxy
    (fun _ _ _ _ u v _ h ↦ h.elim (not_readLow_empty u · |>.elim) (not_readLow_empty v · |>.elim))
    (by rwa [lf_empty])

end Binding

end Minimalist.LinearizedSyntacticObject.Marked
