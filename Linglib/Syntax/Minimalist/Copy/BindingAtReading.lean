/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.ToTree
public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# Binding at a reading

This file proves that binding at the copy object is binding at one reading. A token c-commands
another in the copy object just when it does in the reading in which the chains holding the second
are read low. So the choice of copies the semantic interface reads loses no binding relation, and
the reading that shows a given relation is found from the bound token alone.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.Marked.MarksName`,
  `Minimalist.LinearizedSyntacticObject.Marked.TraceFree`,
  `Minimalist.LinearizedSyntacticObject.Marked.DistinctDaughters`: the conditions on the final
  object.

## Main results

* `Minimalist.Derivation.bindsAtReading_carrying_iff`: binding at the copy object is binding at the
  reading `carrying y`.

## Implementation notes

* A reading is an object with material deleted and contracted, so binding at the reading `carrying`
  implies binding at the copy object with no condition on the derivation. The converse is by
  induction on the steps of the derivation.
* The theorem names one reading rather than some reading. Some reading may bind where the copy
  object does not: an object that moves from itself, read low, comes to c-command the sister of its
  movement node. `DistinctDaughters` excludes that derivation, and `carrying` does not read such a
  chain low.
* Two chains sharing a mark could have `mark` reach copies with different terms, which `MarksName`
  excludes. Reading each chain high or low is enough because the theorem concerns one pair of tokens
  at a time.

## References

* [chomsky-1995]
* [collins-2005]
* [collins-2026]
-/

@[expose] public section

namespace Minimalist.LinearizedSyntacticObject.Marked

open RoseTree SyntacticObject

local notation "MT" => RoseTree (CopyMark × Vertex)

/-! ### C-command between tokens, on ordered trees -/

/-- The tree holds the token `y`. -/
private def Holds (y : LexicalItem.Token) (p : RoseTree Vertex) : Prop :=
  Sum.inl (some y) ∈ p.leaves

private instance (y : LexicalItem.Token) : DecidablePred (Holds y) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

variable {x y : LexicalItem.Token}

@[local simp] private theorem holds_leaf (a : Vertex) :
    Holds y (.node a []) ↔ a = Sum.inl (some y) := by
  simp [Holds, eq_comm]

private theorem holds_pair (a : Vertex) (l r : RoseTree Vertex) :
    Holds y (.node a [l, r]) ↔ Holds y l ∨ Holds y r := by
  simp [Holds]

private theorem mem_list_sum {α : Type*} {a : α} {L : List (Multiset α)} :
    a ∈ L.sum ↔ ∃ s ∈ L, a ∈ s := by
  induction L with
  | nil => simp
  | cons s L ih => simp [ih]

private theorem holds_node_of_mem {a : Vertex} {cs : List (RoseTree Vertex)} {c : RoseTree Vertex}
    (hc : c ∈ cs) (h : Holds y c) : Holds y (.node a cs) := by
  rcases cs with _ | ⟨c₀, cs⟩
  · simp at hc
  · rw [Holds, leaves_node_cons, mem_list_sum]
    exact ⟨c.leaves, List.mem_map_of_mem hc, h⟩

private theorem exists_mem_of_holds_node {a : Vertex} {c₀ : RoseTree Vertex}
    {cs : List (RoseTree Vertex)} (h : Holds y (.node a (c₀ :: cs))) :
    ∃ c ∈ c₀ :: cs, Holds y c := by
  rw [Holds, leaves_node_cons, mem_list_sum] at h
  obtain ⟨s, hs, hy⟩ := h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hs
  exact ⟨c, hc, hy⟩

private theorem exists_mem_of_holds_map {α : Type*} {a : Vertex} {cs : List α}
    {f : α → RoseTree Vertex} (hne : cs ≠ []) (h : Holds y (.node a (cs.map f))) :
    ∃ c ∈ cs, Holds y (f c) := by
  rcases cs with _ | ⟨c₀, cs⟩
  · exact absurd rfl hne
  · obtain ⟨c, hc, hyc⟩ := exists_mem_of_holds_node h
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 (show c ∈ (c₀ :: cs).map f from hc)
    exact ⟨c', hc', hyc⟩

private theorem holds_of_mem_subtrees {r z : RoseTree Vertex} (hr : r ∈ z.subtrees)
    (h : Holds y r) : Holds y z := by
  induction z with
  | node a cs ih =>
    rw [subtrees_node, List.mem_cons, List.mem_flatMap] at hr
    rcases hr with rfl | ⟨c, hc, hrc⟩
    · exact h
    · exact holds_node_of_mem hc (ih c hc hrc)

private theorem holds_congr {p q : RoseTree Vertex} (h : UnorderedTree.mk p = UnorderedTree.mk q) :
    Holds y p ↔ Holds y q := by
  rw [Holds, Holds, ← UnorderedTree.leaves_mk, ← UnorderedTree.leaves_mk q, h]

/-- `x` c-commands `y` in an ordered tree: `x` is a daughter whose sister holds `y`. -/
private inductive CC (x y : LexicalItem.Token) : RoseTree Vertex → Prop
  | inl {a l r} : CC x y l → CC x y (.node a [l, r])
  | inr {a l r} : CC x y r → CC x y (.node a [l, r])
  | left {a r} : Holds y r → CC x y (.node a [.node (.inl (some x)) [], r])
  | right {a l} : Holds y l → CC x y (.node a [l, .node (.inl (some x)) []])

private theorem CC.exists_pair {p : RoseTree Vertex} (h : CC x y p) :
    ∃ a l r, p = .node a [l, r] := by
  cases h <;> exact ⟨_, _, _, rfl⟩

private theorem CC.holds {p : RoseTree Vertex} (h : CC x y p) : Holds y p := by
  induction h with
  | inl _ ih => exact (holds_pair _ _ _).2 (.inl ih)
  | inr _ ih => exact (holds_pair _ _ _).2 (.inr ih)
  | left hy => exact (holds_pair _ _ _).2 (.inr hy)
  | right hy => exact (holds_pair _ _ _).2 (.inl hy)

private theorem CC.of_mem_subtrees {r z : RoseTree Vertex} (hr : r ∈ z.subtrees) (h : CC x y r)
    (hz : IsSyntacticObject (UnorderedTree.mk z)) : CC x y z := by
  induction z with
  | node a cs ih =>
    rw [subtrees_node, List.mem_cons, List.mem_flatMap] at hr
    rcases hr with rfl | ⟨c, hc, hrc⟩
    · exact h
    · have hl := (licensed_node_iff.1 ((isSyntacticObject_mk _).1 hz)).2
      rcases length_eq_zero_or_two hz with hlen | hlen
      · rw [List.length_eq_zero_iff] at hlen
        subst hlen
        simp at hc
      · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
        rcases List.mem_pair.1 hc with rfl | rfl
        · exact .inl (ih _ hc hrc (hl _ (by simp)))
        · exact .inr (ih _ hc hrc (hl _ (by simp)))

private theorem eq_node_of_coe_eq {v : RoseTree Vertex}
    (h : UnorderedTree.mk (.node (Sum.inl (some x)) []) = UnorderedTree.mk v) :
    v = .node (Sum.inl (some x)) [] := by
  obtain ⟨b, ds⟩ := v
  obtain ⟨rfl, hd⟩ := UnorderedTree.mk_node_eq_mk_node_iff.1 h
  rcases ds with _ | ⟨d, ds⟩
  · rfl
  · have := congrArg Multiset.card hd
    simp at this

/-- The token is a term of the object just when the tree holds it. -/
private theorem coe_mem_terms_iff (p : LinearizedSyntacticObject) :
    (↑y : SyntacticObject) ∈ p.toSyntacticObject.terms ↔ Holds y p.val := by
  obtain ⟨p, h⟩ := p
  induction p with
  | node a cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · rw [List.length_eq_zero_iff] at hlen
      subst hlen
      have ht : (LinearizedSyntacticObject.toSyntacticObject ⟨.node a [], h⟩).terms =
          {LinearizedSyntacticObject.toSyntacticObject ⟨.node a [], h⟩} := by
        rcases a with (_ | v) | (_ | v)
        · exact absurd h (by simp [licensed_node_iff, Vertex.Licenses])
        · exact terms_leaf v
        · exact terms_trace
        · exact terms_traceOf v
      rw [ht, Multiset.mem_singleton, Subtype.ext_iff, holds_leaf]
      change UnorderedTree.mk (.node (Sum.inl (some y)) []) = UnorderedTree.mk (.node a []) ↔ _
      rw [UnorderedTree.mk_node_eq_mk_node_iff]
      simp [eq_comm]
    · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hu, hv⟩ := (isSyntacticObject_mk_merge _ _).1 h
      change (↑y : SyntacticObject) ∈ (LinearizedSyntacticObject.toSyntacticObject
        (LinearizedSyntacticObject.merge ⟨u, hu⟩ ⟨v, hv⟩)).terms ↔ _
      rw [LinearizedSyntacticObject.toSyntacticObject_merge, terms_merge, Multiset.mem_cons,
        Multiset.mem_add, holds_pair, ih u (by simp) hu, ih v (by simp) hv]
      exact or_iff_right (leaf_ne_merge _ _ _)

/-- On a syntactic object c-command between distinct tokens is `CC`. -/
private theorem cCommands_iff_cc (hxy : x ≠ y) (p : LinearizedSyntacticObject) :
    CCommands p.toSyntacticObject ↑x ↑y ↔ CC x y p.val := by
  obtain ⟨p, h⟩ := p
  induction p with
  | node a cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · rw [List.length_eq_zero_iff] at hlen
      subst hlen
      constructor
      · rintro ⟨z, -, ⟨w, hw, hwx, -, -⟩, -⟩
        have ht : (LinearizedSyntacticObject.toSyntacticObject ⟨.node a [], h⟩).terms =
            {LinearizedSyntacticObject.toSyntacticObject ⟨.node a [], h⟩} := by
          rcases a with (_ | v) | (_ | v)
          · exact absurd h (by simp [licensed_node_iff, Vertex.Licenses])
          · exact terms_leaf v
          · exact terms_trace
          · exact terms_traceOf v
        rw [ht, Multiset.mem_singleton] at hw
        subst hw
        simp [ImmediatelyContains] at hwx
      · intro hc
        cases hc
    · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hu, hv⟩ := (isSyntacticObject_mk_merge _ _).1 h
      let U : LinearizedSyntacticObject := ⟨u, hu⟩
      let V : LinearizedSyntacticObject := ⟨v, hv⟩
      change CCommands (LinearizedSyntacticObject.toSyntacticObject
        (LinearizedSyntacticObject.merge U V)) _ _ ↔ _
      rw [LinearizedSyntacticObject.toSyntacticObject_merge]
      constructor
      · rintro ⟨z, -, hs, hzy⟩
        rcases Sisters.of_merge hs with hc | hc | ⟨he, rfl⟩ | ⟨he, rfl⟩
        · exact .inl ((ih u (by simp) hu).1 ⟨z, hc.mem_right, hc, hzy⟩)
        · exact .inr ((ih v (by simp) hv).1 ⟨z, hc.mem_right, hc, hzy⟩)
        · obtain rfl := eq_node_of_coe_eq (congrArg (·.val) he)
          exact .left ((coe_mem_terms_iff V).1 (mem_terms.2 hzy))
        · obtain rfl := eq_node_of_coe_eq (congrArg (·.val) he)
          exact .right ((coe_mem_terms_iff U).1 (mem_terms.2 hzy))
      · intro hc
        cases hc with
        | inl hl =>
          exact ((ih u (by simp) hu).2 hl).mono fun t ht ↦ by
            rw [terms_merge]; exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl ht))
        | inr hr =>
          exact ((ih v (by simp) hv).2 hr).mono fun t ht ↦ by
            rw [terms_merge]; exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr ht))
        | left hy =>
          refine cCommands_merge_left (l := U.toSyntacticObject) (r := V.toSyntacticObject)
            (fun he ↦ ?_) ((coe_mem_terms_iff V).2 hy)
          have hv' : v = .node (.inl (some x)) [] := eq_node_of_coe_eq (congrArg (·.val) he)
          rw [hv', holds_leaf] at hy
          exact hxy (Option.some.inj (Sum.inl.inj hy))
        | right hy =>
          refine ⟨U.toSyntacticObject, mem_terms.2 (.single
            ((immediatelyContains_merge _ _ _).2 (.inl rfl))), ⟨_, self_mem_terms _,
              (immediatelyContains_merge _ _ _).2 (.inr rfl),
              (immediatelyContains_merge _ _ _).2 (.inl rfl), fun he ↦ ?_⟩,
            mem_terms.1 ((coe_mem_terms_iff U).2 hy)⟩
          have hu' : u = .node (.inl (some x)) [] := eq_node_of_coe_eq (congrArg (·.val) he)
          rw [hu', holds_leaf] at hy
          exact hxy (Option.some.inj (Sum.inl.inj hy))

/-! ### The reading of a token -/

/-- The copy holds the token `y`. -/
private abbrev Has (y : LexicalItem.Token) (r : MT) : Prop := Holds y (r.map Prod.snd)

private theorem has_node {k : CopyMark} {a : Vertex} {cs : List MT} :
    Has y (.node (k, a) cs) ↔ Holds y (.node a (cs.map (RoseTree.map Prod.snd))) := by
  rw [Has, map_node]

private theorem has_pair {k : CopyMark} {a : Vertex} {u v : MT} :
    Has y (.node (k, a) [u, v]) ↔ Has y u ∨ Has y v := by
  rw [has_node]
  exact holds_pair _ _ _

section Equations

variable (P : MT → Prop) [DecidablePred P]

private theorem lfBy_pair (a : Vertex) (u v : MT) :
    lfBy P (.node (none, a) [u, v]) =
      if (lowerCopy? u v).isSome then
        (if P u then lfBy P v else .node a [lfBy P u, lfBy P v])
      else if (lowerCopy? v u).isSome then
        (if P v then lfBy P u else .node a [lfBy P u, lfBy P v])
      else .node a [lfBy P u, lfBy P v] := by
  unfold lfBy
  rw [reading_node]
  simp only [readStep, List.map]
  rcases lowerCopy? u v with _ | l <;> rcases lowerCopy? v u with _ | l' <;> simp

private theorem lfBy_some (l : Option LexicalItem.Token) (a : Vertex) (cs : List MT) :
    lfBy P (.node (some l, a) cs) =
      if P (.node (some l, a) cs) then lfBy P (.node (none, a) cs) else .node (.inr l) [] := by
  unfold lfBy
  rw [reading_node, reading_node]
  simp [readStep, List.map_map, Function.comp_def]

@[simp] theorem lfBy_leaf (a : Vertex) : lfBy P (.node (none, a) []) = .node a [] := by
  unfold lfBy
  rw [reading_node]
  simp [readStep]

end Equations

private theorem isSome_lowerCopy?_iff {u v : MT} :
    (lowerCopy? u v).isSome ↔ ∃ r ∈ v.subtrees, r.value.1.isSome ∧ termOf r = termOf u := by
  rw [lowerCopy?, List.findSome?_isSome_iff]
  refine exists_congr fun r ↦ and_congr_right fun _ ↦ ?_
  rcases r.value.1 with _ | l <;> by_cases h : termOf r = termOf u <;> simp [h]

private theorem lfBy_of_length_ne (P : MT → Prop) [DecidablePred P] (a : Vertex) {cs : List MT}
    (hc : cs.length ≠ 2) : lfBy P (.node (none, a) cs) = .node a (cs.map (lfBy P)) := by
  unfold lfBy
  rw [reading_node]
  rcases cs with _ | ⟨u, _ | ⟨v, _ | ⟨w, ws⟩⟩⟩
  · simp [readStep]
  · simp [readStep]
  · simp at hc
  · simp [readStep, List.map_map, Function.comp_def]

private instance (y : LexicalItem.Token) : DecidablePred (Has y) :=
  fun _ ↦ inferInstanceAs (Decidable (Holds y _))

/-- A copy of what a daughter's lower copy is a copy of holds the same tokens, so its sister does.
-/
private theorem has_of_isSome_lowerCopy? {u v : MT} (h : (lowerCopy? u v).isSome) (hu : Has y u) :
    Has y v := by
  obtain ⟨r, hr, -, ht⟩ := isSome_lowerCopy?_iff.1 h
  have hr' : Has y r := (holds_congr ht).2 hu
  have hmem : r.map Prod.snd ∈ (v.map Prod.snd).subtrees := by
    rw [subtrees_map]; exact List.mem_map_of_mem hr
  exact holds_of_mem_subtrees hmem hr'

/-- What holds `y` still does in the reading that reads low every copy holding `y`. -/
private theorem holds_lfBy {s : MT} (h : Has y s) : Holds y (lfBy (Has y) s) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    have hn : Holds y (lfBy (Has y) (.node (none, a) cs)) := by
      by_cases hlen : cs.length = 2
      · obtain ⟨u, w, rfl⟩ := List.length_eq_two.1 hlen
        have hsplit : Has y u ∨ Has y w := has_pair.1 h
        have hu := ih u (by simp)
        have hw := ih w (by simp)
        rw [lfBy_pair]
        split_ifs with h1 h2 h3 h4
        · exact hw (has_of_isSome_lowerCopy? h1 h2)
        · exact (holds_pair _ _ _).2 (.inr (hw (hsplit.resolve_left h2)))
        · exact hu (has_of_isSome_lowerCopy? h3 h4)
        · exact (holds_pair _ _ _).2 (.inl (hu (hsplit.resolve_right h4)))
        · exact (holds_pair _ _ _).2 (hsplit.imp hu hw)
      · rw [lfBy_of_length_ne _ _ hlen]
        have hm := has_node.1 h
        rcases cs with _ | ⟨c₀, cs⟩
        · simpa using hm
        · obtain ⟨c, hc, hyc⟩ := exists_mem_of_holds_map (by simp) hm
          exact holds_node_of_mem (List.mem_map_of_mem hc) (ih c hc hyc)
    cases k with
    | none => exact hn
    | some l =>
      rw [lfBy_some, ite_eq_left h]
      exact hn

/-- A reading holds only what the copy object does. -/
private theorem has_of_holds_lfBy (P : MT → Prop) [DecidablePred P] {w : LexicalItem.Token}
    {s : MT} (h : Holds w (lfBy P s)) : Has w s := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [has_node]
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

/-- A token other than `y` is a daughter in the reading only where it is an unmarked daughter. -/
private theorem eq_node_of_lfBy_eq {w : LexicalItem.Token} (hw : w ≠ y) {s : MT}
    (h : lfBy (Has y) s = .node (.inl (some w)) []) : s = .node (none, .inl (some w)) [] := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    have hn : lfBy (Has y) (.node (none, a) cs) = .node (.inl (some w)) [] →
        RoseTree.node ((none : CopyMark), a) cs = .node (none, .inl (some w)) [] := by
      intro he
      by_cases hlen : cs.length = 2
      · obtain ⟨u, z, rfl⟩ := List.length_eq_two.1 hlen
        rw [lfBy_pair] at he
        split_ifs at he with h1 h2 h3 h4 <;> try simp at he
        · obtain rfl := ih z (by simp) he
          obtain ⟨r, hr, hm, -⟩ := isSome_lowerCopy?_iff.1 h1
          simp at hr
          subst hr
          simp at hm
        · obtain rfl := ih u (by simp) he
          obtain ⟨r, hr, hm, -⟩ := isSome_lowerCopy?_iff.1 h3
          simp at hr
          subst hr
          simp at hm
      · rw [lfBy_of_length_ne _ _ hlen] at he
        simp only [RoseTree.node.injEq, List.map_eq_nil_iff] at he
        obtain ⟨rfl, rfl⟩ := he
        rfl
    cases k with
    | none => exact hn h
    | some l =>
      rw [lfBy_some] at h
      split_ifs at h with hp
      · obtain he := hn h
        simp only [RoseTree.node.injEq, Prod.mk.injEq, true_and] at he
        obtain ⟨rfl, rfl⟩ := he
        have : Holds y (.node (Sum.inl (some w)) []) := by simpa using has_node.1 hp
        exact absurd (Option.some.inj (Sum.inl.inj ((holds_leaf _).1 this))) hw
      · simp at h

/-- If the reading binds, the copy object does: a reading only deletes and contracts. -/
private theorem cc_of_cc_lfBy (hxy : x ≠ y) {s : MT} (h : CC x y (lfBy (Has y) s)) :
    CC x y (s.map Prod.snd) := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [map_node]
    have hn : CC x y (lfBy (Has y) (.node (none, a) cs)) →
        CC x y (.node a (cs.map (RoseTree.map Prod.snd))) := by
      intro hc
      by_cases hlen : cs.length = 2
      · obtain ⟨u, z, rfl⟩ := List.length_eq_two.1 hlen
        have hu := ih u (by simp)
        have hz := ih z (by simp)
        have hnode : CC x y (.node a [lfBy (Has y) u, lfBy (Has y) z]) →
            CC x y (.node a [u.map Prod.snd, z.map Prod.snd]) := by
          intro hc'
          generalize hlu : lfBy (Has y) u = lu at hc'
          generalize hlz : lfBy (Has y) z = lz at hc'
          cases hc' with
          | inl hl => exact .inl (hu (hlu ▸ hl))
          | inr hr => exact .inr (hz (hlz ▸ hr))
          | left hy =>
            obtain rfl := eq_node_of_lfBy_eq hxy hlu
            exact .left (has_of_holds_lfBy _ (hlz ▸ hy))
          | right hy =>
            obtain rfl := eq_node_of_lfBy_eq hxy hlz
            exact .right (has_of_holds_lfBy _ (hlu ▸ hy))
        rw [lfBy_pair] at hc
        simp only [List.map_cons, List.map_nil]
        split_ifs at hc with h1 h2 h3 h4
        · exact .inr (hz hc)
        · exact hnode hc
        · exact .inl (hu hc)
        · exact hnode hc
        · exact hnode hc
      · rw [lfBy_of_length_ne _ _ hlen] at hc
        obtain ⟨_, _, _, he⟩ := hc.exists_pair
        simp only [RoseTree.node.injEq] at he
        have := congrArg List.length he.2
        simp at this
        exact absurd this hlen
    cases k with
    | none => exact hn h
    | some l =>
      rw [lfBy_some] at h
      split_ifs at h with hp
      · exact hn h
      · have := h.exists_pair
        simp at this

/-! ### Chains -/

/-- Daughters of a node share a term only where one has a lower copy of the other. -/
private def NodeOK (r : MT) : Prop :=
  ∀ k a u v, r = .node (k, a) [u, v] →
    ((∃ q ∈ v.subtrees, termOf q = termOf u) → (lowerCopy? u v).isSome) ∧
      ((∃ q ∈ u.subtrees, termOf q = termOf v) → (lowerCopy? v u).isSome)

/-- Daughters share a term only at movement nodes. -/
private def Chains (s : MT) : Prop := ∀ r ∈ s.subtrees, NodeOK r

private theorem chains_node {v : CopyMark × Vertex} {cs : List MT} :
    Chains (.node v cs) ↔ NodeOK (.node v cs) ∧ ∀ c ∈ cs, Chains c := by
  simp only [Chains, subtrees_node, List.mem_cons, List.mem_flatMap, forall_eq_or_imp]
  exact and_congr_right fun _ ↦ ⟨fun h c hc r hr ↦ h r ⟨c, hc, hr⟩,
    fun h r ⟨c, hc, hr⟩ ↦ h c hc r hr⟩

/-- A mark names one chain: lower copies with one mark have one term. -/
def MarksName (s : MT) : Prop :=
  ∀ r₁ ∈ s.subtrees, ∀ r₂ ∈ s.subtrees,
    r₁.value.1.isSome → r₁.value.1 = r₂.value.1 → termOf r₁ = termOf r₂

instance : DecidablePred MarksName := fun _ ↦ inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The copy object has no trace vertex. -/
def TraceFree (s : MT) : Prop := ∀ r ∈ (s.map Prod.snd).subtrees, r.value.isLeft

instance : DecidablePred TraceFree := fun _ ↦ inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The two daughters of a binary node have different terms. -/
def DaughtersDiffer : RoseTree Vertex → Prop
  | .node _ [u, v] => UnorderedTree.mk u ≠ UnorderedTree.mk v
  | _ => True

instance : DecidablePred DaughtersDiffer := fun r ↦ by
  obtain ⟨a, cs⟩ := r
  match cs with
  | [u, v] => exact inferInstanceAs (Decidable (UnorderedTree.mk u ≠ UnorderedTree.mk v))
  | [] => exact isTrue trivial
  | [_] => exact isTrue trivial
  | _ :: _ :: _ :: _ => exact isTrue trivial

/-- No node of the copy object has two daughters with one term: nothing moves from itself. -/
def DistinctDaughters (s : MT) : Prop := ∀ r ∈ (s.map Prod.snd).subtrees, DaughtersDiffer r

instance : DecidablePred DistinctDaughters := fun _ ↦ inferInstanceAs (Decidable (∀ _ ∈ _, _))

private theorem child_mem_subtrees {α : Type*} {a : α} {c : RoseTree α} {cs : List (RoseTree α)}
    (hc : c ∈ cs) : c ∈ (RoseTree.node a cs).subtrees := by
  rw [subtrees_node]
  exact .tail _ (List.mem_flatMap.2 ⟨c, hc, self_mem_subtrees c⟩)

private theorem mem_subtrees_trans {α : Type*} {r s t : RoseTree α} (hr : r ∈ s.subtrees)
    (hs : s ∈ t.subtrees) : r ∈ t.subtrees :=
  mem_subtrees.2 ((mem_subtrees.1 hr).trans (mem_subtrees.1 hs))

private theorem map_mem_subtrees {r s : MT} (h : r ∈ s.subtrees) :
    r.map Prod.snd ∈ (s.map Prod.snd).subtrees := by
  rw [subtrees_map]
  exact List.mem_map_of_mem h

/-- Copies contracting alike have one term, marks naming chains. -/
private theorem termOf_eq_of_contract_eq {t : MT} (hMN : MarksName t) (hTF : TraceFree t)
    {r₁ r₂ : MT} (h₁ : r₁ ∈ t.subtrees) (h₂ : r₂ ∈ t.subtrees)
    (h : UnorderedTree.mk (contractTree r₁) = UnorderedTree.mk (contractTree r₂)) :
    termOf r₁ = termOf r₂ := by
  induction r₁ generalizing r₂ with
  | node v cs ih =>
    obtain ⟨k₁, a₁⟩ := v
    obtain ⟨⟨k₂, a₂⟩, ds⟩ := r₂
    have hl₁ : a₁.isLeft := by
      simpa using hTF _ (map_mem_subtrees h₁)
    have hl₂ : a₂.isLeft := by
      simpa using hTF _ (map_mem_subtrees h₂)
    cases k₁ with
    | none =>
      cases k₂ with
      | none =>
        rw [contractTree_none, contractTree_none, UnorderedTree.mk_node_eq_mk_node_iff] at h
        obtain ⟨rfl, hcs⟩ := h
        simp only [termOf, map_node]
        rw [UnorderedTree.mk_node_eq_mk_node_iff]
        refine ⟨rfl, ?_⟩
        rw [List.map_map, List.map_map, ← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.rel_eq,
          Multiset.rel_map] at hcs ⊢
        exact hcs.mono fun c hc d hd hcd ↦ ih c (Multiset.mem_coe.1 hc)
          (mem_subtrees_trans (child_mem_subtrees (Multiset.mem_coe.1 hc)) h₁)
          (mem_subtrees_trans (child_mem_subtrees (Multiset.mem_coe.1 hd)) h₂) hcd
      | some l =>
        rw [contractTree_none, contractTree_some, UnorderedTree.mk_node_eq_mk_node_iff] at h
        rw [h.1] at hl₁
        simp at hl₁
    | some l =>
      cases k₂ with
      | none =>
        rw [contractTree_some, contractTree_none, UnorderedTree.mk_node_eq_mk_node_iff] at h
        rw [← h.1] at hl₂
        simp at hl₂
      | some l' =>
        rw [contractTree_some, contractTree_some, UnorderedTree.mk_node_eq_mk_node_iff] at h
        obtain rfl := Sum.inr.inj h.1
        exact hMN _ h₁ _ h₂ (by simp) rfl

section Mark

variable {m : SyntacticObject} {l : Option LexicalItem.Token}

private theorem termOf_markTree (s : MT) : termOf (markTree m l s) = termOf s :=
  congrArg UnorderedTree.mk (map_snd_markTree m l s)

private theorem has_markTree {s : MT} : Has y (markTree m l s) ↔ Has y s := by
  rw [Has, map_snd_markTree]

private theorem not_hit_of_some (hm : m.val.value.isLeft) (l' : Option LexicalItem.Token)
    (a : Vertex) (cs : List MT) :
    UnorderedTree.mk (contractTree (.node (some l', a) cs)) ≠ m.val := by
  rw [contractTree_some]
  intro h
  have hv := congrArg UnorderedTree.value h
  rw [← hv] at hm
  simp at hm

private theorem exists_mem_markTree (hm : m.val.value.isLeft) {s r : MT} (hr : r ∈ s.subtrees) :
    ∃ r' ∈ (markTree m l s).subtrees, termOf r' = termOf r ∧
      (r.value.1.isSome → r'.value.1 = r.value.1) := by
  induction s with
  | node v cs ih =>
    rw [subtrees_node, List.mem_cons, List.mem_flatMap] at hr
    rw [markTree_node]
    obtain ⟨k, a⟩ := v
    split_ifs with hit
    · cases k with
      | some l' => exact absurd hit (not_hit_of_some hm l' a cs)
      | none =>
        rcases hr with rfl | ⟨c, hc, hrc⟩
        · refine ⟨.node (some l, a) cs, ?_, ?_, by simp⟩
          · simp only [setMark, subtrees_node]
            exact List.mem_cons_self
          · simp only [termOf, map_node]
        · exact ⟨r, by
            simp only [setMark, subtrees_node, List.mem_cons, List.mem_flatMap]
            exact .inr ⟨c, hc, hrc⟩, rfl, fun _ ↦ rfl⟩
    · rcases hr with rfl | ⟨c, hc, hrc⟩
      · refine ⟨.node (k, a) (cs.map (markTree m l)), by simp, ?_, fun _ ↦ rfl⟩
        have := termOf_markTree (m := m) (l := l) (.node (k, a) cs)
        rwa [markTree_node, ite_eq_right hit] at this
      · obtain ⟨r', hr', ht, hk⟩ := ih c hc hrc
        refine ⟨r', ?_, ht, hk⟩
        simp only [subtrees_node, List.mem_cons, List.mem_flatMap, List.mem_map]
        exact .inr ⟨_, ⟨c, hc, rfl⟩, hr'⟩

private theorem exists_mem_of_mem_markTree {s r' : MT} (h : r' ∈ (markTree m l s).subtrees) :
    ∃ r ∈ s.subtrees, termOf r' = termOf r := by
  induction s with
  | node v cs ih =>
    rw [markTree_node] at h
    split_ifs at h with hit
    · obtain ⟨k, a⟩ := v
      simp only [setMark, subtrees_node, List.mem_cons, List.mem_flatMap] at h
      rcases h with rfl | ⟨c, hc, hrc⟩
      · exact ⟨.node (k, a) cs, by simp, rfl⟩
      · exact ⟨r', by
          simp only [subtrees_node, List.mem_cons, List.mem_flatMap]
          exact .inr ⟨c, hc, hrc⟩, rfl⟩
    · simp only [subtrees_node, List.mem_cons, List.mem_flatMap, List.mem_map] at h
      rcases h with rfl | ⟨_, ⟨c, hc, rfl⟩, hrc⟩
      · refine ⟨.node v cs, by simp, ?_⟩
        have := termOf_markTree (m := m) (l := l) (.node v cs)
        rwa [markTree_node, ite_eq_right hit] at this
      · obtain ⟨r, hr, ht⟩ := ih c hc hrc
        refine ⟨r, ?_, ht⟩
        simp only [subtrees_node, List.mem_cons, List.mem_flatMap]
        exact .inr ⟨c, hc, hr⟩

/-- Marking adds a lower copy only of a chain whose term the sister already holds. -/
private theorem isSome_lowerCopy?_markTree (hm : m.val.value.isLeft) {u v : MT}
    (hok : (∃ q ∈ v.subtrees, termOf q = termOf u) → (lowerCopy? u v).isSome) :
    (lowerCopy? (markTree m l u) (markTree m l v)).isSome ↔ (lowerCopy? u v).isSome := by
  rw [isSome_lowerCopy?_iff, termOf_markTree]
  constructor
  · rintro ⟨r', hr', -, ht⟩
    obtain ⟨r, hr, hrt⟩ := exists_mem_of_mem_markTree hr'
    exact hok ⟨r, hr, hrt.symm.trans ht⟩
  · intro h
    obtain ⟨r, hr, hk, ht⟩ := isSome_lowerCopy?_iff.1 h
    obtain ⟨r', hr', hrt, hk'⟩ := exists_mem_markTree (l := l) hm hr
    exact ⟨r', hr', by rw [hk' hk]; exact hk, hrt.trans ht⟩

private theorem chains_markTree (hm : m.val.value.isLeft) {s : MT} (hs : Chains s) :
    Chains (markTree m l s) := by
  induction s with
  | node v cs ih =>
    obtain ⟨hn, hc⟩ := chains_node.1 hs
    obtain ⟨k, a⟩ := v
    rw [markTree_node]
    split_ifs with hit
    · refine chains_node.2 ⟨?_, hc⟩
      rintro k' a' u w he
      simp only [RoseTree.node.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact hn k a u w rfl
    · refine chains_node.2 ⟨?_, fun c hc' ↦ ?_⟩
      · rintro k' a' u' w' he
        simp only [RoseTree.node.injEq, Prod.mk.injEq] at he
        obtain ⟨⟨rfl, rfl⟩, he⟩ := he
        obtain ⟨u, w, rfl⟩ : ∃ u w, cs = [u, w] := by
          have := congrArg List.length he
          simp only [List.length_map, List.length_cons, List.length_nil] at this
          exact List.length_eq_two.1 this
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h1, h2⟩ := hn _ _ u w rfl
        refine ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩
        · refine (isSome_lowerCopy?_markTree hm h1).2 (h1 ?_)
          obtain ⟨q, hq, ht⟩ := hq
          obtain ⟨r, hr, hrt⟩ := exists_mem_of_mem_markTree hq
          exact ⟨r, hr, hrt.symm.trans (ht.trans (termOf_markTree _))⟩
        · refine (isSome_lowerCopy?_markTree hm h2).2 (h2 ?_)
          obtain ⟨q, hq, ht⟩ := hq
          obtain ⟨r, hr, hrt⟩ := exists_mem_of_mem_markTree hq
          exact ⟨r, hr, hrt.symm.trans (ht.trans (termOf_markTree _))⟩
      · obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
        exact ih c' hc'' (hc c' hc'')

/-- If every occurrence marked holds `y`, marking leaves the reading unchanged. -/
private theorem lfBy_markTree_of_has (hm : m.val.value.isLeft) {s : MT} (hs : Chains s)
    (H : ∀ r ∈ s.subtrees, UnorderedTree.mk (contractTree r) = m.val → Has y r) :
    lfBy (Has y) (markTree m l s) = lfBy (Has y) s := by
  induction s with
  | node v cs ih =>
    obtain ⟨hn, hc⟩ := chains_node.1 hs
    obtain ⟨k, a⟩ := v
    have hch : ∀ c ∈ cs, lfBy (Has y) (markTree m l c) = lfBy (Has y) c := fun c hc' ↦
      ih c hc' (hc c hc') fun r hr ↦ H r (by
        simp only [subtrees_node, List.mem_cons, List.mem_flatMap]
        exact .inr ⟨c, hc', hr⟩)
    rw [markTree_node]
    split_ifs with hit
    · cases k with
      | some l' => exact absurd hit (not_hit_of_some hm l' a cs)
      | none =>
        have hp := H _ (by simp) hit
        simp only [setMark]
        rw [lfBy_some, ite_eq_left (show Has y (.node (some l, a) cs) from has_node.2
            (has_node.1 hp))]
    · have hnone : lfBy (Has y) (.node (none, a) (cs.map (markTree m l))) =
          lfBy (Has y) (.node (none, a) cs) := by
        by_cases hlen : cs.length = 2
        · obtain ⟨u, w, rfl⟩ := List.length_eq_two.1 hlen
          obtain ⟨h1, h2⟩ := hn k a u w rfl
          simp only [List.map_cons, List.map_nil]
          rw [lfBy_pair, lfBy_pair, hch u (by simp), hch w (by simp)]
          have e1 := isSome_lowerCopy?_markTree (l := l) hm h1
          have e2 := isSome_lowerCopy?_markTree (l := l) hm h2
          simp only [e1, e2, has_markTree]
        · rw [lfBy_of_length_ne _ _ (by simpa using hlen), lfBy_of_length_ne _ _ hlen, List.map_map]
          exact congrArg _ (List.map_congr_left hch)
      cases k with
      | none => exact hnone
      | some l' =>
        rw [lfBy_some, lfBy_some, hnone]
        have hiff : Has y (.node (some l', a) (cs.map (markTree m l))) ↔
            Has y (.node (some l', a) cs) := by
          rw [has_node, has_node, List.map_map]
          have : cs.map (RoseTree.map Prod.snd ∘ markTree m l) = cs.map (RoseTree.map Prod.snd) :=
            List.map_congr_left fun c _ ↦ map_snd_markTree m l c
          rw [this]
        simp only [hiff]

/-- If no occurrence marked holds `y`, a c-command in the reading survives marking, unless the
commander is what was marked. -/
private theorem cc_lfBy_markTree (hm : m.val.value.isLeft) (hxy : x ≠ y) {s : MT} (hs : Chains s)
    (H : ∀ r ∈ s.subtrees, UnorderedTree.mk (contractTree r) = m.val → ¬ Has y r)
    (h : CC x y (lfBy (Has y) s)) :
    CC x y (lfBy (Has y) (markTree m l s)) ∨ m.val =
      UnorderedTree.mk (.node (Sum.inl (some x)) []) := by
  induction s with
  | node v cs ih =>
    obtain ⟨hn, hc⟩ := chains_node.1 hs
    obtain ⟨k, a⟩ := v
    rw [markTree_node]
    split_ifs with hit
    · exact absurd (has_of_holds_lfBy _ h.holds) (H _ (by simp) hit)
    · have hch : ∀ c ∈ cs, CC x y (lfBy (Has y) c) →
          CC x y (lfBy (Has y) (markTree m l c)) ∨
            m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) := fun c hc' hcc ↦
        ih c hc' (hc c hc') (fun r hr ↦ H r (by
          simp only [subtrees_node, List.mem_cons, List.mem_flatMap]
          exact .inr ⟨c, hc', hr⟩)) hcc
      have hholds : ∀ {c : MT}, Holds y (lfBy (Has y) c) →
          Holds y (lfBy (Has y) (markTree m l c)) := fun hy ↦
        holds_lfBy (has_markTree.2 (has_of_holds_lfBy _ hy))
      have hleaf : ∀ {c : MT}, lfBy (Has y) c = .node (.inl (some x)) [] →
          lfBy (Has y) (markTree m l c) = .node (.inl (some x)) [] ∨
            m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) := by
        intro c hc'
        obtain rfl := eq_node_of_lfBy_eq hxy hc'
        rw [markTree_node]
        split_ifs with hit'
        · rw [contractTree_none] at hit'
          exact .inr (by simpa using hit'.symm)
        · exact .inl (by simp)
      have hcore : CC x y (lfBy (Has y) (.node (none, a) cs)) →
          CC x y (lfBy (Has y) (.node (none, a) (cs.map (markTree m l)))) ∨
            m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) := by
        intro hcc
        by_cases hlen : cs.length = 2
        · obtain ⟨u, w, rfl⟩ := List.length_eq_two.1 hlen
          obtain ⟨h1, h2⟩ := hn k a u w rfl
          have e1 := isSome_lowerCopy?_markTree (l := l) hm h1
          have e2 := isSome_lowerCopy?_markTree (l := l) hm h2
          have hu := hch u (by simp)
          have hw := hch w (by simp)
          have hnode : CC x y (.node a [lfBy (Has y) u, lfBy (Has y) w]) →
              CC x y (.node a [lfBy (Has y) (markTree m l u), lfBy (Has y) (markTree m l w)]) ∨
                m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) := by
            intro hc'
            generalize hlu : lfBy (Has y) u = lu at hc'
            generalize hlw : lfBy (Has y) w = lw at hc'
            cases hc' with
            | inl hl => exact (hu (hlu ▸ hl)).imp .inl id
            | inr hr => exact (hw (hlw ▸ hr)).imp .inr id
            | left hy =>
              rcases hleaf hlu with he | he
              · exact .inl (he ▸ .left (hholds (hlw ▸ hy)))
              · exact .inr he
            | right hy =>
              rcases hleaf hlw with he | he
              · exact .inl (he ▸ .right (hholds (hlu ▸ hy)))
              · exact .inr he
          simp only [List.map_cons, List.map_nil]
          rw [lfBy_pair] at hcc ⊢
          simp only [e1, e2, has_markTree]
          split_ifs at hcc ⊢ with c1 c2 c3 c4
          · exact hw (by simpa using hcc)
          · exact hnode hcc
          · exact hu (by simpa using hcc)
          · exact hnode hcc
          · exact hnode hcc
        · rw [lfBy_of_length_ne _ _ hlen] at hcc
          obtain ⟨_, _, _, he⟩ := hcc.exists_pair
          simp only [RoseTree.node.injEq] at he
          have := congrArg List.length he.2
          simp at this
          exact absurd this hlen
      cases k with
      | none => exact hcore h
      | some l' =>
        have hiff : Has y (.node (some l', a) (cs.map (markTree m l))) ↔
            Has y (.node (some l', a) cs) := by
          rw [has_node, has_node, List.map_map]
          have : cs.map (RoseTree.map Prod.snd ∘ markTree m l) = cs.map (RoseTree.map Prod.snd) :=
            List.map_congr_left fun c _ ↦ map_snd_markTree m l c
          rw [this]
        rw [lfBy_some] at h ⊢
        simp only [hiff]
        split_ifs at h ⊢ with hp
        · exact hcore h
        · have := h.exists_pair
          simp at this

/-- A copy of a chain every occurrence of which has the term `τ` is marked. -/
private theorem exists_marked_of_hit {s r₀ : MT} {τ : UnorderedTree Vertex}
    (hu : ∀ r ∈ s.subtrees, UnorderedTree.mk (contractTree r) = m.val → termOf r = τ)
    (h₀ : r₀ ∈ s.subtrees) (hit : UnorderedTree.mk (contractTree r₀) = m.val) :
    ∃ r' ∈ (markTree m l s).subtrees, r'.value.1.isSome ∧ termOf r' = τ := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    rw [markTree_node]
    split_ifs with hroot
    · refine ⟨.node (some l, a) cs, ?_, by simp, ?_⟩
      · simp only [setMark, subtrees_node]
        exact List.mem_cons_self
      · have := hu _ (by simp) hroot
        rw [← this]
        simp only [termOf, map_node]
    · rw [subtrees_node, List.mem_cons, List.mem_flatMap] at h₀
      rcases h₀ with rfl | ⟨c, hc, hrc⟩
      · exact absurd hit hroot
      · obtain ⟨r', hr', hk, ht⟩ := ih c hc (fun r hr ↦ hu r (by
          simp only [subtrees_node, List.mem_cons, List.mem_flatMap]
          exact .inr ⟨c, hc, hr⟩)) hrc
        refine ⟨r', ?_, hk, ht⟩
        simp only [subtrees_node, List.mem_cons, List.mem_flatMap, List.mem_map]
        exact .inr ⟨_, ⟨c, hc, rfl⟩, hr'⟩

private theorem marksName_of_markTree (hm : m.val.value.isLeft) {s : MT}
    (h : MarksName (markTree m l s)) : MarksName s := by
  intro r₁ h₁ r₂ h₂ hk he
  obtain ⟨r₁', hr₁, ht₁, hk₁⟩ := exists_mem_markTree (l := l) hm h₁
  have hk₂ : r₂.value.1.isSome := he ▸ hk
  obtain ⟨r₂', hr₂, ht₂, hk₂'⟩ := exists_mem_markTree (l := l) hm h₂
  rw [← ht₁, ← ht₂]
  exact h _ hr₁ _ hr₂ (by rw [hk₁ hk]; exact hk) (by rw [hk₁ hk, hk₂' hk₂, he])

end Mark

/-! ### The steps of a derivation -/

private theorem CC.swap {a : Vertex} {l r : RoseTree Vertex} (h : CC x y (.node a [l, r])) :
    CC x y (.node a [r, l]) := by
  generalize he : RoseTree.node a [l, r] = p at h
  cases h with
  | inl hl =>
    simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .inr hl
  | inr hr =>
    simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .inl hr
  | left hy =>
    simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .right hy
  | right hy =>
    simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact .left hy

private theorem holds_iff_mem_yield {w : LexicalItem.Token} (p : LinearizedSyntacticObject) :
    Holds w p.val ↔ w ∈ p.toSyntacticObject.yield :=
  (coe_mem_terms_iff p).symm.trans mem_yield_iff.symm

/-- A trace-free object holds a token. -/
private theorem exists_holds {p : RoseTree Vertex} (h : IsSyntacticObject (UnorderedTree.mk p))
    (hTF : ∀ r ∈ p.subtrees, r.value.isLeft) : ∃ w, Holds w p := by
  induction p with
  | node a cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · rw [List.length_eq_zero_iff] at hlen
      subst hlen
      have ha := hTF _ (self_mem_subtrees _)
      simp only [value] at ha
      rcases a with (_ | w) | l
      · exact absurd h (by simp [licensed_node_iff, Vertex.Licenses])
      · exact ⟨w, by simp⟩
      · simp at ha
    · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
      have hl := (licensed_node_iff.1 ((isSyntacticObject_mk _).1 h)).2
      obtain ⟨w, hw⟩ := ih u (by simp) (hl u (by simp)) fun r hr ↦ hTF r
        (mem_subtrees_trans hr (child_mem_subtrees (by simp)))
      exact ⟨w, holds_node_of_mem (by simp) hw⟩

/-- An object with no marks, whose tokens are distinct, has no movement nodes and needs none. -/
private theorem chains_map_none {p : RoseTree Vertex} (h : IsSyntacticObject (UnorderedTree.mk p))
    (hTF : ∀ r ∈ p.subtrees, r.value.isLeft)
    (hd : (LinearizedSyntacticObject.toSyntacticObject ⟨p, h⟩).yield.Nodup) :
    Chains (p.map ((none, ·) : Vertex → CopyMark × Vertex)) := by
  induction p with
  | node a cs ih =>
    rw [map_node]
    rcases length_eq_zero_or_two h with hlen | hlen
    · rw [List.length_eq_zero_iff] at hlen
      subst hlen
      refine chains_node.2 ⟨?_, by simp⟩
      rintro k b u v he
      simp at he
    · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hu, hv⟩ := (isSyntacticObject_mk_merge _ _).1 h
      have hsum : (LinearizedSyntacticObject.toSyntacticObject ⟨u, hu⟩).yield +
          (LinearizedSyntacticObject.toSyntacticObject ⟨v, hv⟩).yield =
          (LinearizedSyntacticObject.toSyntacticObject ⟨.node Vertex.bare [u, v], h⟩).yield := by
        rw [show (LinearizedSyntacticObject.toSyntacticObject ⟨.node Vertex.bare [u, v], h⟩) =
          SyntacticObject.merge (LinearizedSyntacticObject.toSyntacticObject ⟨u, hu⟩)
            (LinearizedSyntacticObject.toSyntacticObject ⟨v, hv⟩) from
          LinearizedSyntacticObject.toSyntacticObject_merge ⟨u, hu⟩ ⟨v, hv⟩, yield_merge]
      rw [← hsum, Multiset.nodup_add] at hd
      obtain ⟨hdu, hdv, hdis⟩ := hd
      have htu : ∀ r ∈ u.subtrees, r.value.isLeft := fun r hr ↦ hTF r
        (mem_subtrees_trans hr (child_mem_subtrees (by simp)))
      have htv : ∀ r ∈ v.subtrees, r.value.isLeft := fun r hr ↦ hTF r
        (mem_subtrees_trans hr (child_mem_subtrees (by simp)))
      have hno : ∀ w, Holds w u → Holds w v → False := fun w h₁ h₂ ↦
        Multiset.disjoint_left.1 hdis ((holds_iff_mem_yield ⟨u, hu⟩).1 h₁)
          ((holds_iff_mem_yield ⟨v, hv⟩).1 h₂)
      refine chains_node.2 ⟨?_, ?_⟩
      · rintro k b u' v' he
        simp only [List.map_cons, List.map_nil, RoseTree.node.injEq, List.cons.injEq, and_true,
          Prod.mk.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        refine ⟨fun ⟨q, hq, ht⟩ ↦ ?_, fun ⟨q, hq, ht⟩ ↦ ?_⟩
        · obtain ⟨w, hw⟩ := exists_holds hu htu
          have hq' : Has w q := (holds_congr ht).2 (by simpa [map_snd_map] using hw)
          exact (hno w hw (by
            simpa [map_snd_map] using holds_of_mem_subtrees (map_mem_subtrees hq) hq')).elim
        · obtain ⟨w, hw⟩ := exists_holds hv htv
          have hq' : Has w q := (holds_congr ht).2 (by simpa [map_snd_map] using hw)
          exact (hno w (by
            simpa [map_snd_map] using holds_of_mem_subtrees (map_mem_subtrees hq) hq') hw).elim
      · intro c hc
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        rcases List.mem_pair.1 hc' with rfl | rfl
        · exact ih _ (by simp) hu htu hdu
        · exact ih _ (by simp) hv htv hdv

/-- External Merge of an item that shares no token with the object. -/
private theorem step_em {t : Marked} {item : LinearizedSyntacticObject} (e : Edge)
    (hroot : t.val.value.1 = none) (hdis : ∀ w, Has w t.val → ¬ Holds w item.val)
    (hTFi : ∀ r ∈ item.val.subtrees, r.value.isLeft) (hdi : item.toSyntacticObject.yield.Nodup)
    (hTFt : TraceFree t.val) (hCh : Chains t.val)
    (hIH : ∀ x y, x ≠ y → CC x y (t.val.map Prod.snd) → CC x y (lfBy (Has y) t.val)) :
    Chains (t.attach e (ofLinearized item)).val ∧ ∀ x y, x ≠ y →
      CC x y ((t.attach e (ofLinearized item)).val.map Prod.snd) →
      CC x y (lfBy (Has y) (t.attach e (ofLinearized item)).val) := by
  obtain ⟨p, hp⟩ := item
  let d : MT := p.map ((none, ·) : Vertex → CopyMark × Vertex)
  have hdm : d.map Prod.snd = p := map_snd_map p
  obtain ⟨w₀, hw₀⟩ := exists_holds hp hTFi
  obtain ⟨w₁, hw₁⟩ := exists_holds t.2 hTFt
  have hno₁ : ¬ ∃ q ∈ t.val.subtrees, termOf q = termOf d := fun ⟨q, hq, ht⟩ ↦
    hdis w₀ (holds_of_mem_subtrees (map_mem_subtrees hq)
      ((holds_congr ht).2 (by rw [hdm]; exact hw₀))) hw₀
  have hno₂ : ¬ ∃ q ∈ d.subtrees, termOf q = termOf t.val := fun ⟨q, hq, ht⟩ ↦
    hdis w₁ hw₁ (by
      have := holds_of_mem_subtrees (map_mem_subtrees hq) ((holds_congr ht).2 hw₁)
      rwa [hdm] at this)
  have hdet₁ : ¬ (lowerCopy? d t.val).isSome := fun h ↦ by
    obtain ⟨r, hr, -, ht⟩ := isSome_lowerCopy?_iff.1 h
    exact hno₁ ⟨r, hr, ht⟩
  have hdet₂ : ¬ (lowerCopy? t.val d).isSome := by
    rw [lowerCopy?_map_none]; simp
  have hcd : Chains d := chains_map_none hp hTFi hdi
  have core : ∀ x y, x ≠ y → CC x y (.node Vertex.bare [p, t.val.map Prod.snd]) →
      CC x y (.node Vertex.bare [p, lfBy (Has y) t.val]) := by
    intro x y hxy hc
    generalize hq : t.val.map Prod.snd = q at hc
    cases hc with
    | inl hl => exact .inl hl
    | inr hr => exact .inr (hIH x y hxy (by rw [hq]; exact hr))
    | left hy => exact .left (holds_lfBy (by rw [Has, hq]; exact hy))
    | right hy =>
      rcases ht : t.val with ⟨⟨k, a⟩, cs⟩
      rw [ht, map_node] at hq
      simp only [RoseTree.node.injEq, List.map_eq_nil_iff] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [ht] at hroot
      obtain rfl : k = none := hroot
      rw [lfBy_leaf]
      exact .right hy
  cases e with
  | left =>
    have hval : (t.attach .left (ofLinearized ⟨p, hp⟩)).val =
        .node (none, Vertex.bare) [d, t.val] := rfl
    rw [hval]
    refine ⟨chains_node.2 ⟨?_, ?_⟩, fun x y hxy hc ↦ ?_⟩
    · rintro k a u v he
      simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl⟩ := he
      exact ⟨fun h ↦ absurd h hno₁, fun h ↦ absurd h hno₂⟩
    · intro c hc
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact hcd
      · exact hCh
    · rw [map_node] at hc
      simp only [List.map_cons, List.map_nil, hdm] at hc
      rw [lfBy_pair, ite_eq_right hdet₁, ite_eq_right hdet₂, lfBy_map_none]
      exact core x y hxy hc
  | right =>
    have hval : (t.attach .right (ofLinearized ⟨p, hp⟩)).val =
        .node (none, Vertex.bare) [t.val, d] := rfl
    rw [hval]
    refine ⟨chains_node.2 ⟨?_, ?_⟩, fun x y hxy hc ↦ ?_⟩
    · rintro k a u v he
      simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl⟩ := he
      exact ⟨fun h ↦ absurd h hno₂, fun h ↦ absurd h hno₁⟩
    · intro c hc
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact hCh
      · exact hcd
    · rw [map_node] at hc
      simp only [List.map_cons, List.map_nil, hdm] at hc
      rw [lfBy_pair, ite_eq_right hdet₂, ite_eq_right hdet₁, lfBy_map_none]
      exact (core x y hxy hc.swap).swap

/-- Internal Merge of a phrase found in the object, other than the object itself. -/
private theorem step_im {t s₀ : Marked} {m : SyntacticObject} {l : Option LexicalItem.Token}
    (e : Edge) (hfind : t.find? m = some s₀) (hm : m.val.value.isLeft) (hMN : MarksName t.val)
    (hTF : TraceFree t.val) (hne : termOf s₀.val ≠ termOf t.val) (hCh : Chains t.val)
    (hIH : ∀ x y, x ≠ y → CC x y (t.val.map Prod.snd) → CC x y (lfBy (Has y) t.val)) :
    Chains ((t.mark m l).attach e s₀).val ∧ ∀ x y, x ≠ y →
      CC x y (((t.mark m l).attach e s₀).val.map Prod.snd) →
      CC x y (lfBy (Has y) ((t.mark m l).attach e s₀).val) := by
  have hr₀ : s₀.val ∈ t.val.subtrees := by
    obtain ⟨r, hr, -, rfl⟩ := Option.pmap_eq_some_iff.1 hfind
    exact mem_subtrees.2 (isSubtree_of_mem_subtreesUntil hr)
  have hit₀ := mk_contractTree_of_find? hfind
  rcases hs : s₀.val with ⟨⟨k₀, a₀⟩, cs₀⟩
  rw [hs] at hr₀ hit₀ hne
  let r₀ : MT := .node (k₀, a₀) cs₀
  obtain rfl : k₀ = none := by
    cases k₀ with
    | none => rfl
    | some l' => exact absurd hit₀ (not_hit_of_some hm l' a₀ cs₀)
  have hτ : ∀ r ∈ t.val.subtrees, UnorderedTree.mk (contractTree r) = m.val →
      termOf r = termOf r₀ := fun r hr h ↦
    termOf_eq_of_contract_eq hMN hTF hr hr₀ (h.trans hit₀.symm)
  have hdet : (lowerCopy? r₀ (markTree m l t.val)).isSome := by
    obtain ⟨r', hr', hk, ht⟩ := exists_marked_of_hit (l := l) hτ hr₀ hit₀
    exact isSome_lowerCopy?_iff.2 ⟨r', hr', hk, ht⟩
  have hsize : ∀ q ∈ r₀.subtrees, termOf q ≠ termOf t.val := by
    intro q hq ht
    have hn : q.numNodes = t.val.numNodes := by
      have := congrArg UnorderedTree.numNodes ht
      simpa [termOf] using this
    have h₁ := (mem_subtrees.1 hq).numNodes_le
    exact hne (congrArg termOf ((mem_subtrees.1 hr₀).eq_of_numNodes_le (hn ▸ h₁)))
  have hndet : ¬ (lowerCopy? (markTree m l t.val) r₀).isSome := fun h ↦ by
    obtain ⟨q, hq, -, ht⟩ := isSome_lowerCopy?_iff.1 h
    exact hsize q hq (ht.trans (termOf_markTree _))
  have hcr : Chains r₀ := fun r hr ↦ hCh r (mem_subtrees_trans hr hr₀)
  have hcm : Chains (markTree m l t.val) := chains_markTree hm hCh
  have core : ∀ x y, x ≠ y → CC x y (.node Vertex.bare [r₀.map Prod.snd, t.val.map Prod.snd]) →
      (if Has y r₀ then CC x y (lfBy (Has y) t.val) else
        CC x y (.node Vertex.bare [lfBy (Has y) r₀, lfBy (Has y) (markTree m l t.val)])) := by
    intro x y hxy hc
    have hCCt : CC x y (r₀.map Prod.snd) ∨ CC x y (t.val.map Prod.snd) ∨
        (r₀.map Prod.snd = .node (.inl (some x)) [] ∧ Holds y (t.val.map Prod.snd)) := by
      generalize hq : r₀.map Prod.snd = q at hc ⊢
      generalize hq' : t.val.map Prod.snd = q' at hc ⊢
      cases hc with
      | inl hl => exact .inl hl
      | inr hr => exact .inr (.inl hr)
      | left hy => exact .inr (.inr ⟨rfl, hy⟩)
      | right hy =>
        exfalso
        have hmem : r₀.map Prod.snd ∈ (t.val.map Prod.snd).subtrees := map_mem_subtrees hr₀
        rw [hq', hq, subtrees_node] at hmem
        simp only [List.flatMap_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rw [hmem] at hy
        exact hxy (Option.some.inj (Sum.inl.inj ((holds_leaf _).1 hy)))
    have hsub : ∀ {hc' : CC x y (r₀.map Prod.snd)}, CC x y (t.val.map Prod.snd) := by
      intro hc'
      exact hc'.of_mem_subtrees (map_mem_subtrees hr₀) t.2
    have hHas : ∀ r ∈ t.val.subtrees, UnorderedTree.mk (contractTree r) = m.val →
        (Has y r ↔ Has y r₀) := fun r hr h ↦ holds_congr (hτ r hr h)
    split_ifs with hp
    · have hc' : CC x y (t.val.map Prod.snd) := by
        rcases hCCt with h | h | ⟨hq, -⟩
        · exact @hsub h
        · exact h
        · exfalso
          rw [Has, hq] at hp
          exact hxy (Option.some.inj (Sum.inl.inj ((holds_leaf _).1 hp)))
      exact hIH x y hxy hc'
    · have hleaf : m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) →
          lfBy (Has y) r₀ = .node (.inl (some x)) [] := by
        intro hv
        rw [hv, contractTree_none, UnorderedTree.mk_node_eq_mk_node_iff] at hit₀
        obtain ⟨rfl, hd⟩ := hit₀
        rcases cs₀ with _ | ⟨c, cs⟩
        · exact lfBy_leaf _ _
        · have := congrArg Multiset.card hd
          simp at this
      have hnew : ∀ {h' : CC x y (t.val.map Prod.snd)},
          CC x y (.node Vertex.bare [lfBy (Has y) r₀, lfBy (Has y) (markTree m l t.val)]) := by
        intro h'
        have hL := hIH x y hxy h'
        rcases cc_lfBy_markTree (l := l) hm hxy hCh (fun r hr h ↦ (hHas r hr h).not.2 hp) hL with
          h'' | hv
        · exact .inr h''
        · rw [hleaf hv]
          exact .left (holds_lfBy (has_markTree.2 (has_of_holds_lfBy _ hL.holds)))
      rcases hCCt with h | h | ⟨hq, hy⟩
      · exact @hnew (@hsub h)
      · exact @hnew h
      · have hr₀leaf : r₀ = .node (none, .inl (some x)) [] := by
          simp only [r₀, map_node, RoseTree.node.injEq, List.map_eq_nil_iff] at hq ⊢
          exact ⟨by rw [hq.1], hq.2⟩
        rw [hr₀leaf, lfBy_leaf]
        exact .left (holds_lfBy (has_markTree.2 hy))
  have hHas' : ∀ y, Has y r₀ → ∀ r ∈ t.val.subtrees,
      UnorderedTree.mk (contractTree r) = m.val → Has y r := fun y hy r hr h ↦
    (holds_congr (hτ r hr h)).2 hy
  have hmr : (r₀.map Prod.snd) = s₀.val.map Prod.snd := by rw [hs]
  cases e with
  | left =>
    have hval : ((t.mark m l).attach .left s₀).val =
        .node (none, Vertex.bare) [s₀.val, markTree m l t.val] := rfl
    rw [hval, hs]
    refine ⟨chains_node.2 ⟨?_, ?_⟩, fun x y hxy hc ↦ ?_⟩
    · rintro k a u v he
      simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl⟩ := he
      refine ⟨fun _ ↦ hdet, fun ⟨q, hq, ht⟩ ↦ ?_⟩
      exact absurd (ht.trans (termOf_markTree _)) (hsize q hq)
    · intro c hc
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact hcr
      · exact hcm
    · have hc' : CC x y (.node Vertex.bare [r₀.map Prod.snd, t.val.map Prod.snd]) := by
        rw [map_node] at hc
        simp only [List.map_cons, List.map_nil, map_snd_markTree] at hc
        exact hc
      have hco := core x y hxy hc'
      rw [lfBy_pair, ite_eq_left hdet]
      split_ifs at hco ⊢ with hp
      · rw [lfBy_markTree_of_has hm hCh (hHas' y hp)]
        exact hco
      · exact hco
  | right =>
    have hval : ((t.mark m l).attach .right s₀).val =
        .node (none, Vertex.bare) [markTree m l t.val, s₀.val] := rfl
    rw [hval, hs]
    refine ⟨chains_node.2 ⟨?_, ?_⟩, fun x y hxy hc ↦ ?_⟩
    · rintro k a u v he
      simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl⟩ := he
      refine ⟨fun ⟨q, hq, ht⟩ ↦ ?_, fun _ ↦ hdet⟩
      exact absurd (ht.trans (termOf_markTree _)) (hsize q hq)
    · intro c hc
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact hcm
      · exact hcr
    · have hc' : CC x y (.node Vertex.bare [t.val.map Prod.snd, r₀.map Prod.snd]) := by
        rw [map_node] at hc
        simp only [List.map_cons, List.map_nil, map_snd_markTree] at hc
        exact hc
      have hco := core x y hxy hc'.swap
      rw [lfBy_pair, ite_eq_right hndet, ite_eq_left hdet]
      split_ifs at hco ⊢ with hp
      · rw [lfBy_markTree_of_has hm hCh (hHas' y hp)]
        exact hco
      · exact hco.swap

private theorem marksName_of_mem {v : CopyMark × Vertex} {cs : List MT} {c : MT} (hc : c ∈ cs)
    (h : MarksName (.node v cs)) : MarksName c := fun r₁ h₁ r₂ h₂ ↦
  h r₁ (mem_subtrees_trans h₁ (child_mem_subtrees hc)) r₂
    (mem_subtrees_trans h₂ (child_mem_subtrees hc))

private theorem traceFree_of_mem {v : CopyMark × Vertex} {cs : List MT} {c : MT} (hc : c ∈ cs)
    (h : TraceFree (.node v cs)) : TraceFree c := fun r hr ↦
  h r (mem_subtrees_trans hr (by
    rw [map_node]
    exact child_mem_subtrees (List.mem_map_of_mem hc)))

private theorem distinct_of_mem {v : CopyMark × Vertex} {cs : List MT} {c : MT} (hc : c ∈ cs)
    (h : DistinctDaughters (.node v cs)) : DistinctDaughters c := fun r hr ↦
  h r (mem_subtrees_trans hr (by
    rw [map_node]
    exact child_mem_subtrees (List.mem_map_of_mem hc)))

/-- Only a reading's tests of a copy with a marked copy matter. -/
private theorem lfBy_congr {P Q : MT → Prop} [DecidablePred P] [DecidablePred Q] {T : MT}
    (h : ∀ r ∈ T.subtrees, (r.value.1.isSome ∨ ∃ q ∈ T.subtrees, q.value.1.isSome ∧ termOf q = termOf r) → (P r ↔ Q r))
    {s : MT} (hs : s ∈ T.subtrees) : lfBy P s = lfBy Q s := by
  induction s with
  | node v cs ih =>
    obtain ⟨k, a⟩ := v
    have hch : ∀ c ∈ cs, lfBy P c = lfBy Q c := fun c hc ↦
      ih c hc (mem_subtrees_trans (child_mem_subtrees hc) hs)
    have hn : lfBy P (.node (none, a) cs) = lfBy Q (.node (none, a) cs) := by
      by_cases hlen : cs.length = 2
      · obtain ⟨u, w, rfl⟩ := List.length_eq_two.1 hlen
        have hu : u ∈ T.subtrees := mem_subtrees_trans (child_mem_subtrees (by simp)) hs
        have hw : w ∈ T.subtrees := mem_subtrees_trans (child_mem_subtrees (by simp)) hs
        rw [lfBy_pair, lfBy_pair, hch u (by simp), hch w (by simp)]
        by_cases h₁ : (lowerCopy? u w).isSome
        · have hiff : P u ↔ Q u := by
            obtain ⟨q, hq, hk, ht⟩ := isSome_lowerCopy?_iff.1 h₁
            exact h u hu (.inr ⟨q, mem_subtrees_trans hq hw, hk, ht⟩)
          rw [ite_eq_left h₁, ite_eq_left h₁]
          simp only [hiff]
        · by_cases h₂ : (lowerCopy? w u).isSome
          · have hiff : P w ↔ Q w := by
              obtain ⟨q, hq, hk, ht⟩ := isSome_lowerCopy?_iff.1 h₂
              exact h w hw (.inr ⟨q, mem_subtrees_trans hq hu, hk, ht⟩)
            rw [ite_eq_right h₁, ite_eq_right h₁, ite_eq_left h₂, ite_eq_left h₂]
            simp only [hiff]
          · rw [ite_eq_right h₁, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₂]
      · rw [lfBy_of_length_ne _ _ hlen, lfBy_of_length_ne _ _ hlen]
        exact congrArg _ (List.map_congr_left hch)
    cases k with
    | none => exact hn
    | some l =>
      have hiff : P (.node (some l, a) cs) ↔ Q (.node (some l, a) cs) := h _ hs (.inl (by simp))
      rw [lfBy_some, lfBy_some, hn]
      simp only [hiff]

/-- On a copy with a marked copy, the reading `carrying y` is the test that the copy holds `y`. -/
private theorem readLow_carrying_iff (t : Marked) {r : MT}
    (hrel : r.value.1.isSome ∧ r ∈ t.val.subtrees ∨ ∃ q ∈ t.val.subtrees, q.value.1.isSome ∧ termOf q = termOf r) :
    ReadLow (t.carrying y) r ↔ Has y r := by
  obtain ⟨q₀, hq₀, hk₀, ht₀⟩ : ∃ q ∈ t.val.subtrees, q.value.1.isSome ∧ termOf q = termOf r := by
    rcases hrel with ⟨hk, hr⟩ | h
    · exact ⟨r, hr, hk, rfl⟩
    · exact h
  have hso : ∀ q ∈ t.val.subtrees, IsSyntacticObject (termOf q) := fun q hq ↦
    (isSyntacticObject_mk _).2
      (((isSyntacticObject_mk _).1 t.2).of_isSubtree ((mem_subtrees.1 hq).map _))
  constructor
  · rintro ⟨m, hm, he⟩
    simp only [carrying, List.mem_toFinset, List.mem_filterMap, List.mem_filter] at hm
    obtain ⟨q, ⟨hq, hd⟩, hdite⟩ := hm
    rw [dite_eq_left (hso q hq)] at hdite
    obtain rfl := Option.some.inj hdite
    exact (holds_congr he).1 (of_decide_eq_true hd).2
  · intro hy
    refine ⟨⟨termOf q₀, hso q₀ hq₀⟩, ?_, ht₀⟩
    simp only [carrying, List.mem_toFinset, List.mem_filterMap, List.mem_filter]
    refine ⟨q₀, ⟨hq₀, decide_eq_true ⟨hk₀, (holds_congr ht₀).2 hy⟩⟩, ?_⟩
    rw [dite_eq_left (hso q₀ hq₀)]

private theorem val_mem_subtrees_of_find? {t s : Marked} {m : SyntacticObject}
    (h : t.find? m = some s) : s.val ∈ t.val.subtrees := by
  obtain ⟨r, hr, -, rfl⟩ := Option.pmap_eq_some_iff.1 h
  exact mem_subtrees.2 (isSubtree_of_mem_subtreesUntil hr)

private theorem attach_val (t d : Marked) (e : Edge) :
    ∃ cs, (t.attach e d).val = .node (none, Vertex.bare) cs ∧ t.val ∈ cs ∧ d.val ∈ cs ∧ ∀ w,
      Has w (t.attach e d).val ↔ Has w t.val ∨ Has w d.val := by
  cases e with
  | left =>
    exact ⟨[d.val, t.val], rfl, by simp, by simp, fun w ↦ by
      rw [show (t.attach .left d).val = .node (none, Vertex.bare) [d.val, t.val] from rfl, has_pair,
        or_comm]⟩
  | right =>
    exact ⟨[t.val, d.val], rfl, by simp, by simp, fun w ↦ by
      rw [show (t.attach .right d).val = .node (none, Vertex.bare) [t.val, d.val] from rfl,
        has_pair]⟩

private theorem lfBy_readLow_carrying (t : Marked) :
    lfBy (ReadLow (t.carrying y)) t.val = lfBy (Has y) t.val :=
  lfBy_congr (T := t.val) (fun r hr hrel ↦ readLow_carrying_iff t (by
    rcases hrel with hk | h
    · exact .inl ⟨hk, hr⟩
    · exact .inr h)) (self_mem_subtrees _)

end Minimalist.LinearizedSyntacticObject.Marked

namespace Minimalist.Derivation

open RoseTree SyntacticObject
open LinearizedSyntacticObject (Marked)
open LinearizedSyntacticObject.Marked

variable {x y : LexicalItem.Token}

/-- What the steps of a derivation preserve, given what its final object satisfies. -/
private theorem replayWithCopies?_invariants {d : Derivation} (hd : d.lexTokens.Nodup)
    (hm : ∀ step ∈ d.steps, step.IsMerge)
    (hmv : ∀ step ∈ d.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) {c : Cfg Marked}
    (hc : d.replayWithCopies? = some c) (hMN : MarksName c.current.val)
    (hTF : TraceFree c.current.val) (hDD : DistinctDaughters c.current.val) :
    c.current.val.value.1 = none ∧ Chains c.current.val ∧
      (∀ w, Has w c.current.val → w ∈ d.lexTokens) ∧ ∀ x y, x ≠ y →
      CC x y (c.current.val.map Prod.snd) → CC x y (lfBy (Has y) c.current.val) := by
  obtain ⟨init, steps⟩ := d
  induction steps using List.reverseRecOn generalizing c with
  | nil =>
    simp only [replayWithCopies?, List.foldlM_nil] at hc
    obtain ⟨p, hp, hpc⟩ := Option.bind_eq_some_iff.1 hc
    obtain rfl := Option.some.inj hpc
    have hinit := SyntacticObject.toSyntacticObject_of_toLinearizedLeaf? hp
    have hm₀ : (Marked.ofLinearized p).val.map Prod.snd = p.val := map_snd_map p.val
    have hTFp : ∀ r ∈ p.val.subtrees, r.value.isLeft := fun r hr ↦
      hTF r (by rw [show (Cfg.current ⟨Marked.ofLinearized p, []⟩).val.map Prod.snd
          = p.val from hm₀]; exact hr)
    refine ⟨?_, chains_map_none p.2 hTFp ?_, fun w hw ↦ ?_, fun x y _ hcc ↦ ?_⟩
    · change (p.val.map ((none, ·) : Vertex → CopyMark × Vertex)).value.1 = none
      rcases p.val with ⟨a, cs⟩
      simp [map_node]
    · have : (LinearizedSyntacticObject.toSyntacticObject ⟨p.val, p.2⟩) = init := hinit
      rw [this]
      simpa [lexTokens, items] using hd
    · have hw' : Holds w p.val := by
        have : Has w (Marked.ofLinearized p).val := hw
        rwa [Has, hm₀] at this
      have := (holds_iff_mem_yield p).1 hw'
      rw [hinit] at this
      simpa [lexTokens, items] using this
    · have hcc' : CC x y p.val := by
        have : CC x y ((Marked.ofLinearized p).val.map Prod.snd) := hcc
        rwa [hm₀] at this
      change CC x y (lfBy (Has y) (p.val.map ((none, ·) : Vertex → CopyMark × Vertex)))
      rwa [lfBy_map_none]
  | append_singleton ss st ih =>
    have happ : (⟨init, ss ++ [st]⟩ : Derivation) = (⟨init, ss⟩ : Derivation).append [st] := rfl
    rw [happ] at hc hd ⊢
    rw [replayWithCopies?_append_singleton] at hc
    obtain ⟨c₀, hc₀, hstep⟩ := Option.bind_eq_some_iff.1 hc
    rw [lexTokens_append] at hd ⊢
    obtain ⟨hd₀, hdi, hdis⟩ := Multiset.nodup_add.1 hd
    have hm₀ : ∀ step ∈ ss, step.IsMerge := fun s hs ↦ hm s (List.mem_append_left _ hs)
    have hmv₀ : ∀ step ∈ ss, ∀ m ∈ step.mover?, m.val.value.isLeft := fun s hs ↦
      hmv s (List.mem_append_left _ hs)
    have hst : st.IsMerge := hm st (by simp)
    rcases st with ⟨side, item⟩ | ⟨mover, side⟩ | mover | side
    · obtain ⟨t, stk⟩ := c₀
      simp only [Step.replayWithCopies?, Option.some.injEq] at hstep
      subst hstep
      obtain ⟨cs, hv, ht, hdc, hhas⟩ := attach_val t (Marked.ofLinearized item) side
      simp only at hMN hTF hDD ⊢
      rw [hv] at hMN hTF hDD
      obtain ⟨hroot, hCh, hTok, hIH⟩ := ih (c := ⟨t, stk⟩) (marksName_of_mem ht hMN)
        (traceFree_of_mem ht hTF) (distinct_of_mem ht hDD) hd₀ hm₀ hmv₀ hc₀
      have hTFd := traceFree_of_mem hdc hTF
      have hmd : (Marked.ofLinearized item).val.map Prod.snd = item.val := map_snd_map item.val
      have hsum : ((Step.itemsList [Step.em side item]).map SyntacticObject.yield).sum =
          item.toSyntacticObject.yield := by
        simp [Step.itemsList, Step.items]
      rw [hsum] at hdi hdis ⊢
      obtain ⟨hch', hcc'⟩ := step_em side hroot
        (fun w hw hi ↦ Multiset.disjoint_left.1 hdis (hTok w hw) ((holds_iff_mem_yield item).1 hi))
        (fun r hr ↦ hTFd r (by rw [hmd]; exact hr)) hdi (traceFree_of_mem ht hTF) hCh hIH
      refine ⟨by rw [hv]; rfl, hch', fun w hw ↦ ?_, hcc'⟩
      rcases (hhas w).1 hw with h | h
      · exact Multiset.mem_add.2 (.inl (hTok w h))
      · refine Multiset.mem_add.2 (.inr ((holds_iff_mem_yield item).1 ?_))
        rwa [Has, hmd] at h
    · obtain ⟨t, stk⟩ := c₀
      simp only [Step.replayWithCopies?] at hstep
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hstep
      have hmL : mover.val.value.isLeft := hmv (.im mover side) (by simp) mover (by simp)
      obtain ⟨cs, hv, ht, hdc, hhas⟩ := attach_val (t.mark mover (selHead mover)) s side
      simp only at hMN hTF hDD ⊢
      have hmt : (t.mark mover (selHead mover)).val.map Prod.snd = t.val.map Prod.snd :=
        map_snd_markTree _ _ _
      have hne : termOf s.val ≠ termOf t.val := by
        have hroot := hDD _ (self_mem_subtrees _)
        cases side with
        | left =>
          change DaughtersDiffer (RoseTree.map Prod.snd (.node (none, Vertex.bare)
            [s.val, (t.mark mover (selHead mover)).val])) at hroot
          rw [map_node] at hroot
          simpa only [List.map_cons, List.map_nil, hmt, DaughtersDiffer, termOf] using hroot
        | right =>
          change DaughtersDiffer (RoseTree.map Prod.snd (.node (none, Vertex.bare)
            [(t.mark mover (selHead mover)).val, s.val])) at hroot
          rw [map_node] at hroot
          simpa only [List.map_cons, List.map_nil, hmt, DaughtersDiffer, termOf, ne_comm] using
              hroot
      rw [hv] at hMN hTF hDD
      have hMNt : MarksName t.val := marksName_of_markTree hmL (marksName_of_mem ht hMN)
      have hTFt : TraceFree t.val := fun r hr ↦
        traceFree_of_mem ht hTF r (by rw [hmt]; exact hr)
      have hDDt : DistinctDaughters t.val := fun r hr ↦
        distinct_of_mem ht hDD r (by rw [hmt]; exact hr)
      obtain ⟨hroot, hCh, hTok, hIH⟩ := ih (c := ⟨t, stk⟩) hMNt hTFt hDDt hd₀ hm₀ hmv₀ hc₀
      have hsum : ((Step.itemsList [Step.im mover side]).map SyntacticObject.yield).sum = 0 := by
        simp [Step.itemsList, Step.items]
      obtain ⟨hch', hcc'⟩ := step_im (l := selHead mover) side hs hmL hMNt hTFt hne hCh hIH
      refine ⟨by rw [hv]; rfl, hch', fun w hw ↦ ?_, hcc'⟩
      rw [hsum, add_zero]
      rcases (hhas w).1 hw with h | h
      · exact hTok w (has_markTree.1 h)
      · exact hTok w (holds_of_mem_subtrees (map_mem_subtrees (val_mem_subtrees_of_find? hs)) h)
    · simp [Step.IsMerge] at hst
    · simp [Step.IsMerge] at hst

/-- Binding at the copy object is binding at the reading in which the chains holding the bound token
are read low, in a derivation of Merge steps that merges no token twice and moves no trace, when
marks name chains, the copy object has no traces and nothing moves from itself. -/
theorem bindsAtReading_carrying_iff {d : Derivation} (hxy : x ≠ y) (hd : d.lexTokens.Nodup)
    (hm : ∀ step ∈ d.steps, step.IsMerge)
    (hmv : ∀ step ∈ d.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) {c : Cfg Marked}
    (hc : d.replayWithCopies? = some c) (hMN : MarksName c.current.val)
    (hTF : TraceFree c.current.val) (hDD : DistinctDaughters c.current.val) :
    d.BindsAtReading (c.current.carrying y) ↑x ↑y ↔ d.BindsAtLF ↑x ↑y := by
  simp only [BindsAtReading, BindsAtLF, lf?, copyObject?, hc, Option.map_some, Option.mem_def,
    Option.some.injEq, exists_eq_left']
  rw [cCommands_iff_cc hxy, cCommands_iff_cc hxy]
  change CC x y (lfBy (ReadLow (c.current.carrying y)) c.current.val) ↔
    CC x y (c.current.val.map Prod.snd)
  rw [lfBy_readLow_carrying]
  exact ⟨cc_of_cc_lfBy hxy, (replayWithCopies?_invariants hd hm hmv hc hMN hTF hDD).2.2.2 x y hxy⟩

end Minimalist.Derivation
