/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Linglib.Core.Data.UnorderedTree.Leaves

/-!
# C-command between tokens on ordered trees

This file reads c-command between two tokens off an ordered tree of vertices, by recursion on the
tree: a token c-commands another when it is a daughter whose sister holds the other. The recursion
needs no licensing, so it applies to the raw trees that recursions over a marked object produce.
Between distinct tokens of a planar object it [is `CCommands`](##cCommands_iff_tokenCCommands).

## Main definitions

* `Minimalist.PlanarSyntacticObject.Holds`: the tree has a token as a leaf.
* `Minimalist.PlanarSyntacticObject.TokenCCommands`: c-command between tokens.
-/

@[expose] public section

namespace Minimalist.PlanarSyntacticObject

open RoseTree SyntacticObject

/-- The tree holds the token `y`. -/
def Holds (y : LexicalItem.Token) (p : RoseTree Vertex) : Prop :=
  Sum.inl (some y) ∈ p.leaves

instance (y : LexicalItem.Token) : DecidablePred (Holds y) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

variable {x y : LexicalItem.Token}

@[simp] theorem holds_leaf (a : Vertex) :
    Holds y (.node a []) ↔ a = Sum.inl (some y) := by
  simp [Holds, eq_comm]

theorem holds_pair (a : Vertex) (l r : RoseTree Vertex) :
    Holds y (.node a [l, r]) ↔ Holds y l ∨ Holds y r := by
  simp [Holds]

theorem holds_node_of_mem {a : Vertex} {cs : List (RoseTree Vertex)} {c : RoseTree Vertex}
    (hc : c ∈ cs) (h : Holds y c) : Holds y (.node a cs) :=
  Multiset.mem_of_le (leaves_le_of_mem_children hc) h

theorem exists_mem_of_holds_map {α : Type*} {a : Vertex} {cs : List α}
    {f : α → RoseTree Vertex} (hne : cs ≠ []) (h : Holds y (.node a (cs.map f))) :
    ∃ c ∈ cs, Holds y (f c) := by
  obtain ⟨_, ht, hy⟩ := (mem_leaves_node_of_ne_nil a (mt List.map_eq_nil_iff.1 hne)).1 h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ht
  exact ⟨c, hc, hy⟩

theorem holds_of_mem_subtrees {r z : RoseTree Vertex} (hr : r ∈ z.subtrees)
    (h : Holds y r) : Holds y z := by
  induction z with
  | node a cs ih =>
    rw [subtrees_node, List.mem_cons, List.mem_flatMap] at hr
    rcases hr with rfl | ⟨c, hc, hrc⟩
    · exact h
    · exact holds_node_of_mem hc (ih c hc hrc)

theorem holds_congr {p q : RoseTree Vertex} (h : UnorderedTree.mk p = UnorderedTree.mk q) :
    Holds y p ↔ Holds y q := by
  rw [Holds, Holds, ← UnorderedTree.leaves_mk, ← UnorderedTree.leaves_mk q, h]

/-- `x` c-commands `y` in an ordered tree: `x` is a daughter whose sister holds `y`. -/
inductive TokenCCommands (x y : LexicalItem.Token) : RoseTree Vertex → Prop
  | inl {a l r} : TokenCCommands x y l → TokenCCommands x y (.node a [l, r])
  | inr {a l r} : TokenCCommands x y r → TokenCCommands x y (.node a [l, r])
  | left {a r} : Holds y r → TokenCCommands x y (.node a [.node (.inl (some x)) [], r])
  | right {a l} : Holds y l → TokenCCommands x y (.node a [l, .node (.inl (some x)) []])

theorem tokenCCommands_pair_iff {a : Vertex} {l r : RoseTree Vertex} :
    TokenCCommands x y (.node a [l, r]) ↔ TokenCCommands x y l ∨ TokenCCommands x y r ∨
      (l = .node (.inl (some x)) [] ∧ Holds y r) ∨ (r = .node (.inl (some x)) [] ∧ Holds y l) := by
  constructor
  · generalize he : RoseTree.node a [l, r] = p
    intro h
    cases h with
    | inl h' => simp_all
    | inr h' => simp_all
    | left h' => simp_all
    | right h' => simp_all
  · rintro (h | h | ⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact .inl h
    · exact .inr h
    · exact .left h
    · exact .right h

theorem not_tokenCCommands_of_length_ne {a : Vertex} {cs : List (RoseTree Vertex)}
    (h : cs.length ≠ 2) : ¬ TokenCCommands x y (.node a cs) := by
  generalize he : RoseTree.node a cs = p
  intro hc
  cases hc <;> simp_all

theorem TokenCCommands.swap {a : Vertex} {l r : RoseTree Vertex}
    (h : TokenCCommands x y (.node a [l, r])) : TokenCCommands x y (.node a [r, l]) := by
  rw [tokenCCommands_pair_iff] at h ⊢
  tauto

theorem TokenCCommands.holds {p : RoseTree Vertex} (h : TokenCCommands x y p) : Holds y p := by
  induction h with
  | inl _ ih => exact (holds_pair _ _ _).2 (.inl ih)
  | inr _ ih => exact (holds_pair _ _ _).2 (.inr ih)
  | left hy => exact (holds_pair _ _ _).2 (.inr hy)
  | right hy => exact (holds_pair _ _ _).2 (.inl hy)

theorem TokenCCommands.of_mem_subtrees {r z : RoseTree Vertex} (hr : r ∈ z.subtrees)
    (h : TokenCCommands x y r) (hz : IsSyntacticObject (UnorderedTree.mk z)) :
    TokenCCommands x y z := by
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

private theorem terms_of_nil {a : Vertex}
    (h : IsSyntacticObject (UnorderedTree.mk (.node a []))) :
    (PlanarSyntacticObject.ofRoseTree (.node a []) h).toSyntacticObject.terms =
      {(PlanarSyntacticObject.ofRoseTree (.node a []) h).toSyntacticObject} := by
  have hv := PlanarSyntacticObject.toRoseTree_ofRoseTree _ h
  generalize PlanarSyntacticObject.ofRoseTree (.node a []) h = p at hv
  cases p with
  | of x => rfl
  | mul l r => simp [PlanarSyntacticObject.toRoseTree] at hv

/-- The token is a term of the object just when the tree holds it. -/
theorem coe_mem_terms_iff (p : PlanarSyntacticObject) :
    (↑y : SyntacticObject) ∈ p.toSyntacticObject.terms ↔ Holds y p.toRoseTree := by
  obtain ⟨p, h, rfl⟩ := p.exists_eq_ofRoseTree
  rw [toRoseTree_ofRoseTree]
  induction p with
  | node a cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · rw [List.length_eq_zero_iff] at hlen
      subst hlen
      rw [terms_of_nil, Multiset.mem_singleton, ← SyntacticObject.toUnorderedTree_inj,
          toUnorderedTree_toSyntacticObject,
        toRoseTree_ofRoseTree, holds_leaf]
      change UnorderedTree.mk (.node (Sum.inl (some y)) []) = UnorderedTree.mk (.node a []) ↔ _
      rw [UnorderedTree.mk_node_eq_mk_node_iff]
      simp [eq_comm]
    · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hu, hv⟩ := (isSyntacticObject_mk_merge _ _).1 h
      rw [ofRoseTree_node_bare, PlanarSyntacticObject.toSyntacticObject_merge, terms_merge,
        Multiset.mem_cons,
        Multiset.mem_add, holds_pair, ih u (by simp) hu, ih v (by simp) hv]
      exact or_iff_right (leaf_ne_merge _ _ _)

/-- On a syntactic object c-command between distinct tokens is `TokenCCommands`. -/
theorem cCommands_iff_tokenCCommands (hxy : x ≠ y) (p : PlanarSyntacticObject) :
    CCommands p.toSyntacticObject ↑x ↑y ↔ TokenCCommands x y p.toRoseTree := by
  obtain ⟨p, h, rfl⟩ := p.exists_eq_ofRoseTree
  rw [toRoseTree_ofRoseTree]
  induction p with
  | node a cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · rw [List.length_eq_zero_iff] at hlen
      subst hlen
      refine ⟨?_, fun hc ↦ by cases hc⟩
      rintro ⟨z, -, ⟨w, hw, hwx, -, -⟩, -⟩
      rw [terms_of_nil, Multiset.mem_singleton] at hw
      subst hw
      simp [ImmediatelyContains] at hwx
    · obtain ⟨u, v, rfl⟩ := List.length_eq_two.1 hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hu, hv⟩ := (isSyntacticObject_mk_merge _ _).1 h
      let U : PlanarSyntacticObject := ofRoseTree u hu
      let V : PlanarSyntacticObject := ofRoseTree v hv
      have hUv : U.toRoseTree = u := toRoseTree_ofRoseTree u hu
      have hVv : V.toRoseTree = v := toRoseTree_ofRoseTree v hv
      have hval (W : PlanarSyntacticObject) {w : RoseTree Vertex} (hW : W.toRoseTree = w)
          (he : (↑x : SyntacticObject) = W.toSyntacticObject) :
          UnorderedTree.mk (.node (Sum.inl (some x)) []) = UnorderedTree.mk w :=
        (congrArg SyntacticObject.toUnorderedTree he).trans
          ((toUnorderedTree_toSyntacticObject W).trans (congrArg UnorderedTree.mk hW))
      rw [ofRoseTree_node_bare]
      change CCommands (PlanarSyntacticObject.toSyntacticObject
        (PlanarSyntacticObject.merge U V)) _ _ ↔ _
      rw [PlanarSyntacticObject.toSyntacticObject_merge]
      constructor
      · rintro ⟨z, -, hs, hzy⟩
        rcases Sisters.of_merge hs with hc | hc | ⟨he, rfl⟩ | ⟨he, rfl⟩
        · exact .inl ((ih u (by simp) hu).1 ⟨z, hc.mem_right, hc, hzy⟩)
        · exact .inr ((ih v (by simp) hv).1 ⟨z, hc.mem_right, hc, hzy⟩)
        · have hu' := eq_node_of_coe_eq (hval U hUv he)
          rw [hu']
          exact .left (hVv ▸ (coe_mem_terms_iff V).1 (mem_terms.2 hzy))
        · have hv' := eq_node_of_coe_eq (hval V hVv he)
          rw [hv']
          exact .right (hUv ▸ (coe_mem_terms_iff U).1 (mem_terms.2 hzy))
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
            (fun he ↦ ?_) ((coe_mem_terms_iff V).2 (hVv.symm ▸ hy))
          have hv' : v = .node (.inl (some x)) [] := eq_node_of_coe_eq (hval V hVv he)
          rw [hv', holds_leaf] at hy
          exact hxy (Option.some.inj (Sum.inl.inj hy))
        | right hy =>
          refine ⟨U.toSyntacticObject, mem_terms.2 (.single
            ((immediatelyContains_merge _ _ _).2 (.inl rfl))), ⟨_, self_mem_terms _,
              (immediatelyContains_merge _ _ _).2 (.inr rfl),
              (immediatelyContains_merge _ _ _).2 (.inl rfl), fun he ↦ ?_⟩,
            mem_terms.1 ((coe_mem_terms_iff U).2 (hUv.symm ▸ hy))⟩
          have hu' : u = .node (.inl (some x)) [] := eq_node_of_coe_eq (hval U hUv he)
          rw [hu', holds_leaf] at hy
          exact hxy (Option.some.inj (Sum.inl.inj hy))

theorem holds_iff_mem_yield {w : LexicalItem.Token} (p : PlanarSyntacticObject) :
    Holds w p.toRoseTree ↔ w ∈ p.toSyntacticObject.yield :=
  (coe_mem_terms_iff p).symm.trans mem_yield_iff.symm

/-- A trace-free object holds a token. -/
theorem exists_holds {p : RoseTree Vertex} (h : IsSyntacticObject (UnorderedTree.mk p))
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
        (mem_subtrees.2 ((mem_subtrees.1 hr).trans (.of_mem_children (by simp))))
      exact ⟨w, holds_node_of_mem (by simp) hw⟩


end Minimalist.PlanarSyntacticObject
