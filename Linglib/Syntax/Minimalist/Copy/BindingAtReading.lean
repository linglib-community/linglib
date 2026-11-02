/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.ToTree

/-!
# Binding at a reading

This file proves that binding at the copy object is [binding at one
reading](##bindsAtReading_carrying_iff): a token c-commands another in the copy object just when it
does in the reading in which the chains holding the second are read low. So the choice of copies
the semantic interface reads loses no binding relation, and the reading that shows a given relation
is found from the bound token alone. When nothing moves from itself a reading also [creates no
binding](##BindsAtReading.bindsAtLF), so binding at the copy object is [binding at some
reading](##exists_bindsAtReading_iff).

## Implementation notes

* The theorem names one reading as well as some reading because the reading is found locally, and
  the step-by-step induction needs that: the test that a copy holds `y` is independent of the stage.
* Without `DistinctDaughters` a reading may bind where the copy object does not: an object that
  moves from itself, read low, comes to c-command the sister of its movement node.
* Two chains sharing a mark could have `mark` reach copies with different terms, which `MarksName`
  excludes. Reading each chain high or low is enough because the theorem concerns one pair of tokens
  at a time.

## References

* [chomsky-1995]
* [collins-2005]
* [collins-2026]
-/

@[expose] public section

local notation "CC" => Minimalist.LinearizedSyntacticObject.TokenCCommands

namespace Minimalist.LinearizedSyntacticObject.Marked

open RoseTree SyntacticObject

local notation "MT" => RoseTree (CopyMark × Vertex)

variable {x y : LexicalItem.Token}

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

private theorem termOf_ne_of_distinctDaughters {s : MT} (h : DistinctDaughters s) (P : MT → Prop) :
    ∀ r ∈ s.subtrees, ∀ k a u v, r = .node (k, a) [u, v] → P u ∨ P v → termOf u ≠ termOf v := by
  rintro r hr k a u v rfl -
  have := h _ (map_mem_subtrees hr)
  rw [map_node] at this
  exact this

/-- A token other than `y` is a daughter in the reading only where it is an unmarked daughter. -/
private theorem eq_node_of_lfBy_eq {w : LexicalItem.Token} (hw : w ≠ y) {s : MT}
    (hDD : DistinctDaughters s) (h : lfBy (Has y) s = .node (.inl (some w)) []) :
    s = .node (none, .inl (some w)) [] := by
  have hs := map_snd_eq_leaf_of_lfBy_eq (termOf_ne_of_distinctDaughters hDD _) h
  obtain ⟨⟨k, a⟩, cs⟩ := s
  rw [map_node, RoseTree.node.injEq, List.map_eq_nil_iff] at hs
  obtain ⟨rfl, rfl⟩ := hs
  cases k with
  | none => rfl
  | some l =>
    rw [lfBy_some, ite_eq_right fun hp ↦ hw (Option.some.inj (Sum.inl.inj ((holds_leaf _).1
      (has_node.1 hp))))] at h
    simp at h

private theorem distinct_of_mem {v : CopyMark × Vertex} {cs : List MT} {c : MT} (hc : c ∈ cs)
    (h : DistinctDaughters (.node v cs)) : DistinctDaughters c := fun r hr ↦
  h r (mem_subtrees_trans hr (by
    rw [map_node]
    exact child_mem_subtrees (List.mem_map_of_mem hc)))

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

private theorem has_node_map_markTree {v : CopyMark × Vertex} {cs : List MT} :
    Has y (.node v (cs.map (markTree m l))) ↔ Has y (.node v cs) := by
  obtain ⟨k, a⟩ := v
  rw [has_node, has_node, List.map_map,
    show cs.map (RoseTree.map Prod.snd ∘ markTree m l) = cs.map (RoseTree.map Prod.snd) from
      List.map_congr_left fun c _ ↦ map_snd_markTree m l c]

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
        have pull : ∀ {p q : MT},
            (∃ r ∈ (markTree m l q).subtrees, termOf r = termOf (markTree m l p)) →
              ∃ r ∈ q.subtrees, termOf r = termOf p := fun ⟨r', hr', ht⟩ ↦ by
          obtain ⟨r, hr, hrt⟩ := exists_mem_of_mem_markTree hr'
          exact ⟨r, hr, hrt.symm.trans (ht.trans (termOf_markTree _))⟩
        exact ⟨fun hq ↦ (isSome_lowerCopy?_markTree hm h1).2 (h1 (pull hq)),
          fun hq ↦ (isSome_lowerCopy?_markTree hm h2).2 (h2 (pull hq))⟩
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
      ih c hc' (hc c hc') fun r hr ↦ H r (mem_subtrees_trans hr (child_mem_subtrees hc'))
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
        simp only [has_node_map_markTree]

/-- If no occurrence marked holds `y`, a c-command in the reading survives marking, unless the
commander is what was marked. -/
private theorem cc_lfBy_markTree (hm : m.val.value.isLeft) (hxy : x ≠ y) {s : MT} (hs : Chains s)
    (hDD : DistinctDaughters s)
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
    · exact absurd (holds_of_holds_lfBy h.holds) (H _ (by simp) hit)
    · have hch : ∀ c ∈ cs, CC x y (lfBy (Has y) c) →
          CC x y (lfBy (Has y) (markTree m l c)) ∨
            m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) := fun c hc' hcc ↦
        ih c hc' (hc c hc') (distinct_of_mem hc' hDD)
          (fun r hr ↦ H r (mem_subtrees_trans hr (child_mem_subtrees hc'))) hcc
      have hholds : ∀ {c : MT}, Holds y (lfBy (Has y) c) →
          Holds y (lfBy (Has y) (markTree m l c)) := fun hy ↦
        holds_lfBy (has_markTree.2 (holds_of_holds_lfBy hy))
      have hleaf : ∀ {c : MT}, c ∈ cs → lfBy (Has y) c = .node (.inl (some x)) [] →
          lfBy (Has y) (markTree m l c) = .node (.inl (some x)) [] ∨
            m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) := by
        intro c hcm hc'
        obtain rfl := eq_node_of_lfBy_eq hxy (distinct_of_mem hcm hDD) hc'
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
            rw [tokenCCommands_pair_iff]
            rintro (h' | h' | ⟨hl, hy⟩ | ⟨hl, hy⟩)
            · exact (hu h').imp .inl id
            · exact (hw h').imp .inr id
            · rcases hleaf (by simp) hl with he | he
              · exact .inl (he ▸ .left (hholds hy))
              · exact .inr he
            · rcases hleaf (by simp) hl with he | he
              · exact .inl (he ▸ .right (hholds hy))
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
          exact absurd hcc (not_tokenCCommands_of_length_ne (by simpa using hlen))
      cases k with
      | none => exact hcore h
      | some l' =>
        rw [lfBy_some] at h ⊢
        simp only [has_node_map_markTree]
        split_ifs at h ⊢ with hp
        · exact hcore h
        · exact absurd h (not_tokenCCommands_of_length_ne (by simp))

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
      · obtain ⟨r', hr', hk, ht⟩ := ih c hc
          (fun r hr ↦ hu r (mem_subtrees_trans hr (child_mem_subtrees hc))) hrc
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
        have shared : ∀ {w : LexicalItem.Token} {p₁ p₂ : RoseTree Vertex}, Holds w p₁ →
            (∃ q ∈ (p₂.map ((none, ·) : Vertex → CopyMark × Vertex)).subtrees, termOf q =
              termOf (p₁.map ((none, ·) : Vertex → CopyMark × Vertex))) → Holds w p₂ :=
          @fun w _ _ hw ⟨q, hq, ht⟩ ↦ by
            have hq' : Has w q := (holds_congr ht).2 (by simpa [map_snd_map] using hw)
            simpa [map_snd_map] using holds_of_mem_subtrees (map_mem_subtrees hq) hq'
        obtain ⟨w, hw⟩ := exists_holds hu htu
        obtain ⟨w', hw'⟩ := exists_holds hv htv
        exact ⟨fun hq ↦ (hno w hw (shared hw hq)).elim, fun hq ↦ (hno w' (shared hw' hq) hw').elim⟩
      · intro c hc
        obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
        rcases List.mem_pair.1 hc' with rfl | rfl
        · exact ih _ (by simp) hu htu hdu
        · exact ih _ (by simp) hv htv hdv

private theorem val_mem_subtrees_of_find? {t s : Marked} {m : SyntacticObject}
    (h : t.find? m = some s) : s.val ∈ t.val.subtrees := by
  obtain ⟨r, hr, -, rfl⟩ := Option.pmap_eq_some_iff.1 h
  exact mem_subtrees.2 (isSubtree_of_mem_subtreesUntil hr)

/-- What the steps of a derivation preserve: daughters share a term only at movement nodes, and a
token c-commanding another in the copy object does so in the reading that reads low what holds the
other. -/
private def Good (s : MT) : Prop :=
  Chains s ∧ ∀ x y, x ≠ y → CC x y (s.map Prod.snd) → CC x y (lfBy (Has y) s)

/-- A node with at most one movement direction is `Good` in either order of its daughters. -/
private theorem Good.swap {a : Vertex} {u v : MT}
    (h : ¬ ((lowerCopy? u v).isSome ∧ (lowerCopy? v u).isSome))
    (hg : Good (.node (none, a) [u, v])) : Good (.node (none, a) [v, u]) := by
  obtain ⟨hn, hc⟩ := chains_node.1 hg.1
  refine ⟨chains_node.2 ⟨?_, fun c hc' ↦ hc c (by simp_all [or_comm])⟩, fun x y hxy hcc ↦ ?_⟩
  · rintro k b u' v' he
    simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact (hn none a _ _ rfl).symm
  · rw [map_node] at hcc
    have := hg.2 x y hxy (by rw [map_node]; exact hcc.swap)
    rw [lfBy_pair] at this ⊢
    by_cases h1 : (lowerCopy? u v).isSome
    · have h2 : ¬ (lowerCopy? v u).isSome := fun h2 ↦ h ⟨h1, h2⟩
      rw [ite_eq_left h1] at this
      rw [ite_eq_right h2, ite_eq_left h1]
      split_ifs at this ⊢
      · exact this
      · exact this.swap
    · rw [ite_eq_right h1] at this
      by_cases h2 : (lowerCopy? v u).isSome
      · rw [ite_eq_left h2] at this ⊢
        split_ifs at this ⊢
        · exact this
        · exact this.swap
      · rw [ite_eq_right h2] at this
        rw [ite_eq_right h2, ite_eq_right h1]
        exact this.swap

/-- External Merge of an item that shares no token with the object. -/
private theorem step_em {t : Marked} {item : LinearizedSyntacticObject} (e : Edge)
    (hroot : t.val.value.1 = none) (hdis : ∀ w, Has w t.val → ¬ Holds w item.val)
    (hTFi : ∀ r ∈ item.val.subtrees, r.value.isLeft) (hdi : item.toSyntacticObject.yield.Nodup)
    (hTFt : TraceFree t.val) (hg : Good t.val) : Good (t.attach e (ofLinearized item)).val := by
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
  have hleft : Good (.node (none, Vertex.bare) [d, t.val]) := by
    refine ⟨chains_node.2 ⟨?_, ?_⟩, fun x y hxy hc ↦ ?_⟩
    · rintro k a u v he
      simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl⟩ := he
      exact ⟨fun h ↦ absurd h hno₁, fun h ↦ absurd h hno₂⟩
    · intro c hc
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact chains_map_none hp hTFi hdi
      · exact hg.1
    · rw [map_node] at hc
      simp only [List.map_cons, List.map_nil, hdm] at hc
      rw [lfBy_pair, ite_eq_right hdet₁, ite_eq_right hdet₂, lfBy_map_none]
      rw [tokenCCommands_pair_iff] at hc ⊢
      rcases hc with h | h | ⟨hl, hy⟩ | ⟨hq, hy⟩
      · exact .inl h
      · exact .inr (.inl (hg.2 x y hxy h))
      · exact .inr (.inr (.inl ⟨hl, holds_lfBy (by rw [Has, ] at *; exact hy)⟩))
      · rcases ht : t.val with ⟨⟨k, a⟩, cs⟩
        rw [ht, map_node] at hq
        simp only [RoseTree.node.injEq, List.map_eq_nil_iff] at hq
        obtain ⟨rfl, rfl⟩ := hq
        rw [ht] at hroot
        obtain rfl : k = none := hroot
        rw [lfBy_leaf]
        exact .inr (.inr (.inr ⟨rfl, hy⟩))
  cases e with
  | left => exact hleft
  | right => exact hleft.swap fun h ↦ hdet₁ h.1

/-- Internal Merge of a phrase found in the object, other than the object itself. -/
private theorem step_im {t s₀ : Marked} {m : SyntacticObject} {l : Option LexicalItem.Token}
    (e : Edge) (hfind : t.find? m = some s₀) (hm : m.val.value.isLeft) (hMN : MarksName t.val)
    (hTF : TraceFree t.val) (hDD : DistinctDaughters t.val) (hne : termOf s₀.val ≠ termOf t.val)
    (hg : Good t.val) :
    Good ((t.mark m l).attach e s₀).val := by
  obtain ⟨hCh, hIH⟩ := hg
  have hr₀ := val_mem_subtrees_of_find? hfind
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
  have hleft : Good (.node (none, Vertex.bare) [r₀, markTree m l t.val]) := by
    refine ⟨chains_node.2 ⟨?_, ?_⟩, fun x y hxy hc ↦ ?_⟩
    · rintro k a u v he
      simp only [RoseTree.node.injEq, List.cons.injEq, and_true] at he
      obtain ⟨-, rfl, rfl⟩ := he
      refine ⟨fun _ ↦ hdet, fun ⟨q, hq, ht⟩ ↦ ?_⟩
      exact absurd (ht.trans (termOf_markTree _)) (hsize q hq)
    · intro c hc
      rcases List.mem_pair.1 hc with rfl | rfl
      · exact fun r hr ↦ hCh r (mem_subtrees_trans hr hr₀)
      · exact chains_markTree hm hCh
    · rw [map_node] at hc
      simp only [List.map_cons, List.map_nil, map_snd_markTree] at hc
      have hCCt : CC x y (r₀.map Prod.snd) ∨ CC x y (t.val.map Prod.snd) ∨
          (r₀.map Prod.snd = .node (.inl (some x)) [] ∧ Holds y (t.val.map Prod.snd)) := by
        rcases tokenCCommands_pair_iff.1 hc with h | h | h | ⟨hq, hy⟩
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
        · exfalso
          have hmem := map_mem_subtrees hr₀
          rw [hq, subtrees_node] at hmem
          simp only [List.flatMap_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rw [hmem] at hy
          exact hxy (Option.some.inj (Sum.inl.inj ((holds_leaf _).1 hy)))
      have hsub : CC x y (r₀.map Prod.snd) → CC x y (t.val.map Prod.snd) := fun h ↦
        h.of_mem_subtrees (map_mem_subtrees hr₀) t.2
      rw [lfBy_pair, ite_eq_left hdet]
      split_ifs with hp
      · have hHas : ∀ r ∈ t.val.subtrees, UnorderedTree.mk (contractTree r) = m.val → Has y r :=
          fun r hr h ↦ (holds_congr (hτ r hr h)).2 hp
        rw [lfBy_markTree_of_has hm hCh hHas]
        rcases hCCt with h | h | ⟨hq, -⟩
        · exact hIH x y hxy (hsub h)
        · exact hIH x y hxy h
        · rw [Has, hq] at hp
          exact absurd (Option.some.inj (Sum.inl.inj ((holds_leaf _).1 hp))) hxy
      · have hleaf : m.val = UnorderedTree.mk (.node (Sum.inl (some x)) []) →
            lfBy (Has y) r₀ = .node (.inl (some x)) [] := by
          intro hv
          rw [hv, contractTree_none, UnorderedTree.mk_node_eq_mk_node_iff] at hit₀
          obtain ⟨rfl, hd⟩ := hit₀
          rcases cs₀ with _ | ⟨c, cs⟩
          · exact lfBy_leaf _ _
          · have := congrArg Multiset.card hd
            simp at this
        have hnew : CC x y (t.val.map Prod.snd) →
            CC x y (.node Vertex.bare [lfBy (Has y) r₀, lfBy (Has y) (markTree m l t.val)]) := by
          intro h'
          have hL := hIH x y hxy h'
          rcases cc_lfBy_markTree (l := l) hm hxy hCh hDD
            (fun r hr h ↦ (holds_congr (hτ r hr h)).not.2 hp) hL with h'' | hv
          · exact .inr h''
          · rw [hleaf hv]
            exact .left (holds_lfBy (has_markTree.2 (holds_of_holds_lfBy hL.holds)))
        rcases hCCt with h | h | ⟨hq, hy⟩
        · exact hnew (hsub h)
        · exact hnew h
        · have hr₀leaf : r₀ = .node (none, .inl (some x)) [] := by
            simp only [r₀, map_node, RoseTree.node.injEq, List.map_eq_nil_iff] at hq ⊢
            exact ⟨by rw [hq.1], hq.2⟩
          rw [hr₀leaf, lfBy_leaf]
          exact .left (holds_lfBy (has_markTree.2 hy))
  cases e with
  | left =>
    rw [show ((t.mark m l).attach .left s₀).val =
      .node (none, Vertex.bare) [s₀.val, markTree m l t.val] from rfl, hs]
    exact hleft
  | right =>
    rw [show ((t.mark m l).attach .right s₀).val =
      .node (none, Vertex.bare) [markTree m l t.val, s₀.val] from rfl, hs]
    exact hleft.swap fun h ↦ hndet h.2

private theorem marksName_of_mem {v : CopyMark × Vertex} {cs : List MT} {c : MT} (hc : c ∈ cs)
    (h : MarksName (.node v cs)) : MarksName c := fun r₁ h₁ r₂ h₂ ↦
  h r₁ (mem_subtrees_trans h₁ (child_mem_subtrees hc)) r₂
    (mem_subtrees_trans h₂ (child_mem_subtrees hc))

private theorem traceFree_of_mem {v : CopyMark × Vertex} {cs : List MT} {c : MT} (hc : c ∈ cs)
    (h : TraceFree (.node v cs)) : TraceFree c := fun r hr ↦
  h r (mem_subtrees_trans hr (by
    rw [map_node]
    exact child_mem_subtrees (List.mem_map_of_mem hc)))

/-- Only a reading's tests of a copy with a marked copy matter. -/
private theorem lfBy_congr {P Q : MT → Prop} [DecidablePred P] [DecidablePred Q] {T : MT}
    (h : ∀ r ∈ T.subtrees, (r.value.1.isSome ∨
      ∃ q ∈ T.subtrees, q.value.1.isSome ∧ termOf q = termOf r) → (P r ↔ Q r))
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
        have test : ∀ {p q : MT}, p ∈ T.subtrees → q ∈ T.subtrees → (lowerCopy? p q).isSome →
            (P p ↔ Q p) := fun hp hq' he ↦ by
          obtain ⟨q, hq, hk, ht⟩ := isSome_lowerCopy?_iff.1 he
          exact h _ hp (.inr ⟨q, mem_subtrees_trans hq hq', hk, ht⟩)
        rw [lfBy_pair, lfBy_pair, hch u (by simp), hch w (by simp)]
        by_cases h₁ : (lowerCopy? u w).isSome
        · simp [h₁, test hu hw h₁]
        · by_cases h₂ : (lowerCopy? w u).isSome
          · simp [h₁, h₂, test hw hu h₂]
          · simp [h₁, h₂]
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
    (hrel : r.value.1.isSome ∧ r ∈ t.val.subtrees ∨
      ∃ q ∈ t.val.subtrees, q.value.1.isSome ∧ termOf q = termOf r) :
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

private theorem termOf_ne_of_attach {t d : Marked} {e : Edge}
    (h : DistinctDaughters (t.attach e d).val) : termOf d.val ≠ termOf t.val := by
  cases e with
  | left =>
    exact termOf_ne_of_distinctDaughters h (fun _ ↦ True) _ (self_mem_subtrees _) none _ _ _ rfl
      (.inl trivial)
  | right =>
    exact (termOf_ne_of_distinctDaughters h (fun _ ↦ True) _ (self_mem_subtrees _) none _ _ _ rfl
      (.inl trivial)).symm

private theorem lfBy_readLow_carrying (t : Marked) :
    lfBy (ReadLow (t.carrying y)) t.val = lfBy (Has y) t.val :=
  lfBy_congr (T := t.val) (fun r hr hrel ↦ readLow_carrying_iff t (by
    rcases hrel with hk | h
    · exact .inl ⟨hk, hr⟩
    · exact .inr h)) (self_mem_subtrees _)

end Minimalist.LinearizedSyntacticObject.Marked

namespace Minimalist.Derivation

open RoseTree SyntacticObject
open LinearizedSyntacticObject (Marked Holds cCommands_iff_tokenCCommands holds_iff_mem_yield
  holds_of_mem_subtrees)
open LinearizedSyntacticObject.Marked

variable {x y : LexicalItem.Token}

/-- What the steps of a derivation preserve, given what its final object satisfies. -/
private theorem replayWithCopies?_invariants {d : Derivation} (hd : d.lexTokens.Nodup)
    (hm : ∀ step ∈ d.steps, step.IsMerge)
    (hmv : ∀ step ∈ d.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) {c : Cfg Marked}
    (hc : d.replayWithCopies? = some c) (hMN : MarksName c.current.val)
    (hTF : TraceFree c.current.val) (hDD : DistinctDaughters c.current.val) :
    c.current.val.value.1 = none ∧ Good c.current.val ∧
      ∀ w, Has w c.current.val → w ∈ d.lexTokens := by
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
    refine ⟨?_, ⟨chains_map_none p.2 hTFp ?_, fun x y _ hcc ↦ ?_⟩, fun w hw ↦ ?_⟩
    · change (p.val.map ((none, ·) : Vertex → CopyMark × Vertex)).value.1 = none
      rcases p.val with ⟨a, cs⟩
      simp [map_node]
    · have : (LinearizedSyntacticObject.toSyntacticObject ⟨p.val, p.2⟩) = init := hinit
      rw [this]
      simpa [lexTokens, items] using hd
    · have hcc' : CC x y p.val := by
        have : CC x y ((Marked.ofLinearized p).val.map Prod.snd) := hcc
        rwa [hm₀] at this
      change CC x y (lfBy (Has y) (p.val.map ((none, ·) : Vertex → CopyMark × Vertex)))
      rwa [lfBy_map_none]
    · have hw' : Holds w p.val := by
        have : Has w (Marked.ofLinearized p).val := hw
        rwa [Has, hm₀] at this
      have := (holds_iff_mem_yield p).1 hw'
      rw [hinit] at this
      simpa [lexTokens, items] using this
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
      obtain ⟨hroot, hg, hTok⟩ := ih (c := ⟨t, stk⟩) (marksName_of_mem ht hMN)
        (traceFree_of_mem ht hTF) (distinct_of_mem ht hDD) hd₀ hm₀ hmv₀ hc₀
      have hTFd := traceFree_of_mem hdc hTF
      have hmd : (Marked.ofLinearized item).val.map Prod.snd = item.val := map_snd_map item.val
      have hsum : ((Step.itemsList [Step.em side item]).map SyntacticObject.yield).sum =
          item.toSyntacticObject.yield := by
        simp [Step.itemsList, Step.items]
      rw [hsum] at hdi hdis ⊢
      have hg' := step_em side hroot
        (fun w hw hi ↦ Multiset.disjoint_left.1 hdis (hTok w hw) ((holds_iff_mem_yield item).1 hi))
        (fun r hr ↦ hTFd r (by rw [hmd]; exact hr)) hdi (traceFree_of_mem ht hTF) hg
      refine ⟨by rw [hv]; rfl, hg', fun w hw ↦ ?_⟩
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
        exact fun h ↦ termOf_ne_of_attach hDD (h.trans (termOf_markTree _).symm)
      rw [hv] at hMN hTF hDD
      have hMNt : MarksName t.val := marksName_of_markTree hmL (marksName_of_mem ht hMN)
      have hTFt : TraceFree t.val := fun r hr ↦
        traceFree_of_mem ht hTF r (by rw [hmt]; exact hr)
      have hDDt : DistinctDaughters t.val := fun r hr ↦
        distinct_of_mem ht hDD r (by rw [hmt]; exact hr)
      obtain ⟨-, hg, hTok⟩ := ih (c := ⟨t, stk⟩) hMNt hTFt hDDt hd₀ hm₀ hmv₀ hc₀
      have hsum : ((Step.itemsList [Step.im mover side]).map SyntacticObject.yield).sum = 0 := by
        simp [Step.itemsList, Step.items]
      refine ⟨by rw [hv]; rfl, step_im side hs hmL hMNt hTFt hDDt hne hg, fun w hw ↦ ?_⟩
      rw [hsum, add_zero]
      rcases (hhas w).1 hw with h | h
      · exact hTok w (has_markTree.1 h)
      · exact hTok w (holds_of_mem_subtrees (map_mem_subtrees (val_mem_subtrees_of_find? hs)) h)
    · simp [Step.IsMerge] at hst
    · simp [Step.IsMerge] at hst

/-- Binding at a reading is binding at the copy object, when nothing moves from itself. -/
theorem BindsAtReading.bindsAtLF {d : Derivation} {low : Finset SyntacticObject} (hxy : x ≠ y)
    {c : Cfg Marked} (hc : d.replayWithCopies? = some c) (hDD : DistinctDaughters c.current.val)
    (h : d.BindsAtReading low ↑x ↑y) : d.BindsAtLF ↑x ↑y := by
  simp only [BindsAtReading, BindsAtLF, lf?, copyObject?, hc, Option.map_some, Option.mem_def,
    Option.some.injEq, exists_eq_left'] at h ⊢
  exact cCommands_unmark_of_cCommands_lf hxy (termOf_ne_of_distinctDaughters hDD _) h

/-- Binding at the copy object is binding at the reading in which the chains holding the bound token
are read low, in a derivation of Merge steps that merges no token twice and moves no trace, when
marks name chains, the copy object has no traces and nothing moves from itself. -/
theorem bindsAtReading_carrying_iff {d : Derivation} (hxy : x ≠ y) (hd : d.lexTokens.Nodup)
    (hm : ∀ step ∈ d.steps, step.IsMerge)
    (hmv : ∀ step ∈ d.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) {c : Cfg Marked}
    (hc : d.replayWithCopies? = some c) (hMN : MarksName c.current.val)
    (hTF : TraceFree c.current.val) (hDD : DistinctDaughters c.current.val) :
    d.BindsAtReading (c.current.carrying y) ↑x ↑y ↔ d.BindsAtLF ↑x ↑y := by
  refine ⟨BindsAtReading.bindsAtLF hxy hc hDD, fun h ↦ ?_⟩
  simp only [BindsAtReading, BindsAtLF, lf?, copyObject?, hc, Option.map_some, Option.mem_def,
    Option.some.injEq, exists_eq_left'] at h ⊢
  rw [cCommands_iff_tokenCCommands hxy] at h ⊢
  change CC x y (lfBy (ReadLow (c.current.carrying y)) c.current.val)
  rw [lfBy_readLow_carrying]
  exact (replayWithCopies?_invariants hd hm hmv hc hMN hTF hDD).2.1.2 x y hxy h

/-- Binding at the copy object is binding at some reading. -/
theorem exists_bindsAtReading_iff {d : Derivation} (hxy : x ≠ y) (hd : d.lexTokens.Nodup)
    (hm : ∀ step ∈ d.steps, step.IsMerge)
    (hmv : ∀ step ∈ d.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) {c : Cfg Marked}
    (hc : d.replayWithCopies? = some c) (hMN : MarksName c.current.val)
    (hTF : TraceFree c.current.val) (hDD : DistinctDaughters c.current.val) :
    (∃ low, d.BindsAtReading low ↑x ↑y) ↔ d.BindsAtLF ↑x ↑y :=
  ⟨fun ⟨_, h⟩ ↦ h.bindsAtLF hxy hc hDD,
    fun h ↦ ⟨_, (bindsAtReading_carrying_iff hxy hd hm hmv hc hMN hTF hDD).2 h⟩⟩

end Minimalist.Derivation
