/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Mathlib.Data.List.MinMax

/-!
# Spell-out of multidominance

When Merge applies to a term a second time, the linearized object lists that term at each of its
occurrences: a term remerged inside its own root, moved, stands above its lower occurrences, and a
term remerged with another root, shared, stands under mothers none of which dominates another. PF
pronounces each term once, under one of its highest mothers, in Gračanin-Yuksek's sense, those no
other mother of it dominates. A moved term has one highest mother and is pronounced at its highest
occurrence. Accounts differ over which highest mother a shared term is pronounced under: de Vries
takes the one pronounced last, so that right-node raising pronounces shared material in the last
conjunct, and Yip's right dislocation the one pronounced first. The choice is a parameter, a pick
among a term's candidate positions in left-to-right order.

## Main definitions

* `Minimalist.mothers`, `Minimalist.IsHighestMother`: the terms a term is a daughter of, and those
  no other mother of it dominates.
* `Minimalist.candidates`, `Minimalist.spellOutPosition`: the positions at which a term may be
  pronounced, and the one the pick chooses.
* `Minimalist.remergedYield`: the pronounced tokens, left to right.

## Main statements

* `Minimalist.remergedYield_perm_tokens`: each token is pronounced exactly once, whatever the pick.
* `Minimalist.remergedYield_eq_of_chain`: where the mothers of every term are ordered by dominance,
  as movement leaves them, the pick makes no difference.
* `Minimalist.remergedYield_getLast?_eq_tokens`: where no mother of a term dominates another, as
  sharing leaves them, the last pick pronounces each token at its last occurrence, as `tokens`
  keeps them.

## Implementation notes

* De Vries's spell-out of remerged nodes, his (56), decides at each visit of a term from which of
  its mothers the traversal has reached, and his algorithm (71) counts a visit that omits a term as
  reaching it, which can pronounce a token twice (`DeVries2009`). Here the choice is made once per
  term, and the term is silent at its other occurrences.
* Each step of the recursion moves from a term to a strictly larger mother, so the size of the
  object bounds it.

## TODO

* A copy object pronounced at the highest occurrence of each moved term as the externalization of
  its contraction (`Copy/Marked.lean`), Nunes's chain reduction.
* The conditions that exclude structures from linearization, such as Wilder's restriction of
  shared material to the right edge, as predicates on objects.

## References

* [de-vries-2009]
* [gracanin-yuksek-2013]
* [yip-k-f-2026]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order

variable (pick : List TreePath → Option TreePath) (t : LinearizedSyntacticObject)

/-- The mothers of `s` in `t`: the terms of `t` with `s` as a daughter. -/
def mothers (s : RoseTree Vertex) : List (RoseTree Vertex) :=
  (t.val.subtrees.filter (s ∈ ·.children)).dedup

/-- `m` is a highest mother of `s`: a mother of `s` that no other mother of `s` dominates. -/
def IsHighestMother (s m : RoseTree Vertex) : Prop :=
  s ∈ m.children ∧ ∀ g ∈ mothers t s, ¬ (IsSubtree m g ∧ m ≠ g)

instance (s m : RoseTree Vertex) : Decidable (IsHighestMother t s m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The positions at which `s` may be pronounced once `pos` places its mothers: its occurrences,
left to right, under a highest mother pronounced there. -/
def candidates (pos : RoseTree Vertex → Option TreePath) (s : RoseTree Vertex) : List TreePath :=
  (t.val.positionedSubtrees.filter fun x ↦ x.2 = s ∧
    (t.val[x.1.parent.toList]?).any fun m ↦
      decide (IsHighestMother t s m) && pos m == some x.1.parent).map Prod.fst

/-- Where `s` is pronounced, within `n` steps of the root: the root at the root, and any other term
at the candidate `pick` chooses. -/
def spellOutPositionAux : ℕ → RoseTree Vertex → Option TreePath
  | 0, _ => none
  | n + 1, s => if s = t.val then some ⊥ else pick (candidates t (spellOutPositionAux n) s)

/-- The position at which `s` is pronounced, `none` when `s` is not a term of `t`. -/
def spellOutPosition (s : RoseTree Vertex) : Option TreePath :=
  spellOutPositionAux pick t (t.val.numNodes + 1) s

/-- The pronounced tokens, left to right: each at the position where its leaf is pronounced. -/
def remergedYield : List LexicalItem.Token :=
  (tokenList t.val).filterMap fun x ↦
    if spellOutPosition pick t (.node (.lex x.2) []) = some x.1 then some x.2 else none

/-- A token is pronounced once at most, however many times Merge applied to it. -/
theorem nodup_remergedYield : (remergedYield pick t).Nodup := by
  refine ((nodup_map_fst_positions _ t.val).of_map Prod.fst).filterMap fun x y tok hx hy ↦ ?_
  simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at hx hy
  obtain ⟨hx, rfl⟩ := hx
  obtain ⟨hy, hxy⟩ := hy
  exact Prod.ext (Option.some_injective _ (hx.symm.trans (hxy ▸ hy))) hxy.symm

/-! ### Candidates -/

variable {pick t} {pos pos' : RoseTree Vertex → Option TreePath} {s : RoseTree Vertex}

theorem mem_candidates {p : TreePath} :
    p ∈ candidates t pos s ↔ t.val[p.toList]? = some s ∧
      ∃ m, t.val[p.parent.toList]? = some m ∧ IsHighestMother t s m ∧
        pos m = some p.parent := by
  simp only [candidates, List.mem_map, List.mem_filter, mem_positionedSubtrees, decide_eq_true_eq,
    Prod.exists, exists_and_right, exists_eq_right]
  rcases t.val[p.parent.toList]? with _ | m <;> simp

theorem candidates_congr (h : ∀ m, IsHighestMother t s m → IsSubtree m t.val → pos m = pos' m) :
    candidates t pos s = candidates t pos' s := by
  refine congrArg _ (List.filter_congr fun x _ ↦ ?_)
  rcases hm : t.val[x.1.parent.toList]? with _ | m
  · simp
  · by_cases hh : IsHighestMother t s m
    · simp [h m hh (isSubtree_iff_exists_getElem?.2 ⟨_, hm⟩)]
    · simp [hh]

/-- A term other than the root has a candidate once `pos` places each larger term at a position of
its own. -/
theorem candidates_ne_nil (hs : IsSubtree s t.val) (hroot : s ≠ t.val)
    (hpos : ∀ m, IsSubtree m t.val → s.numNodes < m.numNodes →
      ∃ p, pos m = some p ∧ t.val[p.toList]? = some m) :
    candidates t pos s ≠ [] := by
  obtain ⟨q, hq⟩ := isSubtree_iff_exists_getElem?.1 hs
  obtain ⟨q, i, rfl⟩ : ∃ q' i, q = q' ++ [i] := by
    rcases List.eq_nil_or_concat q with rfl | ⟨q', i, rfl⟩
    · exact absurd (Option.some.inj hq).symm hroot
    · exact ⟨q', i, List.concat_eq_append ..⟩
  rw [getElem?_append] at hq
  obtain ⟨m₀, hm₀, hm₀s⟩ := Option.bind_eq_some_iff.1 hq
  have hm₀mem : m₀ ∈ mothers t s := by
    simp only [mothers, List.mem_dedup, List.mem_filter, mem_subtrees, decide_eq_true_eq]
    exact ⟨isSubtree_iff_exists_getElem?.2 ⟨q, hm₀⟩, List.mem_of_getElem? (by simpa using hm₀s)⟩
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1
    (mt List.argmax_eq_none.1 (List.ne_nil_of_mem hm₀mem) : (mothers t s).argmax numNodes ≠ none)
  have hmem := List.argmax_mem hm
  simp only [mothers, List.mem_dedup, List.mem_filter, mem_subtrees, decide_eq_true_eq] at hmem
  have hhigh : IsHighestMother t s m :=
    ⟨hmem.2, fun g hg ⟨hmg, hne⟩ ↦ hne (hmg.eq_of_numNodes_le (List.le_of_mem_argmax hg hm))⟩
  obtain ⟨pm, hpm, hpmm⟩ := hpos m hmem.1 (numNodes_lt_of_mem hmem.2)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem.2
  refine List.ne_nil_of_mem (a := ⟨pm.toList ++ [j]⟩) (mem_candidates.2 ⟨?_, m, ?_, hhigh, ?_⟩)
  · rw [getElem?_append, hpmm]
    simpa using hj
  · simpa [TreePath.parent] using hpmm
  · simpa [TreePath.parent] using hpm

/-! ### Every token is pronounced -/

/-- A term of `t` is pronounced at one of its own positions when the recursion has room to reach
the root and `pick` chooses among the positions it is given. -/
theorem exists_spellOutPositionAux
    (hpick : ∀ l : List TreePath, l ≠ [] → ∃ p ∈ l, pick l = some p) :
    ∀ (n : ℕ) (s : RoseTree Vertex), IsSubtree s t.val → t.val.numNodes < s.numNodes + n →
      ∃ p, spellOutPositionAux pick t n s = some p ∧ t.val[p.toList]? = some s
  | 0, s, hs, hn => absurd hs.numNodes_le (by omega)
  | n + 1, s, hs, hn => by
    rw [spellOutPositionAux]
    split_ifs with hroot
    · exact ⟨⊥, rfl, by rw [hroot]; rfl⟩
    obtain ⟨p, hp, hpick'⟩ := hpick _ (candidates_ne_nil hs hroot fun m hm hlt ↦
      exists_spellOutPositionAux hpick n m hm (by omega))
    exact ⟨p, hpick', (mem_candidates.1 hp).1⟩

/-- The term at a position holding a token is that token's leaf. -/
theorem eq_leaf_of_getElem? {p : List ℕ} {s : RoseTree Vertex} {tok : LexicalItem.Token}
    (hs : t.val[p]? = some s) (hv : s.value = .lex tok) : s = .node (.lex tok) [] := by
  obtain ⟨a, cs⟩ := s
  obtain rfl : a = .lex tok := hv
  have h := (((isSyntacticObject_mk _).1 t.2).of_getElem? hs).rel_root
  simp only [Vertex.Licenses, Multiset.coe_eq_zero, List.map_eq_nil_iff] at h
  rw [h]

theorem mem_tokenList_iff {p : TreePath} {tok : LexicalItem.Token} :
    (p, tok) ∈ tokenList t.val ↔ t.val[p.toList]? = some (.node (.lex tok) []) := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_positions_iff.2 ⟨_, h, rfl⟩⟩
  obtain ⟨s, hs, hv⟩ := mem_positions_iff.1 h
  have hsv : s.value = .lex tok := by
    rcases h : s.value with (_ | _) | _ <;> simp_all
  rwa [← eq_leaf_of_getElem? hs hsv]

theorem mem_remergedYield (hpick : ∀ l : List TreePath, l ≠ [] → ∃ p ∈ l, pick l = some p)
    {tok : LexicalItem.Token} : tok ∈ remergedYield pick t ↔ ∃ p, (p, tok) ∈ tokenList t.val := by
  simp only [remergedYield, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq]
  refine ⟨fun ⟨x, hx, _, h⟩ ↦ ⟨x.1, h ▸ hx⟩, fun ⟨p, hp⟩ ↦ ?_⟩
  have hs := mem_tokenList_iff.1 hp
  obtain ⟨p', hp', hp's⟩ := exists_spellOutPositionAux hpick (t.val.numNodes + 1) _
    (isSubtree_iff_exists_getElem?.2 ⟨_, hs⟩) (by have := numNodes_pos (t := t.val); omega)
  exact ⟨(p', tok), mem_tokenList_iff.2 hp's, hp', rfl⟩

/-- PF pronounces each token exactly once, whatever the pick. -/
theorem remergedYield_perm_tokens
    (hpick : ∀ l : List TreePath, l ≠ [] → ∃ p ∈ l, pick l = some p) :
    (remergedYield pick t).Perm (tokens t) :=
  (List.perm_ext_iff_of_nodup (nodup_remergedYield pick t) (List.nodup_dedup _)).2 fun tok ↦ by
    simp [mem_remergedYield hpick, List.mem_dedup]

/-! ### Movement -/

theorem mem_mothers {g : RoseTree Vertex} :
    g ∈ mothers t s ↔ IsSubtree g t.val ∧ s ∈ g.children := by
  simp [mothers, mem_subtrees]

/-- Where the mothers of `s` are ordered by dominance and none has `s` as two daughters, `s` has
one candidate at most. -/
theorem eq_of_mem_candidates
    (hchain : ∀ g ∈ mothers t s, ∀ g' ∈ mothers t s, IsSubtree g g' ∨ IsSubtree g' g)
    (hnodup : ∀ g ∈ mothers t s, g.children.Nodup)
    {p q : TreePath} (hp : p ∈ candidates t pos s) (hq : q ∈ candidates t pos s) : p = q := by
  obtain ⟨hps, m, hm, hhm, hposp⟩ := mem_candidates.1 hp
  obtain ⟨hqs, m', hm', hhm', hposq⟩ := mem_candidates.1 hq
  have hmem : ∀ {g : RoseTree Vertex} {r : List ℕ}, t.val[r]? = some g →
      s ∈ g.children → g ∈ mothers t s :=
    fun h hs ↦ mem_mothers.2 ⟨isSubtree_iff_exists_getElem?.2 ⟨_, h⟩, hs⟩
  obtain rfl : m = m' := by
    rcases hchain _ (hmem hm hhm.1) _ (hmem hm' hhm'.1) with h | h
    · exact by_contra fun hne ↦ hhm.2 _ (hmem hm' hhm'.1) ⟨h, hne⟩
    · exact by_contra fun hne ↦ hhm'.2 _ (hmem hm hhm.1) ⟨h, Ne.symm hne⟩
  have hpar : p.parent = q.parent := Option.some.inj (hposp.symm.trans hposq)
  have key : ∀ {r : TreePath}, t.val[r.toList]? = some s →
      t.val[r.parent.toList]? = some m →
      ∃ i, r.toList = r.parent.toList ++ [i] ∧ m.children[i]? = some s := by
    intro r hr hrm
    have hne : r.toList ≠ [] := by
      intro h
      rw [h] at hr
      rw [TreePath.parent, h] at hrm
      obtain rfl := Option.some.inj hr
      obtain rfl := Option.some.inj hrm
      exact lt_irrefl _ (numNodes_lt_of_mem hhm.1)
    refine ⟨r.toList.getLast hne, (List.dropLast_concat_getLast hne).symm, ?_⟩
    have hrm' : t.val[r.toList.dropLast]? = some m := hrm
    rw [← List.dropLast_concat_getLast hne, getElem?_append, hrm'] at hr
    simpa using hr
  obtain ⟨i, hpi, hi⟩ := key hps hm
  obtain ⟨j, hqj, hj⟩ := key hqs hm'
  have hij : i = j :=
    ((hnodup _ (hmem hm hhm.1)).getElem?_inj (List.getElem?_eq_some_iff.1 hi).1).1
      (hi.trans hj.symm)
  exact TreePath.ext (by rw [hpi, hqj, hpar, hij])

/-- Where the mothers of every term are ordered by dominance, as movement leaves them, and no term
is merged with itself, a term is pronounced at the same position whatever the pick. -/
theorem spellOutPositionAux_eq_of_chain {pick' : List TreePath → Option TreePath}
    (hpick : ∀ l : List TreePath, l ≠ [] → ∃ p ∈ l, pick l = some p)
    (hpick' : ∀ l : List TreePath, l ≠ [] → ∃ p ∈ l, pick' l = some p)
    (hchain : ∀ s ∈ t.val.subtrees, ∀ g ∈ mothers t s, ∀ g' ∈ mothers t s,
      IsSubtree g g' ∨ IsSubtree g' g)
    (hself : ∀ g ∈ t.val.subtrees, g.children.Nodup) :
    ∀ (n : ℕ) (s : RoseTree Vertex), IsSubtree s t.val → t.val.numNodes < s.numNodes + n →
      spellOutPositionAux pick t n s = spellOutPositionAux pick' t n s
  | 0, _, _, _ => rfl
  | n + 1, s, hs, hn => by
    simp only [spellOutPositionAux]
    split_ifs with hroot
    · rfl
    rw [candidates_congr (pos' := spellOutPositionAux pick' t n) fun m hm hmt ↦
      spellOutPositionAux_eq_of_chain hpick hpick' hchain hself n m hmt
        (by have := numNodes_lt_of_mem hm.1; omega)]
    have hne := candidates_ne_nil hs hroot fun m hm hlt ↦
      exists_spellOutPositionAux hpick' n m hm (by omega)
    obtain ⟨p, hp, h⟩ := hpick _ hne
    obtain ⟨p', hp', h'⟩ := hpick' _ hne
    rw [h, h', eq_of_mem_candidates (hchain s (mem_subtrees.2 hs))
      (fun g hg ↦ hself g (mem_subtrees.2 (mem_mothers.1 hg).1)) hp hp']

/-- Where movement alone remerges terms, the pronounced tokens do not depend on the pick. -/
theorem remergedYield_eq_of_chain {pick' : List TreePath → Option TreePath}
    (hpick : ∀ l : List TreePath, l ≠ [] → ∃ p ∈ l, pick l = some p)
    (hpick' : ∀ l : List TreePath, l ≠ [] → ∃ p ∈ l, pick' l = some p)
    (hchain : ∀ s ∈ t.val.subtrees, ∀ g ∈ mothers t s, ∀ g' ∈ mothers t s,
      IsSubtree g g' ∨ IsSubtree g' g)
    (hself : ∀ g ∈ t.val.subtrees, g.children.Nodup) :
    remergedYield pick t = remergedYield pick' t :=
  List.filterMap_congr fun x hx ↦ by
    have hs := mem_tokenList_iff.1 hx
    rw [spellOutPosition, spellOutPosition, spellOutPositionAux_eq_of_chain hpick hpick' hchain
      hself _ _ (isSubtree_iff_exists_getElem?.2 ⟨_, hs⟩)
      (by have := numNodes_pos (t := t.val); omega)]

/-! ### Sharing -/

variable (t) in
/-- The positions of `s` in `t`, left to right. -/
def positionsOf (s : RoseTree Vertex) : List TreePath :=
  (t.val.positionedSubtrees.filter (·.2 = s)).map Prod.fst

theorem mem_positionsOf {p : TreePath} :
    p ∈ positionsOf t s ↔ t.val[p.toList]? = some s := by
  simp [positionsOf, mem_positionedSubtrees]

private theorem pairwise_lt_positionsOf :
    (positionsOf t s).Pairwise fun p q ↦ p.toList < q.toList :=
  List.pairwise_map.2 ((pairwise_lt_positionedSubtrees t.val).filter _)

private theorem pairwise_lt_candidates :
    (candidates t pos s).Pairwise fun p q ↦ p.toList < q.toList :=
  List.pairwise_map.2 ((pairwise_lt_positionedSubtrees t.val).filter _)

private theorem pairwise_lt_tokenList :
    (tokenList t.val).Pairwise fun x y ↦ x.1.toList < y.1.toList :=
  (pairwise_lt_positionedSubtrees t.val).filterMap _ fun _ _ h _ ha _ hb ↦ by
    simp only [Option.map_eq_some_iff] at ha hb
    obtain ⟨_, -, rfl⟩ := ha
    obtain ⟨_, -, rfl⟩ := hb
    exact h

/-- In a list of positions increasing left to right, the last is the one no other follows. -/
private theorem getLast?_eq_some_iff_of_pairwise {l : List TreePath}
    (hl : l.Pairwise fun p q ↦ p.toList < q.toList) {x : TreePath} :
    l.getLast? = some x ↔ x ∈ l ∧ ∀ y ∈ l, ¬ x.toList < y.toList := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hmax⟩ ↦ ?_⟩
  · obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 h
    rw [List.pairwise_append] at hl
    refine ⟨List.mem_append_right _ (List.mem_singleton_self _), fun y hy ↦ ?_⟩
    rcases List.mem_append.1 hy with hy | hy
    · exact List.le_of_lt (hl.2.2 y hy x (List.mem_singleton_self _))
    · rw [List.mem_singleton.1 hy]
      exact List.lt_irrefl _
  · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1
      (mt List.getLast?_eq_none_iff.1 (List.ne_nil_of_mem hx))
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hz
    rw [hz]
    rcases List.mem_append.1 hx with hx | hx
    · rw [List.pairwise_append] at hl
      exact absurd (hl.2.2 x hx z (List.mem_singleton_self _))
        (hmax z (List.mem_append_right _ (List.mem_singleton_self _)))
    · rw [List.mem_singleton.1 hx]

/-- Keeping each value at its last position, in a list of positions increasing left to right, keeps
the values `List.dedup` keeps. -/
private theorem filterMap_last_eq_dedup {β : Type*} [DecidableEq β] :
    ∀ {l : List (TreePath × β)}, l.Pairwise (fun x y ↦ x.1.toList < y.1.toList) →
      l.filterMap (fun x ↦
        if ∀ y ∈ l, y.2 = x.2 → ¬ x.1.toList < y.1.toList then some x.2 else none) =
        (l.map Prod.snd).dedup
  | [], _ => rfl
  | x :: rest, hl => by
    rw [List.pairwise_cons] at hl
    have htail : rest.filterMap (fun y ↦
        if ∀ z ∈ x :: rest, z.2 = y.2 → ¬ y.1.toList < z.1.toList then some y.2 else none) =
        rest.filterMap (fun y ↦
          if ∀ z ∈ rest, z.2 = y.2 → ¬ y.1.toList < z.1.toList then some y.2 else none) :=
      List.filterMap_congr fun y hy ↦ if_congr
        (List.forall_mem_cons.trans (and_iff_right fun _ ↦ List.le_of_lt (hl.1 y hy))) rfl rfl
    rw [List.filterMap_cons, htail, filterMap_last_eq_dedup hl.2, List.map_cons]
    by_cases hmem : x.2 ∈ rest.map Prod.snd
    · rw [List.dedup_cons_of_mem hmem]
      split_ifs with h
      · obtain ⟨z, hz, hzx⟩ := List.mem_map.1 hmem
        exact absurd (hl.1 z hz) (h z (List.mem_cons_of_mem _ hz) hzx)
      · rfl
    · rw [List.dedup_cons_of_notMem hmem]
      split_ifs with h
      · rfl
      · refine absurd (List.forall_mem_cons.2 ⟨fun _ ↦ List.lt_irrefl _, fun z hz hzx ↦ ?_⟩) h
        exact absurd (List.mem_map.2 ⟨z, hz, hzx⟩) hmem

/-- Where no mother of a term dominates another, a term pronounced under its highest mother
pronounced last is pronounced at its last position. -/
theorem spellOutPositionAux_getLast?
    (hshare : ∀ s ∈ t.val.subtrees, ∀ g ∈ mothers t s, ∀ g' ∈ mothers t s,
      IsSubtree g g' → g = g') :
    ∀ (n : ℕ) (s : RoseTree Vertex), IsSubtree s t.val → t.val.numNodes < s.numNodes + n →
      spellOutPositionAux List.getLast? t n s = (positionsOf t s).getLast?
  | 0, s, hs, hn => absurd hs.numNodes_le (by omega)
  | n + 1, s, hs, hn => by
    have hO : positionsOf t s ≠ [] := by
      obtain ⟨q, hq⟩ := isSubtree_iff_exists_getElem?.1 hs
      exact List.ne_nil_of_mem ((mem_positionsOf (p := ⟨q⟩)).2 hq)
    have hP := (getLast?_eq_some_iff_of_pairwise pairwise_lt_positionsOf).1
      (List.getLast?_eq_some_getLast hO)
    set P := (positionsOf t s).getLast hO
    have hPs := mem_positionsOf.1 hP.1
    rw [List.getLast?_eq_some_getLast hO, spellOutPositionAux]
    split_ifs with hroot
    · refine congrArg some (TreePath.ext ?_)
      rcases hPl : P.toList with _ | ⟨k, r⟩
      · rfl
      · rw [hPl, hroot] at hPs
        exact absurd (numNodes_lt_of_getElem?_cons hPs) (lt_irrefl _)
    refine (getLast?_eq_some_iff_of_pairwise pairwise_lt_candidates).2
      ⟨?_, fun y hy ↦ hP.2 y (mem_positionsOf.2 (mem_candidates.1 hy).1)⟩
    have hPne : P.toList ≠ [] := fun h ↦ hroot (by rw [h] at hPs; exact (Option.some.inj hPs).symm)
    have hPeq : P.toList = P.parent.toList ++ [P.toList.getLast hPne] :=
      (List.dropLast_concat_getLast hPne).symm
    obtain ⟨m, hm, hms⟩ : ∃ m, t.val[P.parent.toList]? = some m ∧
        m.children[P.toList.getLast hPne]? = some s := by
      rw [hPeq, getElem?_append] at hPs
      obtain ⟨m, hm, hms⟩ := Option.bind_eq_some_iff.1 hPs
      exact ⟨m, hm, by simpa using hms⟩
    have hsm : s ∈ m.children := List.mem_of_getElem? hms
    have hmt : IsSubtree m t.val := isSubtree_iff_exists_getElem?.2 ⟨_, hm⟩
    refine mem_candidates.2 ⟨hPs, m, hm,
      ⟨hsm, fun g hg ⟨hmg, hne⟩ ↦
        hne (hshare s (mem_subtrees.2 hs) m (mem_mothers.2 ⟨hmt, hsm⟩) g hg hmg)⟩, ?_⟩
    rw [spellOutPositionAux_getLast? hshare n m hmt (by have := numNodes_lt_of_mem hsm; omega)]
    refine (getLast?_eq_some_iff_of_pairwise pairwise_lt_positionsOf).2
      ⟨mem_positionsOf.2 hm, fun Q hQ ↦ ?_⟩
    have hQm := mem_positionsOf.1 hQ
    rcases TreePath.Precedes.trichotomy Q P.parent with h | h | h | h
    · exact List.IsPrefix.le h
    · obtain ⟨r, hr⟩ := h
      rcases r with _ | ⟨k, r⟩
      · rw [List.append_nil] at hr
        rw [← hr]
        exact List.lt_irrefl _
      · rw [← hr, getElem?_append, hm, Option.bind_some] at hQm
        exact absurd (numNodes_lt_of_getElem?_cons hQm) (lt_irrefl _)
    · exact List.le_of_lt h.lt
    · have hQs : (⟨Q.toList ++ [P.toList.getLast hPne]⟩ : TreePath) ∈ positionsOf t s :=
        mem_positionsOf.2 (by rw [getElem?_append, hQm]; simpa using hms)
      exact absurd (h.mono (TreePath.parent_le P) (List.prefix_append _ _)).lt (hP.2 _ hQs)

/-- Where no mother of a term dominates another, as sharing leaves them, pronouncing each term under
its highest mother pronounced last pronounces each token at its last occurrence: the tokens
`tokens` keeps, in its order. -/
theorem remergedYield_getLast?_eq_tokens
    (hshare : ∀ s ∈ t.val.subtrees, ∀ g ∈ mothers t s, ∀ g' ∈ mothers t s,
      IsSubtree g g' → g = g') :
    remergedYield List.getLast? t = tokens t := by
  rw [remergedYield, tokens, ← filterMap_last_eq_dedup pairwise_lt_tokenList]
  refine List.filterMap_congr fun x hx ↦ if_congr ?_ rfl rfl
  have hs := mem_tokenList_iff.1 hx
  rw [spellOutPosition, spellOutPositionAux_getLast? hshare _ _
    (isSubtree_iff_exists_getElem?.2 ⟨_, hs⟩) (by have := numNodes_pos (t := t.val); omega),
    getLast?_eq_some_iff_of_pairwise pairwise_lt_positionsOf]
  simp only [mem_positionsOf, ← mem_tokenList_iff]
  exact ⟨fun h y hy hyx ↦ h.2 y.1 (hyx ▸ hy), fun h ↦ ⟨hx, fun y hy ↦ h (y, x.2) hy rfl⟩⟩

end Minimalist
