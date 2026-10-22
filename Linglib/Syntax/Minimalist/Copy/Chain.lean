/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Projection
public import Linglib.Core.Data.RoseTree.Get

/-!
# Chains on linearized syntactic objects

A linearized syntactic object is a copy-theoretic representation. A vertex `Vertex.lex tok` is a
pronounced copy of `tok` and a vertex `Vertex.traceOf tok` a deleted one, the trace Internal Merge
leaves, Marcolli, Chomsky and Berwick's cancellation `T/T_v` with the head of `T_v` remembered.
The chain of a token is the list of its copies, and a copy stands for the maximal projection of
its token, so a moved phrase sits where its head projects. A token moves when it has a deleted
copy. A token bound in situ by an operator, as for Pesetsky, has a single copy. A deleted copy
above the pronounced one is Huang's covert movement, and a pronounced copy between two deleted
ones is Sato and Ngui's partial movement, so where a phrase is pronounced and where it takes scope
come apart without a separate choice of the copy to spell out. A token with two pronounced copies
is shared, dominated by two mothers, Citko's Parallel Merge.

A copy is linked to the nearest copy above it, the one whose projection c-commands it with no
other copy's projection in between, c-command being Reinhart's (`RoseTree.CCommands`).
A token with one copy has no link (`links_eq_nil_of_length_le_one`). The locality conditions on
links are in `SyntacticObject/Locality.lean`.

## Main definitions

* `Minimalist.tokenList`, `Minimalist.traceList`: the pronounced and the deleted copies.
* `occurrences`, `traces`, `chain`, `Moves`, `IsShared`: the copies of a token.
* `projectionAt`: the phrase a copy stands for, its maximal projection along head daughters
  (`LinearizedSyntacticObject.headIndexAt`, `PhraseStructure.maximalProjectionAt`).
* `complement`: the sister of a head, the positions below which it c-commands
  (`mem_cCommandDomain_iff_complement_le`).
* `HasAntecedent`, `orphanTraces`: whether a pronounced copy c-commands a deleted one, and the
  deleted copies without antecedents, seen from their own conjunct copies.
* `IsLink`, `links`, `chainTop`: the links of a chain and its scope position.

## Implementation notes

* Positions, not terms, individuate copies: two deleted copies of one token are the same term.
* The head daughters follow the raising head, and the drawing convention only where it is
  undefined (`headIndex?`, `SyntacticObject/Position.lean`), so that a phrase with a specifier
  merged in place still has a maximal projection to locate a copy in.
* A chain here is the copies an object contains; the replay of a derivation
  (`Derivation.externalize?`) builds overt chains, while covert movement and sharing are available
  to the representation only. Remnant movement carries a deleted copy away from its antecedent,
  so an externalized object can have orphan traces.

## TODO

* Chains on the copy object of `Derivation.replayWithCopies?` (`Copy/Replay.lean`), the
  positions holding one term, with the token chains here as their case without remnant movement.

## References

* [marcolli-chomsky-berwick-2025]
* [citko-2005]
* [pesetsky-1987]
* [huang-1982]
* [sato-ngui-2017]
* [barker-pullum-1990]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

/-! ### Copies -/

/-- The positions of `t` whose label `f` accepts, with the values, in preorder. -/
def positions {β : Type*} (f : Vertex → Option β) (t : RoseTree Vertex) : List (TreePath × β) :=
  t.positionedSubtrees.filterMap fun x ↦ (f x.2.value).map (x.1, ·)

theorem mem_positions_iff {β : Type*} {f : Vertex → Option β} {t : RoseTree Vertex}
    {p : TreePath} {b : β} :
    (p, b) ∈ positions f t ↔ ∃ s, subtreeAt t p.toList = some s ∧ f s.value = some b := by
  simp only [positions, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists,
    mem_positionedSubtrees]
  exact ⟨fun ⟨_, s, hs, _, hb, rfl, rfl⟩ ↦ ⟨s, hs, hb⟩,
    fun ⟨s, hs, hb⟩ ↦ ⟨p, s, hs, b, hb, rfl, rfl⟩⟩

theorem nodup_map_fst_positions {β : Type*} (f : Vertex → Option β) (t : RoseTree Vertex) :
    ((positions f t).map Prod.fst).Nodup := by
  rw [positions, List.map_filterMap]
  refine (List.pairwise_map.1 t.nodup_map_fst_positionedSubtrees).filterMap _
    fun _ _ hne b hb b' hb' ↦ ?_
  simp only [Option.map_map, Function.comp_def, Option.map_eq_some_iff] at hb hb'
  obtain ⟨-, -, rfl⟩ := hb
  obtain ⟨-, -, rfl⟩ := hb'
  exact hne

/-- The pronounced copies, left to right. -/
def tokenList : RoseTree Vertex → List (TreePath × LexicalItem.Token) :=
  positions (Sum.elim id fun _ ↦ none)

/-- The deleted copies, left to right. -/
def traceList : RoseTree Vertex → List (TreePath × LexicalItem.Token) :=
  positions (Sum.elim (fun _ ↦ none) id)

variable (t : LinearizedSyntacticObject) (tok : LexicalItem.Token)

/-- The positions of the pronounced copies of `tok`. -/
def occurrences : List TreePath :=
  (tokenList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The positions of the deleted copies of `tok`. -/
def traces : List TreePath :=
  (traceList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The chain of `tok` lists the positions of its copies, pronounced or deleted, left to right. -/
def chain : List TreePath :=
  (positions (Sum.elim id id) t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- `tok` moves when it has a deleted copy. -/
def Moves : Prop := traces t tok ≠ []

instance : Decidable (Moves t tok) := inferInstanceAs (Decidable (_ ≠ _))

/-- `tok` is shared, dominated by two mothers, when it has two pronounced copies. -/
def IsShared : Prop := 2 ≤ (occurrences t tok).length

instance : Decidable (IsShared t tok) := inferInstanceAs (Decidable (_ ≤ _))

/-! ### The phrase a copy stands for -/

/-- The maximal projection of the copy at `p` is the highest position reached from `p` by
climbing while the position is the head daughter of its mother. -/
def projectionAt (p : TreePath) : TreePath :=
  maximalProjectionAt t.headIndexAt p

/-- The complement of the head at `p` is its sister. -/
def complement (p : TreePath) : TreePath := ⟨p.toList.dropLast ++ [1 - p.toList.getLastD 0]⟩

/-- The mother of a position is covered by its complement. -/
theorem parent_covBy_complement (p : TreePath) : p.parent ⋖ complement p :=
  TreePath.covBy_iff.2 ⟨_, rfl⟩

variable {t} in
/-- In a syntactic object, a head other than the root c-commands exactly the positions below its
complement. -/
theorem mem_cCommandDomain_iff_complement_le {h q : TreePath} (hh : h ∈ t.val.validPaths)
    (h0 : h ≠ ⊥) (hq : q ∈ t.val.validPaths) :
    q ∈ t.val.cCommandDomain h ↔ complement h ≤ q := by
  set hp : t.val.Positions := ⟨h, hh⟩
  have hp0 : hp ≠ ⊥ := fun he ↦ h0 (congrArg Subtype.val he)
  have hm : Order.pred hp ⋖ hp :=
    Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using hp0)
  have hmv : (Order.pred hp).val = h.parent := Positions.pred_val hp
  have hlen := LinearizedSyntacticObject.length_children_subtree (not_isMax_of_lt hm.lt)
  have hcv : complement h ∈ t.val.validPaths := by
    refine mem_validPaths_append_singleton_iff.2 ⟨(Order.pred hp).subtree, ?_, ?_⟩
    · rw [← TreePath.parent_toList, ← hmv]
      exact (Order.pred hp).subtreeAt_eq
    · rw [hlen]
      omega
  set hc : t.val.Positions := ⟨complement h, hcv⟩
  have hmc : Order.pred hp ⋖ hc :=
    Positions.covBy_iff.2 (hmv ▸ parent_covBy_complement h)
  have hhc : hp ≠ hc := fun he ↦ by
    have := congrArg (fun r : t.val.Positions ↦ r.val.toList.getLastD 0) he
    simp only [hp, hc, complement, List.getLastD_concat] at this
    omega
  rw [RoseTree.mem_cCommandDomain, cCommands_iff_parent_lt h0
    (LinearizedSyntacticObject.isBranchingAt_parent (t := t) hp0)]
  set qp : t.val.Positions := ⟨q, hq⟩
  constructor
  · rintro ⟨hlt, hnl⟩
    obtain ⟨e, hme, heq⟩ := exists_covBy_le_of_lt
      (show Order.pred hp < qp from Subtype.coe_lt_coe.1 (hmv ▸ hlt))
    rcases LinearizedSyntacticObject.eq_or_eq_of_covBy hm hmc hhc hme with rfl | rfl
    · exact absurd heq hnl
    · exact heq
  · intro hcq
    refine ⟨(parent_covBy_complement h).lt.trans_le hcq, fun hhq ↦ hhc (Subtype.ext ?_)⟩
    exact IsLeftLinear.eq_of_covBy_of_le (Positions.covBy_iff.1 hm) (Positions.covBy_iff.1 hmc)
      hhq hcq

theorem projectionAt_le (p : TreePath) : projectionAt t p ≤ p := maximalProjectionAt_le _ p

/-- A deleted copy has an antecedent when the projection of a pronounced copy of its token
c-commands it. -/
def HasAntecedent (x : TreePath × LexicalItem.Token) : Prop :=
  ∃ p ∈ occurrences t x.2, CCommands t.val (projectionAt t p) x.1

instance (x : TreePath × LexicalItem.Token) : Decidable (HasAntecedent t x) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The deleted copies without antecedents. -/
def orphanTraces : List (TreePath × LexicalItem.Token) :=
  (traceList t.val).filter (¬ HasAntecedent t ·)

/-! ### Links -/

/-- The copy at `p` is linked to the copy at `q` below it when its projection c-commands `q` and
the projection of no other copy of `tok` lies between them. -/
def IsLink (p q : TreePath) : Prop :=
  CCommands t.val (projectionAt t p) q ∧
    ∀ r ∈ chain t tok, CCommands t.val (projectionAt t p) (projectionAt t r) →
      ¬ CCommands t.val (projectionAt t r) q

instance (p q : TreePath) : Decidable (IsLink t tok p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The links of the chain of `tok` pair each copy with the projection of the copy linked to it. -/
def links : List (TreePath × TreePath) :=
  (chain t tok).flatMap fun q ↦
    ((chain t tok).filter fun p ↦ IsLink t tok p q).map fun p ↦ (projectionAt t p, q)

/-- The top of the chain of `tok` consists of the copies no copy's projection c-commands, where it
takes scope. -/
def chainTop : List TreePath :=
  (chain t tok).filter fun q ↦ (chain t tok).all fun p ↦ ¬ CCommands t.val (projectionAt t p) q

theorem not_isLink_self (p : TreePath) : ¬ IsLink t tok p p :=
  fun h ↦ h.1.2.1 (projectionAt_le t p)

/-- A token with at most one copy has no link. -/
theorem links_eq_nil_of_length_le_one (h : (chain t tok).length ≤ 1) : links t tok = [] := by
  simp only [links, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq]
  intro q hq p hp
  obtain rfl : p = q := by
    rcases hc : chain t tok with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [hc] at hp
    · simp only [hc, List.mem_singleton] at hp hq
      rw [hp, hq]
    · simp [hc] at h
  exact not_isLink_self t tok p


end Minimalist
