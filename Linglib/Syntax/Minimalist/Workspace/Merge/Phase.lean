/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Merge.Internal
public import Linglib.Syntax.Minimalist.Phase.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Tree

/-!
# Merge at a restricted coproduct

A condition on what Merge may extract is a restriction of the coproduct. For a relation `C` between
a tree and its accessible terms, `restrictCuts C cuts` keeps the cuts of `cuts` every tree of whose
crown satisfies `C`, so that the coproduct sums over fewer terms. Restricted cuts still admit
Merge, and the unit stage of Internal Merge vanishes on a tree whose mover fails `C`
(`mergeOpUnitOfCuts_restrictCuts_eq_zero`): a movement the condition excludes is not a term of the
coproduct.

Marcolli, Chomsky and Berwick read Phase Theory this way. Their phase coproduct (Definition 1.14.5)
extracts the accessible terms that are not in the interior of a lower phase, here `phaseCuts`, the
restriction of a cut enumeration to the terms that are not `SyntacticObject.Inaccessible`.

## TODO

* The phase coproduct is coassociative (their Lemma 1.14.6), its terms being those of the trace
  coproduct on the tree whose lower phase interiors are cut off.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}
  {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}

/-- The cuts of `T` every tree of whose crown satisfies `C` in `T`. -/
def restrictCuts (C : UnorderedTree α → UnorderedTree α → Prop) [∀ T, DecidablePred (C T)]
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (T : UnorderedTree α) : Multiset (Forest (UnorderedTree α) × UnorderedTree α) :=
  (cuts T).filter fun p ↦ ∀ x ∈ p.1, C T x

section

variable {C : UnorderedTree α → UnorderedTree α → Prop} [∀ T, DecidablePred (C T)]
  {T β : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α}

theorem mem_restrictCuts : p ∈ restrictCuts C cuts T ↔ p ∈ cuts T ∧ ∀ x ∈ p.1, C T x :=
  Multiset.mem_filter

theorem restrictCuts_le : restrictCuts C cuts T ≤ cuts T := Multiset.filter_le _ _

/-- Cuts restricted by a condition on what is extracted still admit Merge. -/
instance [h : IsMergeCuts cuts] : IsMergeCuts (restrictCuts C cuts) where
  crown_numEdges_lt hp := h.crown_numEdges_lt (mem_restrictCuts.1 hp).1
  mem_subtrees_of_mem_crown hp := h.mem_subtrees_of_mem_crown (mem_restrictCuts.1 hp).1
  filter_empty T := by
    rw [restrictCuts, Multiset.filter_filter, ← h.filter_empty T]
    refine Multiset.filter_congr fun p _ ↦ ⟨fun hp ↦ hp.1, fun hp ↦ ⟨hp, fun x hx ↦ ?_⟩⟩
    rw [Multiset.card_eq_zero.1 hp] at hx
    exact absurd hx (Multiset.notMem_zero x)

/-- The unit stage of Internal Merge at restricted cuts vanishes on a tree in which the mover does
not satisfy the condition. -/
theorem mergeOpUnitOfCuts_restrictCuts_eq_zero [DecidableEq (UnorderedTree α)] (hne : T ≠ β)
    (h : ¬ C T β) : mergeOpUnitOfCuts (R := R) (restrictCuts C cuts) β (of' {T}) = 0 := by
  rw [mergeOpUnitOfCuts_apply_singleton, ite_eq_right hne, zero_add]
  refine Multiset.sum_eq_zero fun y hy ↦ ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
  refine ite_eq_right fun hp1 ↦ h ((mem_restrictCuts.1 hp).2 β ?_)
  rw [hp1]
  exact Multiset.mem_singleton_self β

end

/-! ### The phase coproduct -/

open SyntacticObject

variable {P : LexicalItem.Token → Prop}
  {cuts : UnorderedTree Vertex → Multiset (Forest (UnorderedTree Vertex) × UnorderedTree Vertex)}

open Classical in
/-- The cuts of the phase coproduct, with `P` the phase heads: those of `cuts` that extract no term
in the interior of a lower phase. -/
noncomputable def phaseCuts (P : LexicalItem.Token → Prop)
    (cuts : UnorderedTree Vertex →
      Multiset (Forest (UnorderedTree Vertex) × UnorderedTree Vertex)) :
    UnorderedTree Vertex → Multiset (Forest (UnorderedTree Vertex) × UnorderedTree Vertex) :=
  restrictCuts (fun T x ↦ ∀ T' x' : SyntacticObject, T'.toUnorderedTree = T →
    x'.toUnorderedTree = x → ¬ T'.Inaccessible P x') cuts

instance [IsMergeCuts cuts] : IsMergeCuts (phaseCuts P cuts) := by
  unfold phaseCuts; infer_instance

open Classical in
/-- The unit stage of Internal Merge at the phase coproduct vanishes on an inaccessible mover: a
term in the interior of a lower phase does not move. -/
theorem mergeOpUnitOfCuts_phaseCuts_eq_zero {T x : SyntacticObject} (hne : T ≠ x)
    (h : T.Inaccessible P x) :
    mergeOpUnitOfCuts (R := R) (phaseCuts P cuts) x.toUnorderedTree (of' {T.toUnorderedTree}) = 0 :=
  mergeOpUnitOfCuts_restrictCuts_eq_zero (fun he ↦ hne (toUnorderedTree_injective he))
    fun hC ↦ hC T x rfl rfl h

end Minimalist.Merge
