/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Syntax.Minimalist.SyntacticObject.Replace
public import Mathlib.Data.Multiset.Bind

/-!
# Workspaces

A workspace is a forest, a finite multiset, of syntactic objects. MERGE applies to a workspace: it
takes two of its terms, `P` and `Q`, and returns the workspace with `{P, Q}` added, and with `P`
and `Q` removed where they were members. External Merge merges two members, Internal Merge a member
with one of its terms, and Parallel, Sideward, Late and Countercyclic Merge are the other places
the two may come from. `mergeWith leave` is MERGE leaving `leave P` and `leave Q` at the other
occurrences of the targets, substituted simultaneously, and `merge`, leaving copies, is its case
`leave = id`; MERGE leaving copies keeps every term of the workspace
(`Workspace.terms_subset_terms_merge`). The forest product is disjoint union, so a workspace is
what `of'` lifts into the Hopf algebra `ConnesKreimer ℤ (UnorderedTree Vertex)`, where the Merge
operator of `Workspace/Algebra/` computes MERGE leaving traces on Internal and Sideward Merge
(`SyntacticObject.mergeOpC_im_of'_merge`, `SyntacticObject.mergeOpC_sideward2b_of'_merge`).

## Main definitions

* `Minimalist.Workspace`: forests of syntactic objects.
* `Minimalist.Workspace.terms`: the terms of a workspace.
* `Minimalist.Workspace.mergeWith`, `Minimalist.Workspace.merge`: MERGE leaving what a function
  gives, and leaving copies.

## Main results

* `Minimalist.Workspace.merge_def`: MERGE leaving copies.
* `Minimalist.Workspace.terms_subset_terms_merge`: Preservation of Terms.
* `Minimalist.Workspace.mergeWith_internal`, `mergeWith_sideward_member`, `mergeWith_sideward`:
  Internal Merge and Sideward Merge.

## References

* [marcolli-chomsky-berwick-2025], §1.2 (Definition 1.2.1)
* [kitahara-seely-2026]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-- A workspace is a forest of syntactic objects. -/
abbrev Workspace : Type := Forest SyntacticObject

namespace Workspace

variable (W : Workspace) (P Q : SyntacticObject)

/-- The terms of a workspace are the terms of its members, the objects MERGE may target. -/
def terms : Multiset SyntacticObject := W.bind SyntacticObject.terms

theorem mem_terms {W : Workspace} {S : SyntacticObject} : S ∈ W.terms ↔ ∃ U ∈ W, S ∈ U.terms :=
  Multiset.mem_bind

/-- The substitution contracting the targets `P` and `Q` of MERGE to what they leave behind. -/
def contraction (leave : SyntacticObject → SyntacticObject) (P Q u : SyntacticObject) :
    Option SyntacticObject :=
  if u = P then some (leave P) else if u = Q then some (leave Q) else none

/-- MERGE `P` and `Q` in `W`, leaving `leave P` and `leave Q` behind: `{P, Q}` joins the
workspace, `P` and `Q` leave it where they were members, and their other occurrences, in the rest
and in each other, are replaced by what they leave. -/
noncomputable def mergeWith (leave : SyntacticObject → SyntacticObject) (W : Workspace)
    (P Q : SyntacticObject) : Workspace :=
  (W - {P, Q}).map (subst (contraction leave P Q)) +
    {SyntacticObject.merge (P.replace Q (leave Q)) (Q.replace P (leave P))}

/-- MERGE `P` and `Q` in `W` leaving copies. -/
noncomputable def merge : Workspace := W.mergeWith id P Q

variable {W P Q} {leave : SyntacticObject → SyntacticObject} {U : SyntacticObject}

theorem subst_contraction_of_notMem (hP : P ∉ U.terms) (hQ : Q ∉ U.terms) :
    U.subst (contraction leave P Q) = U :=
  subst_eq_self fun u hu r hr ↦ by
    rw [contraction, ite_eq_right fun h : u = P ↦ hP (h ▸ hu),
      ite_eq_right fun h : u = Q ↦ hQ (h ▸ hu)] at hr
    cases hr

theorem subst_contraction_of_notMem_right (hQ : Q ∉ U.terms) :
    U.subst (contraction leave P Q) = U.replace P (leave P) :=
  subst_congr fun u hu ↦ by
    simp only [contraction, ite_eq_right fun h : u = Q ↦ hQ (h ▸ hu)]

theorem subst_contraction_of_notMem_left (hP : P ∉ U.terms) :
    U.subst (contraction leave P Q) = U.replace Q (leave Q) :=
  subst_congr fun u hu ↦ by
    rw [contraction, ite_eq_right fun h : u = P ↦ hP (h ▸ hu)]

@[simp] theorem subst_contraction_id : U.subst (contraction id P Q) = U :=
  subst_eq_self fun u _ r hr ↦ by
    unfold contraction at hr
    split_ifs at hr with h h' <;> cases hr
    exacts [h.symm, h'.symm]

theorem merge_def : W.merge P Q = W - {P, Q} + {SyntacticObject.merge P Q} := by
  rw [merge, mergeWith, id, id, replace_self_self, replace_self_self,
    Multiset.map_congr rfl fun U _ ↦ subst_contraction_id, Multiset.map_id']

/-- Preservation of Terms: every term of a workspace is a term of the workspace MERGE makes. -/
theorem terms_subset_terms_merge : W.terms ⊆ (W.merge P Q).terms := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Multiset.mem_bind.1 hx
  simp only [terms, merge_def, Multiset.add_bind, Multiset.singleton_bind, Multiset.mem_add]
  rcases Multiset.mem_add.1 (Multiset.mem_of_le le_add_tsub hs) with h | h
  · refine .inr ?_
    rw [terms_merge]
    rcases Multiset.mem_cons.1 h with h | h
    · rw [h] at hxs
      exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl hxs))
    · rw [Multiset.mem_singleton.1 h] at hxs
      exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr hxs))
  · exact .inl (Multiset.mem_bind.2 ⟨s, h, hxs⟩)

/-! ### Internal and Sideward Merge -/

private theorem map_subst_contraction {W : Workspace} (hW : ∀ U ∈ W, P ∉ U.terms ∧ Q ∉ U.terms) :
    W.map (subst (contraction leave P Q)) = W := by
  conv_rhs => rw [← Multiset.map_id W]
  exact Multiset.map_congr rfl fun U hU ↦ subst_contraction_of_notMem (hW U hU).1 (hW U hU).2

theorem mergeWith_internal {mover current : SyntacticObject} {W : Workspace}
    (hmc : mover ∈ current.terms) (hne : current ≠ mover) (hW : ∀ U ∈ W, mover ∉ U.terms) :
    ({current} + W).mergeWith leave mover current =
      W + {SyntacticObject.merge mover (current.replace mover (leave mover))} := by
  have hmW : mover ∉ W := fun h ↦ hW mover h (self_mem_terms mover)
  have hcm : current ∉ mover.terms := fun h ↦ hne (mem_terms_antisymm h hmc)
  rw [mergeWith, Multiset.insert_eq_cons, Multiset.sub_cons,
    Multiset.erase_of_notMem (by simpa [Ne.symm hne] using hmW), add_tsub_cancel_left,
    map_subst_contraction fun U hU ↦ ⟨hW U hU, fun h ↦ hW U hU (terms_subset_terms
      (SyntacticObject.mem_terms.1 h) hmc)⟩, replace_of_notMem_terms hcm]

theorem mergeWith_sideward_member {T T' S' : SyntacticObject} {W : Workspace}
    (hS' : S' ∈ T'.terms) (hne : T' ≠ S') (hT : T ∉ T'.terms) (hS'T : S' ∉ T.terms)
    (hW : ∀ U ∈ W, T ∉ U.terms ∧ S' ∉ U.terms) :
    ({T, T'} + W).mergeWith leave T S' =
      {T'.replace S' (leave S')} + W + {SyntacticObject.merge T S'} := by
  have hS'W : S' ∉ W := fun h ↦ (hW S' h).2 (self_mem_terms S')
  have hTS' : T ∉ S'.terms := fun h ↦ hT (terms_subset_terms (SyntacticObject.mem_terms.1 hS') h)
  have hS'm : S' ∉ ({T'} + W : Workspace) := by simpa [Ne.symm hne] using hS'W
  rw [mergeWith, Multiset.insert_eq_cons T ({S'} : Workspace), Multiset.sub_cons,
    Multiset.sub_singleton, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.erase_cons_head,
    Multiset.erase_of_notMem hS'm, Multiset.map_add,
    Multiset.map_singleton, subst_contraction_of_notMem_left hT, map_subst_contraction hW,
    replace_of_notMem_terms hS'T, replace_of_notMem_terms hTS']

theorem mergeWith_sideward {T T' S S' : SyntacticObject} {W : Workspace} (hS : S ∈ T.terms)
    (hS' : S' ∈ T'.terms) (hneS : T ≠ S) (hneS' : T' ≠ S') (hST' : S ∉ T'.terms)
    (hS'T : S' ∉ T.terms) (hW : ∀ U ∈ W, S ∉ U.terms ∧ S' ∉ U.terms) :
    ({T, T'} + W).mergeWith leave S S' =
      {T.replace S (leave S), T'.replace S' (leave S')} + W + {SyntacticObject.merge S S'} := by
  have hSW : S ∉ W := fun h ↦ (hW S h).1 (self_mem_terms S)
  have hS'W : S' ∉ W := fun h ↦ (hW S' h).2 (self_mem_terms S')
  have hT'S : T' ≠ S := fun h ↦ hST' (h ▸ self_mem_terms T')
  have hTS' : T ≠ S' := fun h ↦ hS'T (h ▸ self_mem_terms T)
  have hSS' : S ∉ S'.terms := fun h ↦ hST' (terms_subset_terms (SyntacticObject.mem_terms.1 hS') h)
  have hS'S : S' ∉ S.terms := fun h ↦ hS'T (terms_subset_terms (SyntacticObject.mem_terms.1 hS) h)
  have hSm : S ∉ ({T, T'} + W : Workspace) := by simp [Ne.symm hneS, Ne.symm hT'S, hSW]
  have hS'm : S' ∉ ({T, T'} + W : Workspace) := by simp [Ne.symm hTS', Ne.symm hneS', hS'W]
  have hrem : ({T, T'} + W) - {S, S'} = {T, T'} + W := by
    rw [Multiset.insert_eq_cons S, Multiset.sub_cons, Multiset.sub_singleton,
      Multiset.erase_of_notMem hSm, Multiset.erase_of_notMem hS'm]
  rw [mergeWith, hrem, Multiset.map_add, map_subst_contraction hW, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, subst_contraction_of_notMem_right hS'T,
    subst_contraction_of_notMem_left hST', replace_of_notMem_terms hS'S,
    replace_of_notMem_terms hSS', ← Multiset.insert_eq_cons]

end Workspace

end Minimalist
