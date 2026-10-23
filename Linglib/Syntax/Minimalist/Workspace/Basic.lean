/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Syntax.Minimalist.SyntacticObject.Term
public import Mathlib.Data.Multiset.Bind

/-!
# Workspaces

A workspace is a forest, a finite multiset, of syntactic objects. MERGE applies to a workspace: it
takes two of its terms, `P` and `Q`, and returns the workspace with `{P, Q}` added, and with `P`
and `Q` removed where they were members. External Merge merges two members, Internal Merge a member
with one of its terms, and Parallel, Sideward, Late and Countercyclic Merge are the other places
the two may come from. Whatever MERGE does, the terms of the workspace stay terms of it
(`Workspace.terms_subset_terms_merge`). The forest product is disjoint union, so a workspace is
what `of'` lifts into the Hopf algebra `ConnesKreimer ℤ (UnorderedTree Vertex)`, where the Merge
operator of `Workspace/Algebra/` computes MERGE (`SyntacticObject.mergeOpC_of'_merge`,
`SyntacticObject.mergeOpC_im_of'_merge`).

## Main definitions

* `Minimalist.Workspace`: forests of syntactic objects.
* `Minimalist.Workspace.terms`, `Minimalist.Workspace.merge`: the terms of a workspace, and MERGE.

## Main results

* `Minimalist.Workspace.terms_subset_terms_merge`: Preservation of Terms.

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

/-- MERGE `P` and `Q` in `W`: `{P, Q}` joins the workspace, and `P` and `Q` leave it where they
were members, the rest carried over. -/
noncomputable def merge : Workspace := W - {P, Q} + {SyntacticObject.merge P Q}

/-- Preservation of Terms: every term of a workspace is a term of the workspace MERGE makes. -/
theorem terms_subset_terms_merge : W.terms ⊆ (W.merge P Q).terms := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Multiset.mem_bind.1 hx
  simp only [terms, merge, Multiset.add_bind, Multiset.singleton_bind, Multiset.mem_add]
  rcases Multiset.mem_add.1 (Multiset.mem_of_le le_add_tsub hs) with h | h
  · refine .inr ?_
    rw [terms_merge]
    rcases Multiset.mem_cons.1 h with h | h
    · rw [h] at hxs
      exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl hxs))
    · rw [Multiset.mem_singleton.1 h] at hxs
      exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr hxs))
  · exact .inl (Multiset.mem_bind.2 ⟨s, h, hxs⟩)

end Workspace

end Minimalist
