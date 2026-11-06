/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.AdmissibleCut
public import Linglib.Core.Combinatorics.RootedTree.ContractUnary
public import Linglib.Core.Combinatorics.RootedTree.CutFilterMap
public import Linglib.Core.Data.UnorderedTree.FilterMap
public import Linglib.Syntax.Minimalist.Workspace.Coproduct.Trace

/-!
# The deletion coproduct and the erasure of traces

Marcolli, Chomsky and Berwick extract accessible terms from a syntactic object with three
coproducts, which differ in the remainder an extraction leaves. `Δ^c` contracts each extracted
term to a trace leaf, `Δ^ρ` leaves the remainder of the admissible cut, and `Δ^d` deletes the
term and contracts the vertices left with a single child. They relate the three by projections
of the right channel: `Π_{ρ,c}` deletes the trace leaves, `Π_{d,ρ}` contracts the non-branching
vertices, and `Δ^d = (id ⊗ Π_{d,ρ}) ∘ Δ^ρ = (id ⊗ Π_{d,ρ} ∘ Π_{ρ,c}) ∘ Δ^c`, displayed before
their (1.3.10). Here `Δ^d` is defined by the first expression. The second is
[proved for trees without traces](##contractUnary_eraseTraces_traceComulAlgHom), from
[the same relation between `Δ^c` and `Δ^ρ`](##eraseTraces_traceComulAlgHom). In a full binary tree,
[deleting one accessible term costs two accessible terms besides its own](##deletionCuts_numEdges),
the book's (1.6.7). `Merge/Basic.lean` carries the relations over to Merge.

## Implementation notes

* Trees without traces are `UnorderedTree α` and trees with traces are `UnorderedTree (α ⊕ β)`,
  so the relations hold along the embedding `rename (UnorderedTree.map Sum.inl)`. The left
  channel of `Δ^c` on an embedded tree is embedded and the right channel is not, which is why
  the projections act on the right channel alone.
* The book's `Π_{d,ρ}` takes a tree whose vertices have at most two children to the maximal
  binary tree obtained by contracting edges. Here it is `UnorderedTree.contractUnary`, on trees
  of any arity.
* `Δ^d` carries no `Bialgebra` structure: its coassociativity holds only up to the multiplicity
  of some terms (the book's Lemma 1.2.12).
* (1.6.7) extends to a cut extracting several terms only when no two of them are sisters. A cut
  extracting both children of a vertex leaves it a leaf, with nothing to contract, so the two
  cost one accessible term each (`admissibleCuts_numUnary`).

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### Erasing traces -/

/-- `eraseTraces` is the projection `Π_{ρ,c}`. It sends a tree whose root is a trace to `1` and
    removes from any other tree the subtrees rooted at a trace. -/
noncomputable def eraseTraces :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₐ[R] ConnesKreimer R (UnorderedTree α) :=
  aeval fun T ↦ (T.filterMap Sum.getLeft?).elim 1 ofTree

@[simp] theorem eraseTraces_ofTree (T : UnorderedTree (α ⊕ β)) :
    eraseTraces (R := R) (ofTree T) = (T.filterMap Sum.getLeft?).elim 1 ofTree :=
  aeval_ofTree _ T

/-- Erasure is a retraction of the embedding of the trees without traces. -/
theorem eraseTraces_comp_rename_inl :
    (eraseTraces (R := R) (β := β)).comp (rename (UnorderedTree.map Sum.inl)) =
      AlgHom.id R (ConnesKreimer R (UnorderedTree α)) := by
  ext T
  simp

/-- The trace cuts of a tree without traces are its admissible cuts with a trace leaf left at each
    cut site: the crowns agree, and erasing the trace leaves of a trunk gives the trunk of the
    admissible cut. -/
theorem traceCuts_map_inl (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree α) :
    (traceCuts τ (T.map Sum.inl)).map (Prod.map id (UnorderedTree.filterMap Sum.getLeft?)) =
      (admissibleCuts T).map (Prod.map (Multiset.map (UnorderedTree.map Sum.inl)) some) :=
  Quotient.inductionOn T fun t ↦ by
    have h := map_rootCuts_map (E := leaveTrace (τ ∘ UnorderedTree.mk)) (E' := leaveNothing)
      (g := Sum.inl) (f := Sum.getLeft?) (fun t ↦ by cases t; simp [leaveNothing, traceLeaf]) t
    have h' := congrArg
      (Multiset.map (Prod.map (Multiset.map UnorderedTree.mk) (Option.map UnorderedTree.mk))) h
    simpa [UnorderedTree.map_mk, projCut, Multiset.map_map, Function.comp_def,
      Prod.map_apply'] using h'

/-- On trees without traces, erasing the traces that `Δ^c` leaves in the right channel gives the
    Connes–Kreimer coproduct `Δ^ρ`. -/
theorem eraseTraces_traceComulAlgHom (τ : UnorderedTree (α ⊕ β) → β) :
    ((Algebra.TensorProduct.map (.id R _) eraseTraces).comp (traceComulAlgHom τ)).comp
        (rename (UnorderedTree.map Sum.inl)) =
      (Algebra.TensorProduct.map (rename (UnorderedTree.map Sum.inl)) (.id R _)).comp
        (comulAlgHom (R := R) (α := α)) := by
  ext T
  have h := congrArg (fun s ↦ (s.map fun q : Multiset (UnorderedTree (α ⊕ β)) ×
      Option (UnorderedTree α) ↦ of' (R := R) q.1 ⊗ₜ[R] q.2.elim 1 (ofTree (R := R))).sum)
    (traceCuts_map_inl τ T)
  simp only [Multiset.map_map, Function.comp_def, Prod.map_apply', id, Option.elim_some] at h
  simp [comulTreeOfCuts, map_multiset_sum, Multiset.map_map,
    Function.comp_def, h]

/-! ### The deletion coproduct -/

/-- The deletion coproduct `Δ^d` is the Connes–Kreimer coproduct `Δ^ρ` followed, on the right
    channel, by the contraction `Π_{d,ρ}` of unary vertices. -/
noncomputable def deletionComulAlgHom : ConnesKreimer R (UnorderedTree α) →ₐ[R]
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  (Algebra.TensorProduct.map (.id R _) (rename UnorderedTree.contractUnary)).comp comulAlgHom

/-- The deletion cuts of a tree are its admissible cuts with the unary vertices of each trunk
    contracted. -/
def deletionCuts (T : UnorderedTree α) :
    Multiset (Multiset (UnorderedTree α) × UnorderedTree α) :=
  (admissibleCuts T).map fun p ↦ (p.1, p.2.contractUnary)

/-- On a tree, `Δ^d` sums the deletion cuts. -/
theorem deletionComulAlgHom_apply_ofTree (T : UnorderedTree α) :
    deletionComulAlgHom (R := R) (ofTree T) = ofTree T ⊗ₜ[R] 1 +
      ((deletionCuts T).map fun p ↦ of' (R := R) p.1 ⊗ₜ[R] ofTree p.2).sum := by
  simp [deletionComulAlgHom, deletionCuts, comulTreeOfCuts, map_multiset_sum, Multiset.map_map]

/-- `Δ^d` is the admissible-cut coproduct at the deletion cuts. -/
theorem comulOfCuts_deletionCuts :
    comulOfCuts (R := R) (deletionCuts (α := α)) = deletionComulAlgHom := by
  ext T
  simp [deletionComulAlgHom_apply_ofTree, comulTreeOfCuts]

/-! ### The cost of a deletion -/

section Cost

variable {T : UnorderedTree α} {p : Multiset (UnorderedTree α) × UnorderedTree α}

/-- A deletion cut of a full binary tree extracting at most one tree costs two edges for it
    besides the tree's own. -/
theorem deletionCuts_numEdges_of_card_le_one (hT : T.IsFullBinary)
    (hp : p ∈ deletionCuts T) (h : Multiset.card p.1 ≤ 1) :
    T.numEdges = (p.1.map UnorderedTree.numEdges).sum + p.2.numEdges + 2 * Multiset.card p.1 := by
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  obtain ⟨k, hk⟩ := admissibleCuts_numUnary hT hq
  have := admissibleCuts_numEdges_contractUnary hq
  dsimp only at h ⊢
  omega

/-- Deleting one accessible term costs two accessible terms besides its own
    ([marcolli-chomsky-berwick-2025] (1.6.7)). -/
theorem deletionCuts_numEdges (hT : T.IsFullBinary) (hp : p ∈ deletionCuts T)
    {v : UnorderedTree α} (hv : p.1 = {v}) : T.numEdges = v.numEdges + p.2.numEdges + 2 := by
  simpa [hv] using deletionCuts_numEdges_of_card_le_one hT hp (by simp [hv])

/-- A choice of deletion cuts of full binary trees, extracting at most one tree from each tree it
    cuts, costs two edges for each tree it extracts. -/
theorem hasExtractionCost_numEdges_deletionCuts {F : Multiset (UnorderedTree α)}
    {s : CutChoice α} (hF : ∀ T ∈ F, T.IsFullBinary) (hs : s ∈ forestCutChoices deletionCuts F)
    (h : ∀ x ∈ s, x.2.2 ≠ 0 → Multiset.card x.2.1 ≤ 1) :
    s.HasExtractionCost UnorderedTree.numEdges 2 :=
  .of_mem_forestCutChoices hs fun x hx p hp hpx ↦
    deletionCuts_numEdges_of_card_le_one (hF x.1 (fst_mem_of_mem_forestCutChoices hs hx)) hp <| by
      have := h x hx (by rw [← hpx]; exact Multiset.singleton_ne_zero _)
      rwa [← hpx] at this

end Cost

/-- On trees without traces, erasing the traces that `Δ^c` leaves and contracting the unary
    vertices gives the deletion coproduct `Δ^d`. -/
theorem contractUnary_eraseTraces_traceComulAlgHom (τ : UnorderedTree (α ⊕ β) → β) :
    ((Algebra.TensorProduct.map (.id R _)
          ((rename UnorderedTree.contractUnary).comp eraseTraces)).comp (traceComulAlgHom τ)).comp
        (rename (UnorderedTree.map Sum.inl)) =
      (Algebra.TensorProduct.map (rename (UnorderedTree.map Sum.inl)) (.id R _)).comp
        (deletionComulAlgHom (R := R) (α := α)) := by
  have h := congrArg
    (AlgHom.comp (Algebra.TensorProduct.map (.id R _) (rename UnorderedTree.contractUnary)))
    (eraseTraces_traceComulAlgHom (R := R) τ)
  simpa only [deletionComulAlgHom, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    AlgHom.comp_id, AlgHom.id_comp] using h

end ConnesKreimer
