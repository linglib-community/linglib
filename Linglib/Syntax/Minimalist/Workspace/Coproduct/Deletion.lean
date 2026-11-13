/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.AdmissibleCut
public import Linglib.Core.Combinatorics.RootedTree.ContractUnary
public import Linglib.Core.Combinatorics.RootedTree.CutFilterMap
public import Linglib.Core.Combinatorics.RootedTree.CutPrune
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

/-! ### The deletion coproduct

The remainder of a deletion is the trunk of the admissible cut restricted to its leaves: a vertex
whose children the cut all removed is no leaf of the tree, and goes with them. The label `b` is
that of the vertices with children, the one Merge gives a new root. -/

section Deletion

variable [DecidableEq α] (b : α)

/-- The remainder `T /^d F` of a deletion ([marcolli-chomsky-berwick-2025] Definition 1.2.5), from
    the trunk `T` of the admissible cut: the vertices above one not labelled `b`, with the unary
    vertices contracted. It is `none` when the cut leaves no leaf. -/
def deletionQuotient (T : UnorderedTree α) : Option (UnorderedTree α) :=
  (T.prune (· ≠ b)).map UnorderedTree.contractUnary

/-- A tree whose leaves are not labelled `b` has nothing to prune. -/
theorem deletionQuotient_eq_some {T : UnorderedTree α} (h : ∀ a ∈ T.leaves, a ≠ b) :
    deletionQuotient b T = some T.contractUnary := by
  rw [deletionQuotient, UnorderedTree.prune_eq_some_self _ h, Option.map_some]

/-- The projection `Π_{d,ρ}` of the right channel: a tree goes to the remainder of its deletion,
    and to `1` when nothing remains. -/
noncomputable def deletionProj :
    ConnesKreimer R (UnorderedTree α) →ₐ[R] ConnesKreimer R (UnorderedTree α) :=
  aeval fun T ↦ (deletionQuotient b T).elim 1 ofTree

@[simp] theorem deletionProj_ofTree (T : UnorderedTree α) :
    deletionProj (R := R) b (ofTree T) = (deletionQuotient b T).elim 1 ofTree :=
  aeval_ofTree _ T

/-- The deletion coproduct `Δ^d` is the Connes–Kreimer coproduct `Δ^ρ` followed, on the right
    channel, by the projection `Π_{d,ρ}`. -/
noncomputable def deletionComulAlgHom : ConnesKreimer R (UnorderedTree α) →ₐ[R]
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  (Algebra.TensorProduct.map (.id R _) (deletionProj b)).comp comulAlgHom

/-- The deletion cuts of a tree are its admissible cuts, each with the remainder of its trunk. -/
def deletionCuts (T : UnorderedTree α) :
    Multiset (Multiset (UnorderedTree α) × Option (UnorderedTree α)) :=
  (admissibleCuts T).map fun p ↦ (p.1, deletionQuotient b p.2)

/-- On a tree, `Δ^d` sums the deletion cuts. -/
theorem deletionComulAlgHom_apply_ofTree (T : UnorderedTree α) :
    deletionComulAlgHom (R := R) b (ofTree T) = ofTree T ⊗ₜ[R] 1 +
      ((deletionCuts b T).map fun p ↦ of' (R := R) p.1 ⊗ₜ[R] p.2.elim 1 ofTree).sum := by
  simp [deletionComulAlgHom, deletionCuts, comulTreeOfCuts, map_multiset_sum, Multiset.map_map]

variable {b} {T : UnorderedTree α} {p : Multiset (UnorderedTree α) × Option (UnorderedTree α)}

/-- A deletion keeps the leaves: those of a tree are those of the terms a deletion cut extracts
    and of its remainder. -/
theorem deletionCuts_leaves (hT : T.Licensed fun a ks ↦ (a = b ↔ ks ≠ 0))
    (hp : p ∈ deletionCuts b T) :
    T.leaves = (p.1.map UnorderedTree.leaves).sum + p.2.elim 0 UnorderedTree.leaves := by
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  rw [admissibleCuts_leaves_prune b hT hq, deletionQuotient]
  cases q.2.prune (· ≠ b) <;> simp

/-! ### The cost of a deletion -/

/-- A deletion cut of a full binary tree extracting at most one tree leaves the contracted trunk
    of an admissible cut. -/
theorem exists_mem_admissibleCuts_of_card_le_one
    (hT : T.Licensed fun a ks ↦ (a = b ↔ ks ≠ 0) ∧
      (Multiset.card ks = 0 ∨ Multiset.card ks = 2))
    (hp : p ∈ deletionCuts b T) (h : Multiset.card p.1 ≤ 1) :
    ∃ q ∈ admissibleCuts T, p = (q.1, some q.2.contractUnary) := by
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  exact ⟨q, hq, by rw [deletionQuotient, admissibleCuts_prune_eq_some b hT hq h, Option.map_some]⟩

/-- A deletion cut of a full binary tree extracting at most one tree costs two edges for it
    besides the tree's own. -/
theorem deletionCuts_numEdges_of_card_le_one
    (hT : T.Licensed fun a ks ↦ (a = b ↔ ks ≠ 0) ∧
      (Multiset.card ks = 0 ∨ Multiset.card ks = 2))
    (hp : p ∈ deletionCuts b T) (h : Multiset.card p.1 ≤ 1) :
    T.numEdges = (p.1.map UnorderedTree.numEdges).sum + p.2.elim 0 UnorderedTree.numEdges +
      2 * Multiset.card p.1 := by
  obtain ⟨q, hq, rfl⟩ := exists_mem_admissibleCuts_of_card_le_one hT hp h
  obtain ⟨k, hk⟩ := admissibleCuts_numUnary (hT.mono fun _ _ h ↦ h.2) hq
  have := admissibleCuts_numEdges_contractUnary hq
  dsimp only [Option.elim_some] at h ⊢
  omega

/-- Deleting one accessible term costs two accessible terms besides its own
    ([marcolli-chomsky-berwick-2025] (1.6.7)). -/
theorem deletionCuts_numEdges
    (hT : T.Licensed fun a ks ↦ (a = b ↔ ks ≠ 0) ∧
      (Multiset.card ks = 0 ∨ Multiset.card ks = 2))
    (hp : p ∈ deletionCuts b T) {v : UnorderedTree α} (hv : p.1 = {v}) :
    T.numEdges = v.numEdges + p.2.elim 0 UnorderedTree.numEdges + 2 := by
  simpa [hv] using deletionCuts_numEdges_of_card_le_one hT hp (by simp [hv])

end Deletion

/-- On trees without traces, erasing the traces that `Δ^c` leaves and projecting by `Π_{d,ρ}`
    gives the deletion coproduct `Δ^d`. -/
theorem deletionProj_eraseTraces_traceComulAlgHom [DecidableEq α] (b : α)
    (τ : UnorderedTree (α ⊕ β) → β) :
    ((Algebra.TensorProduct.map (.id R _)
          ((deletionProj b).comp eraseTraces)).comp (traceComulAlgHom τ)).comp
        (rename (UnorderedTree.map Sum.inl)) =
      (Algebra.TensorProduct.map (rename (UnorderedTree.map Sum.inl)) (.id R _)).comp
        (deletionComulAlgHom (R := R) (α := α) b) := by
  have h := congrArg
    (AlgHom.comp (Algebra.TensorProduct.map (.id R _) (deletionProj (R := R) b)))
    (eraseTraces_traceComulAlgHom (R := R) τ)
  simpa only [deletionComulAlgHom, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    AlgHom.comp_id, AlgHom.id_comp] using h

end ConnesKreimer
