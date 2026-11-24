/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.FreeCommNonUnitalNonAssocAlgebra
public import Linglib.Core.Algebra.RootedTree.BirkhoffFactorization
public import Linglib.Core.Algebra.RootedTree.Coproduct.Primitive
public import Linglib.Core.RingTheory.HahnSeries.RotaBaxter
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Syntax.Minimalist.Workspace.Economy
public import Linglib.Syntax.Minimalist.Workspace.Merge.MinimalSearch
public import Linglib.Syntax.Minimalist.Workspace.Merge.Sideward
public import Linglib.Syntax.Minimalist.Label.Selection
public import Linglib.Syntax.Minimalist.Copy.FormCopy
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Tactic.Abel

/-!
# Marcolli, Chomsky and Berwick (2025): Mathematical Structure of Syntactic Merge

Marcolli, Chomsky and Berwick model Merge as an operator on the Hopf algebra of workspaces. The
algebra itself is the `Syntax/Minimalist/` theory layer and `Core/Algebra/RootedTree/`; this file
holds the book's worked examples and the results that are stated for one construction.

Internal Merge is checked on the book's example, which raises *the apple* out of
`T = {was, {eaten, {the, apple}}}`: the unit stage `M_{T₂,1}` splits `T` into *the apple* beside the
quotient `T/T₂`, and the composite with `M_{T/T₂,T₂}` merges the two. On the workspace
`{eaten, {the, apple}}` Sideward Merge has a nonzero term, which Minimal Search removes at `ε = 0`
while it keeps External and Internal Merge, and which Minimal Yield under trace counting does not
exclude.

The core computational structure of Merge is a fixed point. Let `𝔗 = FreeCommMagma Unit` be the
nonplanar binary rooted trees with unlabelled leaves and `V(𝔗)` the free commutative
nonassociative algebra on one generator `x`, whose product is Merge. A formal sum `X = ∑ₗ Xₗ`
graded by the number of leaves solves `X = 𝔐(X, X)` with `X₁ = x` when
`Xₙ = ∑_{i+j=n} Xᵢ * Xⱼ` for `n ≥ 2`. In any nonassociative semiring such a solution is unique,
and a homomorphism takes solutions to solutions. The sum of the planar binary trees with `n`
leaves solves the equation in the free nonassociative algebra, so its image under the quotient by
commutativity solves it in `V(𝔗)`, where the coefficient of a tree is its number of planar
embeddings; its image under the sum of coefficients is the sequence of Catalan numbers.

FormSet groups components of a workspace under a new root. It is the composite
`⊔ ∘ (B ⊗ id) ∘ Π_(k) ∘ Δ_P`, where the primitive coproduct `Δ_P` splits a workspace in every way,
so `FS^(k)(F)` sums `B(S) ⊔ (F - S)` over the `k`-component subworkspaces `S`, and on workspaces of
syntactic objects it lands in the extended workspaces.

In the book's syntax–semantics interface a character of the Hopf algebra into a semiring is
renormalized by Birkhoff factorization. For the head-following character, which sends a tree to
the value of a probe at its head and a tree without a head to zero, and the identity operator on
an idempotent semiring, the renormalized value of a syntactic object is at least the value at its
head. For the projection of Laurent series onto their polar part, the renormalized part of any
character lands in the power series, and the grading character `ϕt` is its own renormalized part.

Obligatory control is derived by External Merge alone: in *the man tried to read a book* both
inscriptions of *the man* merge into theta positions as repetitions of one another, and Form Copy
relates them, while *a book* is no copy of *the man*.

## Correspondence with the book

The book's algebra lives in `Core/` and in `Syntax/Minimalist/{Workspace,Merge,Economy}/`:

* Definitions 1.2.6 and 1.2.8 (admissible cuts, the coproducts `Δ^ω`):
  `ConnesKreimer.admissibleCuts` and `comulAlgHom` for `Δ^ρ`, which Remark 1.2.9 identifies with the
  Connes–Kreimer coproduct; `traceCuts` and `traceComulAlgHom` for `Δ^c`.
* Lemma 1.2.10: `ConnesKreimer.traceComulAlgHom_coassoc` and the edge grading of
  `Coproduct/TraceGrading`.
* Lemma 1.2.11 and (1.2.12): `ConnesKreimer.instBialgebra`, the `HopfAlgebra` instance, and
  `antipode_ofTree`.
* The projections `Π_{ρ,c}` and `Π_{d,ρ}` and the relations `Δ^d = (id ⊗ Π_{d,ρ}) ∘ Δ^ρ =
  (id ⊗ Π_{d,c}) ∘ Δ^c` displayed before (1.3.10): `ConnesKreimer.eraseTraces`,
  `UnorderedTree.contractUnary`, `ConnesKreimer.deletionCuts`, `ConnesKreimer.deletionComulAlgHom`,
  `ConnesKreimer.eraseTraces_traceComulAlgHom`, `contractUnary_eraseTraces_traceComulAlgHom`.
* Definition 1.3.4: `Minimalist.Merge.mergeOpOfCuts` over a cut enumeration, with the book's
  `mergeOp` at `Δ^d` and `traceMergeOp` at `Δ^c`; (1.3.10):
  `Minimalist.Merge.mergeOp_eq_comp_comulAlgHom` and `mergeOp_eq_comp_traceComulAlgHom`, and on
  objects without unary vertices `mergeOp_eq_rename_contractUnary_comp` and
  `mergeOp_eq_comp_traceMergeOp`; (1.3.11): `Minimalist.Merge.mergeOpOfCuts_apply_of'`.
* `T/d T₂ = Π_{d,c}(T/c T₂)` of §1.4.4 and p. 82, for the first stage of Internal Merge:
  `Minimalist.Merge.mergeOpUnit_eq_comp_traceMergeOpUnit`.
* Lemma 1.4.1: `Minimalist.Merge.mergeOpOfCuts_pair`, `mergeOpOfCuts_pair_residual`, with the
  residual workspace passing through by `mergeOpOfCuts_of'_mul`.
* Proposition 1.4.2: `Minimalist.Merge.mergeOpOfCuts_im_composition`, at `Δ^d`
  `Minimalist.Merge.mergeOp_im_composition`; on syntactic objects
  `Minimalist.SyntacticObject.mergeOp_im` and `traceMergeOp_im`, and for a derivation
  `Minimalist.Derivation.mergeOpList_initial`.
* Lemmas 1.4.4 and 1.4.5: `Minimalist.Merge.mergeOpOfCuts_sideward_2b`, `mergeOpOfCuts_sideward_3b`,
  `mergeOpOfCuts_sideward_3a`.
* (1.5.1) and the weights of §1.5.2: `Minimalist.Merge.comulEps`, `mergeOpEps`, with
  `comulEps_one` and `comulEps_zero` (the primitive coproduct); Proposition 1.5.1 at `ε = 0`:
  `mergeOpEps_zero_of'_of_not_le`, `mergeOpEps_zero_pair_add`; at every `ε`: `mergeOpEps_pair`,
  `mergeOpEps_im_composition`, `mergeOpEps_of'_eq_smul_of_not_le`.
* Definition 1.6.1 and Proposition 1.6.4: `Minimalist.MinimalYield` over a counting,
  `MinimalYield.em_pair`, `em_pair_accessibleCount`, `im_accessibleCount_of_cut`.
* Lemma 1.6.3 (1.6.8) and (1.6.10): `ConnesKreimer.traceCuts_accessibleCount`,
  `traceCuts_accessibleSize`. Proposition 1.6.8 and
  Remark 1.6.7, on the terms of Merge (`Minimalist.Merge.mergeOpOfCuts_apply_of'_eq_sum`):
  `Minimalist.card_singleton_add_trunk_add_numWhole`, `accessibleCount_merge_term`,
  `accessibleSize_merge_term`, `MinimalYield.merge_term_accessibleCount_iff`,
  `accessibleCount_unit_term` for `Δ^c`, and `MinimalYield.merge_term_numEdges_iff` for `Δ^d`.
  Remark 1.6.9, Sideward Merge of type 2(b) on the workspace of §1.3.4:
  `MarcolliChomskyBerwick2025.sideward2b_minimalYield`.
* Lemma 1.6.3 (1.6.7): `ConnesKreimer.deletionCuts_numEdges`, from the unary vertices a cut
  leaves (`ConnesKreimer.admissibleCuts_numUnary`); for Internal Merge,
  `Minimalist.numEdges_im_of_cut`, `MinimalYieldWeak.im_numEdges_of_cut`,
  `MinimalYield.not_im_numEdges_of_cut`. Each cut's cost over a workspace:
  `ConnesKreimer.CutChoice.HasExtractionCost`.
* Definition 1.6.2 and Proposition 1.6.10: `Minimalist.NoComplexityLoss`, met by every admissible
  derivation step (`Minimalist.Step.noComplexityLoss`); along the induced map of a term of Merge
  (`Minimalist.componentMap`, `NoComplexityLoss.of_componentMap`),
  `NoComplexityLoss.map_componentMap_merge_iff`,
  `not_map_componentMap_merge`, `not_map_componentMap_unit`, and at the trace cuts graded by `σ`,
  `not_map_accessibleSize_componentMap_merge`.
* Definition 1.6.2's degree `#L`: `UnorderedTree.numLeaves`; Lemma 1.6.3:
  `ConnesKreimer.traceCuts_numNodes`.
* The functionals of (1.7.5) and their Lie algebra: `Bialgebra.IsDualPrimitive` and
  `Bialgebra.dualPrimitives`; they are supported on single trees
  (`ConnesKreimer.isDualPrimitive_iff`).
* Lemma 1.7.3, for `Δ^ρ` and grafting at vertices: `ConnesKreimer.isDualPrimitive_lcoeff_iff`,
  `lie_lcoeff_singleton_apply_ofTree`, `lie_lcoeff_singleton_apply_of'`, and
  `GrossmanLarson.pairingLie` for the bracket of the grafting product.
* Definition 3.1.1 and the weight `+1` identity of Definition 3.1.2: `IsRotaBaxter` at weights
  `-1` and `+1`; the identity operator of Remark 3.2.2, at weight `+1` on an idempotent semiring:
  `isRotaBaxter_id`.
* Definitions 3.1.3, 3.1.5 and 3.1.6, Proposition 3.1.7, Remark 3.1.8:
  `ConnesKreimer.birkhoffMinus`, `birkhoffPrepTree`, `birkhoffPlus`, `birkhoffPlus_eq_convMul`,
  `birkhoffFactorization`, with the operator `-R`; the subalgebras of Proposition 3.1.7:
  `ConnesKreimer.birkhoffMinus_of'_mem_range`, `birkhoffPlus_of'_mem_range`; Proposition 3.1.9:
  `ConnesKreimer.convMul_birkhoffMinus_apply_ofTree`.
* Proposition 3.5.2 and (3.5.4): `HahnSeries.isRotaBaxter_truncLT`. The gradings of §3.5.2.1:
  `δb₀`, `δα`, `δσ`, `minimalYield_iff_gradings`, `minimalYieldWeak_iff_truncLT`. Proposition
  3.5.3 for `δα`, without the derivation coefficients: `gradingChar`; Lemma 3.5.5:
  `truncLT_gradingChar_of'`; the first step of the proof of Proposition 3.5.6:
  `truncLT_birkhoffPlus_of'`.

## Implementation notes

In §1.4.4 the book displays the result with the deletion quotient `T/d T₂ = {was, eaten}`, and
alternatively with the contraction quotient `T/c T₂`, whose contracted leaf it labels by the
extracted term `{the, apple}`. The trace cuts of the carrier label that leaf by the head of the
extracted term (`traceEncoder`), so the example's quotient is `{was, {eaten, t}}` with `t` the
trace of *the*.

The book writes the equation as `X = 𝔐(X, X)` with the initial condition `X₁ = x`.
`IsMergeSolution` takes the initial condition as its degree-one clause and the equation from
degree two on, the form to which the proof of Proposition 1.10.2 reduces it. A formal sum is a
sequence of its homogeneous terms, power series over a nonassociative ring not being available.

The planar binary trees are enumerated by mathlib's `BinaryTree.treesOfNumNodesEq`, whose trees
with `n` internal nodes have `n + 1` leaves, and read in the free magma by `toFreeMagma`.

`formSet` is defined for every `k` on all forests, with the root label of `B` a parameter.
Definition 1.16.1 takes `k ≥ 3` and the domain `V(𝔉_{SO₀})` of workspaces of syntactic objects;
`map_formSet_le` is stated on that domain, with the bare root label of the syntactic objects.

Lemma 3.2.5 takes the tropical semiring `(ℝ ∪ {-∞}, max, +)` as target, with `-∞`, its zero, on
a tree without a head, and §3.2.5 the Boolean semiring. `headProbeChar` takes any commutative
semiring, and the comparison of Lemma 3.2.7 any idempotent one, with its canonical order. The
Bogolyubov recursion takes its operator at weight `+1`, which the identity has on an idempotent
semiring (`isRotaBaxter_id`).

## TODO

§1.17 reads (1.10.1) as the quadratic case of the combinatorial Dyson–Schwinger equation
`X = B(P(X))` of (1.17.2), with the grafting operator `B` of Definition 1.3.2 and the recursive
solution (1.17.3), which the book cites rather than proves. Stating it needs `B` on formal series
in the grading by vertices, in which `B` raises the degree by one. With `x = B(1)` the Merge case
is `P(t) = 1 + t²`, while the book writes `P(X) = X²` next to its requirement `a₀ = 1`.

Lemma 1.16.5 extends the coproducts `Δ^ω` to extended workspaces by excluding the cuts of edges at
a root of valence at least three, so that Merge does not undo the grouping FormSet builds
(§1.16.2). It is not formalized.

Proposition 1.6.8 assumes that no cut falls on the edges immediately below the root of a
component. The Sideward case 3(a) on *the apple* is that case, *the* and *apple* being the two
children of the root: the deletion leaves nothing of the component, and Merge rebuilds it.

Corollary 3.5.4's character `ψt` sums over the pairs of intermediate derivations of a target,
which needs a Merge step relation on workspaces; it, and Proposition 3.5.6 beyond the first step of
its proof, are not formalized.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-etal-2023]
-/

@[expose] public section

namespace MarcolliChomskyBerwick2025

open RoseTree UnorderedTree Minimalist SyntacticObject ConnesKreimer

/-! ### Internal Merge: an example (§1.4.4) -/

/-- *the apple*, the term `T₂` that Internal Merge raises in §1.4.4. -/
def theApplePlanar : PlanarSyntacticObject :=
  PlanarSyntacticObject.merge (.leaf ⟨.of .D [.N] "the", 0⟩) (.leaf ⟨.of .N [] "apple", 1⟩)

/-- *the apple* as a syntactic object. -/
def theApple : SyntacticObject := theApplePlanar.toSyntacticObject

/-- The workspace `T = {was, {eaten, {the, apple}}}` of §1.4.4. -/
private def wasEatenTheApple : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf ⟨.of .T [.V] "was", 2⟩)
    (.merge (.leaf ⟨.of .V [.D] "eaten", 3⟩)
      (.merge (.leaf ⟨.of .D [.N] "the", 0⟩) (.leaf ⟨.of .N [] "apple", 1⟩)))).toSyntacticObject

/-- The quotient `T/T₂`, with the trace of the head *the* in place of *the apple*. -/
private def wasEatenTrace : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf ⟨.of .T [.V] "was", 2⟩)
    (.merge (.leaf ⟨.of .V [.D] "eaten", 3⟩) (.traceOf ⟨.of .D [.N] "the", 0⟩))).toSyntacticObject

/-- The remainder of raising *the apple* out of `T` is the quotient `T/T₂`. -/
example : deleteAccessible theApple wasEatenTheApple = wasEatenTrace := by decide

/-- The first stage `M_{T₂,1}` splits `T` into `T₂` beside the quotient `T/T₂`. -/
example :
    Merge.traceMergeOpUnit (R := ℤ) traceEncoder theApple.toUnorderedTree
        (of' ({wasEatenTheApple.toUnorderedTree} : Forest (UnorderedTree Vertex)))
      = of' ({theApple.toUnorderedTree, wasEatenTrace.toUnorderedTree} : Forest (UnorderedTree
          Vertex)) := by
  rw [traceMergeOpUnit_current (by decide) (by decide) (by decide),
    show deleteAccessible theApple wasEatenTheApple = wasEatenTrace by decide]

/-- The deletion quotient `T/d T₂ = {was, eaten}` that §1.4.4 displays. -/
private def wasEaten : SyntacticObject :=
  (PlanarSyntacticObject.merge (.leaf ⟨.of .T [.V] "was", 2⟩)
    (.leaf ⟨.of .V [.D] "eaten", 3⟩)).toSyntacticObject

/-- A syntactic object with its traces erased, on the labels of the trees without traces. -/
private def erased (T : SyntacticObject) : UnorderedTree (Option LexicalItem.Token) :=
  (T.toUnorderedTree.filterMap Sum.getLeft?).getD (.leaf none)

/-- The projection `Π_{d,c}` takes `T/c T₂` to `T/d T₂`, as §1.4.4 displays. -/
example : (wasEatenTrace.toUnorderedTree.filterMap Sum.getLeft?).map UnorderedTree.contractUnary =
    some (erased wasEaten) := by decide

/-- The projection `Π_{ρ,c}` alone leaves *eaten* under a unary vertex: it reaches `T/ρ T₂`, and
    `Π_{d,ρ}` takes that to `T/d T₂`. -/
example : wasEatenTrace.toUnorderedTree.filterMap Sum.getLeft? ≠ some (erased wasEaten) := by decide

/-- The first stage at the deletion coproduct leaves `T₂` beside `T/d T₂`: projecting the stage at
    the trace cuts by `Π_{d,c}` gives the workspace that §1.4.4 displays. -/
example :
    Merge.mergeOpUnit (R := ℤ) none (erased theApple)
        (of' ({erased wasEatenTheApple} : Forest (UnorderedTree (Option LexicalItem.Token))))
      = of' ({erased theApple, erased wasEaten} :
          Forest (UnorderedTree (Option LexicalItem.Token))) := by
  have h₁ : (erased theApple).map Sum.inl = theApple.toUnorderedTree := by decide
  have h₂ : (erased wasEatenTheApple).map Sum.inl = wasEatenTheApple.toUnorderedTree := by decide
  rw [Merge.mergeOpUnit_eq_comp_traceMergeOpUnit traceEncoder none (by decide)]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, rename_of', Multiset.map_singleton, h₁,
    h₂]
  rw [traceMergeOpUnit_current (by decide) (by decide) (by decide),
    show deleteAccessible theApple wasEatenTheApple = wasEatenTrace by decide]
  have h₃ : theApple.toUnorderedTree.filterMap Sum.getLeft? = some (erased theApple) := by decide
  have h₄ : wasEatenTrace.toUnorderedTree.filterMap Sum.getLeft? = some (erased wasEatenTrace) := by
      decide
  have h₅ : deletionQuotient none (erased theApple) = some (erased theApple) := by decide
  have h₆ : deletionQuotient none (erased wasEatenTrace) = some (erased wasEaten) := by decide
  simp only [AlgHom.comp_apply, Multiset.insert_eq_cons, ← Multiset.singleton_add, of'_add,
    of'_singleton, map_mul, eraseTraces_ofTree, h₃, h₄, Option.elim_some, deletionProj_ofTree,
    h₅, h₆]

/-- The composite `M_{T/T₂,T₂} ∘ M_{T₂,1}` is Internal Merge of *the apple*: it merges `T₂` with the
    quotient `T/T₂` (Proposition 1.4.2). -/
example :
    Merge.traceMergeOp (R :=
        ℤ) traceEncoder Vertex.bare wasEatenTrace.toUnorderedTree theApple.toUnorderedTree
        (Merge.traceMergeOpUnit traceEncoder theApple.toUnorderedTree
          (of' ({wasEatenTheApple.toUnorderedTree} : Forest (UnorderedTree Vertex))))
      = of' ({(merge wasEatenTrace theApple).toUnorderedTree} : Forest (UnorderedTree Vertex)) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact traceMergeOp_im (by decide) (by decide) (by decide)

/-- This Internal Merge satisfies Minimal Yield under trace counting, the Δᶜ row of the table of
    Proposition 1.6.4. -/
example :
    MinimalYield UnorderedTree.accessibleCount
      (({wasEatenTheApple} : Workspace).map SyntacticObject.toUnorderedTree)
      (({merge wasEatenTrace theApple} : Workspace).map SyntacticObject.toUnorderedTree) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact Step.minimalYield (step := .im theApple) (W := 0)
    ⟨by decide, by decide, by decide, by simp⟩ (by decide) (by simp [Step.items])

/-- It loses no complexity graded by the size `σ`: *was eaten the apple* goes to the Merge of
    *the apple* with the remainder, of one greater size (Proposition 1.6.10). -/
example :
    NoComplexityLoss (fun T ↦ Forest.accessibleSize {T})
      (({wasEatenTheApple} : Workspace).map SyntacticObject.toUnorderedTree)
      (({merge wasEatenTrace theApple} : Workspace).map SyntacticObject.toUnorderedTree) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact Step.noComplexityLoss (step := .im theApple) (W := 0)
    ⟨by decide, by decide, by decide, by simp⟩ (by decide) (by simp [Step.items])

/-! ### Sideward Merge, Minimal Search and economy on the workspace of §1.3.4

The workspace `{eaten, {the, apple}}` of §1.3.4 also admits Sideward Merge of type 2(b), which
merges *eaten* with *the* cut out of *the apple*, and *the apple* alone admits Internal Merge of
*the* and Sideward Merge of type 3(a) of *the* and *apple*. On these the general results of §1.4–1.6
give Sideward Merge a nonzero term, which Minimal Search removes at `ε = 0` while it keeps
External and Internal Merge. The 2(b) term satisfies Minimal Yield under trace counting, as
Remark 1.6.9 says. No Complexity Loss excludes it at the admissible cuts graded by vertices, and at
the trace cuts graded by the size `σ`. At the trace cuts the vertex count does not exclude it,
because the trace of *the* takes the place of *the*. -/

/-- *the*, a term of *the apple*. -/
def theD : SyntacticObject :=
  (PlanarSyntacticObject.leaf ⟨.of .D [.N] "the", 0⟩).toSyntacticObject

/-- *apple*, the other term of *the apple*. -/
def appleN : SyntacticObject :=
  (PlanarSyntacticObject.leaf ⟨.of .N [] "apple", 1⟩).toSyntacticObject

/-- *eaten*, the other component of the workspace of §1.3.4. -/
def eaten : SyntacticObject :=
  (PlanarSyntacticObject.leaf ⟨.of .V [.D] "eaten", 3⟩).toSyntacticObject

/-- External Merge of *the apple* with *eaten* loses no complexity graded by the size `σ`: its term
    of Merge takes both whole (Proposition 1.6.10). -/
example :
    NoComplexityLoss (fun T ↦ Forest.accessibleSize {T})
      (({eaten, theApple} : Workspace).map SyntacticObject.toUnorderedTree)
      (({merge theApple eaten} : Workspace).map SyntacticObject.toUnorderedTree) :=
  Step.noComplexityLoss (step := .em .left theApplePlanar) (W := 0) (by simp [Step.Admissible])
    (by decide) (by simp only [Step.items, Multiset.mem_singleton, forall_eq]; decide)

private def admTok (i : Nat) : LexicalItem.Token := ⟨.of .N [], i⟩

/-- Raising the item a derivation has just merged is admissible, so `mergeOpList_initial` applies
    to it. -/
example :
    (Derivation.mk (admTok 0) [Step.em .left (admTok 1), Step.im (admTok 1)]).Admissible := by
  have hne : merge ↑(admTok 1) ↑(admTok 0) ≠ (↑(admTok 1) : SyntacticObject) := fun h ↦ by
    have := congrArg (fun s : SyntacticObject ↦ s.toUnorderedTree.numNodes) h
    simp at this
  simp only [Derivation.Admissible, Step.AdmissibleList, Step.Admissible, Step.itemsList_cons,
    Step.itemsList_nil, Step.items, Step.apply_em, add_zero, Multiset.notMem_zero,
    IsEmpty.forall_iff, implies_true, and_true, true_and, ne_eq,
    PlanarSyntacticObject.toSyntacticObject_leaf, hne, not_false_eq_true]
  refine ⟨rfl, ?_⟩
  rw [terms_merge, Multiset.count_cons_of_ne hne.symm]
  simp [admTok]

private theorem admissibleCuts_theApple : admissibleCuts theApple.toUnorderedTree =
    {({theD.toUnorderedTree, appleN.toUnorderedTree}, UnorderedTree.leaf Vertex.bare),
      ({theD.toUnorderedTree}, UnorderedTree.node Vertex.bare {appleN.toUnorderedTree}),
      ({appleN.toUnorderedTree}, UnorderedTree.node Vertex.bare {theD.toUnorderedTree}),
      (0, theApple.toUnorderedTree)} := by decide

private theorem filter_admissibleCuts_theApple :
    (admissibleCuts theApple.toUnorderedTree).filter (·.1 = {theD.toUnorderedTree}) =
      {({theD.toUnorderedTree}, UnorderedTree.node Vertex.bare {appleN.toUnorderedTree})} := by
  decide

/-- Sideward Merge of type 2(b) at the trace cuts merges *eaten* with *the* beside the remainder
    of *the apple* (Lemma 1.4.4). -/
example :
    Merge.traceMergeOp (R := ℤ) traceEncoder Vertex.bare eaten.toUnorderedTree theD.toUnorderedTree
        (of' ({eaten.toUnorderedTree, theApple.toUnorderedTree} : Forest (UnorderedTree Vertex))) =
      of' ({(merge eaten theD).toUnorderedTree, (deleteAccessible theD theApple).toUnorderedTree} :
        Forest (UnorderedTree Vertex)) := by
  rw [Merge.traceMergeOp, Merge.mergeOpOfCuts_sideward_2b Vertex.bare
      (by rw [toUnorderedTree_mem_subtrees]; decide)
      (fun h ↦ (by decide : theD ≠ theApple) (SyntacticObject.toUnorderedTree_injective h)),
    traceCuts_filter_mover (by decide) (by decide) (by decide), Multiset.map_singleton,
    Multiset.sum_singleton, toUnorderedTree_merge, ← of'_singleton, ← of'_add]
  rfl

/-- At `ε = 1` weighted Sideward Merge of type 2(b) is Sideward Merge at the admissible cuts. -/
example :
    Merge.mergeOpEps (R := ℤ) 1 Vertex.bare eaten.toUnorderedTree theD.toUnorderedTree
        (of' ({eaten.toUnorderedTree, theApple.toUnorderedTree} : Forest (UnorderedTree Vertex))) =
      of' ({(merge eaten theD).toUnorderedTree,
          UnorderedTree.node Vertex.bare {appleN.toUnorderedTree}} :
        Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpEps_one, Merge.mergeOpOfCuts_sideward_2b Vertex.bare
      (by rw [toUnorderedTree_mem_subtrees]; decide)
      (fun h ↦ (by decide : theD ≠ theApple) (SyntacticObject.toUnorderedTree_injective h)),
    filter_admissibleCuts_theApple, Multiset.map_singleton, Multiset.sum_singleton,
        toUnorderedTree_merge,
    ← of'_singleton, ← of'_add]
  rfl

/-- At `ε = 0` Minimal Search removes it (Proposition 1.5.1). -/
example :
    Merge.mergeOpEps (R := ℤ) 0 Vertex.bare eaten.toUnorderedTree theD.toUnorderedTree
      (of' ({eaten.toUnorderedTree, theApple.toUnorderedTree} : Forest (UnorderedTree Vertex))) =
          0 :=
  Merge.mergeOpEps_zero_of'_of_not_le _ (by decide)

/-- At every `ε` it is a multiple of `ε`, so Sideward Merge costs at least one
    (Proposition 1.5.1). -/
example (ε : ℤ) : ∃ y, Merge.mergeOpEps ε Vertex.bare eaten.toUnorderedTree theD.toUnorderedTree
    (of' ({eaten.toUnorderedTree, theApple.toUnorderedTree} : Forest (UnorderedTree Vertex))) =
        ε • y :=
  Merge.mergeOpEps_of'_eq_smul_of_not_le ε _ (by decide)

/-- At `ε = 0` External Merge of the two components survives. -/
example :
    Merge.mergeOpEps (R := ℤ) 0 Vertex.bare eaten.toUnorderedTree theApple.toUnorderedTree
        (of' ({eaten.toUnorderedTree, theApple.toUnorderedTree} : Forest (UnorderedTree Vertex))) =
      of' ({(merge eaten theApple).toUnorderedTree} : Forest (UnorderedTree Vertex)) := by
  simpa using Merge.mergeOpEps_zero_pair_add (R := ℤ) (F := 0) Vertex.bare
    (S := eaten.toUnorderedTree) (S' := theApple.toUnorderedTree) (Multiset.notMem_zero
        _) (Multiset.notMem_zero _)

/-- At `ε = 0` Internal Merge of *the* inside *the apple* at the admissible cuts survives, while
    Sideward Merge of the same *the* does not. The admissible cut leaves *apple* under a unary
    vertex, so the result is no syntactic object. -/
example :
    Merge.mergeOpEps (R := ℤ) 0 Vertex.bare (UnorderedTree.node Vertex.bare
        {appleN.toUnorderedTree}) theD.toUnorderedTree
        (Merge.mergeOpUnitOfCuts admissibleCuts theD.toUnorderedTree
          (of' ({theApple.toUnorderedTree} : Forest (UnorderedTree Vertex)))) =
      of' ({UnorderedTree.node Vertex.bare
              {UnorderedTree.node Vertex.bare {appleN.toUnorderedTree}, theD.toUnorderedTree}} :
        Forest (UnorderedTree Vertex)) :=
  Merge.mergeOpEps_im_composition _ _ _ _ _ _ filter_admissibleCuts_theApple rfl
    (fun h ↦ (by decide : theApple ≠ theD) (SyntacticObject.toUnorderedTree_injective h))

/-- At the deletion coproduct, the book's Merge, the same Internal Merge contracts that vertex and
    merges *the* with *apple*, a syntactic object, here *the apple* again. -/
example :
    Merge.mergeOp (R := ℤ) Vertex.bare appleN.toUnorderedTree theD.toUnorderedTree
        (Merge.mergeOpUnit Vertex.bare theD.toUnorderedTree
          (of' ({theApple.toUnorderedTree} : Forest (UnorderedTree Vertex)))) =
      of' ({theApple.toUnorderedTree} : Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOp_im_composition Vertex.bare _ _ _ _ filter_admissibleCuts_theApple
    (by decide)
    (fun h ↦ (by decide : theApple ≠ theD) (SyntacticObject.toUnorderedTree_injective h))
    (deletionQuotient_of_isSyntacticObject theD.isSyntacticObject_toUnorderedTree)
    (deletionQuotient_of_isSyntacticObject appleN.isSyntacticObject_toUnorderedTree),
    show theApple = merge theD appleN by decide, toUnorderedTree_merge, Multiset.pair_comm]

private theorem mem_traceCuts_theApple :
    ({theD.toUnorderedTree}, (deleteAccessible theD
        theApple).toUnorderedTree) ∈ traceCuts traceEncoder theApple.toUnorderedTree := by decide

/-- The term of Sideward Merge of type 2(b) at the trace cuts takes *eaten* whole and cuts *the*
    out of *the apple*. -/
private noncomputable def sidewardTermC : CutChoice Vertex :=
  {(eaten.toUnorderedTree, ({eaten.toUnorderedTree}, 0)),
    (theApple.toUnorderedTree, ({theD.toUnorderedTree}, {(deleteAccessible theD
        theApple).toUnorderedTree}))}

/-- The same term at the admissible cuts, where the trunk of *the apple* keeps *apple* under a
    unary vertex that the deletion contracts. -/
private noncomputable def sidewardTermN : CutChoice Vertex :=
  {(eaten.toUnorderedTree, ({eaten.toUnorderedTree}, 0)),
    (theApple.toUnorderedTree, ({theD.toUnorderedTree},
      {UnorderedTree.node Vertex.bare {appleN.toUnorderedTree}}))}

private theorem sidewardTermC_mem :
    sidewardTermC ∈ forestCutChoices (traceCuts traceEncoder) {eaten.toUnorderedTree,
        theApple.toUnorderedTree} := by
  rw [Multiset.insert_eq_cons, forestCutChoices_cons, ← Multiset.cons_zero, forestCutChoices_cons,
    forestCutChoices_zero]
  exact Multiset.mem_bind.mpr ⟨({eaten.toUnorderedTree}, 0), Multiset.mem_cons_self _ _,
    Multiset.mem_map.mpr ⟨_, Multiset.mem_bind.mpr ⟨_,
      Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ mem_traceCuts_theApple),
      Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩, rfl⟩⟩

private theorem sidewardTermN_mem :
    sidewardTermN ∈ forestCutChoices admissibleCuts {eaten.toUnorderedTree,
        theApple.toUnorderedTree} := by
  rw [Multiset.insert_eq_cons, forestCutChoices_cons, ← Multiset.cons_zero, forestCutChoices_cons,
    forestCutChoices_zero]
  exact Multiset.mem_bind.mpr ⟨({eaten.toUnorderedTree}, 0), Multiset.mem_cons_self _ _,
    Multiset.mem_map.mpr ⟨_, Multiset.mem_bind.mpr ⟨_,
      Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem (fun p ↦ (p.1, {p.2}))
        (show ({theD.toUnorderedTree}, UnorderedTree.node Vertex.bare {appleN.toUnorderedTree}) ∈
            admissibleCuts theApple.toUnorderedTree
          by rw [admissibleCuts_theApple]; simp)),
      Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩, rfl⟩⟩

theorem sideward2b_minimalYield :
    MinimalYield UnorderedTree.accessibleCount {eaten.toUnorderedTree, theApple.toUnorderedTree}
      {(merge eaten theD).toUnorderedTree, (deleteAccessible theD theApple).toUnorderedTree} := by
  have := (MinimalYield.merge_term_accessibleCount_iff none sidewardTermC_mem
    (S := eaten.toUnorderedTree) (S' := theD.toUnorderedTree)
    (fun x hx _ ↦ by
      rw [sidewardTermC, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> rfl)
    (by simp [sidewardTermC])).mpr (by simp [sidewardTermC])
  simpa [sidewardTermC] using this

/-- At the admissible cuts the 2(b) term loses complexity along its component map, since *the apple*
    goes to the lighter trunk `{apple}` (Proposition 1.6.10). -/
example : ¬ NoComplexityLoss.Map UnorderedTree.numNodes
    (componentMap (UnorderedTree.node Vertex.bare {eaten.toUnorderedTree, theD.toUnorderedTree})
        sidewardTermN) :=
  NoComplexityLoss.not_map_componentMap_merge sidewardTermN_mem
    (hasExtractionCost_numNodes_admissibleCuts sidewardTermN_mem) UnorderedTree.numNodes_pos
    (S := eaten.toUnorderedTree) (S' := theD.toUnorderedTree) (by simp [sidewardTermN]) (by
        decide) (by decide)
    (.inr (by decide))

/-- At the trace cuts the 2(b) term loses no vertices along its component map, since the trace of
    *the* takes its place in *the apple*. -/
example : NoComplexityLoss.Map UnorderedTree.numNodes
    (componentMap (UnorderedTree.node Vertex.bare {eaten.toUnorderedTree, theD.toUnorderedTree})
        sidewardTermC) := by
  simp [NoComplexityLoss.Map, componentMap, sidewardTermC]
  decide

/-- Graded by the size `σ`, which the trace cuts conserve, the 2(b) term at the trace cuts does
    lose complexity (Proposition 1.6.10). -/
example : ¬ NoComplexityLoss.Map (fun T ↦ Forest.accessibleSize {T})
    (componentMap (UnorderedTree.node Vertex.bare {eaten.toUnorderedTree, theD.toUnorderedTree})
        sidewardTermC) :=
  NoComplexityLoss.not_map_accessibleSize_componentMap_merge none sidewardTermC_mem
    (fun x hx _ ↦ by
      rw [sidewardTermC, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> rfl)
    (S := eaten.toUnorderedTree) (S' := theD.toUnorderedTree) (by simp [sidewardTermC]) (.inr (by
        decide))

/-- The term of Sideward Merge of type 3(a) of *the* and *apple* cuts both out of *the apple*. -/
private noncomputable def sideward3a : CutChoice Vertex :=
  {(theApple.toUnorderedTree, ({theD.toUnorderedTree, appleN.toUnorderedTree},
    {UnorderedTree.leaf Vertex.bare}))}

/-- It raises the number of components, so it violates Minimal Yield under any counting
    (Proposition 1.6.8). -/
example (acc : UnorderedTree Vertex → ℕ) (X : UnorderedTree Vertex) :
    ¬ MinimalYieldWeak acc {theApple.toUnorderedTree} ({X} + sideward3a.trunk) := by
  have hs : sideward3a ∈ forestCutChoices admissibleCuts {theApple.toUnorderedTree} := by
    rw [← Multiset.cons_zero, forestCutChoices_cons, forestCutChoices_zero]
    exact Multiset.mem_bind.mpr ⟨_, Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem
      (fun p ↦ (p.1, {p.2}))
      (show ({theD.toUnorderedTree, appleN.toUnorderedTree}, UnorderedTree.leaf Vertex.bare) ∈
          admissibleCuts theApple.toUnorderedTree
        by rw [admissibleCuts_theApple]; exact Multiset.mem_cons_self _ _)),
      Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩
  exact MinimalYieldWeak.not_of_forall_notMem acc hs (by simp [sideward3a]; decide) X

/-- Under `Δ^d` the 3(a) term of *the apple* extracts both children of the root, the case the
    book sets aside before Proposition 1.6.8: nothing remains of the component, and Merge rebuilds
    it. -/
example : sideward3a.trunk.filterMap (deletionQuotient Vertex.bare) = 0 ∧
    merge theD appleN = theApple := by decide

/-- The remainder of a deletion is the largest syntactic object the trunk contracts to
    (Definition 1.2.5). Extracting two terms that are not sisters leaves each parent a single
    child, and the remainder is what is left below them, as in the book's example after (1.2.7),
    whose remainder is the one lexical item `γ`. -/
example : deletionQuotient Vertex.bare
      (.node Vertex.bare {.node Vertex.bare {appleN.toUnorderedTree}}) =
    some appleN.toUnorderedTree := by decide

/-- Extracting *the* and *apple* from `{eaten, {the, apple}}` leaves their parent without a child.
    It is no leaf of the object, so it goes with them, and the remainder is *eaten*. -/
example : deletionQuotient Vertex.bare
      (.node Vertex.bare {eaten.toUnorderedTree, .leaf Vertex.bare}) =
    some eaten.toUnorderedTree := by decide

/-- Contracting unary vertices alone would keep that childless parent as a leaf, which no
    syntactic object has. -/
example : ¬ IsSyntacticObject (UnorderedTree.contractUnary
    (.node Vertex.bare {eaten.toUnorderedTree, .leaf Vertex.bare})) := by decide

/-- A trunk with no leaf of the object left has no remainder. -/
example : deletionQuotient Vertex.bare (.leaf Vertex.bare : UnorderedTree Vertex) = none := by
  decide

/-- Under deletion counting the 2(b) term satisfies the weak form of Minimal Yield but not the
    strong one, since it takes only *eaten* whole (Proposition 1.6.8). -/
example : MinimalYieldWeak UnorderedTree.numEdges {eaten.toUnorderedTree, theApple.toUnorderedTree}
      {(merge eaten theD).toUnorderedTree, appleN.toUnorderedTree} ∧
    ¬ MinimalYield UnorderedTree.numEdges {eaten.toUnorderedTree, theApple.toUnorderedTree}
      {(merge eaten theD).toUnorderedTree, appleN.toUnorderedTree} := by
  have hF : ∀ T ∈ ({eaten.toUnorderedTree, theApple.toUnorderedTree} : Forest (UnorderedTree
      Vertex)),
      T.Licensed fun a ks ↦ (a = Vertex.bare ↔ ks ≠ 0) ∧
        (Multiset.card ks = 0 ∨ Multiset.card ks = 2) := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    rintro _ (rfl | rfl)
    exacts [licensed_bare_of_isSyntacticObject eaten.isSyntacticObject_toUnorderedTree,
      licensed_bare_of_isSyntacticObject theApple.isSyntacticObject_toUnorderedTree]
  have hK : sidewardTermN.crown = {eaten.toUnorderedTree, theD.toUnorderedTree} := by
      simp [sidewardTermN]
  have hX : (merge eaten theD).toUnorderedTree.numEdges = eaten.toUnorderedTree.numEdges +
      theD.toUnorderedTree.numEdges + 2 := by
    rw [toUnorderedTree_merge]; exact UnorderedTree.numEdges_node_pair _ _ _
  have hne : ∀ t ∈ sidewardTermN.trunk, deletionQuotient Vertex.bare t ≠ none := by decide
  have hu (S : SyntacticObject) : S.toUnorderedTree.numUnary = 0 :=
    S.isSyntacticObject_toUnorderedTree.isFullBinary.numUnary_eq_zero
  rw [show ({(merge eaten theD).toUnorderedTree, appleN.toUnorderedTree} : Forest (UnorderedTree
      Vertex)) =
      {(merge eaten theD).toUnorderedTree} +
        sidewardTermN.trunk.filterMap (deletionQuotient Vertex.bare) by decide,
    MinimalYieldWeak.merge_term_numEdges_iff Vertex.bare hF sidewardTermN_mem hne hK (hu _) (hu _)
      (hu _) hX,
    MinimalYield.merge_term_numEdges_iff Vertex.bare hF sidewardTermN_mem hne hK (hu _) (hu _)
      (hu _) hX,
    show sidewardTermN.numWhole = 1 by decide]
  decide

/-! ### The core computational structure of Merge (§1.10)

The set `𝔗` of binary rooted trees without planar structure and without labels is
`FreeCommMagma Unit`, and `V(𝔗)` is `FreeCommNonUnitalNonAssocAlgebra ℤ Unit`, whose product is
Merge extended bilinearly. -/

section CoreMerge

open Finset
open Finset.HasAntidiagonal.antidiagonal (fst_le snd_le)

section Solution

variable {A B : Type*} [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]

/-- (1.10.1): a formal sum `X = ∑ₗ Xₗ` solves `X = 𝔐(X, X)` with the initial condition `X₁ = x`
when it has no term of degree zero, its term of degree one is `x`, and each further term is
`Xₙ = ∑_{i+j=n} Xᵢ * Xⱼ`. -/
structure IsMergeSolution (x : A) (X : ℕ → A) : Prop where
  /-- There is no term of degree zero. -/
  zero : X 0 = 0
  /-- The initial condition. -/
  one : X 1 = x
  /-- The equation in degree `n + 2`. -/
  add_two (n : ℕ) : X (n + 2) = ∑ p ∈ antidiagonal (n + 2), X p.1 * X p.2

variable {x : A} {X Y : ℕ → A}

-- The recursive relation of the proof of Proposition 1.10.2
theorem isMergeSolution_iff : IsMergeSolution x X ↔
    X 0 = 0 ∧ X 1 = x ∧ ∀ n, X (n + 2) = ∑ p ∈ antidiagonal n, X (p.1 + 1) * X (p.2 + 1) := by
  refine ⟨fun h ↦ ⟨h.zero, h.one, fun n ↦ ?_⟩, fun ⟨h0, h1, h⟩ ↦ ⟨h0, h1, fun n ↦ ?_⟩⟩
  · rw [h.add_two, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ', h.zero]
    simp
  · rw [h, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ', h0]
    simp

theorem IsMergeSolution.add_two' (h : IsMergeSolution x X) (n : ℕ) :
    X (n + 2) = ∑ p ∈ antidiagonal n, X (p.1 + 1) * X (p.2 + 1) :=
  (isMergeSolution_iff.1 h).2.2 n

theorem IsMergeSolution.map {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B] (f : F)
    (h : IsMergeSolution x X) : IsMergeSolution (f x) (f ∘ X) :=
  ⟨by simp [h.zero], by simp [h.one], fun n ↦ by simp [h.add_two n]⟩

theorem IsMergeSolution.eq (hX : IsMergeSolution x X) (hY : IsMergeSolution x Y) : X = Y := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [hX.zero, hY.zero]
    · rw [hX.one, hY.one]
    · rw [hX.add_two', hY.add_two']
      refine sum_congr rfl fun p hp ↦ ?_
      rw [ih (p.1 + 1) (by have := fst_le hp; omega), ih (p.2 + 1) (by have := snd_le hp; omega)]

theorem IsMergeSolution.two (h : IsMergeSolution x X) : X 2 = x * x := by
  simp [h.add_two' 0, h.one]

end Solution

section Comm

variable {A : Type*} [NonUnitalNonAssocCommSemiring A] {x : A} {X : ℕ → A}

theorem IsMergeSolution.three (h : IsMergeSolution x X) : X 3 = 2 • (x * (x * x)) := by
  simp [h.add_two' 1, Finset.Nat.sum_antidiagonal_succ, h.one, h.two, two_nsmul, mul_comm]

-- `X₄ = 4{x{x{xx}}} + {{xx}{xx}}`
theorem IsMergeSolution.four (h : IsMergeSolution x X) :
    X 4 = 4 • (x * (x * (x * x))) + x * x * (x * x) := by
  simp only [h.add_two' 2, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    sum_singleton, zero_add, Nat.reduceAdd, h.one, h.two, h.three, two_nsmul, mul_add, add_mul]
  rw [mul_comm (x * (x * x)) x]
  abel

end Comm

/-- A planar binary tree with unlabelled leaves as an element of the free magma on one generator,
its leaves being the `nil`s. -/
def toFreeMagma : BinaryTree Unit → FreeMagma Unit
  | .nil => .of ()
  | .node _ l r => toFreeMagma l * toFreeMagma r

/-- The formal sum of the planar binary trees with `n` leaves. -/
noncomputable def planarSum : ℕ → FreeNonUnitalNonAssocAlgebra ℤ Unit
  | 0 => 0
  | n + 1 => ∑ P ∈ BinaryTree.treesOfNumNodesEq n, MonoidAlgebra.single (toFreeMagma P) 1

theorem isMergeSolution_planarSum :
    IsMergeSolution (FreeNonUnitalNonAssocAlgebra.of ℤ ()) planarSum := by
  refine isMergeSolution_iff.2 ⟨rfl, ?_, fun n ↦ ?_⟩
  · simp [planarSum, toFreeMagma, FreeNonUnitalNonAssocAlgebra.of]
  · rw [planarSum, BinaryTree.treesOfNumNodesEq_succ, sum_biUnion]
    · refine sum_congr rfl fun p _ ↦ ?_
      simp only [BinaryTree.pairwiseNode, sum_map, sum_product, planarSum, sum_mul, mul_sum,
        MonoidAlgebra.single_mul_single, mul_one]
      rw [sum_comm]
      rfl
    · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
      aesop

/-- The series `X = ∑ₗ Xₗ` of Proposition 1.10.2: the sum of the planar binary trees, their planar
structure forgotten. -/
noncomputable def mergeSolution : ℕ → FreeCommNonUnitalNonAssocAlgebra ℤ Unit :=
  FreeNonUnitalNonAssocAlgebra.toComm ℤ ∘ planarSum

/-- Proposition 1.10.2: the sum of the planar binary trees, their planar structure forgotten,
solves (1.10.1) with `X₁ = x`. -/
theorem isMergeSolution_mergeSolution :
    IsMergeSolution (FreeCommNonUnitalNonAssocAlgebra.of ℤ ()) mergeSolution :=
  FreeNonUnitalNonAssocAlgebra.toComm_of ℤ () ▸
    isMergeSolution_planarSum.map (FreeNonUnitalNonAssocAlgebra.toComm ℤ)

/-- The coefficient of a nonplanar tree in `Xₙ₊₁` is its number of planar embeddings. -/
theorem coeff_mergeSolution_succ (n : ℕ) (T : FreeCommMagma Unit) :
    (mergeSolution (n + 1)).coeff T =
      #{P ∈ BinaryTree.treesOfNumNodesEq n | (toFreeMagma P).toFreeCommMagma = T} := by
  simp only [mergeSolution, Function.comp_apply, planarSum, map_sum,
    FreeNonUnitalNonAssocAlgebra.toComm_single, MonoidAlgebra.coeff_sum, Finset.sum_apply',
    MonoidAlgebra.coeff_single, Finsupp.single_apply, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- The sum of the coefficients, the homomorphism to `ℤ` sending the generator to `1`. -/
noncomputable def coeffSum : FreeCommNonUnitalNonAssocAlgebra ℤ Unit →ₙₐ[ℤ] ℤ :=
  FreeCommNonUnitalNonAssocAlgebra.lift ℤ fun _ ↦ 1

theorem isMergeSolution_catalan :
    IsMergeSolution (1 : ℤ) fun n ↦ n.casesOn 0 fun k ↦ (catalan k : ℤ) :=
  isMergeSolution_iff.2 ⟨rfl, by simp, fun n ↦ by simp [catalan_succ']⟩

-- The coefficients of `Xₙ₊₁` sum to the Catalan number `Cₙ`.
theorem coeffSum_mergeSolution_succ (n : ℕ) : coeffSum (mergeSolution (n + 1)) = catalan n := by
  have h := isMergeSolution_mergeSolution.map coeffSum
  rw [coeffSum, FreeCommNonUnitalNonAssocAlgebra.lift_of_apply] at h
  exact congrFun (h.eq isMergeSolution_catalan) (n + 1)

end CoreMerge

/-! ### Externalization (§1.12–1.13) -/

/-- A determiner over a noun, in which `D` selects `N` and so projects. -/
private def theDog : SyntacticObject :=
  merge (leaf ⟨.of .D [.N] (phonForm := "the"), 0⟩) (leaf ⟨.of .N [] (phonForm := "dog"), 1⟩)

/-- In the harmonic head-initial planarization the projecting `D` comes first. -/
example : (theDog.linearize? .left).map (·.yield.map (·.id)) = some [0, 1] := by decide

/-- In the harmonic head-final planarization the same head function is mirrored. -/
example : (theDog.linearize? .right).map (·.yield.map (·.id)) = some [1, 0] := by decide

example : (theDog.linearize? .left).map (·.yield.filterMap (·.item.phonForm?)) =
    some ["the", "dog"] := by decide

/-- Merging *the* on the left of *dog*, which it selects, is harmonic for a head-initial
language, so that derivation records the head-initial planarization
(`Derivation.externalize?_eq_linearized?`); merging it on the right is not harmonic. -/
example :
    Step.HarmonicList (headHom .left) selectionHead
        [.em .left (.leaf ⟨.of .D [.N] (phonForm := "the"), 0⟩)]
        ⟨.leaf ⟨.of .N [] (phonForm := "dog"), 1⟩, []⟩ ∧
      ¬ Step.HarmonicList (headHom .left) selectionHead
        [.em .right (.leaf ⟨.of .D [.N] (phonForm := "the"), 0⟩)]
        ⟨.leaf ⟨.of .N [] (phonForm := "dog"), 1⟩, []⟩ :=
  ⟨⟨⟨rfl, by decide⟩, trivial⟩, fun ⟨⟨_, h⟩, _⟩ ↦ absurd h (by decide)⟩

/-- A harmonic derivation with movement: the verb selects the determiner, tense selects the verb
and then the determiner, which raises to the right of a head-initial tense, leaving the trace
numbered by its place among the movers. -/
private def raisedD : Derivation ℕ :=
  ⟨.leaf ⟨.of .D [], 2⟩, [.em .left (.leaf ⟨.of .V [.D], 1⟩),
    .em .left (.leaf ⟨.of .T [.V, .D], 3⟩), .im (.leaf ⟨.of .D [], 2⟩) .right]⟩

example : raisedD.externalize? raisedD.moverIndex =
    ((LinearizationState.licensing .left).hom raisedD
      (raisedD.final raisedD.moverIndex)).linearized? :=
  Derivation.externalize?_eq_linearized? (LinearizationState.linearizes_hom raisedD) rfl rfl
    (by decide)

/-- Exocentric Merge of two saturated `N`s, neither selecting the other, determines no head and
no order. -/
private def exoNN : SyntacticObject :=
  merge (leaf ⟨.of .N [] (phonForm := "cats"), 0⟩) (leaf ⟨.of .N [] (phonForm := "dogs"), 1⟩)

example : exoNN.linearize? .left = none ∧ exoNN.linearize? .right = none := by decide

/-! ### FormSet (§1.16) -/

section FormSet

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- FormSet `FS^(k) = ⊔ ∘ (B ⊗ id) ∘ Π_(k) ∘ Δ_P` (Definition 1.16.1, (1.16.2)) splits the
workspace by the primitive coproduct, keeps the terms whose left factor has `k` components,
grafts those under a new root labelled `a`, and multiplies back. -/
noncomputable def formSet (a : α) (k : ℕ) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mul' R _ ∘ₗ (bPlus a).rTensor _ ∘ₗ (homogeneousComponent k).rTensor _ ∘ₗ
    comulPrim.toLinearMap

variable [DecidableEq α]

/-- FormSet sums `B(S) ⊔ (F - S)` over the `k`-component subworkspaces `S` of `F`, with multiplicity
(Remark 1.16.4). -/
theorem formSet_of' (a : α) (k : ℕ) (F : Forest (UnorderedTree α)) :
    formSet (R := R) a k (of' F) =
      ((F.powersetCard k).map fun S ↦ of' (.node a S ::ₘ (F - S))).sum := by
  rw [formSet, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, rTensor_homogeneousComponent_comulPrim_of', map_multiset_sum,
    map_multiset_sum, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun S _ ↦ ?_)
  simp [bPlus_of']

theorem formSet_of'_of_card_lt (a : α) {k : ℕ} {F : Forest (UnorderedTree α)}
    (h : F.card < k) : formSet (R := R) a k (of' F) = 0 := by
  rw [formSet_of', Multiset.powersetCard_eq_empty _ h, Multiset.map_zero, Multiset.sum_zero]

-- p. 144
theorem formSet_of'_card (a : α) (F : Forest (UnorderedTree α)) :
    formSet (R := R) a F.card (of' F) = ofTree (.node a F) := by
  simp [formSet_of']

/-- A forest is an extended workspace, in `𝔉̃ᴿ` of (1.16.3), when each component is a syntactic
object or a bare root of any valence over syntactic objects, binary below that root. -/
def IsExtendedWorkspace (G : Forest (UnorderedTree Vertex)) : Prop :=
  ∀ T ∈ G, IsSyntacticObject T ∨
    ∃ S : Forest (UnorderedTree Vertex), T = .node Vertex.bare S ∧ ∀ T' ∈ S, IsSyntacticObject T'

-- Definition 1.16.1
theorem map_formSet_le (k : ℕ) :
    (Submodule.span R (of' '' {F | ∀ T ∈ F, IsSyntacticObject T})).map
        (formSet Vertex.bare k) ≤
      Submodule.span R (of' '' {G | IsExtendedWorkspace G}) := by
  rw [Submodule.map_span_le]
  rintro _ ⟨F, hF, rfl⟩
  rw [formSet_of']
  refine multiset_sum_mem _ fun x hx ↦ ?_
  obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp hx
  refine Submodule.subset_span ⟨_, fun T hT ↦ ?_, rfl⟩
  rw [Multiset.mem_powersetCard] at hS
  rcases Multiset.mem_cons.mp hT with rfl | hT
  · exact .inr ⟨S, rfl, fun T' hT' ↦ hF T' (Multiset.mem_of_le hS.1 hT')⟩
  · exact .inl (hF T (Multiset.mem_of_le (Multiset.sub_le_self F S) hT))

end FormSet

/-! ### Head-following characters and their renormalization (§3.2) -/

-- Lemma 1.3.3
theorem ofTree_toUnorderedTree_merge {R : Type*} [CommSemiring R] (l r : SyntacticObject) :
    (ofTree (merge l r).toUnorderedTree : ConnesKreimer R (UnorderedTree Vertex)) =
      bPlus Vertex.bare (ofTree l.toUnorderedTree * ofTree r.toUnorderedTree) := by
  rw [← of'_singleton l.toUnorderedTree, ← of'_singleton r.toUnorderedTree, ← of'_add, bPlus_of',
    toUnorderedTree_merge]
  rfl

section HeadProbe

variable {ℛ : Type*}

section CommSemiring

variable [CommSemiring ℛ] (Υ : LexicalItem.Token → ℛ)

/-- (3.2.1): the head-probe value `Υ_{s,h}` of a tree, the probe `Υ` at the head of the tree by
selection, and zero on a tree without a head. -/
def headProbeTree (T : UnorderedTree Vertex) : ℛ :=
  (treeSelectionState T).head.elim 0 Υ

@[simp] theorem headProbeTree_toUnorderedTree (S : SyntacticObject) :
    headProbeTree Υ S.toUnorderedTree = S.selectionHead.elim 0 Υ := by
  rw [headProbeTree, treeSelectionState_toUnorderedTree]
  rfl

/-- The head-following character `ϕ_{Υ,s,h}` of Lemma 3.2.5, the algebra homomorphism extending
`Υ_{s,h}` multiplicatively to forests. -/
noncomputable def headProbeChar : ConnesKreimer ℕ (UnorderedTree Vertex) →ₐ[ℕ] ℛ :=
  aeval (headProbeTree Υ)

@[simp] theorem headProbeChar_apply_of' (F : Forest (UnorderedTree Vertex)) :
    headProbeChar Υ (of' F) = (F.map (headProbeTree Υ)).prod :=
  aeval_of' _ F

@[simp] theorem headProbeChar_apply_ofTree (T : UnorderedTree Vertex) :
    headProbeChar Υ (ofTree T) = headProbeTree Υ T :=
  aeval_ofTree _ T

-- A probe that is zero on every item has renormalized part zero, under any operator.
theorem birkhoffPlusTree_headProbeChar_zero (P : ℛ →+ ℛ) (T : UnorderedTree Vertex) :
    birkhoffPlusTree (headProbeChar (0 : LexicalItem.Token → ℛ)).toLinearMap P T = 0 :=
  birkhoffPlusTree_eq_zero (fun T ↦ by
    rw [AlgHom.toLinearMap_apply, headProbeChar_apply_ofTree, headProbeTree]
    cases (treeSelectionState T).head <;> rfl) T

/-- The character is zero on the exocentric Merge of two saturated nouns, which has no head. -/
example : headProbeChar Υ (ofTree exoNN.toUnorderedTree) = 0 := by
  rw [headProbeChar_apply_ofTree, headProbeTree_toUnorderedTree,
    show exoNN.selectionHead = none by decide]
  rfl

end CommSemiring

variable [IdemCommSemiring ℛ] (Υ : LexicalItem.Token → ℛ)

/-- Lemma 3.2.7: into an idempotent semiring, the Birkhoff factorization with respect to the
identity gives a syntactic object a value at least that of the probe at its head. -/
theorem selectionHead_le_birkhoffPlusTree (S : SyntacticObject) :
    S.selectionHead.elim 0 Υ ≤
      birkhoffPlusTree (headProbeChar Υ).toLinearMap (.id ℛ) S.toUnorderedTree := by
  simpa using le_birkhoffPlusTree_id (headProbeChar Υ).toLinearMap S.toUnorderedTree

/-- On *the dog* the renormalized value is at least the probe at the determiner. -/
example : Υ ⟨.of .D [.N] (phonForm := "the"), 0⟩ ≤
    birkhoffPlusTree (headProbeChar Υ).toLinearMap (.id ℛ) theDog.toUnorderedTree := by
  simpa [show theDog.selectionHead = some ⟨.of .D [.N] (phonForm := "the"), 0⟩ by decide] using
    selectionHead_le_birkhoffPlusTree Υ theDog

end HeadProbe

/-! ### Minimal Yield and the polar part of Laurent series (§3.5.2) -/

section Laurent

open HahnSeries

variable {α β R : Type*} [CommRing R]

/-- The projection `R` of Laurent series onto their polar part (3.5.4), as an additive map. -/
local notation "𝐑" => LinearMap.toAddMonoidHom (truncLTLinearMap R (0 : ℤ))

section Gradings

variable (F F' : Forest (UnorderedTree (α ⊕ β)))

/-- `δb₀ F F' = b₀ F − b₀ F'`, nonnegative iff `F → F'` does not diverge. -/
def δb₀ : ℤ := (Multiset.card F : ℤ) - Multiset.card F'

/-- `δα F F' = α F' − α F`, nonnegative iff `F → F'` loses no information. -/
def δα : ℤ := ((F'.map UnorderedTree.numEdges).sum : ℤ) - (F.map UnorderedTree.numEdges).sum

/-- `δσ F F' = σ F' − σ F`, equal to `1` iff `F → F'` has minimal yield. -/
def δσ : ℤ := ((F'.map UnorderedTree.numNodes).sum : ℤ) - (F.map UnorderedTree.numNodes).sum

theorem δσ_eq : δσ F F' = δα F F' - δb₀ F F' := by
  simp only [δσ, δα, δb₀, UnorderedTree.sum_map_numNodes]; omega

theorem minimalYieldWeak_iff_gradings :
    MinimalYieldWeak UnorderedTree.numEdges F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' := by
  simp only [δb₀, δα, sub_nonneg, Nat.cast_le]
  exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

theorem minimalYield_iff_gradings :
    MinimalYield UnorderedTree.numEdges F F' ↔ 0 ≤ δb₀ F F' ∧ 0 ≤ δα F F' ∧ δσ F F' = 1 := by
  rw [← and_assoc, ← minimalYieldWeak_iff_gradings, δσ_eq, δα, δb₀]
  exact ⟨fun h ↦ ⟨h.1, by have := h.2; omega⟩, fun h ↦ ⟨h.1, by have := h.2; omega⟩⟩

theorem minimalYieldWeak_iff_truncLT [Nontrivial R] :
    MinimalYieldWeak UnorderedTree.numEdges F F' ↔
      truncLT 0 (single (δb₀ F F') (1 : R)) = 0 ∧ truncLT 0 (single (δα F F') (1 : R)) = 0 := by
  simp only [minimalYieldWeak_iff_gradings, truncLT_single_eq_zero_iff one_ne_zero]

end Gradings

/-- The character `ϕt` of Proposition 3.5.3 for `δ = δα`, recording only the grading, sends a
tree `T` to `t^{α(T)}`, multiplicatively over disjoint union. -/
noncomputable def gradingChar : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R :=
  aeval fun T ↦ single (T.numEdges : ℤ) 1

theorem gradingChar_apply_of' (F : Forest (UnorderedTree α)) :
    gradingChar (R := R) (of' F) = single ((F.map UnorderedTree.numEdges).sum : ℤ) 1 := by
  rw [gradingChar, aeval_of']
  induction F using Multiset.induction with
  | empty => simp
  | cons T F ih => simp [ih, single_mul_single, add_comm]

-- Lemma 3.5.5
theorem truncLT_gradingChar_of' (F : Forest (UnorderedTree α)) :
    truncLT 0 (gradingChar (R := R) (of' F)) = 0 := by
  rw [gradingChar_apply_of', truncLT_single, ite_eq_right_iff]
  exact fun h ↦ absurd h (by omega)

/-- `ϕt` is its own renormalized part. Being nonpolar, it has no negative part, so the Birkhoff
factorization removes nothing and cannot separate Sideward Merge from Internal and External
Merge. -/
theorem birkhoffPlus_gradingChar :
    birkhoffPlus (gradingChar (R := R) (α := α)).toLinearMap (-𝐑) = gradingChar :=
  birkhoffPlus_eq_self fun T ↦ by
    simpa [← of'_singleton] using truncLT_gradingChar_of' (R := R) {T}

theorem truncLT_single_mul_ne [Nontrivial R] :
    truncLT 0 (single (-2 : ℤ) (1 : R) * single 1 1)
      ≠ truncLT 0 (single (-2 : ℤ) (1 : R)) * truncLT 0 (single 1 1) := by
  simp [single_mul_single, truncLT_single]

private theorem isRotaBaxter_neg_polar : IsRotaBaxter (1 : ℕ) ⇑(-𝐑 : LaurentSeries R →+ _) := by
  have h : IsRotaBaxter (-1 : ℤ) ⇑(𝐑 : LaurentSeries R →+ LaurentSeries R) := by
    simpa using isRotaBaxter_truncLT (Γ := ℤ) (R := R) ℤ
  replace h := h.neg
  rw [neg_neg] at h
  exact isRotaBaxter_one_iff.2 (isRotaBaxter_one_iff.1 h)

-- Proposition 3.1.7
theorem truncLT_birkhoffMinus_of' (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R)
    {F : Forest (UnorderedTree α)} (hF : F ≠ 0) :
    truncLT 0 (birkhoffMinus φ.toLinearMap (-𝐑) (of' F))
      = birkhoffMinus φ.toLinearMap (-𝐑) (of' F) := by
  obtain ⟨y, hy⟩ := birkhoffMinus_of'_mem_range (φ := φ.toLinearMap) isRotaBaxter_neg_polar hF
  rw [← hy]
  simp [truncLT_neg]

-- Proposition 3.1.7, Proposition 3.5.6
theorem truncLT_birkhoffPlus_of' (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R)
    (F : Forest (UnorderedTree α)) : truncLT 0 (birkhoffPlus φ.toLinearMap (-𝐑) (of' F)) = 0 := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp [← single_zero_one, truncLT_single]
  obtain ⟨y, hy⟩ := birkhoffPlus_of'_mem_range (φ := φ.toLinearMap) isRotaBaxter_neg_polar hF
  rw [← hy]
  simp [← sub_eq_add_neg, truncLT_sub]

end Laurent

/-! ### Obligatory control by Form Copy (§3.8.2) -/

/-- The controller *the man*, from tokens 0 and 1. -/
noncomputable def theMan : SyntacticObject :=
  merge (leaf ⟨.of .D [.N] "the", 0⟩) (leaf ⟨.of .N [] "man", 1⟩)

/-- The controlled subject *the man*, from fresh tokens 4 and 5. -/
noncomputable def theMan' : SyntacticObject := theMan.renumber 4

/-- *a book*, the object of *read*. -/
noncomputable def aBook : SyntacticObject :=
  merge (leaf ⟨.of .D [.N] "a", 7⟩) (leaf ⟨.of .N [] "book", 8⟩)

/-- The syntactic object (3.8.4) of *the man tried to read a book* is built by External Merge
alone. The controller merges into the theta position of *tried* and the controlled subject into
that of *read*, since Internal Merge into a theta position would break the dichotomy of §3.8.1. -/
noncomputable def triedToRead : SyntacticObject :=
  merge theMan (merge (leaf ⟨.of .V [.T] "tried", 2⟩) (merge (leaf ⟨.of .T [.V] "to", 3⟩)
    (merge theMan' (merge (leaf ⟨.of .V [.D] "read", 6⟩) aBook))))

theorem theMan_isRepetition : IsRepetition theMan theMan' :=
  ⟨structurallyIdentical_renumber 4 theMan, by simp [theMan, theMan', renumber, merge_eq_merge_iff]⟩

theorem theMan_mem_copyRel : (theMan, theMan') ∈ triedToRead.copyRel :=
  mk_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains]) theMan_isRepetition.1

theorem not_mem_copyRel_aBook : (theMan, aBook) ∉ triedToRead.copyRel := fun h ↦ by
  have := h.2
  simp only [StructurallyIdentical, theMan, aBook, erase, SyntacticObject.map_merge,
    SyntacticObject.map_leaf] at this
  exact absurd this (by decide)

end MarcolliChomskyBerwick2025
