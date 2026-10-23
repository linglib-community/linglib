/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.BirkhoffFactorization
public import Linglib.Core.Algebra.RootedTree.Coproduct.Primitive
public import Linglib.Core.RingTheory.HahnSeries.RotaBaxter
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Syntax.Minimalist.Workspace.Derivation
public import Linglib.Syntax.Minimalist.Workspace.Algebra.Merge.MinimalSearch
public import Linglib.Syntax.Minimalist.Workspace.Algebra.Merge.Sideward
public import Linglib.Syntax.Minimalist.Label.Selection
public import Linglib.Syntax.Minimalist.Copy.FormCopy
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Mathlib.RingTheory.LaurentSeries

/-!
# Marcolli, Chomsky and Berwick (2025): Mathematical Structure of Syntactic Merge

This file formalizes parts of Marcolli, Chomsky and Berwick's algebraic model of Merge.

Internal Merge (§1.4.4) is checked on the book's example, which raises *the apple* out of
`T = {was, {eaten, {the, apple}}}`. The unit stage `M_{T₂,1}` splits `T` into *the apple* beside
the quotient `T/T₂`, the composite with `M_{T/T₂,T₂}` merges the two (Proposition 1.4.2), and the
step satisfies Minimal Yield under trace counting (Proposition 1.6.4).

The core computational structure of Merge (§1.10) is a fixed point. Proposition 1.10.2 works in
`V(𝔗)`, the free `ℤ`-module on the nonplanar binary trees with unlabelled leaves, graded by the
number of leaves. It generates these trees by recursively solving `X = 𝔐(X, X)` over formal sums
`X = ∑ Xₗ`, with the initial condition `X₁ = x`, and reads the integer coefficients of the solution
as numbers of planar embeddings. Here `V(𝔗)` sits in the Connes–Kreimer algebra of unlabelled
trees, Merge is the grafting operator after the disjoint union (Lemma 1.3.3), and a formal sum is a
power series whose degree counts leaves. The sum of the planar binary trees, their planar
structure forgotten, solves the equation (`isMergeSolution_mergeSolution`) and is its only solution
(`IsMergeSolution.eq`). The coefficient of each tree is its number of planar embeddings
(`coeff_planarSum_succ`), and the coefficients of `Xₙ₊₁` sum to the Catalan number `Cₙ`
(`aeval_planarSum_succ`). On syntactic objects, Lemma 1.3.3 is `toCK_merge`.

The book's worked examples of externalization are stated on the `SyntacticObject` carrier of
the Minimalist substrate: the harmonic head-initial and head-final orders of a determiner–noun
Merge, the head-side convention flipping the yield, and exocentric elimination, two saturated
nouns determining no head and hence no order. The framework itself is the `Syntax/Minimalist/`
theory layer; the examples are kernel-checked against it.

FormSet (§1.16) groups components of a workspace under a new root. Definition 1.16.1 writes it as
`⊔ ∘ (B ⊗ id) ∘ Π_(k) ∘ Δ_P`, where the primitive coproduct `Δ_P` splits a workspace in every way,
so `FS^(k)(F)` sums `B(S) ⊔ (F - S)` over the `k`-component subworkspaces `S` (`formSet_of'`). On
workspaces of syntactic objects it lands in the extended workspaces of (1.16.3) (`map_formSet_le`).

The book's syntax–semantics interface (Chapter 3) replaces per-feature checking by a single
recursive map, the Birkhoff renormalization of a character of the Connes–Kreimer Hopf algebra
of the syntactic object. The Boolean parsing semiring `Consistency` of §3.5 is the target,
`toCK` embeds a syntactic object into the Hopf algebra, `featureConsistency` is the renormalized
character, and `headConsistency` instantiates it for the head-following character of Lemma 3.2.5,
whose probe reads the §1.13 selection head. The machinery is noncomputable, so these are
specifications of consistency rather than checkers. In §3.5.2 the operator is the projection of
Laurent series onto their polar part. The renormalized part of any character then lands in the
power series (`truncLT_birkhoffPlus_of'`), while the grading character `ϕt` is already nonpolar
and is its own renormalized part (`birkhoffPlus_gradingChar`), so it cannot single out Sideward
Merge.

Obligatory control (§3.8.2) is derived by External Merge alone. In *the man tried to read a
book* both inscriptions of *the man* merge into theta positions, as repetitions of one another,
and Form Copy restricts the object to the diagonal on which they are one
(`theMan_mem_copyRel`), while *a book*, not structurally identical to *the man*, is no copy of it
(`not_mem_copyRel_aBook`).

## Correspondence with the book

The book's algebra lives in `Core/` and in `Syntax/Minimalist/{Workspace,Merge,Economy}/`:

* Definitions 1.2.6 and 1.2.8 (admissible cuts, the coproducts `Δ^ω`): `ConnesKreimer.cutSummandsN`
  and `comulAlgHomN` for `Δ^ρ`, which Remark 1.2.9 identifies with the Connes–Kreimer coproduct;
  `cutSummandsCN` and `comulCAlgHomN` for `Δ^c`.
* Lemma 1.2.10: `ConnesKreimer.comulCN_coassoc` and the edge grading of `Coproduct/TraceGrading`.
* Lemma 1.2.11 and (1.2.12): `ConnesKreimer.instBialgebraRho`, the `HopfAlgebra` instance, and
  `antipode_ofTree`.
* The projections `Π_{ρ,c}` and `Π_{d,ρ}` and the relations `Δ^d = (id ⊗ Π_{d,ρ}) ∘ Δ^ρ =
  (id ⊗ Π_{d,c}) ∘ Δ^c` displayed before (1.3.10): `ConnesKreimer.eraseTraces`,
  `UnorderedTree.contractUnary`, `ConnesKreimer.cutSummandsDN`, `ConnesKreimer.comulDAlgHomN`,
  `ConnesKreimer.eraseTraces_comulCAlgHomN`, `contractUnary_eraseTraces_comulCAlgHomN`.
* Definition 1.3.4: `Minimalist.Merge.mergeOpG` over a cut enumeration, with `mergeOp` at `Δ^ρ`
  and `mergeOpC` at `Δ^c`; (1.3.11): `Minimalist.Merge.mergeOpG_apply_of'`.
* Lemma 1.4.1: `Minimalist.Merge.mergeOpG_pair`, `mergeOpG_pair_residual`, with the residual
  workspace passing through by `mergeOpG_of'_mul`.
* Proposition 1.4.2: `Minimalist.Merge.mergeOpG_im_composition`; on syntactic objects
  `Minimalist.SyntacticObject.mergeOpC_im`, and for a derivation
  `Minimalist.Derivation.mergeOpList_initial`.
* Lemmas 1.4.4 and 1.4.5: `Minimalist.Merge.mergeOpG_sideward_2b`, `mergeOpG_sideward_3b`,
  `mergeOpG_sideward_3a`.
* (1.5.1) and the weights of §1.5.2: `Minimalist.Merge.comulEps`, `mergeOpEps`, with
  `comulEps_one` and `comulEps_zero` (the primitive coproduct); Proposition 1.5.1 at `ε = 0`:
  `mergeOpEps_zero_of'_of_not_le`, `mergeOpEps_zero_pair_add`; at every `ε`: `mergeOpEps_pair`,
  `mergeOpEps_im_composition`, `mergeOpEps_of'_eq_smul_of_not_le`.
* Definition 1.6.1 and Proposition 1.6.4: `Minimalist.MinimalYield` over a counting,
  `MinimalYield.em_pair`, `em_pair_accessibleCount`, `im_accessibleCount_of_cut`.
* Lemma 1.6.3 (1.6.8) and (1.6.10): `ConnesKreimer.cutSummandsCN_accessibleCount`,
  `cutSummandsCN_accessibleSize`. Proposition 1.6.8 and
  Remark 1.6.7, on the terms of Merge (`Minimalist.Merge.mergeOpG_apply_of'_eq_sum`):
  `Minimalist.card_singleton_add_trunk_add_numWhole`, `accessibleCount_merge_term`,
  `accessibleSize_merge_term`, `MinimalYield.merge_term_accessibleCount_iff`,
  `accessibleCount_unit_term` for `Δ^c`, and `MinimalYield.merge_term_numEdges_iff` for `Δ^d`.
  Remark 1.6.9, Sideward Merge of type 2(b) on the workspace of §1.3.4:
  `MarcolliChomskyBerwick2025.sideward2b_minimalYield`.
* Lemma 1.6.3 (1.6.7): `ConnesKreimer.cutSummandsDN_numEdges`, from the unary vertices a cut
  leaves (`ConnesKreimer.cutSummandsN_numUnary`); for Internal Merge,
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
  `ConnesKreimer.cutSummandsCN_numNodes`.
* The functionals of (1.7.5) and their Lie algebra: `Bialgebra.IsDualPrimitive` and
  `Bialgebra.dualPrimitives`; they are supported on single trees
  (`ConnesKreimer.isDualPrimitive_iff`).
* Lemma 1.7.3, for `Δ^ρ` and grafting at vertices: `ConnesKreimer.isDualPrimitive_lcoeff_iff`,
  `lie_lcoeff_singleton_apply_ofTree`, `lie_lcoeff_singleton_apply_of'`, and
  `GrossmanLarson.pairingLie` for the bracket of the grafting product.
* Definition 3.1.1 and the weight `+1` identity of Definition 3.1.2: `IsRotaBaxter` at weights
  `-1` and `+1`; the identity operator of Remark 3.2.2, at weight `+1` on the Boolean semiring:
  `Consistency.isRotaBaxter_id`.
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

The equation carries its initial term, `X = x t + 𝔐(X, X)`. The book writes `X = 𝔐(X, X)` and
supplies `X₁ = x` as an initial condition, but `𝔐(X, X)` has no degree-one term
(`coeff_one_mergeSeries`), so the leaf enters as an inhomogeneous term.

`TreeAlgebra` is spanned by the forests of unlabelled trees, not only by the binary trees of `𝔗`.
`V(𝔗)` is the span of the single binary trees in it, and every term of the solution lies there.

`formSet` is defined for every `k` on all forests, with the root label of `B` a parameter.
Definition 1.16.1 takes `k ≥ 3` and the domain `V(𝔉_{SO₀})` of workspaces of syntactic objects;
`map_formSet_le` is stated on that domain, with the bare root label of the syntactic objects.

The proof of Proposition 1.10.2 prints `X₄ = 2{x{x{xx}}} + {{xx}{xx}}`. Its recursion gives
`𝔐(X₁, X₃) + 𝔐(X₂, X₂) + 𝔐(X₃, X₁) = 4{x{x{xx}}} + {{xx}{xx}}` (`planarSum_four`), and four is
the number of planar embeddings that the proof says the coefficient counts: the five planar binary
trees with four leaves split as four and one.

Definition 3.1.2's weight `-1` semiring identity
`R(a) ⊙ R(b) ⊡ R(a ⊙ b) = R(a ⊙ R(b)) ⊡ R(R(a) ⊙ b)` is not the `IsRotaBaxter` identity at any
weight, and Remark 3.2.2 and Lemma 3.2.7 use `R = id` at that weight on the tropical semiring. On
`Consistency` the identity has weight `+1` as well, since disjunction is idempotent, and the
consistency maps use it at that weight.

## TODO

§1.17 reads (1.10.1) as the quadratic case of the combinatorial Dyson–Schwinger equation
`X = B(P(X))` of (1.17.2), with the grafting operator `B` of Definition 1.3.2 and the recursive
solution (1.17.3), which the book cites rather than proves. Stating it needs `B` on formal series
in the grading by vertices, in which `B` raises the degree by one. With `x = B(1)` the Merge case
is `P(t) = 1 + t²`, while the book writes `P(X) = X²` next to its requirement `a₀ = 1`.

Lemma 1.10.1 identifies `𝔗` with the free nonassociative commutative magma on one generator,
stated below as `carrierEmptyEquiv` on the carrier over the empty lexicon; the carrier over a
lexicon is the free commutative magma on its leaf alphabet,
`SyntacticObject.equivFreeCommMagma`. The identification of `TreeAlgebra`'s binary span with the
carrier over the empty lexicon is not stated.

Lemma 1.16.5 extends the coproducts `Δ^ω` to extended workspaces by excluding the cuts of edges at
a root of valence at least three, so that Merge does not undo the grouping FormSet builds
(§1.16.2). It is not formalized.

Proposition 1.6.8's row for the Sideward case 3(a) under `Δ^d` lowers `α` by two, counting two
contracted edges. When the two terms are sisters, as *the* and *apple* are in *the apple*, the
deletion leaves their parent a leaf and contracts nothing, so `α` is unchanged. The term still
diverges, so the proposition's conclusion stands.

Corollary 3.5.4's character `ψt` sums over the pairs of intermediate derivations of a target,
which needs a Merge step relation on workspaces; it, and Proposition 3.5.6 beyond the first step of
its proof, are not formalized.

The book's section locators (§1.12.1, §1.13, §1.13.2) are transcribed from an earlier
version of this file and are UNVERIFIED against the published text.

## References

* [marcolli-chomsky-berwick-2025]
* [chomsky-etal-2023]
-/

@[expose] public section

namespace MarcolliChomskyBerwick2025

open RoseTree UnorderedTree Minimalist SyntacticObject ConnesKreimer

/-! ### Internal Merge: an example (§1.4.4) -/

/-- *the apple*, the term `T₂` that Internal Merge raises in §1.4.4. -/
def theAppleLinearized : LinearizedSyntacticObject :=
  LinearizedSyntacticObject.merge (.leaf ⟨.of .D [.N] "the", 0⟩) (.leaf ⟨.of .N [] "apple", 1⟩)

/-- *the apple* as a syntactic object. -/
def theApple : SyntacticObject := theAppleLinearized.toSyntacticObject

/-- The workspace `T = {was, {eaten, {the, apple}}}` of §1.4.4. -/
private def wasEatenTheApple : SyntacticObject :=
  (LinearizedSyntacticObject.merge (.leaf ⟨.of .T [.V] "was", 2⟩)
    (.merge (.leaf ⟨.of .V [.D] "eaten", 3⟩)
      (.merge (.leaf ⟨.of .D [.N] "the", 0⟩) (.leaf ⟨.of .N [] "apple", 1⟩)))).toSyntacticObject

/-- The quotient `T/T₂`, with the trace of the head *the* in place of *the apple*. -/
private def wasEatenTrace : SyntacticObject :=
  (LinearizedSyntacticObject.merge (.leaf ⟨.of .T [.V] "was", 2⟩)
    (.merge (.leaf ⟨.of .V [.D] "eaten", 3⟩) (.traceOf ⟨.of .D [.N] "the", 0⟩))).toSyntacticObject

/-- The remainder of raising *the apple* out of `T` is the quotient `T/T₂`. -/
example : deleteAccessible theApple wasEatenTheApple = wasEatenTrace := by decide

/-- The first stage `M_{T₂,1}` splits `T` into `T₂` beside the quotient `T/T₂`. -/
example :
    Merge.mergeOpUnitC (R := ℤ) traceEncoder theApple.val
        (of' ({wasEatenTheApple.val} : Forest (UnorderedTree Vertex)))
      = of' ({theApple.val, wasEatenTrace.val} : Forest (UnorderedTree Vertex)) := by
  rw [mergeOpUnitC_current (by decide) (by decide) (by decide),
    show deleteAccessible theApple wasEatenTheApple = wasEatenTrace by decide]

/-- The composite `M_{T/T₂,T₂} ∘ M_{T₂,1}` is Internal Merge of *the apple*: it merges `T₂` with the
    quotient `T/T₂` (Proposition 1.4.2). -/
example :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare wasEatenTrace.val theApple.val
        (Merge.mergeOpUnitC traceEncoder theApple.val
          (of' ({wasEatenTheApple.val} : Forest (UnorderedTree Vertex))))
      = of' ({(merge wasEatenTrace theApple).val} : Forest (UnorderedTree Vertex)) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact mergeOpC_im (by decide) (by decide) (by decide)

/-- This Internal Merge satisfies Minimal Yield under trace counting, the Δᶜ row of the table of
    Proposition 1.6.4. -/
example :
    MinimalYield UnorderedTree.accessibleCount
      (({wasEatenTheApple} : Workspace).map Subtype.val)
      (({merge wasEatenTrace theApple} : Workspace).map Subtype.val) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact Step.minimalYield (step := .im theApple) (W := 0)
    ⟨by decide, by decide, by decide, by simp⟩ (by decide) (by simp [Step.items])

/-- It loses no complexity graded by the size `σ`: *was eaten the apple* goes to the Merge of
    *the apple* with the remainder, of one greater size (Proposition 1.6.10). -/
example :
    NoComplexityLoss (fun T ↦ Forest.accessibleSize {T})
      (({wasEatenTheApple} : Workspace).map Subtype.val)
      (({merge wasEatenTrace theApple} : Workspace).map Subtype.val) := by
  rw [show wasEatenTrace = deleteAccessible theApple wasEatenTheApple by decide]
  exact Step.noComplexityLoss (step := .im theApple) (W := 0)
    ⟨by decide, by decide, by decide, by simp⟩ (by decide) (by simp [Step.items])

/-! ### Sideward Merge, Minimal Search and economy on the workspace of §1.3.4

The workspace `{eaten, {the, apple}}` of §1.3.4 also admits Sideward Merge of type 2(b), which
merges *eaten* with *the* cut out of *the apple*, and *the apple* alone admits Internal Merge of
*the* and Sideward Merge of type 3(a) of *the* and *apple*. On these the general results of §1.4–1.6
give Sideward Merge a nonzero term, which Minimal Search removes at `ε = 0` while it keeps
External and Internal Merge. The 2(b) term satisfies Minimal Yield under trace counting, as
Remark 1.6.9 says. No Complexity Loss excludes it at the pruning cuts graded by vertices, and at
the trace cuts graded by the size `σ`. At the trace cuts the vertex count does not exclude it,
because the trace of *the* takes the place of *the*. -/

/-- *the*, a term of *the apple*. -/
def theD : SyntacticObject :=
  (LinearizedSyntacticObject.leaf ⟨.of .D [.N] "the", 0⟩).toSyntacticObject

/-- *apple*, the other term of *the apple*. -/
def appleN : SyntacticObject :=
  (LinearizedSyntacticObject.leaf ⟨.of .N [] "apple", 1⟩).toSyntacticObject

/-- *eaten*, the other component of the workspace of §1.3.4. -/
def eaten : SyntacticObject :=
  (LinearizedSyntacticObject.leaf ⟨.of .V [.D] "eaten", 3⟩).toSyntacticObject

/-- External Merge of *the apple* with *eaten* loses no complexity graded by the size `σ`: its term
    of Merge takes both whole (Proposition 1.6.10). -/
example :
    NoComplexityLoss (fun T ↦ Forest.accessibleSize {T})
      (({eaten, theApple} : Workspace).map Subtype.val)
      (({merge theApple eaten} : Workspace).map Subtype.val) :=
  Step.noComplexityLoss (step := .em .left theAppleLinearized) (W := 0) (by simp [Step.Admissible])
    (by decide) (by simp only [Step.items, Multiset.mem_singleton, forall_eq]; decide)

/-- The four pruning cuts of *the apple*. -/
private theorem cutSummandsN_theApple : cutSummandsN theApple.val =
    {({theD.val, appleN.val}, UnorderedTree.leaf Vertex.bare),
      ({theD.val}, UnorderedTree.node Vertex.bare {appleN.val}),
      ({appleN.val}, UnorderedTree.node Vertex.bare {theD.val}),
      (0, theApple.val)} := by
  rw [show theApple.val = UnorderedTree.node Vertex.bare {theD.val, appleN.val} from
      congrArg Subtype.val (by decide : theApple = merge theD appleN),
    cutSummandsN_node, forestCutsG_pair,
    show theD.val = UnorderedTree.leaf (Vertex.lex ⟨.of .D [.N] "the", 0⟩) from rfl,
    show appleN.val = UnorderedTree.leaf (Vertex.lex ⟨.of .N [] "apple", 1⟩) from rfl,
    treeCutsG, treeCutsG, cutSummandsN_leaf, cutSummandsN_leaf]
  simp [combinerProjG, Multiset.cons_product, -cutSummandsN_mk]
  exact Multiset.cons_swap _ _ _

/-- The pruning cut extracting *the* from *the apple* is the only one with crown `{the}`. -/
private theorem filter_cutSummandsN_theApple :
    (cutSummandsN theApple.val).filter (·.1 = {theD.val}) =
      {({theD.val}, UnorderedTree.node Vertex.bare {appleN.val})} := by
  have hne : (UnorderedTree.leaf (Vertex.lex ⟨.of .N [] "apple", 1⟩) : UnorderedTree Vertex) ≠
      UnorderedTree.leaf (Vertex.lex ⟨.of .D [.N] "the", 0⟩) :=
    fun h ↦ (by decide : appleN ≠ theD) (Subtype.ext h)
  have hcard (a b : UnorderedTree Vertex) : a ::ₘ {b} ≠ {a} := fun h ↦ by
    simpa using congrArg Multiset.card h
  rw [show theApple.val = UnorderedTree.node Vertex.bare {theD.val, appleN.val} from
      congrArg Subtype.val (by decide : theApple = merge theD appleN),
    cutSummandsN_node, forestCutsG_pair,
    show theD.val = UnorderedTree.leaf (Vertex.lex ⟨.of .D [.N] "the", 0⟩) from rfl,
    show appleN.val = UnorderedTree.leaf (Vertex.lex ⟨.of .N [] "apple", 1⟩) from rfl,
    treeCutsG, treeCutsG, cutSummandsN_leaf, cutSummandsN_leaf]
  simp [combinerProjG, Multiset.cons_product, Multiset.filter_singleton, hne, hcard,
    -cutSummandsN_mk]

/-- Sideward Merge of type 2(b) at the trace cuts merges *eaten* with *the* beside the remainder
    of *the apple* (Lemma 1.4.4). -/
example :
    Merge.mergeOpC (R := ℤ) traceEncoder Vertex.bare eaten.val theD.val
        (of' ({eaten.val, theApple.val} : Forest (UnorderedTree Vertex))) =
      of' ({(merge eaten theD).val, (deleteAccessible theD theApple).val} :
        Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpC, Merge.mergeOpG_sideward_2b Vertex.bare
      (by rw [val_mem_subtrees]; decide) (fun h ↦ (by decide : theD ≠ theApple) (Subtype.ext h)),
    cutSummandsCN_filter_mover (by decide) (by decide) (by decide), Multiset.map_singleton,
    Multiset.sum_singleton, merge_val, ← of'_singleton, ← of'_add]
  rfl

/-- At `ε = 1` weighted Sideward Merge of type 2(b) is Sideward Merge at the pruning cuts. -/
example :
    Merge.mergeOpEps (R := ℤ) 1 Vertex.bare eaten.val theD.val
        (of' ({eaten.val, theApple.val} : Forest (UnorderedTree Vertex))) =
      of' ({(merge eaten theD).val, UnorderedTree.node Vertex.bare {appleN.val}} :
        Forest (UnorderedTree Vertex)) := by
  rw [Merge.mergeOpEps_one, Merge.mergeOp, Merge.mergeOpG_sideward_2b Vertex.bare
      (by rw [val_mem_subtrees]; decide) (fun h ↦ (by decide : theD ≠ theApple) (Subtype.ext h)),
    filter_cutSummandsN_theApple, Multiset.map_singleton, Multiset.sum_singleton, merge_val,
    ← of'_singleton, ← of'_add]
  rfl

/-- At `ε = 0` Minimal Search removes it (Proposition 1.5.1). -/
example :
    Merge.mergeOpEps (R := ℤ) 0 Vertex.bare eaten.val theD.val
      (of' ({eaten.val, theApple.val} : Forest (UnorderedTree Vertex))) = 0 :=
  Merge.mergeOpEps_zero_of'_of_not_le _ (by decide)

/-- At every `ε` it is a multiple of `ε`, so Sideward Merge costs at least one
    (Proposition 1.5.1). -/
example (ε : ℤ) : ∃ y, Merge.mergeOpEps ε Vertex.bare eaten.val theD.val
    (of' ({eaten.val, theApple.val} : Forest (UnorderedTree Vertex))) = ε • y :=
  Merge.mergeOpEps_of'_eq_smul_of_not_le ε _ (by decide)

/-- At `ε = 0` External Merge of the two components survives. -/
example :
    Merge.mergeOpEps (R := ℤ) 0 Vertex.bare eaten.val theApple.val
        (of' ({eaten.val, theApple.val} : Forest (UnorderedTree Vertex))) =
      of' ({(merge eaten theApple).val} : Forest (UnorderedTree Vertex)) := by
  simpa using Merge.mergeOpEps_zero_pair_add (R := ℤ) (F := 0) Vertex.bare
    (S := eaten.val) (S' := theApple.val) (Multiset.notMem_zero _) (Multiset.notMem_zero _)

/-- At `ε = 0` Internal Merge of *the* inside *the apple* survives, while Sideward Merge of the
    same *the* does not. -/
example :
    Merge.mergeOpEps (R := ℤ) 0 Vertex.bare (UnorderedTree.node Vertex.bare {appleN.val}) theD.val
        (Merge.mergeOpUnit theD.val (of' ({theApple.val} : Forest (UnorderedTree Vertex)))) =
      of' ({UnorderedTree.node Vertex.bare
              {UnorderedTree.node Vertex.bare {appleN.val}, theD.val}} :
        Forest (UnorderedTree Vertex)) :=
  Merge.mergeOpEps_im_composition _ _ _ _ _ _ filter_cutSummandsN_theApple rfl
    (fun h ↦ (by decide : theApple ≠ theD) (Subtype.ext h))

private theorem mem_cutSummandsCN_theApple :
    ({theD.val}, (deleteAccessible theD theApple).val) ∈ cutSummandsCN traceEncoder theApple.val :=
  Multiset.mem_of_mem_filter (p := fun p ↦ p.1 = {theD.val}) (by
    rw [cutSummandsCN_filter_mover (by decide) (by decide) (by decide)]
    exact Multiset.mem_singleton_self _)

/-- The term of Sideward Merge of type 2(b) at the trace cuts takes *eaten* whole and cuts *the*
    out of *the apple*. -/
private noncomputable def sidewardTermC : CutChoice Vertex :=
  {(eaten.val, ({eaten.val}, 0)),
    (theApple.val, ({theD.val}, {(deleteAccessible theD theApple).val}))}

/-- The same term at the pruning cuts. -/
private noncomputable def sidewardTermN : CutChoice Vertex :=
  {(eaten.val, ({eaten.val}, 0)),
    (theApple.val, ({theD.val}, {UnorderedTree.node Vertex.bare {appleN.val}}))}

private theorem sidewardTermC_mem :
    sidewardTermC ∈ forestCutChoicesG (cutSummandsCN traceEncoder) {eaten.val, theApple.val} := by
  rw [Multiset.insert_eq_cons, forestCutChoicesG_cons, ← Multiset.cons_zero, forestCutChoicesG_cons,
    forestCutChoicesG_zero]
  exact Multiset.mem_bind.mpr ⟨({eaten.val}, 0), Multiset.mem_cons_self _ _,
    Multiset.mem_map.mpr ⟨_, Multiset.mem_bind.mpr ⟨_,
      Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ mem_cutSummandsCN_theApple),
      Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩, rfl⟩⟩

private theorem sidewardTermN_mem :
    sidewardTermN ∈ forestCutChoicesG cutSummandsN {eaten.val, theApple.val} := by
  rw [Multiset.insert_eq_cons, forestCutChoicesG_cons, ← Multiset.cons_zero, forestCutChoicesG_cons,
    forestCutChoicesG_zero]
  exact Multiset.mem_bind.mpr ⟨({eaten.val}, 0), Multiset.mem_cons_self _ _,
    Multiset.mem_map.mpr ⟨_, Multiset.mem_bind.mpr ⟨_,
      Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem (fun p ↦ (p.1, {p.2}))
        (show ({theD.val}, UnorderedTree.node Vertex.bare {appleN.val}) ∈ cutSummandsN theApple.val
          by rw [cutSummandsN_theApple]; simp)),
      Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩, rfl⟩⟩

/-- The 2(b) term satisfies Minimal Yield under trace counting, so Minimal Yield does not tell it
    apart from Internal Merge (Remark 1.6.9). -/
theorem sideward2b_minimalYield :
    MinimalYield UnorderedTree.accessibleCount {eaten.val, theApple.val}
      {(merge eaten theD).val, (deleteAccessible theD theApple).val} := by
  have := (MinimalYield.merge_term_accessibleCount_iff none sidewardTermC_mem
    (S := eaten.val) (S' := theD.val)
    (fun x hx _ ↦ by
      rw [sidewardTermC, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩)
    (by simp [sidewardTermC])).mpr (by simp [sidewardTermC])
  simpa [sidewardTermC] using this

/-- At the pruning cuts the 2(b) term loses complexity along its component map, since *the apple*
    goes to the lighter trunk `{apple}` (Proposition 1.6.10). -/
example : ¬ NoComplexityLoss.Map UnorderedTree.numNodes
    (componentMap (UnorderedTree.node Vertex.bare {eaten.val, theD.val}) sidewardTermN) :=
  NoComplexityLoss.not_map_componentMap_merge sidewardTermN_mem
    (hasExtractionCost_numNodes_cutSummandsN sidewardTermN_mem) UnorderedTree.numNodes_pos
    (S := eaten.val) (S' := theD.val) (by simp [sidewardTermN]) (by decide) (by decide)
    (.inr (by decide))

/-- At the trace cuts the 2(b) term loses no vertices along its component map, since the trace of
    *the* takes its place in *the apple*. -/
example : NoComplexityLoss.Map UnorderedTree.numNodes
    (componentMap (UnorderedTree.node Vertex.bare {eaten.val, theD.val}) sidewardTermC) := by
  simp [NoComplexityLoss.Map, componentMap, sidewardTermC]
  decide

/-- Graded by the size `σ`, which the trace cuts conserve, the 2(b) term at the trace cuts does
    lose complexity (Proposition 1.6.10). -/
example : ¬ NoComplexityLoss.Map (fun T ↦ Forest.accessibleSize {T})
    (componentMap (UnorderedTree.node Vertex.bare {eaten.val, theD.val}) sidewardTermC) :=
  NoComplexityLoss.not_map_accessibleSize_componentMap_merge none sidewardTermC_mem
    (fun x hx _ ↦ by
      rw [sidewardTermC, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩)
    (S := eaten.val) (S' := theD.val) (by simp [sidewardTermC]) (.inr (by decide))

/-- The term of Sideward Merge of type 3(a) of *the* and *apple* cuts both out of *the apple*. -/
private noncomputable def sideward3a : CutChoice Vertex :=
  {(theApple.val, ({theD.val, appleN.val}, {UnorderedTree.leaf Vertex.bare}))}

/-- It raises the number of components, so it violates Minimal Yield under any counting
    (Proposition 1.6.8). -/
example (acc : UnorderedTree Vertex → ℕ) (X : UnorderedTree Vertex) :
    ¬ MinimalYieldWeak acc {theApple.val} ({X} + sideward3a.trunk) := by
  have hs : sideward3a ∈ forestCutChoicesG cutSummandsN {theApple.val} := by
    rw [← Multiset.cons_zero, forestCutChoicesG_cons, forestCutChoicesG_zero]
    exact Multiset.mem_bind.mpr ⟨_, Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem
      (fun p ↦ (p.1, {p.2}))
      (show ({theD.val, appleN.val}, UnorderedTree.leaf Vertex.bare) ∈ cutSummandsN theApple.val
        by rw [cutSummandsN_theApple]; exact Multiset.mem_cons_self _ _)),
      Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩
  exact MinimalYieldWeak.not_of_forall_notMem acc hs (by simp [sideward3a]; decide) X

/-- Under deletion counting the 3(a) term keeps the number of accessible terms, where the book's
    table lowers it by two (Proposition 1.6.8): *the* and *apple* are sisters, so deleting both
    leaves their parent a leaf with nothing to contract. -/
example : sideward3a ∈ forestCutChoicesG cutSummandsDN {theApple.val} ∧
    (({(merge theD appleN).val} + sideward3a.trunk).map
      UnorderedTree.numEdges).sum =
    (({theApple.val} : Forest (UnorderedTree Vertex)).map UnorderedTree.numEdges).sum := by
  refine ⟨?_, by decide⟩
  rw [← Multiset.cons_zero, forestCutChoicesG_cons, forestCutChoicesG_zero]
  exact Multiset.mem_bind.mpr ⟨_, Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem
    (fun p ↦ (p.1, {p.2}))
    (show ({theD.val, appleN.val}, UnorderedTree.leaf Vertex.bare) ∈ cutSummandsDN theApple.val
      from Multiset.mem_map.mpr ⟨_, by
        rw [cutSummandsN_theApple]; exact Multiset.mem_cons_self _ _, rfl⟩)),
    Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩

/-- The 2(b) term at the deletion cuts, which contract the trunk `{apple}` to *apple*. -/
private def sidewardTermD : CutChoice Vertex :=
  {(eaten.val, ({eaten.val}, 0)), (theApple.val, ({theD.val}, {appleN.val}))}

private theorem sidewardTermD_mem :
    sidewardTermD ∈ forestCutChoicesG cutSummandsDN {eaten.val, theApple.val} := by
  rw [Multiset.insert_eq_cons, forestCutChoicesG_cons, ← Multiset.cons_zero, forestCutChoicesG_cons,
    forestCutChoicesG_zero]
  exact Multiset.mem_bind.mpr ⟨({eaten.val}, 0), Multiset.mem_cons_self _ _,
    Multiset.mem_map.mpr ⟨_, Multiset.mem_bind.mpr ⟨_,
      Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem (fun p ↦ (p.1, {p.2}))
        (Multiset.mem_map.mpr ⟨({theD.val}, UnorderedTree.node Vertex.bare {appleN.val}),
          by rw [cutSummandsN_theApple]; simp, Prod.ext rfl (by decide)⟩)),
      Multiset.mem_map.mpr ⟨0, Multiset.mem_singleton_self _, rfl⟩⟩, rfl⟩⟩

/-- Under deletion counting the 2(b) term satisfies the weak form of Minimal Yield but not the
    strong one, since it takes only *eaten* whole (Proposition 1.6.8). -/
example : MinimalYieldWeak UnorderedTree.numEdges {eaten.val, theApple.val}
      {(merge eaten theD).val, appleN.val} ∧
    ¬ MinimalYield UnorderedTree.numEdges {eaten.val, theApple.val}
      {(merge eaten theD).val, appleN.val} := by
  have hF : ∀ T ∈ ({eaten.val, theApple.val} : Forest (UnorderedTree Vertex)),
      T.IsFullBinary := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    rintro _ (rfl | rfl)
    exacts [eaten.2.isFullBinary, theApple.2.isFullBinary]
  have hK : sidewardTermD.crown = {eaten.val, theD.val} := by simp [sidewardTermD]
  have hX : (merge eaten theD).val.numEdges = eaten.val.numEdges + theD.val.numEdges + 2 := by
    rw [merge_val]; exact UnorderedTree.numEdges_node_pair _ _ _
  rw [show ({(merge eaten theD).val, appleN.val} : Forest (UnorderedTree Vertex)) =
      {(merge eaten theD).val} + sidewardTermD.trunk by simp [sidewardTermD],
    MinimalYieldWeak.merge_term_numEdges_iff hF sidewardTermD_mem hK hX,
    MinimalYield.merge_term_numEdges_iff hF sidewardTermD_mem hK hX,
    show sidewardTermD.numWhole = 1 by decide]
  decide

/-! ### The core computational structure of Merge (§1.10) -/

section CoreMerge

open PowerSeries Finset
open Finset.HasAntidiagonal.antidiagonal (fst_le snd_le)

/-- The Connes–Kreimer algebra of unlabelled trees over `ℤ`, in which the free `ℤ`-module `V(𝔗)`
on the nonplanar binary trees sits as the span of single trees. -/
abbrev TreeAlgebra := ConnesKreimer ℤ (UnorderedTree Unit)

/-- Forgetting the planar structure of a planar binary tree, whose leaves are its `nil`s. -/
def forgetPlanar : BinaryTree Unit → UnorderedTree Unit
  | .nil => UnorderedTree.leaf ()
  | .node _ l r => UnorderedTree.node () {forgetPlanar l, forgetPlanar r}

/-- The single variable `x`, the one-leaf tree. -/
noncomputable def generator : TreeAlgebra := ofTree (UnorderedTree.leaf ())

/-- Over the empty lexicon every leaf is the bare trace, and the carrier is the free commutative
magma on one generator, the reading of Lemma 1.10.1 on the syntactic-object carrier. -/
noncomputable def carrierEmptyEquiv : SyntacticObject Empty ≃* FreeCommMagma Unit :=
  SyntacticObject.equivFreeCommMagma.trans
    { toFun := FreeCommMagma.lift fun _ ↦ FreeCommMagma.of ()
      invFun := FreeCommMagma.lift fun _ ↦ FreeCommMagma.of (Sum.inr none)
      left_inv := fun x ↦ by
        have h : (FreeCommMagma.lift fun _ ↦
                FreeCommMagma.of (α := Empty ⊕ Option Empty) (Sum.inr none)).comp
              (FreeCommMagma.lift fun _ ↦ FreeCommMagma.of (α := Unit) ())
            = MulHom.id (FreeCommMagma (Empty ⊕ Option Empty)) :=
          FreeCommMagma.hom_ext fun y ↦ by
            rcases y with e | (_ | e)
            · exact e.elim
            · simp
            · exact e.elim
        exact MulHom.ext_iff.1 h x
      right_inv := fun x ↦ by
        have h : (FreeCommMagma.lift fun _ ↦ FreeCommMagma.of (α := Unit) ()).comp
              (FreeCommMagma.lift fun _ ↦
                FreeCommMagma.of (α := Empty ⊕ Option Empty) (Sum.inr none))
            = MulHom.id (FreeCommMagma Unit) :=
          FreeCommMagma.hom_ext fun _ ↦ by simp
        exact MulHom.ext_iff.1 h x
      map_mul' := map_mul _ }

/-- Merge on `V(𝔗)` is the grafting operator after the disjoint union (Lemma 1.3.3), a bilinear
map. -/
noncomputable def mergeLin : TreeAlgebra →ₗ[ℤ] TreeAlgebra →ₗ[ℤ] TreeAlgebra :=
  (LinearMap.mul ℤ TreeAlgebra).compr₂ (bPlusLin ())

@[simp] theorem mergeLin_apply (a b : TreeAlgebra) : mergeLin a b = bPlusLin () (a * b) := rfl

theorem mergeLin_comm (a b : TreeAlgebra) : mergeLin a b = mergeLin b a := by
  rw [mergeLin_apply, mergeLin_apply, _root_.mul_comm]

theorem mergeLin_ofTree (s t : UnorderedTree Unit) :
    mergeLin (ofTree s) (ofTree t) = ofTree (UnorderedTree.node () {s, t}) := by
  rw [mergeLin_apply, ← of'_singleton, ← of'_singleton, ← of'_add, bPlusLin_of']
  rfl

/-- Merge extends to formal series `X = ∑ Xₗ` degree by degree, the degree-`n` term of `𝔐(X, Y)`
being `∑_{i+j=n} 𝔐(Xᵢ, Yⱼ)`. -/
noncomputable def mergeSeries (X Y : TreeAlgebra⟦X⟧) : TreeAlgebra⟦X⟧ :=
  PowerSeries.mk fun n ↦ bPlusLin () (coeff n (X * Y))

@[simp] theorem coeff_mergeSeries (X Y : TreeAlgebra⟦X⟧) (n : ℕ) :
    coeff n (mergeSeries X Y) = ∑ p ∈ antidiagonal n, mergeLin (coeff p.1 X) (coeff p.2 Y) := by
  rw [mergeSeries, coeff_mk, coeff_mul, map_sum]; rfl

/-- `𝔐(X, X)` has no degree-one term, so the printed `X = 𝔐(X, X)` cannot meet `X₁ = x`. -/
theorem coeff_one_mergeSeries {X : TreeAlgebra⟦X⟧} (h0 : coeff 0 X = 0) :
    coeff 1 (mergeSeries X X) = 0 := by
  simp [Finset.Nat.sum_antidiagonal_succ, h0]

/-- A series solves (1.10.1) with its initial condition `X₁ = x` when it has no constant term and
`X = x t + 𝔐(X, X)`. -/
def IsMergeSolution (X : TreeAlgebra⟦X⟧) : Prop :=
  coeff 0 X = 0 ∧ X = monomial 1 generator + mergeSeries X X

/-- The formal sum of the planar binary trees with `n` leaves, planarity forgotten. -/
noncomputable def planarSum : ℕ → TreeAlgebra
  | 0 => 0
  | n + 1 => ∑ P ∈ BinaryTree.treesOfNumNodesEq n, ofTree (forgetPlanar P)

/-- The series `X = ∑ₗ Xₗ` of Proposition 1.10.2. -/
noncomputable def mergeSolution : TreeAlgebra⟦X⟧ := PowerSeries.mk planarSum

/-- The recursion of the proof of Proposition 1.10.2, `Xₙ = ∑_{j=1}^{n-1} 𝔐(Xⱼ, X_{n-j})`. -/
theorem planarSum_add_two (n : ℕ) :
    planarSum (n + 2) =
      ∑ p ∈ antidiagonal n, mergeLin (planarSum (p.1 + 1)) (planarSum (p.2 + 1)) := by
  rw [planarSum, BinaryTree.treesOfNumNodesEq_succ, sum_biUnion]
  · refine sum_congr rfl fun p _ ↦ ?_
    simp only [BinaryTree.pairwiseNode, sum_map, sum_product, planarSum, map_sum,
      LinearMap.sum_apply, mergeLin_ofTree]
    rw [sum_comm]
    rfl
  · simp_rw [Set.PairwiseDisjoint, Set.Pairwise, disjoint_left]
    aesop

private theorem sum_antidiagonal_add_two {f : ℕ → TreeAlgebra} (h0 : f 0 = 0) (n : ℕ) :
    ∑ p ∈ antidiagonal (n + 2), mergeLin (f p.1) (f p.2) =
      ∑ p ∈ antidiagonal n, mergeLin (f (p.1 + 1)) (f (p.2 + 1)) := by
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ', h0]
  simp

/-- The sum of the planar binary trees solves (1.10.1) with `X₁ = x` (Proposition 1.10.2). -/
theorem isMergeSolution_mergeSolution : IsMergeSolution mergeSolution := by
  refine ⟨by simp [mergeSolution, planarSum], PowerSeries.ext fun n ↦ ?_⟩
  rw [map_add, coeff_mergeSeries, coeff_monomial]
  rcases n with _ | _ | n
  · simp [mergeSolution, planarSum]
  · simp [mergeSolution, planarSum, generator, Finset.Nat.sum_antidiagonal_succ, forgetPlanar]
  · rw [ite_eq_right (by omega), zero_add, mergeSolution]
    simp only [coeff_mk]
    show planarSum (n + 2) = ∑ p ∈ antidiagonal (n + 2), mergeLin (planarSum p.1) (planarSum p.2)
    rw [sum_antidiagonal_add_two (f := planarSum) rfl n]
    exact planarSum_add_two n

/-- The solution of Proposition 1.10.2 is unique, since the recursion determines each term from
the lower ones. -/
theorem IsMergeSolution.eq {X : TreeAlgebra⟦X⟧} (h : IsMergeSolution X) : X = mergeSolution := by
  obtain ⟨h0, hX⟩ := h
  refine PowerSeries.ext fun n ↦ ?_
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [h0, mergeSolution, planarSum]
    · have := congrArg (PowerSeries.coeff 1) hX
      rw [this, map_add, coeff_mergeSeries, coeff_monomial_same, Finset.Nat.sum_antidiagonal_succ,
        h0]
      simp [mergeSolution, planarSum, generator, forgetPlanar, h0]
    · have := congrArg (PowerSeries.coeff (n + 2)) hX
      rw [this, map_add, coeff_mergeSeries, coeff_monomial, ite_eq_right (by omega), zero_add]
      show ∑ p ∈ antidiagonal (n + 2), mergeLin (PowerSeries.coeff p.1 X) (PowerSeries.coeff p.2 X)
        = PowerSeries.coeff (n + 2) mergeSolution
      rw [sum_antidiagonal_add_two (f := fun i ↦ PowerSeries.coeff i X) h0, mergeSolution,
        coeff_mk, planarSum_add_two]
      refine sum_congr rfl fun p hp ↦ ?_
      rw [ih (p.1 + 1) (by have := fst_le hp; omega), ih (p.2 + 1) (by have := snd_le hp; omega),
        mergeSolution, coeff_mk, coeff_mk]

/-- The coefficient of a nonplanar tree in `Xₙ₊₁` is its number of planar embeddings. -/
theorem coeff_planarSum_succ (n : ℕ) (T : UnorderedTree Unit) :
    (planarSum (n + 1)).coeff {T} =
      #{P ∈ BinaryTree.treesOfNumNodesEq n | forgetPlanar P = T} := by
  rw [planarSum, ← lcoeff_apply (R := ℤ), map_sum, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun P _ ↦ ?_
  rw [lcoeff_apply, ← of'_singleton, coeff_of']
  simp [Multiset.singleton_inj]

/-- The coefficients of `Xₙ₊₁` sum to the Catalan number `Cₙ`, the number of planar binary trees
with `n + 1` leaves. -/
theorem aeval_planarSum_succ (n : ℕ) :
    aeval (R := ℤ) (fun _ ↦ (1 : ℤ)) (planarSum (n + 1)) = catalan n := by
  simp [planarSum, BinaryTree.treesOfNumNodesEq_card_eq_catalan]

/-- `X₁ = x`. -/
theorem planarSum_one : planarSum 1 = generator := by
  simp [planarSum, generator, forgetPlanar]

/-- `X₂ = {xx}`. -/
theorem planarSum_two : planarSum 2 = mergeLin generator generator := by
  rw [planarSum_add_two]
  simp [planarSum_one]

/-- `X₃ = {x{xx}} + {{xx}x} = 2{x{xx}}`. -/
theorem planarSum_three :
    planarSum 3 = 2 • mergeLin generator (mergeLin generator generator) := by
  rw [planarSum_add_two]
  simp [Finset.Nat.sum_antidiagonal_succ, planarSum_one, planarSum_two, two_smul, _root_.mul_comm]

/-- `X₄ = 4{x{x{xx}}} + {{xx}{xx}}`; the proof of Proposition 1.10.2 prints the coefficient
`2`. -/
theorem planarSum_four :
    planarSum 4 = 4 • mergeLin generator (mergeLin generator (mergeLin generator generator)) +
      mergeLin (mergeLin generator generator) (mergeLin generator generator) := by
  rw [planarSum_add_two]
  simp only [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero, sum_singleton,
    zero_add, Nat.reduceAdd, planarSum_one, planarSum_two, planarSum_three, map_nsmul,
    LinearMap.smul_apply]
  rw [mergeLin_comm (mergeLin generator (mergeLin generator generator)) generator]
  abel

/-- The printed `X₄ = 2{x{x{xx}}} + {{xx}{xx}}` is not the degree-four term of the solution. -/
example : planarSum 4 ≠
    2 • mergeLin generator (mergeLin generator (mergeLin generator generator)) +
      mergeLin (mergeLin generator generator) (mergeLin generator generator) := by
  rw [planarSum_four]
  intro h
  have h' := congrArg (lcoeff ℤ {UnorderedTree.node () {UnorderedTree.leaf (),
    UnorderedTree.node () {UnorderedTree.leaf (), UnorderedTree.node () {UnorderedTree.leaf (),
      UnorderedTree.leaf ()}}}}) (add_right_cancel h)
  simp only [generator, mergeLin_ofTree] at h'
  simp only [map_nsmul, lcoeff_apply, ← of'_singleton, coeff_of'] at h'
  norm_num at h'

end CoreMerge

/-! ### Externalization (§1.12–1.13) -/

/-- A determiner over a noun, in which `D` selects `N` and so projects. -/
private def theDog : SyntacticObject :=
  ⟨UnorderedTree.mk (.node Vertex.bare
    [.node (Vertex.lex ⟨.of .D [.N] (phonForm := "the"), 0⟩) [],
     .node (Vertex.lex ⟨.of .N [] (phonForm := "dog"), 1⟩) []]), by decide⟩

/-- In the harmonic head-initial planarization the projecting `D` comes first. -/
example : (theDog.linearize? .left).map (·.yield.map (·.id)) = some [0, 1] := by decide

/-- In the harmonic head-final planarization the same head function is mirrored. -/
example : (theDog.linearize? .right).map (·.yield.map (·.id)) = some [1, 0] := by decide

example : (theDog.linearize? .left).map (·.yield.filterMap (·.item.phonForm?)) =
    some ["the", "dog"] := by decide

/-- Merging *the* on the left of *dog*, which it selects, is harmonic for a head-initial
language, so that derivation records the head-initial planarization
(`Derivation.externalize?_eq_linearize?`); merging it on the right is not harmonic. -/
example : Step.HarmonicList .left selHead [.em .left (.leaf ⟨.of .D [.N] (phonForm := "the"), 0⟩)]
      ⟨.leaf ⟨.of .N [] (phonForm := "dog"), 1⟩, []⟩ ∧
    ¬ Step.HarmonicList .left selHead [.em .right (.leaf ⟨.of .D [.N] (phonForm := "the"), 0⟩)]
      ⟨.leaf ⟨.of .N [] (phonForm := "dog"), 1⟩, []⟩ :=
  ⟨⟨⟨rfl, by decide⟩, trivial⟩, fun ⟨⟨_, h⟩, _⟩ ↦ absurd h (by decide)⟩

/-- Exocentric Merge of two saturated `N`s, neither selecting the other, determines no head and
no order. -/
private def exoNN : SyntacticObject :=
  ⟨UnorderedTree.mk (.node Vertex.bare
    [.node (Vertex.lex ⟨.of .N [] (phonForm := "cats"), 0⟩) [],
     .node (Vertex.lex ⟨.of .N [] (phonForm := "dogs"), 1⟩) []]), by decide⟩

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
  LinearMap.mul' R _ ∘ₗ (bPlusLin a).rTensor _ ∘ₗ (homogeneousComponent k).rTensor _ ∘ₗ
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
  simp [bPlusLin_of']

/-- With fewer than `k` components there is nothing to group. -/
theorem formSet_of'_of_card_lt (a : α) {k : ℕ} {F : Forest (UnorderedTree α)}
    (h : F.card < k) : formSet (R := R) a k (of' F) = 0 := by
  rw [formSet_of', Multiset.powersetCard_eq_empty _ h, Multiset.map_zero, Multiset.sum_zero]

/-- With exactly `k` components FormSet groups the whole workspace, as in the unbounded
unstructured sequences of p. 144. -/
theorem formSet_of'_card (a : α) (F : Forest (UnorderedTree α)) :
    formSet (R := R) a F.card (of' F) = ofTree (.node a F) := by
  simp [formSet_of']

/-- A forest is an extended workspace, in `𝔉̃ᴿ` of (1.16.3), when each component is a syntactic
object or a bare root of any valence over syntactic objects, binary below that root. -/
def IsExtendedWorkspace (G : Forest (UnorderedTree Vertex)) : Prop :=
  ∀ T ∈ G, IsSyntacticObject T ∨
    ∃ S : Forest (UnorderedTree Vertex), T = .node Vertex.bare S ∧ ∀ T' ∈ S, IsSyntacticObject T'

/-- On workspaces of syntactic objects, the range of FormSet lies in the span of the extended
workspaces (Definition 1.16.1). -/
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

/-! ### Feature consistency as Birkhoff renormalization (Chapter 3) -/

/-- The Boolean consistency semiring of §3.5, the two-element idempotent commutative semiring
with disjunction as addition, some decomposition being consistent, and conjunction as
multiplication, all parts agreeing. -/
inductive Consistency where
  | inconsistent
  | consistent
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Consistency

/-- Disjunction, consistent iff at least one argument is. -/
def or : Consistency → Consistency → Consistency
  | consistent, _ => consistent
  | _, consistent => consistent
  | _, _ => inconsistent

/-- Conjunction, consistent iff both arguments are. -/
def and : Consistency → Consistency → Consistency
  | consistent, consistent => consistent
  | _, _ => inconsistent

instance : CommSemiring Consistency where
  add := or
  mul := and
  zero := inconsistent
  one := consistent
  nsmul n a := n.rec inconsistent fun _ acc ↦ or acc a
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  add_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  zero_add := by rintro ⟨⟩ <;> rfl
  add_zero := by rintro ⟨⟩ <;> rfl
  add_comm := by rintro ⟨⟩ ⟨⟩ <;> rfl
  mul_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  one_mul := by rintro ⟨⟩ <;> rfl
  mul_one := by rintro ⟨⟩ <;> rfl
  mul_comm := by rintro ⟨⟩ ⟨⟩ <;> rfl
  left_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  right_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  zero_mul := by rintro ⟨⟩ <;> rfl
  mul_zero := by rintro ⟨⟩ <;> rfl

/-- The identity is a Rota–Baxter operator of weight `+1` on `Consistency`, since disjunction is
idempotent and absorbs the weight term. On a Boolean target the threshold operator collapses to
the identity, disagreement already being the additive zero. -/
theorem isRotaBaxter_id : IsRotaBaxter (1 : ℕ) (id : Consistency → Consistency) := by
  rintro ⟨⟩ ⟨⟩ <;> rfl

end Consistency

/-- A syntactic object as an element of the Connes–Kreimer Hopf algebra over `ℕ`, the singleton
forest of its underlying nonplanar tree. The base ring is `ℕ` because every commutative
semiring, `Consistency` included, is an `ℕ`-algebra, while a Boolean target is no `ℤ`-algebra. -/
noncomputable def toCK (S : SyntacticObject) : ConnesKreimer ℕ (UnorderedTree Vertex) :=
  ofTree S.val

/-- Merge factors through the grafting operator on the disjoint union of its arguments, with the
bare root label (Lemma 1.3.3). -/
theorem toCK_merge (l r : SyntacticObject) :
    toCK (merge l r) = bPlusLin Vertex.bare (toCK l * toCK r) := by
  rw [toCK, toCK, toCK, ← of'_singleton (R := ℕ) l.val, ← of'_singleton (R := ℕ) r.val, ← of'_add,
    bPlusLin_of', merge_val]
  rfl

open WithConv

/-- The feature-consistency map `φ₊` on a syntactic object, the value at the object of the
renormalized part of a feature character `φ` under an operator `P` on `Consistency`. It is the
single recursive map of §3.1.5 that checks consistency over all substructures. -/
noncomputable def featureConsistency
    (φ : ConnesKreimer ℕ (UnorderedTree Vertex) →ₗ[ℕ] Consistency)
    (P : Consistency →+ Consistency) (S : SyntacticObject) : Consistency :=
  birkhoffPlusTree φ P S.val

/-- For unital `φ`, the feature-consistency map is the Birkhoff convolution `φ₊ = φ₋ ⋆ φ`
(Definition 3.1.6, Proposition 3.1.9). -/
theorem featureConsistency_eq_convMul
    (φ : ConnesKreimer ℕ (UnorderedTree Vertex) →ₗ[ℕ] Consistency)
    (P : Consistency →+ Consistency) (hφ : φ 1 = 1) (S : SyntacticObject) :
    (toConv (birkhoffMinus φ P).toLinearMap * toConv φ) (toCK S) = featureConsistency φ P S :=
  convMul_birkhoffMinus_apply_ofTree φ P hφ S.val

/-- The head-probe value `Υ_{s,h}` on a tree (equation (3.2.1)), the probe `Υ` applied to the
tree's selection head, and `inconsistent` when the tree has no well-defined head. -/
def headProbeTree (Υ : LexicalItem.Token → Consistency) (T : UnorderedTree Vertex) : Consistency :=
  (selCheckN T).head.elim Consistency.inconsistent Υ

/-- The head-following feature character `ϕ_{Υ,s,h}` of Lemma 3.2.5 is the algebra homomorphism
extending `Υ_{s,h}` multiplicatively to forests, so that a workspace is consistent iff each of its
trees is. It is the unrenormalized feature assignment whose Birkhoff renormalization is the
consistency map. -/
noncomputable def headProbeChar (Υ : LexicalItem.Token → Consistency) :
    ConnesKreimer ℕ (UnorderedTree Vertex) →ₐ[ℕ] Consistency :=
  aeval (headProbeTree Υ)

@[simp] theorem headProbeChar_apply_of' (Υ : LexicalItem.Token → Consistency)
    (F : Forest (UnorderedTree Vertex)) :
    headProbeChar Υ (of' F) = (F.map (headProbeTree Υ)).prod :=
  aeval_of' _ F

@[simp] theorem headProbeChar_apply_ofTree (Υ : LexicalItem.Token → Consistency)
    (T : UnorderedTree Vertex) :
    headProbeChar Υ (ofTree T) = headProbeTree Υ T :=
  aeval_ofTree _ T

theorem headProbeChar_one (Υ : LexicalItem.Token → Consistency) : headProbeChar Υ 1 = 1 := map_one _

/-- The feature-consistency verdict on a syntactic object (§3.1.5, Lemmas 3.2.5 and 3.2.7), the
Birkhoff renormalization with the identity operator of the head-following character, consistent
iff the head-probe agreements cohere across all substructures. -/
noncomputable def headConsistency (Υ : LexicalItem.Token → Consistency) (S : SyntacticObject) :
    Consistency :=
  featureConsistency (headProbeChar Υ).toLinearMap (.id _) S

/-- The head-driven verdict factors as the semiring Birkhoff convolution `φ₊ = φ₋ ⋆ φ` of the
head-following character (Definition 3.1.6, Lemma 3.2.7). -/
theorem headConsistency_eq_convMul (Υ : LexicalItem.Token → Consistency) (S : SyntacticObject) :
    (toConv (birkhoffMinus (headProbeChar Υ).toLinearMap (.id _)).toLinearMap
        * toConv (headProbeChar Υ).toLinearMap) (toCK S) = headConsistency Υ S :=
  featureConsistency_eq_convMul _ _ (headProbeChar_one Υ) S

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

/-- Weak Minimal Yield holds iff the `δb₀`- and `δα`-monomials of `F → F'` are both nonpolar. -/
theorem minimalYieldWeak_iff_truncLT [Nontrivial R] :
    MinimalYieldWeak UnorderedTree.numEdges F F' ↔
      truncLT 0 (single (δb₀ F F') (1 : R)) = 0 ∧ truncLT 0 (single (δα F F') (1 : R)) = 0 := by
  simp only [minimalYieldWeak_iff_gradings, truncLT_single_eq_zero_iff one_ne_zero]

end Gradings

/-- The character `ϕt` of Proposition 3.5.3 for `δ = δα`, recording only the grading, sends a
tree `T` to `t^{α(T)}`, multiplicatively over disjoint union. -/
noncomputable def gradingChar : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R :=
  aeval fun T ↦ single (T.numEdges : ℤ) 1

/-- `ϕt(F) = t^{α(F)}`, since `α` is additive over forests. -/
theorem gradingChar_apply_of' (F : Forest (UnorderedTree α)) :
    gradingChar (R := R) (of' F) = single ((F.map UnorderedTree.numEdges).sum : ℤ) 1 := by
  rw [gradingChar, aeval_of']
  induction F using Multiset.induction with
  | empty => simp
  | cons T F ih => simp [ih, single_mul_single, add_comm]

/-- `ϕt` is nonpolar on every forest, since `α(F) ≥ 0` (Lemma 3.5.5). -/
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

/-- The polar projection is not multiplicative: `t⁻² · t = t⁻¹` is polar while `t` is not, so a
product can acquire a polar part that its factors lack. Hence `(1 − R) ∘ φ` need not be a
character, and renormalization goes through the Birkhoff factorization. -/
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

/-- The negative part of every character into Laurent series is polar on nonempty forests, landing
in the subalgebra `R(A[t⁻¹][[t]])` of Proposition 3.1.7. -/
theorem truncLT_birkhoffMinus_of' (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] LaurentSeries R)
    {F : Forest (UnorderedTree α)} (hF : F ≠ 0) :
    truncLT 0 (birkhoffMinus φ.toLinearMap (-𝐑) (of' F))
      = birkhoffMinus φ.toLinearMap (-𝐑) (of' F) := by
  obtain ⟨y, hy⟩ := birkhoffMinus_of'_mem_range (φ := φ.toLinearMap) isRotaBaxter_neg_polar hF
  rw [← hy]
  simp [truncLT_neg]

/-- The renormalized part of every Laurent-series character is nonpolar, landing in `A[[t]]`
(Proposition 3.1.7), the first step toward Proposition 3.5.6. -/
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

/-- The two inscriptions of *the man* are repetitions, structurally identical distinct tokens. -/
theorem theMan_isRepetition : IsRepetition theMan theMan' :=
  ⟨structurallyIdentical_renumber 4 theMan, by simp [theMan, theMan', renumber, merge_eq_merge_iff]⟩

/-- Form Copy relates the controller to the controlled subject, the restriction of (3.8.4) to
the diagonal `Diag₁,₄` of (3.8.5). -/
theorem theMan_mem_copyRel : (theMan, theMan') ∈ triedToRead.copyRel :=
  mk_mem_copyRel_merge (by simp [containsOrEq_iff_eq_or_contains]) theMan_isRepetition.1

/-- *a book* is no copy of *the man*, since Form Copy relates only structurally identical
inscriptions. -/
theorem not_mem_copyRel_aBook : (theMan, aBook) ∉ triedToRead.copyRel := fun h ↦ by
  have := h.2
  simp only [StructurallyIdentical, theMan, aBook, erase_merge, erase_leaf] at this
  exact absurd this (by decide)

end MarcolliChomskyBerwick2025
