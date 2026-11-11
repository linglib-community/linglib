module

public import Linglib.Core.Algebra.BigOperators.Group.Multiset.Basic
public import Linglib.Core.Algebra.BigOperators.Ring.Multiset
public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Core.Combinatorics.RootedTree.DoubleCut
public import Linglib.Core.LinearAlgebra.TensorProduct.Defs
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Generic admissible-cut coproduct on `ConnesKreimer R (UnorderedTree α)`

Admissible-cut coproducts share one shape: a primitive term `ofTree T ⊗ 1` plus a sum over cuts
`(crown, trunk)` of `of' crown ⊗ ofTree trunk`. They differ only in the enumeration `cuts T` of the
cuts. This file defines the shape once, as the algebra homomorphism
`comulOfCuts cuts`; the Connes–Kreimer coproduct is its instance at the admissible cuts
`admissibleCuts` (`Coproduct/AdmissibleCut.lean`).

## Main definitions

* `ConnesKreimer.comulTreeOfCuts`, `ConnesKreimer.comulForestOfCuts`: the generic coproduct on trees
  and forests.
* `ConnesKreimer.comulOfCuts`: the generic coproduct as an algebra hom.
* `ConnesKreimer.WithCuts R cuts`: the carrier indexed by a cut enumeration, a bialgebra when
  `IsBialgebraCuts cuts` holds.

## Main results

* `ConnesKreimer.lTensor_counit_comp_comulOfCuts`: the left counit law, at every cut enumeration.
* `ConnesKreimer.rTensor_counit_comp_comulOfCuts`: the right counit law, when the empty cut is
  the only cut with an empty crown.
* `ConnesKreimer.comulTreeOfCuts_eq_sum`, `ConnesKreimer.comulForestOfCuts_eq_sum`: the coproduct as
  one sum over the cut convolutions `treeCuts` and `forestCuts`.
* `ConnesKreimer.comulOfCuts_coassoc`: coassociativity, when the double cuts through the crown are
  the double cuts through the trunk.

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}
  (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))

/-- The generic admissible-cut coproduct on a tree, for a cut enumeration `cuts`. At the admissible
    cuts `admissibleCuts` it is the Connes–Kreimer coproduct. -/
noncomputable def comulTreeOfCuts (T : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α))
  + ((cuts T).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-- Forest-level generic coproduct (multiplicative extension). -/
noncomputable def comulForestOfCuts (F : Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  (F.map (comulTreeOfCuts (R := R) cuts)).prod

@[simp] theorem comulForestOfCuts_zero :
    comulForestOfCuts (R := R) cuts (0 : Forest (UnorderedTree α)) = 1 := by
  simp only [comulForestOfCuts, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestOfCuts_add (F G : Forest (UnorderedTree α)) :
    comulForestOfCuts (R := R) cuts (F + G) =
      comulForestOfCuts (R := R) cuts F * comulForestOfCuts (R := R) cuts G := by
  unfold comulForestOfCuts
  rw [Multiset.map_add, Multiset.prod_add]

@[simp] theorem comulForestOfCuts_cons (T : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    comulForestOfCuts (R := R) cuts (T ::ₘ F) =
      comulTreeOfCuts (R := R) cuts T * comulForestOfCuts (R := R) cuts F := by
  unfold comulForestOfCuts
  rw [Multiset.map_cons, Multiset.prod_cons]

/-- The **generic admissible-cut coproduct as an algebra hom**, parameterized by
    the cut enumeration `cuts`. -/
noncomputable def comulOfCuts :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  aeval (comulTreeOfCuts cuts)

@[simp] theorem comulOfCuts_apply_of' (F : Forest (UnorderedTree α)) :
    comulOfCuts (R := R) cuts (of' F) = comulForestOfCuts cuts F :=
  aeval_of' _ F

@[simp] theorem comulOfCuts_apply_ofTree (T : UnorderedTree α) :
    comulOfCuts (R := R) cuts (ofTree T) = comulTreeOfCuts cuts T :=
  aeval_ofTree _ T

/-! ### Counit laws -/

/-- The left counit law `(id ⊗ ε) ∘ Δ = rid⁻¹` holds at every cut enumeration: each trunk is a
single tree, which the counit sends to `0`. -/
theorem lTensor_counit_comp_comulOfCuts :
    (Algebra.TensorProduct.map (.id R _) counit).comp (comulOfCuts (R := R) cuts) =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R (UnorderedTree α))).symm :=
  algHom_ext_ofTree fun T ↦ by
    simp [comulTreeOfCuts, map_multiset_sum, Multiset.map_map]

variable {cuts} in
/-- The right counit law `(ε ⊗ id) ∘ Δ = lid⁻¹` holds when the empty cut is the only cut with an
empty crown. -/
theorem rTensor_counit_comp_comulOfCuts
    (h : ∀ T, (cuts T).filter (fun p ↦ p.1.card = 0) = {(0, T)}) :
    (Algebra.TensorProduct.map counit (.id R _)).comp (comulOfCuts (R := R) cuts) =
      (Algebra.TensorProduct.lid R (ConnesKreimer R (UnorderedTree α))).symm :=
  algHom_ext_ofTree fun T ↦ by
    simp [comulTreeOfCuts, map_multiset_sum, Multiset.map_map, TensorProduct.ite_tmul,
      ← Multiset.sum_map_filter, h]

/-! ### The generic coproduct as a sum over cut convolutions

`treeCuts`/`forestCuts` (`Combinatorics/RootedTree/Cut.lean`) enumerate
the (crown, trunk-forest) pairs of a tree and their convolution over a
forest; `cutTensor` sends a pair to `of' crown ⊗ of' trunk`. -/

/-- Tensor-product factor of a (crown, trunk) cut pair. -/
noncomputable def cutTensor (p : Forest (UnorderedTree α) × Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  of' (R := R) p.1 ⊗ₜ[R] of' p.2

theorem cutTensor_add (p q : Forest (UnorderedTree α) × Forest (UnorderedTree α)) :
    cutTensor (R := R) (p + q) = cutTensor p * cutTensor q := by
  simp only [cutTensor, Prod.fst_add, Prod.snd_add, of'_add, Algebra.TensorProduct.tmul_mul_tmul]

/-- `comulTreeOfCuts` as a single multiset sum over `treeCuts`. -/
theorem comulTreeOfCuts_eq_sum (T : UnorderedTree α) :
    comulTreeOfCuts (R := R) cuts T =
      ((treeCuts cuts T).map (cutTensor (R := R))).sum := by
  unfold comulTreeOfCuts treeCuts
  rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
  congr 1

/-- `comulForestOfCuts` as a single multiset sum over `forestCuts`. -/
theorem comulForestOfCuts_eq_sum (F : Forest (UnorderedTree α)) :
    comulForestOfCuts (R := R) cuts F =
      ((forestCuts cuts F).map (cutTensor (R := R))).sum := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestOfCuts_zero, forestCuts_zero, Multiset.map_singleton,
        Multiset.sum_singleton]
    show (1 : _) = of' (R := R) (0 : Forest (UnorderedTree α)) ⊗ₜ[R] of' 0
    rw [of'_zero, Algebra.TensorProduct.one_def]
  | cons T F ih =>
    rw [comulForestOfCuts_cons, comulTreeOfCuts_eq_sum, ih, forestCuts_cons,
      Multiset.sum_map_conv _ _ cutTensor_add]

/-! ### Coassociativity

Both composites `(Δ ⊗ id) ∘ Δ` and `(id ⊗ Δ) ∘ Δ` sum over the pairs of nested cuts of a tree,
the second cut taken in the crown or in the trunk of the first. -/

/-- Tensor-product factor of a (crown, middle, trunk) double cut. -/
noncomputable def cutTensor₃
    (q : Forest (UnorderedTree α) × Forest (UnorderedTree α) × Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) ⊗[R]
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  of' q.1 ⊗ₜ[R] (of' q.2.1 ⊗ₜ[R] of' q.2.2)

/-- `(Δ ⊗ id) ∘ Δ` on a tree sums the double cuts through the crown. -/
theorem assoc_map_comulOfCuts_comulTreeOfCuts (T : UnorderedTree α) :
    Algebra.TensorProduct.assoc R R R _ _ _
        (Algebra.TensorProduct.map (comulOfCuts (R := R) cuts) (.id R _)
          (comulTreeOfCuts cuts T)) =
      ((doubleCutsCrown cuts T).map (cutTensor₃ (R := R))).sum := by
  simp [comulTreeOfCuts_eq_sum, comulForestOfCuts_eq_sum, doubleCutsCrown, cutTensor, cutTensor₃,
    map_multiset_sum, Multiset.map_map, Multiset.map_bind, TensorProduct.sum_map_tmul]

/-- `(id ⊗ Δ) ∘ Δ` on a tree sums the double cuts through the trunk. -/
theorem map_comulOfCuts_comulTreeOfCuts (T : UnorderedTree α) :
    Algebra.TensorProduct.map (.id R _) (comulOfCuts (R := R) cuts) (comulTreeOfCuts cuts T) =
      ((doubleCutsTrunk cuts T).map (cutTensor₃ (R := R))).sum := by
  simp [comulTreeOfCuts_eq_sum, comulForestOfCuts_eq_sum, doubleCutsTrunk, cutTensor, cutTensor₃,
    map_multiset_sum, Multiset.map_map, Multiset.map_bind, TensorProduct.tmul_sum_map]

variable {cuts} in
/-- The generic coproduct is coassociative when the double cuts through the crown are the double
cuts through the trunk. -/
theorem comulOfCuts_coassoc (h : ∀ T, doubleCutsCrown cuts T = doubleCutsTrunk cuts T) :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree α)) _ _).toAlgHom.comp
        ((Algebra.TensorProduct.map (comulOfCuts (R := R) cuts) (.id R _)).comp
          (comulOfCuts cuts)) =
      (Algebra.TensorProduct.map (.id R _) (comulOfCuts (R := R) cuts)).comp (comulOfCuts cuts) :=
  algHom_ext_ofTree fun T ↦ by
    simp [assoc_map_comulOfCuts_comulTreeOfCuts, map_comulOfCuts_comulTreeOfCuts, h]

/-! ### The policy-indexed carrier `WithCuts`

The `WithLp` pattern: a type synonym indexed by the cut policy, whose `Bialgebra` instance is
gated on an admissibility mixin. The Connes–Kreimer coproduct keeps the plain carrier
(`instBialgebra`); other admissible policies get their bialgebra here. -/

set_option linter.unusedVariables false in
variable (R) in
/-- Type synonym for `ConnesKreimer R (UnorderedTree α)` carrying the generic
admissible-cut coproduct at the fixed policy `cuts`. -/
def WithCuts (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α)) :
    Type _ :=
  ConnesKreimer R (UnorderedTree α)

noncomputable instance : CommSemiring (WithCuts R cuts) :=
  inferInstanceAs (CommSemiring (ConnesKreimer R (UnorderedTree α)))

noncomputable instance : Algebra R (WithCuts R cuts) :=
  inferInstanceAs (Algebra R (ConnesKreimer R (UnorderedTree α)))

/-- A cut policy is admissible when nested cuts can be taken in either order and the empty cut is
the only cut with an empty crown. The first makes the generic coproduct `comulOfCuts cuts`
coassociative (`comulOfCuts_coassoc`) and the second makes it right counital
(`rTensor_counit_comp_comulOfCuts`); it is left counital at every policy. Gates the `Bialgebra`
instance on `WithCuts` (the `Fact`-style mixin of the `WithLp` pattern). -/
class IsBialgebraCuts : Prop where
  doubleCutsCrown_eq : ∀ T, doubleCutsCrown cuts T = doubleCutsTrunk cuts T
  filter_card_eq_zero : ∀ T, (cuts T).filter (fun p ↦ p.1.card = 0) = {(0, T)}

/-- Any admissible cut policy makes `WithCuts R cuts` a bialgebra. -/
noncomputable instance WithCuts.instBialgebra [IsBialgebraCuts cuts] :
    Bialgebra R (WithCuts R cuts) :=
  Bialgebra.ofAlgHom (A := WithCuts R cuts) (comulOfCuts cuts) counit
    (comulOfCuts_coassoc IsBialgebraCuts.doubleCutsCrown_eq)
    (rTensor_counit_comp_comulOfCuts IsBialgebraCuts.filter_card_eq_zero)
    (lTensor_counit_comp_comulOfCuts cuts)

end ConnesKreimer
