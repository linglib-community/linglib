module

public import Linglib.Core.Algebra.BigOperators.Multiset
public import Linglib.Core.Algebra.RootedTree.ConnesKreimer
public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Generic admissible-cut coproduct on `ConnesKreimer R (UnorderedTree α)`

Admissible-cut coproducts share one shape: a primitive term `ofTree T ⊗ 1` plus a sum over cut
summands `(crown, trunk)` of `of' crown ⊗ ofTree trunk`. They differ only in the enumeration
`cuts T` of the cut summands. This file defines the shape once, as the algebra homomorphism
`comulAlgHomNG cuts`; the Connes–Kreimer coproduct is its instance at the pruning cuts
`cutSummandsN` (`Coproduct/Pruning.lean`).

## Main definitions

* `ConnesKreimer.comulTreeNG`, `ConnesKreimer.comulForestNG`: the generic coproduct on trees and
  forests.
* `ConnesKreimer.comulAlgHomNG`: the generic coproduct as an algebra hom.
* `ConnesKreimer.WithCuts R cuts`: the carrier indexed by a cut enumeration, a bialgebra when
  `IsAdmissibleCuts cuts` holds.

## Main results

* `ConnesKreimer.comulTreeNG_eq_sum`, `ConnesKreimer.comulForestNG_eq_sum`: the coproduct as one
  sum over the cut convolutions `treeCutsG` and `forestCutsG`.

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- The generic admissible-cut coproduct on a tree, for a cut enumeration `cuts`. At the pruning
    cuts `cutSummandsN` it is the Connes–Kreimer coproduct. -/
noncomputable def comulTreeNG
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (T : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α))
  + ((cuts T).map (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-- Forest-level generic coproduct (multiplicative extension). -/
noncomputable def comulForestNG
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (F : Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  (F.map (comulTreeNG (R := R) cuts)).prod

@[simp] theorem comulForestNG_zero
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)) :
    comulForestNG (R := R) cuts (0 : Forest (UnorderedTree α)) = 1 := by
  simp only [comulForestNG, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestNG_add
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (F G : Forest (UnorderedTree α)) :
    comulForestNG (R := R) cuts (F + G) =
      comulForestNG (R := R) cuts F * comulForestNG (R := R) cuts G := by
  unfold comulForestNG
  rw [Multiset.map_add, Multiset.prod_add]

@[simp] theorem comulForestNG_cons
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (T : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    comulForestNG (R := R) cuts (T ::ₘ F) =
      comulTreeNG (R := R) cuts T * comulForestNG (R := R) cuts F := by
  unfold comulForestNG
  rw [Multiset.map_cons, Multiset.prod_cons]

/-- The **generic admissible-cut coproduct as an algebra hom**, parameterized by
    the cut enumeration `cuts`. -/
noncomputable def comulAlgHomNG
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  aeval (comulTreeNG cuts)

@[simp] theorem comulAlgHomNG_apply_of'
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (F : Forest (UnorderedTree α)) :
    comulAlgHomNG (R := R) cuts (of' F) = comulForestNG cuts F :=
  aeval_of' _ F

@[simp] theorem comulAlgHomNG_apply_ofTree
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (T : UnorderedTree α) :
    comulAlgHomNG (R := R) cuts (ofTree T) = comulTreeNG cuts T :=
  aeval_ofTree _ T

/-! ### The generic coproduct as a sum over cut convolutions

`treeCutsG`/`forestCutsG` (`Combinatorics/RootedTree/Cut.lean`) enumerate
the (crown, trunk-forest) pairs of a tree and their convolution over a
forest; `cutTensor` sends a pair to `of' crown ⊗ of' trunk`. -/

/-- Tensor-product factor of a (crown, trunk) cut pair. -/
noncomputable def cutTensor (p : Forest (UnorderedTree α) × Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  of' (R := R) p.1 ⊗ₜ[R] of' p.2

theorem cutTensor_combinerProjG (p q : Forest (UnorderedTree α) × Forest (UnorderedTree α)) :
    cutTensor (R := R) (combinerProjG (p, q)) = cutTensor p * cutTensor q := by
  obtain ⟨F1, m1⟩ := p
  obtain ⟨F2, m2⟩ := q
  show cutTensor (R := R) (F1 + F2, m1 + m2) = _
  unfold cutTensor
  simp only [of'_add, Algebra.TensorProduct.tmul_mul_tmul]

/-- `comulTreeNG` as a single multiset sum over `treeCutsG`. -/
theorem comulTreeNG_eq_sum
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (T : UnorderedTree α) :
    comulTreeNG (R := R) cuts T =
      ((treeCutsG cuts T).map (cutTensor (R := R))).sum := by
  unfold comulTreeNG treeCutsG
  rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
  congr 1

/-- `comulForestNG` as a single multiset sum over `forestCutsG`. -/
theorem comulForestNG_eq_sum
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α))
    (F : Forest (UnorderedTree α)) :
    comulForestNG (R := R) cuts F =
      ((forestCutsG cuts F).map (cutTensor (R := R))).sum := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestNG_zero, forestCutsG_zero, Multiset.map_singleton,
        Multiset.sum_singleton]
    show (1 : _) = of' (R := R) (0 : Forest (UnorderedTree α)) ⊗ₜ[R] of' 0
    rw [of'_zero, Algebra.TensorProduct.one_def]
  | cons T F ih =>
    rw [comulForestNG_cons, comulTreeNG_eq_sum, ih, forestCutsG_cons,
        Multiset.map_map,
        show (cutTensor (R := R) ∘ combinerProjG) =
            (fun p => cutTensor (R := R) p.1 * cutTensor p.2) from by
          funext p
          obtain ⟨p₁, p₂⟩ := p
          exact cutTensor_combinerProjG p₁ p₂,
        Multiset.sum_map_product_mul]

/-! ### The policy-indexed carrier `WithCuts`

The `WithLp` pattern: a type synonym indexed by the cut policy, whose
`Bialgebra` instance is gated on an admissibility mixin. The pruning coproduct keeps the plain
carrier (`instBialgebraRho`); other admissible policies get their bialgebra here. -/

set_option linter.unusedVariables false in
variable (R) in
/-- Type synonym for `ConnesKreimer R (UnorderedTree α)` carrying the generic
admissible-cut coproduct at the fixed policy `cuts`. -/
def WithCuts (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α)) :
    Type _ :=
  ConnesKreimer R (UnorderedTree α)

variable (cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α))

noncomputable instance : CommSemiring (WithCuts R cuts) :=
  inferInstanceAs (CommSemiring (ConnesKreimer R (UnorderedTree α)))

noncomputable instance : Algebra R (WithCuts R cuts) :=
  inferInstanceAs (Algebra R (ConnesKreimer R (UnorderedTree α)))

/-- A cut policy is admissible when the generic coproduct `comulAlgHomNG cuts` is
coassociative and counital, uniformly in the coefficient ring. Gates the
`Bialgebra` instance on `WithCuts` (the `Fact`-style mixin of the `WithLp`
pattern). -/
class IsAdmissibleCuts : Prop where
  coassoc : ∀ (R : Type*) [CommRing R],
    (Algebra.TensorProduct.assoc R R R
        (ConnesKreimer R (UnorderedTree α)) (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHomNG (R := R) cuts)
        (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))).comp (comulAlgHomNG cuts)) =
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
      (comulAlgHomNG (R := R) cuts)).comp (comulAlgHomNG cuts)
  counit_rTensor : ∀ (R : Type*) [CommSemiring R],
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))).comp (comulAlgHomNG cuts) =
      (Algebra.TensorProduct.lid R (ConnesKreimer R (UnorderedTree α))).symm.toAlgHom
  counit_lTensor : ∀ (R : Type*) [CommSemiring R],
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
        (counit (R := R))).comp (comulAlgHomNG cuts) =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R (UnorderedTree α))).symm.toAlgHom

/-- Any admissible cut policy makes `WithCuts R cuts` a bialgebra. -/
noncomputable instance WithCuts.instBialgebra
    {R : Type*} [CommRing R] [IsAdmissibleCuts cuts] :
    Bialgebra R (WithCuts R cuts) :=
  Bialgebra.ofAlgHom (A := WithCuts R cuts) (comulAlgHomNG cuts) counit
    (IsAdmissibleCuts.coassoc (cuts := cuts) R)
    (IsAdmissibleCuts.counit_rTensor (cuts := cuts) R)
    (IsAdmissibleCuts.counit_lTensor (cuts := cuts) R)

end ConnesKreimer
