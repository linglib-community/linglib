module

public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The pruning coproduct Δ^ρ

The Connes–Kreimer coproduct on unordered rooted trees, summing over admissible cuts that prune
the cut subtrees, with the Hochschild 1-cocycle property of grafting and the counit laws.

## Main definitions

* `ConnesKreimer.comulTreeN`, `ConnesKreimer.comulForestN`, `ConnesKreimer.comulAlgHomN`: the
  Δ^ρ coproduct, as the generic admissible-cut coproduct (`Coproduct/WithCuts.lean`) at the
  enumeration `cutSummandsN`.
* `ConnesKreimer.bPlusLin`: grafting `B+_a` as a linear map.

## Main results

* `ConnesKreimer.comulAlgHomN_bPlusLin_cocycle`: the Hochschild 1-cocycle law
  `Δ^ρ ∘ B+_a = B+_a ⊗ 1 + (id ⊗ B+_a) ∘ Δ^ρ`.
* `ConnesKreimer.counit_rTensor_comulAlgHomN`, `ConnesKreimer.counit_lTensor_comulAlgHomN`: the
  counit laws.
* `ConnesKreimer.comulAlgHomN_coassoc_algHom`, `comulRhoN_coassoc`: coassociativity, by Foissy's
  subalgebra argument.
* `ConnesKreimer.instBialgebraRho`: the Δ^ρ `Bialgebra`, over any `CommSemiring`.

## Implementation notes

`B+` only well-defines on unordered children
(`Multiset (UnorderedTree α) → UnorderedTree α`); on planar trees it would need
a canonical ordering — hence the cocycle and everything downstream live
at the `UnorderedTree` level.

The GL/CK duality theorem lives downstream in
`Coproduct/PruningDuality.lean` (its proof needs the B⁻ calculus of
`BMinus.lean`, which imports this file); the full `HopfAlgebra`
instance is in `HopfAlgebra.lean`.

`[UPSTREAM]` candidate.

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
* [grinberg-reiner-2020]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## UnorderedTree tree- and forest-level Δ^ρ

Definitional instantiations of the generic admissible-cut coproduct
(`Coproduct/WithCuts.lean`) at the Δ^ρ enumeration `cutSummandsN`. -/

/-- The pruning coproduct Δ^ρ of a tree, which is `comulTreeNG` at the pruning cuts. -/
noncomputable def comulTreeN :
    UnorderedTree α →
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  comulTreeNG cutSummandsN

/-- The nonplanar forest-level Δ^ρ (multiplicative extension). -/
noncomputable def comulForestN :
    Forest (UnorderedTree α) →
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  comulForestNG cutSummandsN

@[simp] theorem comulForestN_zero :
    comulForestN (R := R) (0 : Forest (UnorderedTree α)) = 1 :=
  comulForestNG_zero _

@[simp] theorem comulForestN_add (F G : Forest (UnorderedTree α)) :
    comulForestN (R := R) (F + G) =
      comulForestN (R := R) F * comulForestN (R := R) G :=
  comulForestNG_add _ F G

@[simp] theorem comulForestN_cons (T : UnorderedTree α) (F : Forest (UnorderedTree α)) :
    comulForestN (R := R) (T ::ₘ F) =
      comulTreeN (R := R) T * comulForestN (R := R) F :=
  comulForestNG_cons _ T F

/-- The pruning coproduct Δ^ρ as an algebra homomorphism, which is `comulAlgHomNG` at the
pruning cuts. -/
noncomputable def comulAlgHomN :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) :=
  comulAlgHomNG cutSummandsN

@[simp] theorem comulAlgHomN_apply_of' (F : Forest (UnorderedTree α)) :
    comulAlgHomN (R := R) (α := α) (of' F) = comulForestN F :=
  comulAlgHomNG_apply_of' _ F

@[simp] theorem comulAlgHomN_apply_ofTree (T : UnorderedTree α) :
    comulAlgHomN (R := R) (α := α) (ofTree T) = comulTreeN T :=
  comulAlgHomNG_apply_ofTree _ T

/-! ## Hochschild 1-cocycle for `B+_a`

`B+_a : Forest (UnorderedTree α) → UnorderedTree α` is the smart constructor
`UnorderedTree.node a`. Linearly extended to `bPlusLin a : H →ₗ[R] H` (sending
basis element `of' F` to `ofTree (UnorderedTree.node a F)`), it satisfies
the Hochschild 1-cocycle property:

  Δ^ρ ∘ B+_a = (·) ⊗ 1 ∘ B+_a + (id ⊗ B+_a) ∘ Δ^ρ

i.e., for every `x : H`:

  Δ^ρ (B+_a x) = (B+_a x) ⊗ 1 + (id ⊗ B+_a)(Δ^ρ x).

This is the algebraic input to Foissy's clean inductive proof of
coassociativity (§A.7-δ): the subalgebra `A := {x | (Δ ⊗ id)(Δ x) =
(id ⊗ Δ)(Δ x)}` is closed under `B+_a`, contains all leaves (which are
`B+_a 1`), hence equals the whole algebra. -/

/-! ### B+_a as a linear map -/

/-- The grafting map `B+_a` extends the smart constructor `UnorderedTree.node a` linearly
    to an `R`-linear endomorphism of `ConnesKreimer R (UnorderedTree α)`,
    sending the basis element `of' F` to `ofTree (UnorderedTree.node a F)`. -/
noncomputable def bPlusLin (a : α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  ConnesKreimer.linearLift (fun F => ofTree (UnorderedTree.node a F))

@[simp] theorem bPlusLin_of' (a : α) (F : Forest (UnorderedTree α)) :
    bPlusLin (R := R) a (of' F) = ofTree (UnorderedTree.node a F) := by
  rw [bPlusLin, ConnesKreimer.linearLift_of']

@[simp] theorem bPlusLin_one (a : α) :
    bPlusLin (R := R) a (1 : ConnesKreimer R (UnorderedTree α)) =
      ofTree (UnorderedTree.leaf a) := by
  show bPlusLin (R := R) a (of' 0) = _
  rw [bPlusLin_of']
  show ofTree (UnorderedTree.node a 0) = ofTree (UnorderedTree.leaf a)
  rfl

/-! ### `comulForestN` as a sum over forest cuts -/

theorem comulForestN_eq_sum (F : Forest (UnorderedTree α)) :
    comulForestN (R := R) F = ((forestCutsG cutSummandsN F).map
      (fun pf => of' (R := R) pf.1 ⊗ₜ[R] of' (R := R) pf.2)).sum :=
  comulForestNG_eq_sum cutSummandsN F

/-! ### The cocycle theorem (basis-level) -/

theorem comulTreeN_leaf (a : α) :
    comulTreeN (R := R) (UnorderedTree.leaf a) =
      ofTree (UnorderedTree.leaf a) ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] ofTree (UnorderedTree.leaf a) := by
  unfold comulTreeN comulTreeNG
  rw [cutSummandsN_leaf, Multiset.map_singleton, Multiset.sum_singleton, of'_zero]

theorem comulTreeN_node_cocycle (a : α) (F : Forest (UnorderedTree α)) :
    comulTreeN (R := R) (UnorderedTree.node a F) =
      ofTree (UnorderedTree.node a F) ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulForestN F) := by
  unfold comulTreeN comulTreeNG
  rw [cutSummandsN_node, comulForestN_eq_sum,
      map_multiset_sum (LinearMap.lTensor (ConnesKreimer R (UnorderedTree α))
        (bPlusLin (R := R) a))]
  simp only [Multiset.map_map]
  refine congr_arg (_ + ·) (congr_arg Multiset.sum
    (Multiset.map_congr rfl (fun pf _ => ?_)))
  show of' (R := R) pf.1 ⊗ₜ[R] ofTree (UnorderedTree.node a pf.2) =
       (LinearMap.lTensor (ConnesKreimer R (UnorderedTree α)) (bPlusLin (R := R) a))
         (of' (R := R) pf.1 ⊗ₜ[R] of' (R := R) pf.2)
  rw [LinearMap.lTensor_tmul, bPlusLin_of']

theorem comulAlgHomN_bPlusLin_cocycle (a : α) (F : Forest (UnorderedTree α)) :
    comulAlgHomN (R := R) (bPlusLin (R := R) a (of' F)) =
      bPlusLin (R := R) a (of' F) ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulAlgHomN (of' F)) := by
  rw [bPlusLin_of', comulAlgHomN_apply_ofTree, comulAlgHomN_apply_of']
  exact comulTreeN_node_cocycle a F

/-! ## Counit laws

`(ε ⊗ id) ∘ Δ^ρ = lid⁻¹` and `(id ⊗ ε) ∘ Δ^ρ = rid⁻¹`, checked on trees through the cocycle
`comulTreeN_node_cocycle`. The left law needs induction on the tree. -/

private theorem counit_bPlusLin (a : α) (y : ConnesKreimer R (UnorderedTree α)) :
    counit (R := R) (bPlusLin (R := R) a y) = 0 := by
  have h : (counit (R := R)).toLinearMap ∘ₗ bPlusLin (R := R) a = 0 :=
    ConnesKreimer.lhom_ext' fun F ↦ by simp
  exact congr($h y)

theorem counit_rTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (counit (R := R)) (AlgHom.id R _)).comp comulAlgHomN =
      (Algebra.TensorProduct.lid R (ConnesKreimer R (UnorderedTree α))).symm.toAlgHom := by
  refine algHom_ext_ofTree fun T ↦ ?_
  induction T with
  | node a F ih =>
    have hF := algHom_of'_eq_of_ofTree ih
    have h (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
        Algebra.TensorProduct.map counit (AlgHom.id R _)
          (LinearMap.lTensor _ (bPlusLin (R := R) a) z) =
        LinearMap.lTensor R (bPlusLin a) (Algebra.TensorProduct.map counit (AlgHom.id R _) z) := by
      induction z using TensorProduct.inductionOn <;> simp_all
    simp [comulTreeN_node_cocycle, h, by simpa using hF]

theorem counit_lTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (AlgHom.id R _) (counit (R := R))).comp comulAlgHomN =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R (UnorderedTree α))).symm.toAlgHom := by
  refine algHom_ext_ofTree fun T ↦ ?_
  obtain ⟨a, F, rfl⟩ : ∃ a F, T = UnorderedTree.node a F := ⟨_, _, (node_eta T).symm⟩
  have h (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
      Algebra.TensorProduct.map (AlgHom.id R _) counit
        (LinearMap.lTensor _ (bPlusLin (R := R) a) z) = 0 := by
    induction z using TensorProduct.inductionOn <;> simp_all [counit_bPlusLin]
  simp [comulTreeN_node_cocycle, h]

section CoassocFoissy

/-! ### Coassociativity: Foissy's subalgebra argument

Foissy's clean proof ([foissy-introduction-hopf-algebras-trees]; for the
connected-graded-bialgebra framing see [grinberg-reiner-2020]): the set
`A := {x | (id ⊗ Δ)(Δ x) = assoc ((Δ ⊗ id)(Δ x))}` is a subalgebra, closed
under `B+_a` by the Hochschild cocycle, and contains every `ofTree T` by
height induction — hence `A = ⊤`. Works over any `CommSemiring`, with no
pairing or nondegeneracy input. -/

/-- The left-hand side of coassociativity, `x ↦ assoc ((Δ ⊗ id) (Δ x))`, as an algebra
homomorphism. -/
noncomputable def coassocLHS :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R]
        (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  (Algebra.TensorProduct.assoc R R R _ _ _).toAlgHom.comp
    ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
      (AlgHom.id R _)).comp comulAlgHomN)

/-- The right-hand side of coassociativity, `x ↦ (id ⊗ Δ) (Δ x)`, as an algebra homomorphism. -/
noncomputable def coassocRHS :
    ConnesKreimer R (UnorderedTree α) →ₐ[R]
      ConnesKreimer R (UnorderedTree α) ⊗[R]
        (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
    (comulAlgHomN (R := R) (α := α))).comp comulAlgHomN

/-- The coassociativity subalgebra holds the elements on which the two
    sides of coassociativity agree. By Foissy's argument it contains every
    tree (`ofTree_mem_coassocSubalg`), hence is all of `H`. -/
noncomputable def coassocSubalg : Subalgebra R (ConnesKreimer R (UnorderedTree α)) :=
  AlgHom.equalizer (coassocLHS (R := R) (α := α)) coassocRHS

theorem mem_coassocSubalg (x : ConnesKreimer R (UnorderedTree α)) :
    x ∈ coassocSubalg (R := R) (α := α) ↔ coassocLHS x = coassocRHS x :=
  AlgHom.mem_equalizer _ _ _

/-! ### Linear extension of the cocycle

Both sides of `comulAlgHomN_bPlusLin_cocycle` are linear, so it extends from forests to all of
`H` by `ConnesKreimer.lhom_ext'`. -/

theorem comulAlgHomN_bPlusLin_cocycle_general (a : α)
    (x : ConnesKreimer R (UnorderedTree α)) :
    comulAlgHomN (bPlusLin (R := R) a x) =
      bPlusLin (R := R) a x ⊗ₜ[R] (1 : ConnesKreimer R (UnorderedTree α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulAlgHomN x) := by
  have heq : (comulAlgHomN (R := R) (α := α)).toLinearMap ∘ₗ bPlusLin (R := R) a =
      (TensorProduct.mk R _ _).flip 1 ∘ₗ bPlusLin (R := R) a +
        LinearMap.lTensor _ (bPlusLin (R := R) a) ∘ₗ (comulAlgHomN (R := R) (α := α)).toLinearMap :=
    ConnesKreimer.lhom_ext' fun F ↦ comulAlgHomN_bPlusLin_cocycle a F
  exact congr($heq x)

/-! ### Closure of `coassocSubalg` under `B+_a`

The substantive Foissy bit. Uses the cocycle (twice) plus tensor-algebra
calculations. Sketch (Sweedler-style, with `Δ x = Σᵢ aᵢ ⊗ bᵢ`):

* `Δ(B+_a x) = (B+_a x) ⊗ 1 + Σᵢ aᵢ ⊗ B+_a bᵢ` (cocycle).
* `(Δ ⊗ id)(Δ(B+_a x)) = Δ(B+_a x) ⊗ 1 + Σᵢ Δ(aᵢ) ⊗ B+_a bᵢ`. Re-apply cocycle to
  `Δ(B+_a x)` to expand the first summand.
* `assoc((Δ ⊗ id)(Δ(B+_a x))) = (B+_a x) ⊗ (1 ⊗ 1) + Σᵢ aᵢ ⊗ (B+_a bᵢ ⊗ 1) +
  Σᵢ assoc(Δ(aᵢ) ⊗ B+_a bᵢ)`.
* `(id ⊗ Δ)(Δ(B+_a x)) = (B+_a x) ⊗ (1 ⊗ 1) + Σᵢ aᵢ ⊗ (B+_a bᵢ ⊗ 1) +
  Σᵢ aᵢ ⊗ ((id ⊗ B+_a)(Δ bᵢ))`.
* The "shared" first two summands match by inspection. The third summands match via
  `(id ⊗ id ⊗ B+_a)` applied to the hypothesis `assoc((Δ ⊗ id)(Δ x)) = (id ⊗ Δ)(Δ x)`.

A clean Lean implementation would extract a `LinearMap`-level helper
`assoc_lTensor_bPlus_eq : assoc ∘ (Δ ⊗ id) ∘ (id ⊗ B+_a) = (id ⊗ id ⊗ B+_a) ∘ assoc ∘ (Δ ⊗ id)`
(provable by `TensorProduct.inductionOn`), then close by `congrArg ((id ⊗ id ⊗ B+_a))` on `hx`. -/
/-! ### Helper commutations for the bPlus closure proof

Three commutation/identity lemmas for the substantive Foissy bit:

* `comulAlgHomN_lTensor_bPlus_commute`: `(Δ ⊗ id) ∘ (id ⊗ B+) = (id ⊗ id ⊗ B+) ∘ (Δ ⊗ id)`,
  i.e., the comul on the left factor commutes with B+ on the right factor.
* `assoc_lTensor_bPlus_commute`: `assoc ∘ (id ⊗ id_R ⊗ B+ on (H⊗H)⊗H) =
  (id ⊗ id ⊗ B+ on H⊗(H⊗H)) ∘ assoc`, i.e., the associator commutes with B+
  acting on the rightmost factor.
* `lTensor_id_Δ_bPlus_eq`: `(id ⊗ Δ) ∘ (id ⊗ B+) z = assoc((id ⊗ B+)(z) ⊗ 1) +
  (id ⊗ id ⊗ B+) ∘ (id ⊗ Δ)(z)`, by cocycle on the right factor of `(id ⊗ B+)(z)`. -/

private theorem comulAlgHomN_lTensor_bPlus_commute (a : α)
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    (Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
        (AlgHom.id R (ConnesKreimer R (UnorderedTree α))))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.lTensor _ (bPlusLin (R := R) a))
      ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
        (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        LinearMap.lTensor_tmul]
  | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

private theorem assoc_lTensor_bPlus_commute (a : α)
    (z : (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) ⊗[R]
          ConnesKreimer R (UnorderedTree α)) :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α)) (ConnesKreimer R (UnorderedTree α)))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
      ((Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α)) (ConnesKreimer R (UnorderedTree α))) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul w c =>
    -- w : H ⊗ H, c : H. Need to induct on w to expose the (a ⊗ b) ⊗ c form.
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.assoc_tmul,
          Algebra.TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
          LinearMap.lTensor_tmul]
    | add w₁ w₂ ih₁ ih₂ =>
      simp only [TensorProduct.add_tmul, map_add]
      rw [ih₁, ih₂]
  | add z₁ z₂ ih₁ ih₂ =>
    simp only [map_add]
    rw [ih₁, ih₂]

private theorem lTensor_id_Δ_bPlus_eq (a : α)
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
        (comulAlgHomN (R := R) (α := α)))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α)) (ConnesKreimer R (UnorderedTree α)))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a) z) ⊗ₜ
        (1 : ConnesKreimer R (UnorderedTree α))) +
    (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
      ((Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
        (comulAlgHomN (R := R) (α := α))) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    -- LHS: (map id Δ)((lTensor B+a)(x ⊗ y)) = (map id Δ)(x ⊗ B+a y) = x ⊗ Δ(B+a y)
    --    = x ⊗ ((B+a y) ⊗ 1 + (lTensor B+a)(Δ y)) = x ⊗ ((B+a y) ⊗ 1) + x ⊗ (lTensor B+a)(Δ y)
    -- RHS: assoc((x ⊗ B+a y) ⊗ 1) + (lTensor (lTensor B+a))(x ⊗ Δy)
    --    = x ⊗ ((B+a y) ⊗ 1) + x ⊗ (lTensor B+a)(Δ y)
    -- ✓ by simp with all the relevant tmul + cocycle lemmas.
    simp only [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
               Algebra.TensorProduct.assoc_tmul, AlgHom.id_apply,
               comulAlgHomN_bPlusLin_cocycle_general, TensorProduct.tmul_add]
  | add z₁ z₂ ih₁ ih₂ =>
    simp only [map_add, TensorProduct.add_tmul]
    rw [ih₁, ih₂]
    abel

theorem bPlus_mem_coassocSubalg (a : α) (x : ConnesKreimer R (UnorderedTree α))
    (hx : x ∈ coassocSubalg (R := R) (α := α)) :
    bPlusLin (R := R) a x ∈ coassocSubalg (R := R) (α := α) := by
  rw [mem_coassocSubalg] at hx ⊢
  -- The proof structure: express both `coassocLHS (B+_a x)` and `coassocRHS (B+_a x)`
  -- in the form `shared + (lTensor H (lTensor H B+_a))(coassocXXX x)` with the
  -- *same* shared part, then use hx (coassocLHS x = coassocRHS x) to conclude.
  --
  -- shared := (B+_a x) ⊗ (1 ⊗ 1) + assoc(((lTensor H B+_a)(Δ x)) ⊗ 1)
  show (Algebra.TensorProduct.assoc R R R _ _ _)
        ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
          (AlgHom.id R _)) (comulAlgHomN (bPlusLin (R := R) a x))) =
       (Algebra.TensorProduct.map (AlgHom.id R _)
          (comulAlgHomN (R := R) (α := α))) (comulAlgHomN (bPlusLin (R := R) a x))
  -- Apply cocycle on x: Δ(B+_a x) = (B+_a x) ⊗ 1 + (lTensor _ B+_a)(Δ x).
  rw [comulAlgHomN_bPlusLin_cocycle_general]
  -- Distribute (map ⊗ id), (map id ⊗ ·), assoc through the addition.
  rw [map_add, map_add, map_add]
  -- LHS first term: assoc((map Δ id)(Bx ⊗ 1)) = assoc(Δ(Bx) ⊗ 1)
  --                  = assoc(((Bx ⊗ 1) + (lTensor _ B+a)(Δx)) ⊗ 1) [cocycle on Bx]
  --                  = assoc((Bx ⊗ 1) ⊗ 1) + assoc(((lTensor _ B+a)(Δx)) ⊗ 1)
  --                  = Bx ⊗ (1 ⊗ 1) + assoc(((lTensor _ B+a)(Δx)) ⊗ 1)
  rw [show (Algebra.TensorProduct.assoc R R R _ _ _)
        ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
          (AlgHom.id R _)) (bPlusLin (R := R) a x ⊗ₜ
            (1 : ConnesKreimer R (UnorderedTree α)))) =
      (bPlusLin (R := R) a x) ⊗ₜ ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ
        (1 : ConnesKreimer R (UnorderedTree α))) +
      (Algebra.TensorProduct.assoc R R R _ _ _)
        ((LinearMap.lTensor _ (bPlusLin (R := R) a))
          (comulAlgHomN x) ⊗ₜ (1 : ConnesKreimer R (UnorderedTree α))) from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        comulAlgHomN_bPlusLin_cocycle_general, TensorProduct.add_tmul, map_add,
        Algebra.TensorProduct.assoc_tmul]]
  -- LHS second term: use Δ⊗id-vs-id⊗B+a commutation, then assoc-vs-B+a commutation.
  rw [comulAlgHomN_lTensor_bPlus_commute, assoc_lTensor_bPlus_commute]
  -- RHS first term: (map id Δ)(Bx ⊗ 1) = Bx ⊗ Δ(1) = Bx ⊗ (1 ⊗ 1).
  rw [show (Algebra.TensorProduct.map (AlgHom.id R _)
            (comulAlgHomN (R := R) (α := α)))
          (bPlusLin (R := R) a x ⊗ₜ (1 : ConnesKreimer R (UnorderedTree α))) =
        (bPlusLin (R := R) a x) ⊗ₜ
          ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ
            (1 : ConnesKreimer R (UnorderedTree α))) from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
        Algebra.TensorProduct.one_def]]
  -- RHS second term: use cocycle-driven identity `lTensor_id_Δ_bPlus_eq`.
  rw [lTensor_id_Δ_bPlus_eq]
  -- Now both sides are `Bx ⊗ (1⊗1) + assoc(...) + (lTensor (lTensor B+a))(coassocXXX_inner x)`,
  -- modulo associativity. Use hx (coassocLHS x = coassocRHS x — defeq to the inner forms)
  -- to bridge the two third summands; then `abel` for reordering.
  have hlift : (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
                ((Algebra.TensorProduct.assoc R R R _ _ _)
                  ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
                    (AlgHom.id R _)) (comulAlgHomN x))) =
              (LinearMap.lTensor _ (LinearMap.lTensor _ (bPlusLin (R := R) a)))
                ((Algebra.TensorProduct.map (AlgHom.id R _)
                  (comulAlgHomN (R := R) (α := α))) (comulAlgHomN x)) :=
    congrArg _ hx
  rw [hlift]
  abel

/-! ### Tree induction: every `ofTree T` is in `coassocSubalg` -/

private theorem of'_mem_coassocSubalg_of_trees (F : Forest (UnorderedTree α))
    (h : ∀ T ∈ F, ofTree T ∈ coassocSubalg (R := R) (α := α)) :
    of' (R := R) F ∈ coassocSubalg (R := R) (α := α) := by
  induction F using Multiset.induction with
  | empty =>
    rw [show ((0 : Forest (UnorderedTree α)) : Forest (UnorderedTree α))
        = (0 : Forest (UnorderedTree α)) from rfl,
        of'_zero]
    exact one_mem _
  | cons T F' ih =>
    have hT : ofTree T ∈ coassocSubalg (R := R) (α := α) := h T (Multiset.mem_cons_self T F')
    have hF' : ∀ T' ∈ F', ofTree T' ∈ coassocSubalg (R := R) (α := α) :=
      fun T' hT' => h T' (Multiset.mem_cons_of_mem hT')
    have ih' := ih hF'
    rw [of'_cons]
    exact mul_mem hT ih'

theorem ofTree_mem_coassocSubalg (T : UnorderedTree α) :
    ofTree T ∈ coassocSubalg (R := R) (α := α) := by
  -- Strong induction on T.height.
  suffices aux : ∀ n : ℕ, ∀ T : UnorderedTree α, T.height = n →
      ofTree T ∈ coassocSubalg (R := R) (α := α) by
    exact aux T.height T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hT
    -- Pick a planar rep T = mk (RoseTree.node a children).
    obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = UnorderedTree.mk T₀ :=
      ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
    obtain ⟨a, children⟩ := T₀
    -- T = mk (.node a children) = UnorderedTree.node a (Multiset.ofList (children.map mk))
    rw [show (UnorderedTree.mk (RoseTree.node a children) : UnorderedTree α) =
        UnorderedTree.node a (Multiset.ofList (children.map UnorderedTree.mk))
        from (UnorderedTree.node_mk_tree_list a children).symm]
    -- ofTree (UnorderedTree.node a F) = bPlusLin a (of' F) by bPlusLin_of'.
    rw [show ofTree (UnorderedTree.node a (Multiset.ofList (children.map UnorderedTree.mk)))
            = bPlusLin (R := R) a (of' (Multiset.ofList (children.map UnorderedTree.mk)))
            from (bPlusLin_of' a _).symm]
    apply bPlus_mem_coassocSubalg
    -- of' F ∈ coassocSubalg, where F = Multiset.ofList (children.map mk).
    apply of'_mem_coassocSubalg_of_trees
    intro T' hT'
    -- T' ∈ Multiset.ofList (children.map mk). Use IH on T'.height < (mk (.node a children)).height.
    have hT'_depth : T'.height < (UnorderedTree.mk (RoseTree.node a children)).height := by
      have := UnorderedTree.height_lt_of_mem T'
        (Multiset.ofList (children.map UnorderedTree.mk)) hT' a
      rw [show
          (UnorderedTree.node a (Multiset.ofList (children.map UnorderedTree.mk)) :
            UnorderedTree α) =
          UnorderedTree.mk (RoseTree.node a children) from
          UnorderedTree.node_mk_tree_list a children] at this
      exact this
    rw [hT] at hT'_depth
    exact IH T'.height hT'_depth T' rfl

/-! ### Coassociativity at the algebra-hom level

Direct corollary: `coassocLHS = coassocRHS` as algebra homs. The
`Bialgebra.ofAlgHom` constructor takes this in its unfolded form
(without going through the `coassocLHS`/`coassocRHS` named bundles),
so we expose both. -/

theorem coassocLHS_eq_coassocRHS :
    coassocLHS (R := R) (α := α) = coassocRHS := by
  ext T
  exact (mem_coassocSubalg _).mp (ofTree_mem_coassocSubalg T)

theorem comulAlgHomN_coassoc_algHom :
    (Algebra.TensorProduct.assoc R R R (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α)) (ConnesKreimer R (UnorderedTree α))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHomN (R := R) (α := α))
        (AlgHom.id R _)).comp comulAlgHomN) =
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (UnorderedTree α)))
      (comulAlgHomN (R := R) (α := α))).comp comulAlgHomN :=
  coassocLHS_eq_coassocRHS

theorem comulRhoN_coassoc :
    (TensorProduct.assoc R
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))
        (ConnesKreimer R (UnorderedTree α))).toLinearMap ∘ₗ
      (comulAlgHomN (R := R) (α := α)).toLinearMap.rTensor _ ∘ₗ
      (comulAlgHomN (R := R) (α := α)).toLinearMap =
    (comulAlgHomN (R := R) (α := α)).toLinearMap.lTensor _ ∘ₗ
      (comulAlgHomN (R := R) (α := α)).toLinearMap :=
  congrArg AlgHom.toLinearMap comulAlgHomN_coassoc_algHom

end CoassocFoissy

/-- The pruning coproduct makes `ConnesKreimer R (UnorderedTree α)` a bialgebra over any
    commutative semiring. -/
noncomputable instance instBialgebraRho :
    Bialgebra R (ConnesKreimer R (UnorderedTree α)) :=
  Bialgebra.ofAlgHom (A := ConnesKreimer R (UnorderedTree α)) comulAlgHomN counit
    comulAlgHomN_coassoc_algHom
    counit_rTensor_comulAlgHomN
    counit_lTensor_comulAlgHomN

theorem coalgebra_comul_apply (x : ConnesKreimer R (UnorderedTree α)) :
    Coalgebra.comul (R := R) x = comulAlgHomN x := rfl

theorem coalgebra_counit_apply (x : ConnesKreimer R (UnorderedTree α)) :
    CoalgebraStruct.counit (R := R) x = counit x := rfl

/-! ### GL/CK duality: downstream

The GL/CK duality theorem (`pairing_gl_eq_pairing_coproduct_Rho`) lives in
`Coproduct/PruningDuality.lean`, downstream of `BMinus.lean` (whose B⁻
calculus drives its proof). -/

end ConnesKreimer
