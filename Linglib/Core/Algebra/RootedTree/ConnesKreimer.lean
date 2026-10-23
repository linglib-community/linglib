/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The Connes–Kreimer algebra

`ConnesKreimer R T` is the commutative `R`-algebra with a basis indexed by the forests of `T`
(finite multisets of elements of `T`), multiplied by disjoint union, with the empty forest as
unit. It is the free commutative `R`-algebra on `T`. When `T` is a type of rooted trees, cutting
trees makes it the Connes–Kreimer Hopf algebra; the coproducts are in the sibling `Coproduct/`
files and the antipode in `HopfAlgebra.lean`.

## Main definitions

* `UnorderedTree.Forest T`: forests of `T`, as multisets.
* `ConnesKreimer R T`: the algebra.
* `ConnesKreimer.single`, `ConnesKreimer.of'`, `ConnesKreimer.ofTree`: basis vectors.
* `ConnesKreimer.coeff`: the coefficient of a forest.
* `ConnesKreimer.aeval`: the algebra hom determined by its values on trees.
* `ConnesKreimer.basisSingleOne`, `ConnesKreimer.linearLift`: the forest basis and linear maps
  defined on it.
* `ConnesKreimer.counit`: the coefficient of the empty forest, as an algebra hom.

## Implementation notes

`ConnesKreimer R T` wraps `AddMonoidAlgebra R (Forest T)` in a one-field structure, as
`Polynomial` does. The bare carrier already has the group-like bialgebra structure
`AddMonoidAlgebra.instBialgebra`, and a `def` synonym would leak parent instance paths (an
`SMul ℤ` diamond). Consumers use the API of this file; `toFinsuppAlgEquiv` is the bridge to the
bare carrier.

`[UPSTREAM]` candidate.

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

noncomputable section

/-- Forests of elements of `T`, as multisets; addition is disjoint union. -/
abbrev UnorderedTree.Forest (T : Type*) : Type _ := Multiset T

open UnorderedTree

/-- The Connes–Kreimer algebra on `T`, the `R`-span of the forests of `T` with disjoint union
as product. -/
structure ConnesKreimer (R : Type*) [CommSemiring R] (T : Type*) where
  /-- Wrap an `AddMonoidAlgebra` as an element of the Connes–Kreimer algebra. -/
  ofFinsupp ::
  /-- The underlying forest-indexed `AddMonoidAlgebra`. -/
  toFinsupp : AddMonoidAlgebra R (Forest T)

namespace ConnesKreimer

variable {R : Type*} [CommSemiring R] {T : Type*} {S S₁ S₂ : Type*}
  {p q : ConnesKreimer R T}

theorem toFinsupp_injective :
    Function.Injective (toFinsupp : ConnesKreimer R T → AddMonoidAlgebra R (Forest T)) :=
  fun ⟨_⟩ ⟨_⟩ h => congrArg ofFinsupp h

@[simp] theorem toFinsupp_inj : p.toFinsupp = q.toFinsupp ↔ p = q :=
  toFinsupp_injective.eq_iff

@[ext] theorem ext (h : p.toFinsupp = q.toFinsupp) : p = q :=
  toFinsupp_injective h

@[simp] theorem ofFinsupp_toFinsupp (p : ConnesKreimer R T) : ⟨p.toFinsupp⟩ = p := rfl

/-! ### Structural operations

Each operation is defined on the `toFinsupp` field; the `toFinsupp_*`
pushforward lemmas are all `rfl` and form the simp normal form. -/

instance : Zero (ConnesKreimer R T) := ⟨⟨0⟩⟩
instance : One (ConnesKreimer R T) := ⟨⟨1⟩⟩
instance : Add (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp + q.toFinsupp⟩⟩
instance : Mul (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp * q.toFinsupp⟩⟩
instance smulZeroClass [SMulZeroClass S (AddMonoidAlgebra R (Forest T))] :
    SMulZeroClass S (ConnesKreimer R T) where
  smul s p := ⟨s • p.toFinsupp⟩
  smul_zero s := ext (smul_zero s)
instance : NatCast (ConnesKreimer R T) :=
  ⟨fun n => ⟨(n : AddMonoidAlgebra R (Forest T))⟩⟩
instance : Pow (ConnesKreimer R T) ℕ := ⟨fun p n => ⟨p.toFinsupp ^ n⟩⟩

@[simp] theorem toFinsupp_zero : (0 : ConnesKreimer R T).toFinsupp = 0 := rfl
@[simp] theorem toFinsupp_one : (1 : ConnesKreimer R T).toFinsupp = 1 := rfl
@[simp] theorem toFinsupp_add (p q : ConnesKreimer R T) :
    (p + q).toFinsupp = p.toFinsupp + q.toFinsupp := rfl
@[simp] theorem toFinsupp_mul (p q : ConnesKreimer R T) :
    (p * q).toFinsupp = p.toFinsupp * q.toFinsupp := rfl
@[simp] theorem toFinsupp_smul [SMulZeroClass S (AddMonoidAlgebra R (Forest T))]
    (s : S) (p : ConnesKreimer R T) :
    (s • p).toFinsupp = s • p.toFinsupp := rfl
@[simp] theorem toFinsupp_pow (p : ConnesKreimer R T) (n : ℕ) :
    (p ^ n).toFinsupp = p.toFinsupp ^ n := rfl

/-! ### The instance stack

Built by injective transport from the single bottom `instCommSemiring`. -/

instance instCommSemiring : CommSemiring (ConnesKreimer R T) :=
  fast_instance% toFinsupp_injective.commSemiring _ toFinsupp_zero toFinsupp_one
    toFinsupp_add toFinsupp_mul (fun n p => toFinsupp_smul n p) toFinsupp_pow
    (fun _ => rfl)

/-! Granular action instances (mirroring `Polynomial`): keeping these one
synthesis step away from the underlying carrier lets nested-tensor goals
(`CK ⊗ (CK ⊗ CK)`) resolve without deep pending chains. -/

instance distribSMul [DistribSMul S (AddMonoidAlgebra R (Forest T))] :
    DistribSMul S (ConnesKreimer R T) where
  smul_add s p q := ext (smul_add s p.toFinsupp q.toFinsupp)

instance distribMulAction [Monoid S]
    [DistribMulAction S (AddMonoidAlgebra R (Forest T))] :
    DistribMulAction S (ConnesKreimer R T) where
  one_smul p := ext (one_smul S p.toFinsupp)
  mul_smul s t p := ext (mul_smul s t p.toFinsupp)
  smul_zero s := ext (smul_zero s)
  smul_add s p q := ext (smul_add s p.toFinsupp q.toFinsupp)

instance instModule [Semiring S]
    [Module S (AddMonoidAlgebra R (Forest T))] :
    Module S (ConnesKreimer R T) where
  add_smul s t p := ext (add_smul s t p.toFinsupp)
  zero_smul p := ext (zero_smul S p.toFinsupp)

instance smulCommClass
    [SMulZeroClass S₁ (AddMonoidAlgebra R (Forest T))]
    [SMulZeroClass S₂ (AddMonoidAlgebra R (Forest T))]
    [SMulCommClass S₁ S₂ (AddMonoidAlgebra R (Forest T))] :
    SMulCommClass S₁ S₂ (ConnesKreimer R T) :=
  ⟨fun s t p => ext (smul_comm s t p.toFinsupp)⟩

instance isScalarTower [SMul S₁ S₂]
    [SMulZeroClass S₁ (AddMonoidAlgebra R (Forest T))]
    [SMulZeroClass S₂ (AddMonoidAlgebra R (Forest T))]
    [IsScalarTower S₁ S₂ (AddMonoidAlgebra R (Forest T))] :
    IsScalarTower S₁ S₂ (ConnesKreimer R T) :=
  ⟨fun s t p => ext (smul_assoc s t p.toFinsupp)⟩

instance instAlgebra : Algebra R (ConnesKreimer R T) where
  algebraMap :=
    { toFun := fun r => ⟨algebraMap R (AddMonoidAlgebra R (Forest T)) r⟩
      map_one' := ext (map_one _)
      map_mul' := fun r s => ext (map_mul _ r s)
      map_zero' := ext (map_zero _)
      map_add' := fun r s => ext (map_add _ r s) }
  commutes' r x := ext (Algebra.commutes r x.toFinsupp)
  smul_def' r x := ext (Algebra.smul_def r x.toFinsupp)

@[simp] theorem toFinsupp_algebraMap (r : R) :
    (algebraMap R (ConnesKreimer R T) r).toFinsupp
      = algebraMap R (AddMonoidAlgebra R (Forest T)) r := rfl

/-! ### Global ring instance

`zsmul` is the pulled-back structural operation and no parent-type path to
`SMul ℤ` exists, so the instance is safely global. -/

section Ring
variable {R : Type*} [CommRing R] {T : Type*}

instance instNeg : Neg (ConnesKreimer R T) := ⟨fun p => ⟨-p.toFinsupp⟩⟩
instance instSub : Sub (ConnesKreimer R T) :=
  ⟨fun p q => ⟨p.toFinsupp - q.toFinsupp⟩⟩
instance instIntCast : IntCast (ConnesKreimer R T) :=
  ⟨fun z => ⟨(z : AddMonoidAlgebra R (Forest T))⟩⟩

@[simp] theorem toFinsupp_neg (p : ConnesKreimer R T) :
    (-p).toFinsupp = -p.toFinsupp := rfl
@[simp] theorem toFinsupp_sub (p q : ConnesKreimer R T) :
    (p - q).toFinsupp = p.toFinsupp - q.toFinsupp := rfl
instance instCommRing : CommRing (ConnesKreimer R T) :=
  fast_instance% toFinsupp_injective.commRing _ toFinsupp_zero toFinsupp_one
    toFinsupp_add toFinsupp_mul toFinsupp_neg toFinsupp_sub
    (fun n p => toFinsupp_smul n p) (fun z p => toFinsupp_smul z p)
    toFinsupp_pow (fun _ => rfl) (fun _ => rfl)

end Ring

/-! ### The algebra equivalence to the bare carrier -/

/-- `toFinsupp` as an `R`-algebra equivalence, the bridge between the wrapper and the bare
`AddMonoidAlgebra`. -/
def toFinsuppAlgEquiv :
    ConnesKreimer R T ≃ₐ[R] AddMonoidAlgebra R (Forest T) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := toFinsupp_mul
  map_add' := toFinsupp_add
  commutes' _ := rfl

@[simp] theorem toFinsuppAlgEquiv_apply (p : ConnesKreimer R T) :
    toFinsuppAlgEquiv p = p.toFinsupp := rfl

@[simp] theorem toFinsuppAlgEquiv_symm_apply (x : AddMonoidAlgebra R (Forest T)) :
    (toFinsuppAlgEquiv (R := R) (T := T)).symm x = ⟨x⟩ := rfl

/-! ## Basis vectors -/

/-- `single F r` is the basis vector with coefficient `r` on the forest `F`. -/
def single (F : Forest T) (r : R) : ConnesKreimer R T :=
  ⟨.single F r⟩

@[simp] theorem toFinsupp_single (F : Forest T) (r : R) :
    (single F r).toFinsupp = .single F r := rfl

@[elab_as_elim]
theorem induction_linear {motive : ConnesKreimer R T → Prop} (x : ConnesKreimer R T)
    (zero : motive 0) (add : ∀ f g, motive f → motive g → motive (f + g))
    (single : ∀ (F : Forest T) (r : R), motive (ConnesKreimer.single F r)) : motive x :=
  AddMonoidAlgebra.induction_linear (motive := fun y => motive (⟨y⟩ : ConnesKreimer R T))
    x.toFinsupp zero (fun f g hf hg => add ⟨f⟩ ⟨g⟩ hf hg) single

/-- `of' F` is the forest `F` as the basis vector `single F 1`. -/
def of' (F : Forest T) : ConnesKreimer R T := single F 1

/-- `ofTree t` is the forest with the single tree `t`. -/
def ofTree (t : T) : ConnesKreimer R T :=
  of' ({t} : Forest T)

theorem toFinsupp_of' (F : Forest T) :
    (of' (R := R) F : ConnesKreimer R T).toFinsupp = .single F 1 := rfl

theorem smul_of' (F : Forest T) (r : R) : r • of' F = single F r := by
  ext; simp [toFinsupp_of']

@[simp] theorem of'_zero :
    (of' (R := R) (0 : Forest T) : ConnesKreimer R T) = 1 :=
  ext (by simp [toFinsupp_of', AddMonoidAlgebra.one_def])

@[simp] theorem of'_add (F G : Forest T) :
    (of' (R := R) (F + G) : ConnesKreimer R T)
      = of' (R := R) F * of' (R := R) G :=
  ext (by simp [toFinsupp_of', AddMonoidAlgebra.single_mul_single])

@[simp] theorem of'_singleton (t : T) :
    (of' (R := R) ({t} : Forest T) : ConnesKreimer R T) = ofTree t := rfl

@[simp] theorem of'_cons (t : T) (F : Forest T) :
    (of' (R := R) (t ::ₘ F) : ConnesKreimer R T) = ofTree t * of' F := by
  rw [← Multiset.singleton_add, of'_add, of'_singleton]

theorem prod_map_ofTree (F : Forest T) : (F.map (ofTree (R := R))).prod = of' F := by
  induction F using Multiset.induction with
  | empty => simp
  | cons t F ih => rw [Multiset.map_cons, Multiset.prod_cons, ih, of'_cons]

/-! ### Coefficients -/

/-- The coefficient of the forest `F`. -/
def coeff (p : ConnesKreimer R T) (F : Forest T) : R := p.toFinsupp.coeff F

theorem coeff_def (p : ConnesKreimer R T) (F : Forest T) :
    p.coeff F = p.toFinsupp.coeff F := rfl

@[simp] theorem coeff_zero (F : Forest T) : (0 : ConnesKreimer R T).coeff F = 0 := by
  simp [coeff_def]

@[simp] theorem coeff_add (p q : ConnesKreimer R T) (F : Forest T) :
    (p + q).coeff F = p.coeff F + q.coeff F := by
  simp [coeff_def]

@[simp] theorem coeff_smul [SMulZeroClass S R] (s : S)
    (p : ConnesKreimer R T) (F : Forest T) :
    (s • p).coeff F = s • p.coeff F := by
  simp [coeff_def]

theorem coeff_single (F G : Forest T) (r : R) [Decidable (F = G)] :
    (single F r).coeff G = if F = G then r else 0 := by
  rw [coeff_def, toFinsupp_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

@[simp] theorem coeff_single_same (F : Forest T) (r : R) :
    (single F r).coeff F = r := by
  rw [coeff_def, toFinsupp_single, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

theorem coeff_of' (F G : Forest T) [Decidable (F = G)] :
    (of' (R := R) F).coeff G = if F = G then 1 else 0 := coeff_single F G 1

theorem ext_coeff (h : ∀ F, p.coeff F = q.coeff F) : p = q :=
  ext (AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext h))

theorem coeff_sum_map_of' [DecidableEq T] (s : Multiset (Forest T)) (F : Forest T) :
    ((s.map (of' (R := R))).sum).coeff F = s.count F := by
  induction s using Multiset.induction with
  | empty => simp
  | cons G s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, coeff_add, ih, coeff_of', Multiset.count_cons]
    split_ifs <;> subst_vars <;> simp_all [add_comm]

theorem sum_map_of'_injective [CharZero R] :
    Function.Injective fun s : Multiset (Forest T) ↦ (s.map (of' (R := R))).sum := by
  classical
  intro s t h
  ext F
  have := congrArg (coeff · F) h
  simp only [coeff_sum_map_of'] at this
  exact_mod_cast this

variable (R) in
/-- `coeff` bundled as a linear functional (`Polynomial.lcoeff` analogue). -/
def lcoeff (F : Forest T) : ConnesKreimer R T →ₗ[R] R where
  toFun p := p.coeff F
  map_add' p q := coeff_add p q F
  map_smul' s p := coeff_smul s p F

@[simp] theorem lcoeff_apply (F : Forest T) (p : ConnesKreimer R T) :
    lcoeff R F p = p.coeff F := rfl

/-! ## The universal property

`ConnesKreimer R T` is the free commutative algebra on `T`, as `MvPolynomial T R` is: a function
on trees extends uniquely to an algebra hom. The carrier is not literally `MvPolynomial T R`,
whose monomials `T →₀ ℕ` match `Multiset T` only under `DecidableEq T`. -/

section Aeval
variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- `aeval f` is the algebra hom sending each tree `t` to `f t`, and so each forest to the
product of the values of its trees (`MvPolynomial.aeval` analogue). -/
def aeval (f : T → A) : ConnesKreimer R T →ₐ[R] A :=
  (AddMonoidAlgebra.lift R A (Forest T)
    { toFun F := (F.toAdd.map f).prod
      map_one' := by simp
      map_mul' F G := by simp [Multiset.prod_add] }).comp toFinsuppAlgEquiv.toAlgHom

@[simp] theorem aeval_of' (f : T → A) (F : Forest T) :
    aeval (R := R) f (of' F) = (F.map f).prod := by
  show AddMonoidAlgebra.lift R A (Forest T) _ (.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem aeval_ofTree (f : T → A) (t : T) : aeval (R := R) f (ofTree t) = f t := by
  simp [← of'_singleton]

theorem algHom_ext {φ ψ : ConnesKreimer R T →ₐ[R] A}
    (h : ∀ F : Forest T, φ (of' F) = ψ (of' F)) : φ = ψ :=
  (AlgHom.cancel_right (f := toFinsuppAlgEquiv.symm.toAlgHom)
    toFinsuppAlgEquiv.symm.surjective).mp
    (AddMonoidAlgebra.algHom_ext (fun F => h F) (Subsingleton.elim _ _))

theorem algHom_of'_eq_of_ofTree {φ ψ : ConnesKreimer R T →ₐ[R] A} {F : Forest T}
    (h : ∀ t ∈ F, φ (ofTree t) = ψ (ofTree t)) : φ (of' F) = ψ (of' F) := by
  simp only [← prod_map_ofTree, map_multiset_prod, Multiset.map_map, Function.comp_def]
  exact congrArg _ (Multiset.map_congr rfl h)

@[ext] theorem algHom_ext_ofTree {φ ψ : ConnesKreimer R T →ₐ[R] A}
    (h : ∀ t : T, φ (ofTree t) = ψ (ofTree t)) : φ = ψ :=
  algHom_ext fun _ ↦ algHom_of'_eq_of_ofTree fun t _ ↦ h t

end Aeval

section Rename
variable {T' : Type*}

/-- `rename f` replaces each tree `t` of every forest by `f t` (`MvPolynomial.rename`
analogue). -/
def rename (f : T → T') : ConnesKreimer R T →ₐ[R] ConnesKreimer R T' :=
  aeval fun t ↦ ofTree (f t)

@[simp] theorem rename_ofTree (f : T → T') (t : T) :
    rename (R := R) f (ofTree t) = ofTree (f t) :=
  aeval_ofTree _ t

@[simp] theorem rename_of' (f : T → T') (F : Forest T) :
    rename (R := R) f (of' F) = of' (F.map f) := by
  rw [rename, aeval_of', ← prod_map_ofTree, Multiset.map_map]
  rfl

end Rename

/-! ## The forest basis and linear maps -/

/-- The forests, via `of'`, as an `R`-basis (`Polynomial.basisMonomials` analogue). -/
def basisSingleOne :
    Module.Basis (Forest T) R (ConnesKreimer R T) :=
  (AddMonoidAlgebra.basis (Forest T) R).map (toFinsuppAlgEquiv (R := R) (T := T)).symm.toLinearEquiv

@[simp] theorem basisSingleOne_apply (F : Forest T) :
    (basisSingleOne : Module.Basis (Forest T) R (ConnesKreimer R T)) F = of' F := by
  simp only [basisSingleOne, Module.Basis.map_apply, AddMonoidAlgebra.basis_apply]
  rfl

section LinearMap
variable {M : Type*} [AddCommMonoid M] [Module R M]

@[ext high] theorem lhom_ext' {f g : ConnesKreimer R T →ₗ[R] M}
    (h : ∀ F : Forest T, f (of' F) = g (of' F)) : f = g :=
  basisSingleOne.ext fun F ↦ by simpa using h F

/-- `linearLift f` is the linear map sending each forest `F` to `f F`. -/
def linearLift (f : Forest T → M) : ConnesKreimer R T →ₗ[R] M :=
  basisSingleOne.constr R f

@[simp] theorem linearLift_of' (f : Forest T → M) (F : Forest T) :
    linearLift f (of' (R := R) F) = f F := by
  simpa [linearLift] using basisSingleOne.constr_basis R f F

@[simp] theorem linearLift_single (f : Forest T → M) (F : Forest T) (r : R) :
    linearLift f (single F r) = r • f F := by
  rw [← smul_of', map_smul, linearLift_of']

end LinearMap

/-! ## The counit -/

/-- The counit takes the coefficient of the empty forest; it is the algebra hom sending every
tree to `0`. -/
def counit : ConnesKreimer R T →ₐ[R] R :=
  aeval fun _ ↦ 0

@[simp] theorem counit_of' (F : Forest T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (of' F)
      = (if F.card = 0 then 1 else 0 : R) := by
  rw [counit, aeval_of', Multiset.map_const', Multiset.prod_replicate]
  exact zero_pow_eq F.card

@[simp] theorem counit_one :
    (counit : ConnesKreimer R T →ₐ[R] R) 1 = 1 := map_one _

@[simp] theorem counit_ofTree (t : T) :
    (counit : ConnesKreimer R T →ₐ[R] R) (ofTree t) = 0 :=
  aeval_ofTree _ t

end ConnesKreimer

end
