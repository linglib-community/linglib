/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.InsertSum
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.NonAssoc.LieAdmissible.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Tactic.Abel

/-!
# The pre-Lie algebra of rooted trees

`ChapotonLivernet R α` is the free `R`-module on the nonplanar rooted trees labelled by `α`, with
the grafting product: `of T * of S` [sums the trees](##ChapotonLivernet.of_mul_of) obtained by
grafting `S` onto one vertex of `T`. Grafting `S` and then `U` differs from grafting `S * U` by
[the trees that carry `S` and `U` on vertices of `T`](##ChapotonLivernet.of_mul_of_mul_of), an
expression symmetric in `S` and `U`. This is the
[right pre-Lie identity](##ChapotonLivernet.mul_mul_add_mul_mul), so over a commutative ring the
product is right pre-Lie and its commutator a Lie bracket.

Chapoton and Livernet show that this is the free pre-Lie algebra on `α`. Of freeness this file
proves uniqueness: the one-vertex trees
[generate the algebra](##ChapotonLivernet.adjoin_range_of_leaf), so a homomorphism
[is determined by its values on them](##ChapotonLivernet.hom_ext).

## Implementation notes

The host comes first, as in Chapoton and Livernet and in Foissy: `of T * of S` grafts `S` onto
`T`, and the associator is symmetric in its last two arguments. The convention that grafts the
first factor onto the second gives a left pre-Lie algebra, `(ChapotonLivernet R α)ᵐᵒᵖ`.

The carrier is a structure over its coefficients `coeff : UnorderedTree α →₀ R`, as for
`MonoidAlgebra`. Its operations are defined on `coeff` and the instances pulled back along it, so
that the `ℕ`- and `ℤ`-actions agree with the module structure by reducible unfolding.

## TODO

* Existence for the universal property: every `f : α → A` into a right pre-Lie algebra extends
  to a homomorphism `ChapotonLivernet R α →ₙₐ[R] A`, which with `hom_ext` gives
  `lift : (α → A) ≃ (ChapotonLivernet R α →ₙₐ[R] A)`.

## References

* [chapoton-livernet-2001]
* [foissy-2021]
-/

@[expose] public section

noncomputable section

/-- The free module on the nonplanar rooted trees labelled by `α`, which the grafting product
makes a pre-Lie algebra. -/
structure ChapotonLivernet (R : Type*) [Semiring R] (α : Type*) where
  /-- The element with the given coefficients. -/
  ofCoeff ::
  /-- The coefficient of each tree. -/
  coeff : UnorderedTree α →₀ R

namespace ChapotonLivernet

open UnorderedTree

variable {R S α : Type*}

section Semiring

variable [Semiring R] {x y : ChapotonLivernet R α}

/-- `coeff` as an equivalence with the finitely supported functions on trees. -/
def coeffEquiv : ChapotonLivernet R α ≃ (UnorderedTree α →₀ R) where
  toFun := coeff
  invFun := ofCoeff
  left_inv _ := rfl
  right_inv _ := rfl

theorem coeff_injective : Function.Injective (coeff : ChapotonLivernet R α → _) :=
  coeffEquiv.injective

@[simp] theorem coeff_inj : x.coeff = y.coeff ↔ x = y := coeff_injective.eq_iff

@[ext] theorem ext (h : x.coeff = y.coeff) : x = y := coeff_injective h

instance instZero : Zero (ChapotonLivernet R α) := ⟨⟨0⟩⟩

instance instAdd : Add (ChapotonLivernet R α) := ⟨fun x y ↦ ⟨x.coeff + y.coeff⟩⟩

instance instSMul [SMul S (UnorderedTree α →₀ R)] : SMul S (ChapotonLivernet R α) :=
  ⟨fun s x ↦ ⟨s • x.coeff⟩⟩

@[simp] theorem coeff_zero : (0 : ChapotonLivernet R α).coeff = 0 := rfl

@[simp] theorem coeff_add (x y : ChapotonLivernet R α) : (x + y).coeff = x.coeff + y.coeff := rfl

@[simp] theorem coeff_smul [SMul S (UnorderedTree α →₀ R)] (s : S) (x : ChapotonLivernet R α) :
    (s • x).coeff = s • x.coeff := rfl

instance instAddCommMonoid : AddCommMonoid (ChapotonLivernet R α) :=
  fast_instance% coeff_injective.addCommMonoid _ rfl coeff_add fun _ _ ↦ rfl

/-- `coeff` as an additive equivalence. -/
def coeffAddEquiv : ChapotonLivernet R α ≃+ (UnorderedTree α →₀ R) where
  __ := coeffEquiv
  map_add' _ _ := rfl

instance instModule : Module R (ChapotonLivernet R α) :=
  fast_instance% coeff_injective.module R coeffAddEquiv.toAddMonoidHom fun _ _ ↦ rfl

/-- `coeff` as a linear equivalence. -/
def coeffLinearEquiv : ChapotonLivernet R α ≃ₗ[R] (UnorderedTree α →₀ R) where
  __ := coeffAddEquiv
  map_smul' _ _ := rfl

@[simp] theorem coeffLinearEquiv_apply (x : ChapotonLivernet R α) :
    coeffLinearEquiv x = x.coeff := rfl

@[simp] theorem coeffLinearEquiv_symm_apply (f : UnorderedTree α →₀ R) :
    coeffLinearEquiv.symm f = ofCoeff f := rfl

/-! ### The basis of trees -/

/-- `single T r` is `r` times the tree `T`. -/
def single (T : UnorderedTree α) (r : R) : ChapotonLivernet R α :=
  ofCoeff (Finsupp.single T r)

@[simp] theorem coeff_single (T : UnorderedTree α) (r : R) :
    (single T r).coeff = Finsupp.single T r := rfl

/-- `of T` is the basis vector of the tree `T`. -/
abbrev of (T : UnorderedTree α) : ChapotonLivernet R α := single T 1

theorem single_eq_smul_of (T : UnorderedTree α) (r : R) :
    (single T r : ChapotonLivernet R α) = r • of T := by
  ext; simp

@[elab_as_elim]
theorem induction_linear {motive : ChapotonLivernet R α → Prop} (x : ChapotonLivernet R α)
    (zero : motive 0) (add : ∀ x y, motive x → motive y → motive (x + y))
    (single : ∀ T r, motive (single T r)) : motive x :=
  Finsupp.induction_linear (motive := fun f ↦ motive (ofCoeff f)) x.coeff zero
    (fun _ _ ↦ add _ _) single

variable (R α) in
/-- The trees are a basis. -/
def basis : Module.Basis (UnorderedTree α) R (ChapotonLivernet R α) := .ofRepr coeffLinearEquiv

@[simp] theorem basis_apply (T : UnorderedTree α) : basis R α T = of T := rfl

/-- Linear maps that agree on the trees are equal. -/
theorem lhom_ext {M : Type*} [AddCommMonoid M] [Module R M] {f g : ChapotonLivernet R α →ₗ[R] M}
    (h : ∀ T, f (of T) = g (of T)) : f = g :=
  (basis R α).ext h

/-! ### The grafting product -/

/-- `graft T S` sums the basis vectors of the trees in `T ◁ S`. -/
def graft (T S : UnorderedTree α) : ChapotonLivernet R α := ((T ◁ S).map of).sum

/-- The grafting product extends `graft` bilinearly. -/
instance instMul : Mul (ChapotonLivernet R α) where
  mul x y := x.coeff.sum fun T a ↦ y.coeff.sum fun S b ↦ (a * b) • graft T S

theorem mul_def (x y : ChapotonLivernet R α) :
    x * y = x.coeff.sum fun T a ↦ y.coeff.sum fun S b ↦ (a * b) • graft T S := rfl

instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (ChapotonLivernet R α) where
  zero_mul := by simp [mul_def]
  mul_zero := by simp [mul_def]
  left_distrib := by
    classical simp [mul_def, mul_add, add_smul, Finsupp.sum_add, Finsupp.sum_add_index]
  right_distrib := by
    classical simp [mul_def, add_mul, add_smul, Finsupp.sum_add, Finsupp.sum_add_index]

theorem single_mul_single (T S : UnorderedTree α) (a b : R) :
    single T a * single S b = (a * b) • graft T S := by
  simp [mul_def]

theorem of_mul_of (T S : UnorderedTree α) :
    (of T : ChapotonLivernet R α) * of S = ((T ◁ S).map of).sum := by
  rw [single_mul_single, mul_one, one_smul, graft]

theorem of_leaf_mul_of_leaf (a b : α) :
    (of (leaf a) : ChapotonLivernet R α) * of (leaf b) = of (node a {leaf b}) := by
  rw [of_mul_of, ← node_zero, insertSum_node, insertionMultiset_zero_left_of_ne_zero _ (by simp),
    Multiset.map_zero, Multiset.cons_zero, Multiset.map_singleton, Multiset.sum_singleton]
  rfl

instance instIsScalarTower : IsScalarTower R (ChapotonLivernet R α) (ChapotonLivernet R α) where
  smul_assoc r x y := by
    classical simp [mul_def, Finsupp.sum_smul_index, Finsupp.smul_sum, mul_smul]

/-- Grafting `S` and then `U` onto `T` is grafting `S * U`, plus the trees that carry `S` and `U`
on vertices of `T`. -/
theorem of_mul_of_mul_of (T S U : UnorderedTree α) :
    (of T : ChapotonLivernet R α) * of S * of U =
      of T * (of S * of U) + ((insertion T {S, U}).map of).sum := by
  rw [of_mul_of, of_mul_of S, ← Multiset.sum_map_mul_right, ← Multiset.sum_map_mul_left]
  simp only [of_mul_of]
  rw [← Multiset.sum_bind, ← Multiset.sum_bind, ← Multiset.sum_add, ← Multiset.map_bind,
    ← Multiset.map_bind, ← Multiset.map_add, insertSum_bind_insertSum]

end Semiring

section CommSemiring

variable [CommSemiring R]

instance instSMulCommClass : SMulCommClass R (ChapotonLivernet R α) (ChapotonLivernet R α) where
  smul_comm r x y := by
    classical
    simp [mul_def, Finsupp.sum_smul_index, Finsupp.smul_sum, mul_smul]
    exact Finsupp.sum_congr fun _ _ ↦ Finsupp.sum_congr fun _ _ ↦ smul_comm _ _ _

/-- The right pre-Lie identity, stated without subtraction. -/
theorem mul_mul_add_mul_mul (x y z : ChapotonLivernet R α) :
    x * y * z + x * (z * y) = x * z * y + x * (y * z) := by
  induction x using induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [add_mul]; rw [add_add_add_comm, h₁, h₂, add_add_add_comm]
  | single T a =>
  induction y using induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    simp only [add_mul, mul_add]; rw [add_add_add_comm, h₁, h₂, add_add_add_comm]
  | single S b =>
  induction z using induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
    simp only [add_mul, mul_add]; rw [add_add_add_comm, h₁, h₂, add_add_add_comm]
  | single U c =>
    rw [single_eq_smul_of T a, single_eq_smul_of S b, single_eq_smul_of U c]
    simp only [smul_mul_smul_comm]
    rw [mul_right_comm a c b, mul_comm c b, ← mul_assoc a b c, ← smul_add, ← smul_add,
      of_mul_of_mul_of, of_mul_of_mul_of T U S, Multiset.pair_comm U S]
    abel_nf

end CommSemiring

section CommRing

variable [CommRing R]

instance instNeg : Neg (ChapotonLivernet R α) := ⟨fun x ↦ ⟨-x.coeff⟩⟩

instance instSub : Sub (ChapotonLivernet R α) := ⟨fun x y ↦ ⟨x.coeff - y.coeff⟩⟩

@[simp] theorem coeff_neg (x : ChapotonLivernet R α) : (-x).coeff = -x.coeff := rfl

@[simp] theorem coeff_sub (x y : ChapotonLivernet R α) : (x - y).coeff = x.coeff - y.coeff := rfl

instance instAddCommGroup : AddCommGroup (ChapotonLivernet R α) :=
  fast_instance% coeff_injective.addCommGroup _ rfl coeff_add coeff_neg coeff_sub
    (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (ChapotonLivernet R α) where

/-- The associator of three trees sums the trees that carry the second and the third on vertices
of the first. -/
theorem associator_of (T S U : UnorderedTree α) :
    associator (of T : ChapotonLivernet R α) (of S) (of U) = ((insertion T {S, U}).map of).sum := by
  rw [associator_apply, of_mul_of_mul_of, add_sub_cancel_left]

instance instRightPreLieRing : RightPreLieRing (ChapotonLivernet R α) where
  assoc_symm' x y z := by
    rw [associator_apply, associator_apply, sub_eq_sub_iff_add_eq_add]
    exact mul_mul_add_mul_mul x y z

instance instRightPreLieAlgebra : RightPreLieAlgebra R (ChapotonLivernet R α) where

/-! ### Generation by the one-vertex trees -/

/-- A tree whose root has the child `S` is the rest of the tree times `S`, less the trees in
which `S` is grafted below the root. -/
theorem of_node_cons (a : α) (S : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    (of (node a (S ::ₘ F)) : ChapotonLivernet R α) =
      of (node a F) * of S - ((insertionMultiset F {S}).map fun G ↦ of (node a G)).sum := by
  rw [eq_sub_iff_add_eq, of_mul_of, insertSum_node, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_map]
  rfl

theorem of_mem_adjoin (T : UnorderedTree α) :
    of T ∈ NonUnitalAlgebra.adjoin R (Set.range fun a ↦ (of (leaf a) : ChapotonLivernet R α)) := by
  suffices h : ∀ n k (T : UnorderedTree α), T.numNodes = n → Multiset.card T.children = k →
      of T ∈ NonUnitalAlgebra.adjoin R (Set.range fun a ↦ (of (leaf a) : ChapotonLivernet R α))
    from h _ _ T rfl rfl
  intro n
  induction n using Nat.strong_induction_on with | _ n ihn =>
  intro k
  induction k using Nat.strong_induction_on with | _ k ihk =>
  intro T hn hk
  obtain ⟨a, F, rfl⟩ : ∃ a F, T = node a F := ⟨_, _, (node_eta T).symm⟩
  obtain rfl | ⟨S, hS⟩ := F.empty_or_exists_mem
  · exact NonUnitalAlgebra.subset_adjoin R ⟨a, rfl⟩
  obtain ⟨F, rfl⟩ := Multiset.exists_cons_of_mem hS
  subst hn hk
  have hS := S.numNodes_pos
  simp only [numNodes_node, children_node, Multiset.map_cons, Multiset.sum_cons,
    Multiset.card_cons] at ihn ihk
  rw [of_node_cons]
  refine sub_mem (mul_mem (ihn _ ?_ _ _ rfl rfl) (ihn _ ?_ _ _ rfl rfl))
    (multiset_sum_mem _ fun x hx ↦ ?_)
  · rw [numNodes_node]; omega
  · omega
  · obtain ⟨G, hG, rfl⟩ := Multiset.mem_map.mp hx
    refine ihk _ ?_ _ ?_ rfl
    · rw [children_node, insertionMultiset_card_eq _ _ hG]; omega
    · rw [numNodes_of_mem_insertSum (T := node a F) (S := S)
        (by rw [insertSum_node]; exact Multiset.mem_cons_of_mem (Multiset.mem_map_of_mem _ hG)),
        numNodes_node]
      omega

/-- The one-vertex trees generate the algebra. -/
theorem adjoin_range_of_leaf :
    NonUnitalAlgebra.adjoin R (Set.range fun a ↦ (of (leaf a) : ChapotonLivernet R α)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro x -
  induction x using induction_linear with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | single T r => rw [single_eq_smul_of]; exact SMulMemClass.smul_mem r (of_mem_adjoin T)

/-- Homomorphisms that agree on the one-vertex trees are equal. -/
@[ext]
theorem hom_ext {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
    {f g : ChapotonLivernet R α →ₙₐ[R] A} (h : ∀ a, f (of (leaf a)) = g (of (leaf a))) : f = g := by
  have hle : NonUnitalAlgebra.adjoin R
      (Set.range fun a ↦ (of (leaf a) : ChapotonLivernet R α)) ≤ NonUnitalAlgHom.equalizer f g :=
    NonUnitalAlgebra.adjoin_le (Set.range_subset_iff.mpr h)
  rw [adjoin_range_of_leaf] at hle
  exact NonUnitalAlgHom.ext fun x ↦ hle trivial

end CommRing

end ChapotonLivernet
