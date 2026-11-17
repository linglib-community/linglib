/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.Brace
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

This is [the free pre-Lie algebra](##ChapotonLivernet.lift) on `α`, as Chapoton and Livernet
show. The one-vertex trees [generate it](##ChapotonLivernet.adjoin_range_of_leaf), which gives
uniqueness. For existence, a tree is sent to
[the brace of its root's value and its children's values](##ChapotonLivernet.liftTree_node);
the recursion that defines the brace is the rule for
[grafting onto a tree](##ChapotonLivernet.sum_map_liftTree_insertSum).

## Implementation notes

The host comes first, as in Chapoton and Livernet and in Foissy: `of T * of S` grafts `S` onto
`T`, and the associator is symmetric in its last two arguments. The convention that grafts the
first factor onto the second gives a left pre-Lie algebra, `(ChapotonLivernet R α)ᵐᵒᵖ`.

The carrier is a structure over its coefficients `coeff : UnorderedTree α →₀ R`, as for
`MonoidAlgebra`. Its operations are defined on `coeff` and the instances pulled back along it, so
that the `ℕ`- and `ℤ`-actions agree with the module structure by reducible unfolding.

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

/-! ### The universal property -/

section Lift

open RightPreLieRing

variable {A : Type*} [RightPreLieRing A] [RightPreLieAlgebra R A]

/-- The value on a tree of the homomorphism that extends `f`: the brace of the root's value
and the values of its children. -/
def liftTree (f : α → A) : UnorderedTree α → A :=
  fold fun a ks ↦ brace (f a) ks

@[simp] theorem liftTree_node (f : α → A) (a : α) (F : Multiset (UnorderedTree α)) :
    liftTree f (node a F) = brace (f a) (F.map (liftTree f)) :=
  fold_node _ a F

@[simp] theorem liftTree_leaf (f : α → A) (a : α) : liftTree f (leaf a) = f a := by
  rw [← node_zero, liftTree_node, Multiset.map_zero, brace_zero]

/-- Summing over the graftings of `S` into a forest is summing over the ways to multiply one
value by the value of `S`, for a map `φ` on trees that is multiplicative on the forest. -/
theorem sum_map_insertionMultiset_singleton {φ : UnorderedTree α → A} {g : Multiset A → A}
    (hg : ∀ s M : Multiset A, g (s.sum ::ₘ M) = (s.map fun u ↦ g (u ::ₘ M)).sum)
    (F : Multiset (UnorderedTree α)) (S : UnorderedTree α)
    (hF : ∀ T ∈ F, ((T ◁ S).map φ).sum = φ T * φ S) :
    ((insertionMultiset F {S}).map fun G ↦ g (G.map φ)).sum =
      (((F.map φ).mulOnce (φ S)).map g).sum := by
  induction F using Multiset.induction_on generalizing g with
  | empty => simp [insertionMultiset_zero_left_of_ne_zero]
  | cons T F ih =>
    have hg' : ∀ s M : Multiset A,
        g (φ T ::ₘ s.sum ::ₘ M) = (s.map fun u ↦ g (φ T ::ₘ u ::ₘ M)).sum := fun s M ↦ by
      simp only [Multiset.cons_swap (φ T)]
      exact hg s _
    rw [insertionMultiset_cons_singleton, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map, Multiset.map_cons, Multiset.mulOnce_cons, Multiset.map_cons,
      Multiset.sum_cons, Multiset.map_map, ← hF T (Multiset.mem_cons_self T F), hg,
      Multiset.map_map]
    simp only [Function.comp_def, Multiset.map_cons]
    rw [ih (g := fun M ↦ g (φ T ::ₘ M)) hg' fun T' hT' ↦ hF T' (Multiset.mem_cons_of_mem hT')]

/-- The tree map is multiplicative: the values of the graftings of `S` onto `T` sum to the
product of the values. -/
theorem sum_map_liftTree_insertSum (f : α → A) (T S : UnorderedTree α) :
    ((T ◁ S).map (liftTree f)).sum = liftTree f T * liftTree f S := by
  induction T with
  | node a F ih =>
    rw [insertSum_node, Multiset.map_cons, Multiset.sum_cons, Multiset.map_map, liftTree_node,
      liftTree_node, Multiset.map_cons, brace_cons,
      ← sum_map_insertionMultiset_singleton (brace_sum_cons (f a)) F S ih]
    simp only [Function.comp_def, liftTree_node]
    abel

variable (R) in
/-- The homomorphism that extends `f : α → A` from the one-vertex trees. -/
def liftHom (f : α → A) : ChapotonLivernet R α →ₙₐ[R] A where
  toFun := (basis R α).constr R (liftTree f)
  map_smul' r x := map_smul _ r x
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    have hof (T : UnorderedTree α) :
        (basis R α).constr R (liftTree f) (of T) = liftTree f T :=
      (basis R α).constr_basis R (liftTree f) T
    induction x using induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
    | single T a =>
    induction y using induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
    | single S b =>
      rw [single_eq_smul_of T a, single_eq_smul_of S b, smul_mul_smul_comm, map_smul, map_smul,
        map_smul, smul_mul_smul_comm, of_mul_of, map_multiset_sum, Multiset.map_map, hof, hof,
        ← sum_map_liftTree_insertSum]
      simp only [Function.comp_def, hof]

@[simp] theorem liftHom_of (f : α → A) (T : UnorderedTree α) :
    liftHom R f (of T) = liftTree f T :=
  (basis R α).constr_basis R (liftTree f) T

variable (R) in
/-- The rooted trees labelled by `α` are the free right pre-Lie algebra on `α`: a function from
`α` to a right pre-Lie algebra extends uniquely to a homomorphism. -/
def lift : (α → A) ≃ (ChapotonLivernet R α →ₙₐ[R] A) where
  toFun := liftHom R
  invFun F a := F (of (leaf a))
  left_inv f := funext fun a ↦ (liftHom_of f _).trans (liftTree_leaf f a)
  right_inv _ := hom_ext fun a ↦ (liftHom_of _ _).trans (liftTree_leaf _ a)

@[simp] theorem lift_symm_apply (F : ChapotonLivernet R α →ₙₐ[R] A) (a : α) :
    (lift R).symm F a = F (of (leaf a)) := rfl

@[simp] theorem lift_of_leaf (f : α → A) (a : α) : lift R f (of (leaf a)) = f a :=
  (liftHom_of f _).trans (liftTree_leaf f a)

theorem lift_of (f : α → A) (T : UnorderedTree α) : lift R f (of T) = liftTree f T :=
  liftHom_of f T

end Lift

end CommRing

end ChapotonLivernet
