/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.NonAssoc.PreLie.Brace
public import Linglib.Core.Algebra.RootedTree.Derivation
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.Derivation.Lie
public import Mathlib.Tactic.LinearCombination

/-!
# The Oudom–Guin product on the symmetric algebra of a pre-Lie algebra

Let `L` be a right pre-Lie algebra with a basis `b` indexed by `ι`, so that its symmetric algebra
is `ConnesKreimer R ι`, the free commutative algebra on `ι`. Each `X` in `L` acts on the symmetric
algebra by [multiplication by `X` plus the derivation](##OudomGuin.act_apply) that multiplies one
generator on the right by `X`, and the pre-Lie identity makes this
[a right action](##OudomGuin.isRightLieAction_act) of the commutator Lie algebra of `L`. The
[product](##OudomGuin.product) of Oudom and Guin is the brace of this action:
`x ⋆ (X₁ ⋯ Xₙ)` is the brace of `x` and `{X₁, …, Xₙ}`. It is
[associative](##OudomGuin.product_assoc) with [unit `1`](##OudomGuin.product_one_left), and on
generators it is [the commutative product plus the pre-Lie product](##OudomGuin.product_incl_incl),
so that `L` [maps into its commutator Lie algebra](##OudomGuin.product_incl_incl_sub).

## Implementation notes

The basis is what makes the symmetric algebra a module with a basis of monomials, on which a
linear map is given by its values. Associativity is proved by induction on the degree of the
right factor, from the recursion that defines the brace, and does not use a coproduct.

## References

* [oudom-guin-2008]
-/

@[expose] public section

noncomputable section

namespace OudomGuin

open ConnesKreimer RightPreLieRing UnorderedTree

variable {R ι L : Type*} [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]
  (b : Module.Basis ι R L)

/-- The pre-Lie algebra in its symmetric algebra: a basis vector goes to its generator. -/
def incl : L →ₗ[R] ConnesKreimer R ι := b.constr R ofTree

@[simp] theorem incl_basis (i : ι) : incl b (b i) = ofTree i := b.constr_basis R _ i

/-- The derivation of the symmetric algebra that multiplies one generator on the right by
`X`. -/
def derivation (X : L) : Derivation R (ConnesKreimer R ι) (ConnesKreimer R ι) :=
  mkDerivation fun i ↦ incl b (b i * X)

@[simp] theorem derivation_ofTree (X : L) (i : ι) :
    derivation b X (ofTree i) = incl b (b i * X) :=
  mkDerivation_ofTree _ i

theorem derivation_add (X Y : L) : derivation b (X + Y) = derivation b X + derivation b Y :=
  derivation_ext fun i ↦ by simp [mul_add]

theorem derivation_smul (r : R) (X : L) : derivation b (r • X) = r • derivation b X :=
  derivation_ext fun i ↦ by simp [mul_smul_comm]

@[simp] theorem derivation_incl (X Y : L) : derivation b X (incl b Y) = incl b (Y * X) := by
  have h : (derivation b X : ConnesKreimer R ι →ₗ[R] _) ∘ₗ incl b =
      incl b ∘ₗ LinearMap.mulRight R X := b.ext fun i ↦ by simp
  exact LinearMap.congr_fun h Y

/-- The commutator of the derivations is the derivation of the commutator, in the opposite
order. -/
theorem commutator_derivation (y z : L) :
    ⁅derivation b z, derivation b y⁆ = derivation b (y * z) - derivation b (z * y) :=
  derivation_ext fun i ↦ by
    simp only [Derivation.commutator_apply, Derivation.sub_apply, derivation_ofTree,
      derivation_incl, ← map_sub]
    refine congrArg _ ?_
    rw [sub_eq_sub_iff_add_eq_add, add_comm (b i * (y * z))]
    exact mul_mul_add_mul_mul _ _ _

/-- The action of `X` on the symmetric algebra, as a linear map. -/
def actₗ (X : L) : ConnesKreimer R ι →ₗ[R] ConnesKreimer R ι :=
  LinearMap.mulRight R (incl b X) + (derivation b X : ConnesKreimer R ι →ₗ[R] _)

theorem actₗ_apply (X : L) (x : ConnesKreimer R ι) :
    actₗ b X x = x * incl b X + derivation b X x := rfl

/-- The right action of `L` on its symmetric algebra: multiplication by `X` plus the derivation
of `X`. -/
def act : L →+ ConnesKreimer R ι →+ ConnesKreimer R ι :=
  AddMonoidHom.mk' (fun X ↦ (actₗ b X).toAddMonoidHom) fun X Y ↦ AddMonoidHom.ext fun x ↦ by
    simp only [LinearMap.toAddMonoidHom_coe, actₗ_apply, AddMonoidHom.add_apply, map_add,
      derivation_add, Derivation.add_apply, mul_add]
    abel

@[simp] theorem act_apply (X : L) (x : ConnesKreimer R ι) :
    act b X x = x * incl b X + derivation b X x := rfl

theorem act_smul (r : R) (X : L) (x : ConnesKreimer R ι) : act b (r • X) x = r • act b X x := by
  simp [derivation_smul, smul_add]

/-- The symmetric algebra is a right module over the commutator Lie algebra of `L`. -/
theorem isRightLieAction_act : IsRightLieAction (act b) := fun x y z ↦ by
  have h := congrArg (fun D : Derivation R (ConnesKreimer R ι) (ConnesKreimer R ι) ↦ D x)
    (commutator_derivation b y z)
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at h
  simp only [act_apply, map_add, Derivation.leibniz, derivation_incl, smul_eq_mul]
  linear_combination h

/-- The product of Oudom and Guin on the symmetric algebra: on monomials, the brace of the first
and the generators of the second. -/
def product : ConnesKreimer R ι →ₗ[R] ConnesKreimer R ι →ₗ[R] ConnesKreimer R ι :=
  linearLift fun F ↦ linearLift fun G ↦ braceWith (act b) (of' F) (G.map b)

@[simp] theorem product_of'_of' (F G : Forest ι) :
    product b (of' F) (of' G) = braceWith (act b) (of' F) (G.map b) := by
  simp [product]

@[simp] theorem product_one_right (x : ConnesKreimer R ι) : product b x 1 = x := by
  refine LinearMap.congr_fun (lhom_ext' (f := (product b).flip 1) (g := .id) fun F ↦ ?_) x
  rw [LinearMap.flip_apply, ← of'_zero, product_of'_of', Multiset.map_zero, braceWith_zero]
  rfl

/-- The product with a generator is the action of its basis vector. -/
theorem product_ofTree (x : ConnesKreimer R ι) (i : ι) :
    product b x (ofTree i) = x * ofTree i + derivation b (b i) x := by
  refine (LinearMap.congr_fun (lhom_ext' (f := (product b).flip (ofTree i)) (g := actₗ b (b i))
    fun F ↦ ?_) x).trans (by rw [actₗ_apply, incl_basis])
  rw [LinearMap.flip_apply, ← of'_singleton, product_of'_of', Multiset.map_singleton,
    braceWith_singleton (isRightLieAction_act b), act_apply, actₗ_apply]

private theorem product_incl_mul_of' (F E : Forest ι) (v : L) :
    product b (of' F) (incl b v * of' E) = braceWith (act b) (of' F) (v ::ₘ E.map b) := by
  have hρ := isRightLieAction_act b
  let g : L →ₗ[R] ConnesKreimer R ι :=
    { toFun := fun v ↦ braceWith (act b) (of' F) (v ::ₘ E.map b)
      map_add' := fun u v ↦ braceWith_add_cons hρ _ u v _
      map_smul' := fun r v ↦ braceWith_smul_cons hρ (act_smul b) _ r v _ }
  have h : product b (of' F) ∘ₗ LinearMap.mulRight R (of' E) ∘ₗ incl b = g := b.ext fun i ↦ by
    simp only [LinearMap.comp_apply, incl_basis, LinearMap.mulRight_apply]
    rw [← of'_cons, product_of'_of', Multiset.map_cons]
    rfl
  exact LinearMap.congr_fun h v

private theorem product_derivation_of' (F E : Forest ι) (X : L) :
    product b (of' F) (derivation b X (of' E)) =
      (((E.map b).mulOnce X).map (braceWith (act b) (of' F))).sum := by
  classical
  rw [derivation, mkDerivation_of', map_multiset_sum, Multiset.map_map, Multiset.mulOnce,
    Multiset.map_map, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun t ht ↦ ?_)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [mul_comm, product_incl_mul_of', Multiset.map_erase_of_mem _ _ ht]

private theorem product_of'_cons (F E : Forest ι) (i : ι) :
    product b (of' F) (of' (i ::ₘ E)) =
      act b (b i) (product b (of' F) (of' E)) -
        product b (of' F) (derivation b (b i) (of' E)) := by
  rw [product_derivation_of', product_of'_of', product_of'_of', Multiset.map_cons,
    braceWith_cons (isRightLieAction_act b)]

/-- The recursion of the product in its second argument: `x ⋆ (y Xᵢ) = (x ⋆ y) ⋆ Xᵢ - x ⋆ (y ∘ Xᵢ)`,
where `y ∘ Xᵢ` multiplies one generator of `y` on the right by `Xᵢ`. -/
theorem product_mul_ofTree (x y : ConnesKreimer R ι) (i : ι) :
    product b x (y * ofTree i) =
      product b (product b x y) (ofTree i) - product b x (derivation b (b i) y) := by
  have h : (product b).compl₂ (LinearMap.mulRight R (ofTree i)) =
      (product b).compr₂ (actₗ b (b i)) -
        (product b).compl₂ (derivation b (b i) : ConnesKreimer R ι →ₗ[R] _) :=
    lhom_ext' fun F ↦ lhom_ext' fun E ↦ by
      simp only [LinearMap.compl₂_apply, LinearMap.compr₂_apply, LinearMap.sub_apply,
        LinearMap.mulRight_apply, Derivation.coeFn_coe]
      rw [mul_comm, ← of'_cons, product_of'_cons, act_apply, actₗ_apply]
  have h' := LinearMap.congr_fun₂ h x y
  simp only [LinearMap.compl₂_apply, LinearMap.compr₂_apply, LinearMap.sub_apply,
    LinearMap.mulRight_apply, Derivation.coeFn_coe, actₗ_apply, incl_basis] at h'
  rw [h', product_ofTree]

/-- Multiplying on the right by a generator is associative. -/
theorem product_product_ofTree (x y : ConnesKreimer R ι) (i : ι) :
    product b x (product b y (ofTree i)) = product b (product b x y) (ofTree i) := by
  rw [product_ofTree b y, map_add, product_mul_ofTree]
  abel

/-- Linear maps that agree on the monomials of degree `n` agree on the derivation of a monomial
of degree `n`. -/
theorem eqOn_derivation_of' {M : Type*} [AddCommGroup M] [Module R M]
    {f g : ConnesKreimer R ι →ₗ[R] M} {n : ℕ}
    (h : ∀ E : Forest ι, Multiset.card E = n → f (of' E) = g (of' E)) (X : L) (E : Forest ι)
    (hE : Multiset.card E = n) :
    f (derivation b X (of' E)) = g (derivation b X (of' E)) := by
  classical
  rw [derivation, mkDerivation_of', map_multiset_sum, map_multiset_sum, Multiset.map_map,
    Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun t ht ↦ ?_)
  have hfg : f ∘ₗ LinearMap.mulLeft R (of' (E.erase t)) ∘ₗ incl b =
      g ∘ₗ LinearMap.mulLeft R (of' (E.erase t)) ∘ₗ incl b := b.ext fun j ↦ by
    simp only [LinearMap.comp_apply, incl_basis, LinearMap.mulLeft_apply]
    rw [mul_comm, ← of'_cons]
    refine h _ ?_
    rw [Multiset.card_cons, Multiset.card_erase_of_mem ht, ← hE]
    exact Nat.succ_pred_eq_of_pos (Multiset.card_pos_iff_exists_mem.mpr ⟨t, ht⟩)
  simpa [smul_eq_mul] using LinearMap.congr_fun hfg (b t * X)

/-- The product of Oudom and Guin is associative. -/
theorem product_assoc (x y z : ConnesKreimer R ι) :
    product b (product b x y) z = product b x (product b y z) := by
  suffices h : ∀ n (E : Forest ι), Multiset.card E = n →
      product b (product b x y) (of' E) = (product b x ∘ₗ product b y) (of' E) from
    LinearMap.congr_fun (lhom_ext' (f := product b (product b x y))
      (g := product b x ∘ₗ product b y) fun E ↦ h _ E rfl) z
  intro n
  induction n with
  | zero =>
    intro E hE
    obtain rfl := Multiset.card_eq_zero.mp hE
    simp
  | succ n ih =>
    intro E hE
    obtain ⟨i, hi⟩ := (Multiset.card_pos_iff_exists_mem (s := E)).mp (by omega)
    obtain ⟨E, rfl⟩ := Multiset.exists_cons_of_mem hi
    have hE' : Multiset.card E = n := by simpa using hE
    have hD := eqOn_derivation_of' b ih (b i) E hE'
    rw [LinearMap.comp_apply] at hD ⊢
    rw [of'_cons, mul_comm, product_mul_ofTree, product_mul_ofTree b y, map_sub,
      product_product_ofTree, ih E hE', hD]
    rfl

@[simp] theorem product_one_left (y : ConnesKreimer R ι) : product b 1 y = y := by
  suffices h : ∀ n (E : Forest ι), Multiset.card E = n →
      product b 1 (of' E) = (LinearMap.id : ConnesKreimer R ι →ₗ[R] _) (of' E) from
    LinearMap.congr_fun (lhom_ext' (f := product b 1) (g := .id) fun E ↦ h _ E rfl) y
  intro n
  induction n with
  | zero =>
    intro E hE
    obtain rfl := Multiset.card_eq_zero.mp hE
    simp
  | succ n ih =>
    intro E hE
    obtain ⟨i, hi⟩ := (Multiset.card_pos_iff_exists_mem (s := E)).mp (by omega)
    obtain ⟨E, rfl⟩ := Multiset.exists_cons_of_mem hi
    have hE' : Multiset.card E = n := by simpa using hE
    have hD := eqOn_derivation_of' b ih (b i) E hE'
    rw [LinearMap.id_apply] at hD ⊢
    rw [of'_cons, mul_comm, product_mul_ofTree, ih E hE', hD, LinearMap.id_apply,
      product_ofTree]
    abel

/-- The product with an element of `L` is its action. -/
theorem product_incl (x : ConnesKreimer R ι) (Y : L) :
    product b x (incl b Y) = x * incl b Y + derivation b Y x := by
  let g : L →ₗ[R] ConnesKreimer R ι :=
    { toFun := fun Y ↦ x * incl b Y + derivation b Y x
      map_add' := fun Y Z ↦ by simp only [map_add, derivation_add, Derivation.add_apply, mul_add]
                               abel
      map_smul' := fun r Y ↦ by simp [derivation_smul, smul_add] }
  have h : product b x ∘ₗ incl b = g := b.ext fun i ↦ by simp [g, product_ofTree]
  exact LinearMap.congr_fun h Y

/-- On `L` the product is the commutative product plus the pre-Lie product. -/
theorem product_incl_incl (X Y : L) :
    product b (incl b X) (incl b Y) = incl b X * incl b Y + incl b (X * Y) := by
  rw [product_incl, derivation_incl]

/-- The commutator of the product on `L` is the commutator of the pre-Lie product. -/
theorem product_incl_incl_sub (X Y : L) :
    product b (incl b X) (incl b Y) - product b (incl b Y) (incl b X) =
      incl b (X * Y - Y * X) := by
  rw [product_incl_incl, product_incl_incl, mul_comm (incl b Y), map_sub]
  abel

end OudomGuin
