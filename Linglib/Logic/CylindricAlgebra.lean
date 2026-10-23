module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Closure

/-!
# Cylindric algebras

This file defines cylindric algebras. A cylindric algebra of dimension `ι` is a Boolean algebra
with a *cylindrification* `cyl i` for each `i : ι` and a *diagonal element* `diag i j` for each
pair of indices. Cylindrification is the algebraic form of existential quantification over the
`i`-th variable and the diagonal is the algebraic form of the equation between the `i`-th and
`j`-th variables, so cylindric algebras stand to first-order logic with equality as Boolean
algebras stand to propositional logic.

Predicates on assignments `ι → E` form a cylindric algebra, where `cyl i p` holds of `g` when `p`
holds of some `i`-variant of `g` and `diag i j` holds of `g` when `g i = g j`. The existential
quantifiers and identity conditions of the assignment-based dynamic systems are these operations.

## Main definitions

* `CylindricAlgebra ι A`: the cylindrifications and diagonal elements on a Boolean algebra `A`.
* `CylindricAlgebra.cylClosure`: cylindrification as a closure operator.
* `CylindricAlgebra.dimSet`: the dimension set of an element, the indices it depends on.
* `CylindricAlgebra.subst`: substitution of the `j`-th variable for the `i`-th.

## Main results

* `CylindricAlgebra.disjoint_cyl_comm`: cylindrification is conjugate to itself.
* `CylindricAlgebra.cyl_sup`: cylindrification distributes over joins.
* `CylindricAlgebra.subst_compl`, `CylindricAlgebra.subst_sup`, `CylindricAlgebra.subst_inf`:
  substitution is a Boolean endomorphism.
* `CylindricAlgebra.diag_comm`: diagonal elements are symmetric.
* `CylindricAlgebra.subst_apply`: on predicates, substitution evaluates the predicate at the
  assignment updated at `i` with the value at `j`.
* `CylindricAlgebra.dimSet_subset_of_dependsOn`: a predicate that depends only on the variables
  in `s` has its dimension set inside `s`.

## Implementation notes

`CylindricAlgebra ι A` is a mixin over `[BooleanAlgebra A]` rather than an extension of it, as
`Module R M` is over `[AddCommMonoid M]`: the dimension `ι` could not be inferred from a parent
projection to `BooleanAlgebra A`.

The concrete algebra is carried both by predicates `(ι → E) → Prop` with the pointwise Boolean
algebra and by `Set (ι → E)`. The set algebra is defined on `Set` directly rather than transported
from the predicate algebra, so that it agrees reducibly with the condition algebra of every
register structure (`DynamicSemantics.RegisterStructure.cylindricAlgebra`) at the canonical one.

## References

* [henkin-monk-tarski-1971]
-/

@[expose] public section

open Function

/-- The cylindrifications `cyl i` and diagonal elements `diag i j` of a cylindric algebra of
dimension `ι` on the Boolean algebra `A`, with the seven axioms of [henkin-monk-tarski-1971]. -/
class CylindricAlgebra (ι : Type*) (A : Type*) [BooleanAlgebra A] where
  /-- Cylindrification along the index `i`. -/
  cyl : ι → A → A
  /-- The diagonal element of the indices `i` and `j`. -/
  diag : ι → ι → A
  cyl_bot (i : ι) : cyl i ⊥ = ⊥
  le_cyl (i : ι) (x : A) : x ≤ cyl i x
  cyl_inf_cyl (i : ι) (x y : A) : cyl i (x ⊓ cyl i y) = cyl i x ⊓ cyl i y
  cyl_comm (i j : ι) (x : A) : cyl i (cyl j x) = cyl j (cyl i x)
  diag_self (i : ι) : diag i i = ⊤
  cyl_diag_inf_diag {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) :
    cyl i (diag j i ⊓ diag i k) = diag j k
  disjoint_cyl_diag_inf {i j : ι} (hij : i ≠ j) (x : A) :
    Disjoint (cyl i (diag i j ⊓ x)) (cyl i (diag i j ⊓ xᶜ))

namespace CylindricAlgebra

variable {ι A : Type*} [BooleanAlgebra A] [CylindricAlgebra ι A] {i j k : ι} {x y : A}

attribute [simp] cyl_bot le_cyl diag_self

/-! ### Cylindrification -/

@[simp]
theorem cyl_top : cyl i (⊤ : A) = ⊤ :=
  top_unique (le_cyl i ⊤)

@[simp]
theorem cyl_cyl : cyl i (cyl i x) = cyl i x := by
  simpa using cyl_inf_cyl i ⊤ x

theorem cyl_mono : Monotone (cyl i : A → A) := fun x y h ↦ by
  have := cyl_inf_cyl i x y
  rw [inf_eq_left.2 (h.trans (le_cyl i y))] at this
  exact inf_eq_left.1 this.symm

@[gcongr]
theorem cyl_le_cyl (h : x ≤ y) : cyl i x ≤ cyl i y :=
  cyl_mono h

/-- Cylindrification along `i` as a closure operator. Its closed elements are the elements that
do not depend on the `i`-th variable. -/
def cylClosure (i : ι) : ClosureOperator A :=
  .mk' (cyl i) cyl_mono (le_cyl i) fun _ ↦ cyl_cyl.le

@[simp]
theorem cylClosure_apply : cylClosure i x = cyl i x :=
  rfl

@[simp]
theorem cyl_eq_bot : cyl i x = ⊥ ↔ x = ⊥ :=
  ⟨fun h ↦ le_bot_iff.1 (h ▸ le_cyl i x), by rintro rfl; exact cyl_bot i⟩

theorem cyl_cyl_inf (i : ι) (x y : A) : cyl i (cyl i x ⊓ y) = cyl i x ⊓ cyl i y := by
  rw [inf_comm, cyl_inf_cyl, inf_comm]

@[simp]
theorem cyl_compl_cyl : cyl i (cyl i x)ᶜ = (cyl i x)ᶜ := by
  refine (le_cyl ..).antisymm' ?_
  rw [le_compl_iff_disjoint_right, disjoint_iff, ← cyl_inf_cyl, compl_inf_eq_bot, cyl_bot]

theorem disjoint_cyl_comm : Disjoint (cyl i x) y ↔ Disjoint x (cyl i y) := by
  have key {x y : A} (h : Disjoint (cyl i x) y) : Disjoint x (cyl i y) := by
    have : cyl i (y ⊓ cyl i x) = ⊥ := by rw [inf_comm, h.eq_bot, cyl_bot]
    rw [cyl_inf_cyl] at this
    exact (disjoint_iff.2 this).symm.mono_left (le_cyl i x)
  exact ⟨key, fun h ↦ (key h.symm).symm⟩

theorem cyl_sup (i : ι) (x y : A) : cyl i (x ⊔ y) = cyl i x ⊔ cyl i y :=
  eq_of_forall_ge_iff fun z ↦ by
    simp only [← disjoint_compl_right_iff, disjoint_cyl_comm, disjoint_sup_left]

/-! ### Dimension sets -/

/-- The dimension set of `x` is the set of indices along which cylindrification moves `x`. For a
formula these are its free variables. -/
def dimSet (x : A) : Set ι :=
  {i | cyl i x ≠ x}

theorem notMem_dimSet : i ∉ dimSet x ↔ cyl i x = x :=
  not_not

theorem notMem_dimSet_cyl : i ∉ dimSet (cyl i x) :=
  notMem_dimSet.2 cyl_cyl

@[simp]
theorem dimSet_compl (x : A) : dimSet xᶜ = (dimSet x : Set ι) := by
  have key {x : A} {i : ι} (h : i ∉ dimSet x) : i ∉ dimSet xᶜ := by
    rw [notMem_dimSet] at h ⊢
    rw [← h, cyl_compl_cyl]
  ext i
  exact not_iff_not.1 ⟨fun h ↦ by simpa using key h, key⟩

theorem dimSet_inf_subset (x y : A) : (dimSet (x ⊓ y) : Set ι) ⊆ dimSet x ∪ dimSet y := by
  intro i
  contrapose!
  simp only [Set.mem_union, not_or, notMem_dimSet]
  rintro ⟨hx, hy⟩
  rw [← hy, cyl_inf_cyl, hx]

theorem dimSet_sup_subset (x y : A) : (dimSet (x ⊔ y) : Set ι) ⊆ dimSet x ∪ dimSet y := by
  intro i
  contrapose!
  simp only [Set.mem_union, not_or, notMem_dimSet]
  rintro ⟨hx, hy⟩
  rw [cyl_sup, hx, hy]

theorem dimSet_cyl_subset (i : ι) (x : A) : dimSet (cyl i x) ⊆ dimSet x \ {i} := by
  intro j hj
  refine ⟨fun h ↦ hj ?_, fun h ↦ hj (h ▸ cyl_cyl)⟩
  rw [cyl_comm, h]

/-! ### Diagonal elements and substitution -/

theorem cyl_diag (h : i ≠ j) : cyl i (diag i j : A) = ⊤ :=
  top_unique <| by
    rw [← diag_self (A := A) j, ← cyl_diag_inf_diag h h]
    exact cyl_mono inf_le_right

theorem dimSet_diag_subset (i j : ι) : dimSet (diag i j : A) ⊆ {i, j} := by
  intro k
  contrapose!
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, notMem_dimSet]
  rintro ⟨hi, hj⟩
  rw [← cyl_diag_inf_diag hi hj, cyl_cyl]

section Subst

variable [DecidableEq ι]

/-- Substitution of the `j`-th variable for the `i`-th constrains the two to agree and then
forgets the `i`-th. Substituting a variable for itself does nothing. -/
def subst (i j : ι) (x : A) : A :=
  if i = j then x else cyl i (diag i j ⊓ x)

@[simp]
theorem subst_self (i : ι) (x : A) : subst i i x = x := by
  simp [subst]

theorem subst_of_ne (h : i ≠ j) (x : A) : subst i j x = cyl i (diag i j ⊓ x) := by
  simp [subst, h]

theorem subst_sup (i j : ι) (x y : A) : subst i j (x ⊔ y) = subst i j x ⊔ subst i j y := by
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp only [subst_of_ne h, inf_sup_left, cyl_sup]

theorem subst_compl (i j : ι) (x : A) : subst i j xᶜ = (subst i j x)ᶜ := by
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp only [subst_of_ne h]
    refine (IsCompl.compl_eq ⟨disjoint_cyl_diag_inf h x, codisjoint_iff.2 ?_⟩).symm
    rw [← cyl_sup, ← inf_sup_left, sup_compl_eq_top, inf_top_eq, cyl_diag h]

theorem subst_inf (i j : ι) (x y : A) : subst i j (x ⊓ y) = subst i j x ⊓ subst i j y := by
  rw [← compl_inj_iff, ← subst_compl, compl_inf, subst_sup, subst_compl, subst_compl, compl_inf]

@[simp]
theorem subst_top (i j : ι) : subst i j (⊤ : A) = ⊤ := by
  obtain rfl | h := eq_or_ne i j
  · simp
  · rw [subst_of_ne h, inf_top_eq, cyl_diag h]

@[simp]
theorem subst_bot (i j : ι) : subst i j (⊥ : A) = ⊥ := by
  rw [← compl_top, subst_compl, subst_top]

theorem subst_eq_self (h : i ∉ dimSet x) (j : ι) : subst i j x = x := by
  obtain rfl | hij := eq_or_ne i j
  · simp
  · rw [notMem_dimSet] at h
    rw [subst_of_ne hij, ← h, cyl_inf_cyl, cyl_diag hij, top_inf_eq]

end Subst

theorem diag_comm (i j : ι) : (diag i j : A) = diag j i := by
  classical
  have key {i j : ι} (h : i ≠ j) : (diag i j : A) ≤ diag j i := by
    have : subst i j (diag j i : A)ᶜ = ⊥ := by
      rw [subst_compl, subst_of_ne h, inf_comm, cyl_diag_inf_diag h h, diag_self, compl_top]
    rw [subst_of_ne h, cyl_eq_bot] at this
    exact disjoint_compl_right_iff.1 (disjoint_iff.2 this)
  obtain rfl | h := eq_or_ne i j
  · rfl
  · exact (key h).antisymm (key h.symm)

/-! ### The cylindric algebra of predicates on assignments -/

section Pi

variable {E : Type*} [DecidableEq ι] {p : (ι → E) → Prop} {g : ι → E}

/-- Predicates on assignments form a cylindric algebra, in which `cyl i p` holds of `g` when `p`
holds of some `i`-variant of `g`, and `diag i j` holds of `g` when `g i = g j`. -/
instance : CylindricAlgebra ι ((ι → E) → Prop) where
  cyl i p g := ∃ e, p (update g i e)
  diag i j g := g i = g j
  cyl_bot i := by ext g; simp
  le_cyl i p g hg := ⟨g i, by rwa [update_eq_self]⟩
  cyl_inf_cyl i p q := by ext g; simp [update_idem]
  cyl_comm i j p := by
    ext g
    obtain rfl | h := eq_or_ne i j
    · rfl
    · simp only [update_comm h]
      exact exists_comm
  diag_self i := by ext g; simp
  cyl_diag_inf_diag {i j k} hij hik := by
    ext g
    simp [update_of_ne hij.symm, update_of_ne hik.symm, eq_comm]
  disjoint_cyl_diag_inf {i j} hij p := by
    rw [disjoint_iff]
    ext g
    simp only [Pi.inf_apply, Pi.compl_apply, update_self, update_of_ne hij.symm, inf_Prop_eq,
      compl_iff_not, Pi.bot_apply, Prop.bot_eq_false, iff_false]
    rintro ⟨⟨e, rfl, hp⟩, e', rfl, hp'⟩
    exact hp' hp

@[simp]
theorem cyl_apply : cyl i p g ↔ ∃ e, p (update g i e) :=
  Iff.rfl

@[simp]
theorem diag_apply : (diag i j : (ι → E) → Prop) g ↔ g i = g j :=
  Iff.rfl

theorem subst_apply : subst i j p g ↔ p (update g i (g j)) := by
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [subst_of_ne h, update_of_ne h.symm]

theorem dimSet_subset_of_dependsOn {s : Set ι} (hp : DependsOn p s) : dimSet p ⊆ s := by
  intro i
  contrapose!
  intro hi
  rw [notMem_dimSet]
  ext g
  have (e : E) : p (update g i e) ↔ p g :=
    (hp fun k hk ↦ update_of_ne (ne_of_mem_of_not_mem hk hi) ..).to_iff
  exact ⟨fun ⟨e, h⟩ ↦ (this e).1 h, fun h ↦ ⟨g i, (this _).2 h⟩⟩

end Pi

/-- Sets of assignments form the cylindric set algebra of [henkin-monk-tarski-1971], the algebra
of predicates under `Set`'s order. -/
instance instSetPi {E : Type*} [DecidableEq ι] : CylindricAlgebra ι (Set (ι → E)) where
  cyl i t := {g | ∃ e, update g i e ∈ t}
  diag i j := {g | g i = g j}
  cyl_bot := cyl_bot (A := (ι → E) → Prop)
  le_cyl := le_cyl (A := (ι → E) → Prop)
  cyl_inf_cyl := cyl_inf_cyl (A := (ι → E) → Prop)
  cyl_comm := cyl_comm (A := (ι → E) → Prop)
  diag_self := diag_self (A := (ι → E) → Prop)
  cyl_diag_inf_diag := cyl_diag_inf_diag (A := (ι → E) → Prop)
  disjoint_cyl_diag_inf := disjoint_cyl_diag_inf (A := (ι → E) → Prop)

@[simp]
theorem mem_cyl {E : Type*} [DecidableEq ι] {t : Set (ι → E)} {g : ι → E} :
    g ∈ cyl i t ↔ ∃ e, update g i e ∈ t :=
  Iff.rfl

@[simp]
theorem mem_diag {E : Type*} [DecidableEq ι] {g : ι → E} :
    g ∈ (diag i j : Set (ι → E)) ↔ g i = g j :=
  Iff.rfl

end CylindricAlgebra
