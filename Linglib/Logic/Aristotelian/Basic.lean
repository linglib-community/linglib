module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Set

/-!
# The Aristotelian relations

Two elements $x$ and $y$ of a bounded order are *contrary* when they are disjoint but not
codisjoint, $x \sqcap y = \bot$ and $x \sqcup y \ne \top$, and *subcontrary* when they are
codisjoint but not disjoint. Together with complementarity (`IsCompl`, *contradiction*) and the
strict order (`<`, *subalternation*) these are the four Aristotelian relations. In the algebra
`Set W` of propositions, contraries cannot both be true and subcontraries cannot both be false.

The two relations are [order dual](##Aristotelian.isContrary_toDual_iff) to each other, and [a
disjoint pair is either contradictory or
contrary](##Aristotelian.disjoint_iff_isCompl_or_isContrary). In a Boolean algebra, [$x$ is
contrary to $y$ if and only if $x < y^c$](##Aristotelian.isContrary_iff_lt_compl) and
[subcontrary to $y$ if and only if $y^c < x$](##Aristotelian.isSubcontrary_iff_compl_lt), so
[complementing both elements exchanges contrariety and
subcontrariety](##Aristotelian.isContrary_compl_compl).

## Implementation notes

Neither relation asks its elements to differ from $\bot$ and $\top$, so [$\bot$ is contrary to
every $x \ne \top$](##Aristotelian.isContrary_bot_left), among them the elements it lies
strictly below. The opposition and implication relations, which are the four cells of
`(Disjoint x y, Codisjoint x y)` and of `(x ≤ y, y ≤ x)`, are not given types of their own.

## References

* [demey-smessaert-2018]
* [demey-smessaert-2024]
* [deklerck-demey-2025]
* [deklerck-vignero-demey-2024]
* [smessaert-demey-2014]
-/

@[expose] public section

open OrderDual

namespace Aristotelian

variable {α β : Type*}

/-! ### Bounded orders -/

section PartialOrder

variable [PartialOrder α] [BoundedOrder α] {x y : α}

/-- `x` and `y` are **contrary** when they cannot both hold but can both fail. -/
@[mk_iff]
structure IsContrary (x y : α) : Prop where
  /-- Contraries cannot both hold. -/
  protected disjoint : Disjoint x y
  /-- Contraries can both fail. -/
  protected not_codisjoint : ¬ Codisjoint x y

/-- `x` and `y` are **subcontrary** when they cannot both fail but can both hold. -/
@[mk_iff, to_dual existing IsContrary]
structure IsSubcontrary (x y : α) : Prop where
  /-- Subcontraries cannot both fail. -/
  protected codisjoint : Codisjoint x y
  /-- Subcontraries can both hold. -/
  protected not_disjoint : ¬ Disjoint x y

attribute [to_dual existing] IsContrary.casesOn
attribute [to_dual existing isSubcontrary_iff] isContrary_iff

@[to_dual (attr := symm)]
protected theorem IsContrary.symm (h : IsContrary x y) : IsContrary y x :=
  ⟨h.1.symm, fun h' ↦ h.2 h'.symm⟩

@[to_dual isSubcontrary_comm]
theorem isContrary_comm : IsContrary x y ↔ IsContrary y x := ⟨.symm, .symm⟩

@[to_dual]
instance IsContrary.instSymm : Std.Symm (IsContrary : α → α → Prop) := ⟨fun _ _ ↦ .symm⟩

@[to_dual]
theorem IsContrary.not_isCompl (h : IsContrary x y) : ¬ IsCompl x y := fun h' ↦ h.2 h'.2

@[to_dual IsSubcontrary.not_isContrary]
theorem IsContrary.not_isSubcontrary (h : IsContrary x y) : ¬ IsSubcontrary x y :=
  fun h' ↦ h.2 h'.1

/-- Two elements that cannot both hold are contradictory or contrary. -/
@[to_dual codisjoint_iff_isCompl_or_isSubcontrary
  /-- Two elements that cannot both fail are contradictory or subcontrary. -/]
theorem disjoint_iff_isCompl_or_isContrary : Disjoint x y ↔ IsCompl x y ∨ IsContrary x y := by
  rw [isContrary_iff, isCompl_iff, ← and_or_left]
  simp only [or_not, and_true]

/-- Subcontrariety is contrariety in the dual order. -/
@[to_dual (attr := simp) isSubcontrary_toDual_iff
  /-- Contrariety is subcontrariety in the dual order. -/]
theorem isContrary_toDual_iff : IsContrary (toDual x) (toDual y) ↔ IsSubcontrary x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

@[to_dual (attr := simp) isSubcontrary_ofDual_iff]
theorem isContrary_ofDual_iff {x y : αᵒᵈ} :
    IsContrary (ofDual x) (ofDual y) ↔ IsSubcontrary x y :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- `⊥` is contrary to everything but `⊤` ([deklerck-vignero-demey-2024], Remark 1). -/
@[to_dual (attr := simp) isSubcontrary_top_left
  /-- `⊤` is subcontrary to everything but `⊥` ([deklerck-vignero-demey-2024], Remark 1). -/]
theorem isContrary_bot_left : IsContrary ⊥ x ↔ x ≠ ⊤ := by
  simp [isContrary_iff]

@[to_dual (attr := simp) isSubcontrary_top_right]
theorem isContrary_bot_right : IsContrary x ⊥ ↔ x ≠ ⊤ := by
  simp [isContrary_iff]

@[to_dual (attr := simp) not_isSubcontrary_bot_left]
theorem not_isContrary_top_left : ¬ IsContrary ⊤ x := fun h ↦ h.2 codisjoint_top_left

@[to_dual (attr := simp) not_isSubcontrary_bot_right]
theorem not_isContrary_top_right : ¬ IsContrary x ⊤ := fun h ↦ h.2 codisjoint_top_right

end PartialOrder

/-! ### Lattices -/

section Lattice

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] {x y : α}

@[to_dual isSubcontrary_iff_sup_inf]
theorem isContrary_iff_inf_sup : IsContrary x y ↔ x ⊓ y = ⊥ ∧ x ⊔ y ≠ ⊤ := by
  rw [isContrary_iff, disjoint_iff, codisjoint_iff]

@[to_dual (attr := simp) isSubcontrary_map_orderIso_iff]
theorem isContrary_map_orderIso_iff (e : α ≃o β) : IsContrary (e x) (e y) ↔ IsContrary x y := by
  simp only [isContrary_iff, disjoint_map_orderIso_iff, codisjoint_map_orderIso_iff]

end Lattice

/-! ### Boolean algebras -/

section BooleanAlgebra

variable [BooleanAlgebra α] {x y : α}

/-- Contrariety to a complement is subalternation ([deklerck-vignero-demey-2024], Lemma 1). -/
@[simp] theorem isContrary_compl_right_iff : IsContrary x yᶜ ↔ x < y := by
  rw [isContrary_iff, lt_iff_le_not_ge, disjoint_compl_right_iff, codisjoint_iff_compl_le_left,
    compl_compl]

@[simp] theorem isContrary_compl_left_iff : IsContrary xᶜ y ↔ y < x := by
  rw [isContrary_comm, isContrary_compl_right_iff]

/-- Subcontrariety to a complement is subalternation in the other direction
([deklerck-vignero-demey-2024], Lemma 1). -/
@[simp] theorem isSubcontrary_compl_right_iff : IsSubcontrary x yᶜ ↔ y < x := by
  rw [isSubcontrary_iff, lt_iff_le_not_ge, disjoint_compl_right_iff,
    codisjoint_iff_compl_le_left, compl_compl]

@[simp] theorem isSubcontrary_compl_left_iff : IsSubcontrary xᶜ y ↔ x < y := by
  rw [isSubcontrary_comm, isSubcontrary_compl_right_iff]

/-- Contrariety is subalternation into the complement ([deklerck-demey-2025], Definition 3). -/
theorem isContrary_iff_lt_compl : IsContrary x y ↔ x < yᶜ := by
  rw [← isContrary_compl_right_iff, compl_compl]

/-- Subcontrariety is subalternation out of the complement ([deklerck-demey-2025],
Definition 3). -/
theorem isSubcontrary_iff_compl_lt : IsSubcontrary x y ↔ yᶜ < x := by
  rw [← isSubcontrary_compl_right_iff, compl_compl]

/-- Negating both members exchanges contrariety and subcontrariety, complementation being an
isomorphism onto the dual order ([deklerck-vignero-demey-2024], Lemma 1). -/
@[simp] theorem isSubcontrary_compl_compl : IsSubcontrary xᶜ yᶜ ↔ IsContrary x y :=
  isContrary_toDual_iff.symm.trans (isContrary_map_orderIso_iff (OrderIso.compl α))

@[simp] theorem isContrary_compl_compl : IsContrary xᶜ yᶜ ↔ IsSubcontrary x y := by
  rw [← isSubcontrary_compl_compl, compl_compl, compl_compl]

end BooleanAlgebra

end Aristotelian
