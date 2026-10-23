module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Basic

/-!
# The Aristotelian relations

Demey and Smessaert define four relations between elements `x`, `y` of a Boolean algebra, the
*Aristotelian relations*:

| Relation       | Definition                    | Here                 |
|----------------|-------------------------------|----------------------|
| contradictory  | `x ⊓ y = ⊥` and `x ⊔ y = ⊤`   | `IsCompl x y`        |
| contrary       | `x ⊓ y = ⊥` and `x ⊔ y ≠ ⊤`   | `IsContrary x y`     |
| subcontrary    | `x ⊓ y ≠ ⊥` and `x ⊔ y = ⊤`   | `IsSubcontrary x y`  |
| subalternation | `x ⊓ y = x` and `x ⊔ y ≠ x`   | `x < y`              |

Contradiction and subalternation are mathlib's `IsCompl` and `<`, so only contrariety and
subcontrariety are defined here. Taking the algebra to be `Set W`, the Lindenbaum–Tarski algebra
of a logic, or `Fin n → Bool` gives the relations between propositions, between formulas, and
between bitstrings.

## Main definitions

* `IsContrary`, `IsSubcontrary`: contrariety and subcontrariety.

## Main results

* `isContrary_iff_lt_compl`, `isSubcontrary_iff_compl_lt`: contrariety is subalternation into
  the complement, and subcontrariety subalternation out of it.
* `disjoint_iff_isCompl_or_isContrary`, `codisjoint_iff_isCompl_or_isSubcontrary`: `Disjoint`
  and `Codisjoint` split into the relations they cover.
* `isContrary_compl_compl`: negating both members exchanges contrariety and subcontrariety.
* `isContrary_map_orderIso_iff`, `isSubcontrary_map_orderIso_iff`: an order isomorphism of
  Boolean algebras preserves and reflects both relations.

## Implementation notes

The definitions follow the Boolean-algebra version of Demey and Smessaert (2024, Definition 1),
which does not ask for contingency. At `⊥` and `⊤` a pair can therefore stand in several
relations at once: `⊥` is both contrary to and a subaltern of every contingent element, while
two contingent elements stand in at most one (De Klerck, Vignero and Demey, Remark 1 and
the paragraph after it).
Smessaert and Demey's opposition and implication relations are the four cells of
`(Disjoint x y, Codisjoint x y)` and of `(x ≤ y, y ≤ x)`. Every pair falls in exactly one cell
of each, so neither gets a type of its own. De Klerck and Demey (2025, Definition 3) give each
opposition relation its order form, contrariety being `x < yᶜ`, and De Klerck, Vignero and
Demey (Lemma 1) list how negating a member moves a pair between the two families.

## References

* [demey-smessaert-2018]
* [demey-smessaert-2024]
* [deklerck-demey-2025]
* [deklerck-vignero-demey-2024]
* [smessaert-demey-2014]
-/

@[expose] public section

namespace Aristotelian

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β] {x y : α}

/-- `x` and `y` are **contrary** when they cannot both hold (`Disjoint`) but can both fail
(`¬ Codisjoint`). -/
def IsContrary (x y : α) : Prop := Disjoint x y ∧ ¬ Codisjoint x y

/-- `x` and `y` are **subcontrary** when they can both hold (`¬ Disjoint`) but cannot both fail
(`Codisjoint`). -/
def IsSubcontrary (x y : α) : Prop := ¬ Disjoint x y ∧ Codisjoint x y

theorem IsContrary.symm (h : IsContrary x y) : IsContrary y x :=
  ⟨h.1.symm, fun h' ↦ h.2 h'.symm⟩

theorem IsSubcontrary.symm (h : IsSubcontrary x y) : IsSubcontrary y x :=
  ⟨fun h' ↦ h.1 h'.symm, h.2.symm⟩

/-- Two elements that cannot both hold are contradictory or contrary. -/
theorem disjoint_iff_isCompl_or_isContrary : Disjoint x y ↔ IsCompl x y ∨ IsContrary x y := by
  rw [IsContrary, isCompl_iff, ← and_or_left]
  simp only [or_not, and_true]

/-- Two elements that cannot both fail are contradictory or subcontrary. -/
theorem codisjoint_iff_isCompl_or_isSubcontrary :
    Codisjoint x y ↔ IsCompl x y ∨ IsSubcontrary x y := by
  rw [IsSubcontrary, isCompl_iff, ← or_and_right]
  simp only [or_not, true_and]

/-- Contrariety is subalternation into the complement. -/
theorem isContrary_iff_lt_compl : IsContrary x y ↔ x < yᶜ := by
  rw [IsContrary, lt_iff_le_not_ge, le_compl_iff_disjoint_right, codisjoint_iff_compl_le_left]

/-- Subcontrariety is subalternation out of the complement. -/
theorem isSubcontrary_iff_compl_lt : IsSubcontrary x y ↔ yᶜ < x := by
  rw [IsSubcontrary, lt_iff_le_not_ge, le_compl_iff_disjoint_right, codisjoint_iff_compl_le_left,
    and_comm]

@[simp] theorem isContrary_compl_compl : IsContrary xᶜ yᶜ ↔ IsSubcontrary x y := by
  rw [isContrary_iff_lt_compl, isSubcontrary_iff_compl_lt, compl_compl, ← compl_lt_compl_iff_lt,
    compl_compl]

@[simp] theorem isSubcontrary_compl_compl : IsSubcontrary xᶜ yᶜ ↔ IsContrary x y := by
  rw [← isContrary_compl_compl, compl_compl, compl_compl]

@[simp] theorem isContrary_map_orderIso_iff (e : α ≃o β) :
    IsContrary (e x) (e y) ↔ IsContrary x y := by
  simp only [IsContrary, disjoint_map_orderIso_iff, codisjoint_map_orderIso_iff]

@[simp] theorem isSubcontrary_map_orderIso_iff (e : α ≃o β) :
    IsSubcontrary (e x) (e y) ↔ IsSubcontrary x y := by
  simp only [IsSubcontrary, disjoint_map_orderIso_iff, codisjoint_map_orderIso_iff]

end Aristotelian
