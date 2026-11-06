module

public import Linglib.Logic.Bilattice.Guard
public import Linglib.Logic.Trivalent.Knowledge
public import Mathlib.Data.Fintype.Order

/-!
# Belnap's four values

Belnap's four values are the diagonal product `Bool ⊙ Bool`: a value records whether a
proposition has been told true and whether it has been told false. Arieli and Avron develop their
logic as a bilattice, and `FOUR` is the literature's name for it. The consistent values, those
without a glut, are Kleene's three: `Trivalent.orderIsoConsistent` identifies `Trivalent` with them,
carrying Kleene's negation, conjunction and disjunction to `FOUR`'s negation and truth meet and
join, and his knowledge order to `FOUR`'s. Composed with conflation, which exchanges the gap `U`
and the glut `I`, the same values are the anticonsistent part, where the third value reads as
LP's glut. In `FOUR`'s knowledge lattice the two conditional assertions are the supremum and the
infimum over their antecedent's designation: de Finetti's falls back to the gap, Cooper's to the
glut.

## Main definitions

* `Bilattice.FOUR`: `Bool ⊙ Bool`, with the values `U` (neither), `T`, `F` and `I` (both).
* `Trivalent.toFour`: Kleene's values inside `FOUR`.

## Main results

* `Bilattice.FOUR.isConsistent_iff`, `Bilattice.FOUR.isExact_iff`: the consistent values are those
  other than `I`, and the exact values are `F` and `T`.
* `Trivalent.orderIsoConsistent`: `Trivalent` is the consistent part of `FOUR`.
* `Trivalent.toFour_compl`, `Trivalent.toFour_inf`, `Trivalent.toFour_sup`,
  `Trivalent.toFour_kLE_toFour`: the identification respects the connectives and both orders.
* `Trivalent.toFour_transplication`: Blamey's transplication is Fitting's guard on Kleene's
  values.
* `Trivalent.range_conf_toFour`: under conflation Kleene's values are the anticonsistent part.
* `Trivalent.toKnow_toFour_condAssert_k3`, `Trivalent.toKnow_conf_toFour_condAssert_lp`: de
  Finetti's conditional is a supremum and Cooper's an infimum over the antecedent's designation.

## References

* [belnap-1977]
* [arieli-avron-1996]
* [fitting-1994]
* [blamey-1986]
-/

@[expose] public section

namespace Bilattice

open Product

/-- Belnap's four-valued bilattice `FOUR = Bool ⊙ Bool` records whether a proposition has been told
true and whether it has been told false ([belnap-1977]). -/
abbrev FOUR := Bool ⊙ Bool

namespace FOUR

/-- The gap `⊥`, told neither true nor false. -/
def U : FOUR := mk false false
/-- `true`. -/
def T : FOUR := mk true false
/-- `false`. -/
def F : FOUR := mk false true
/-- The glut `⊤`, told both true and false. -/
def I : FOUR := mk true true

/-- The consistent values of `FOUR` are those other than the glut `I`. -/
@[simp] theorem isConsistent_iff (x : FOUR) : IsConsistent x ↔ x ≠ I := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b <;> decide

/-- The exact values of `FOUR` are the classical values `F` and `T` ([fitting-1994]). -/
@[simp] theorem isExact_iff (x : FOUR) : IsExact x ↔ x = F ∨ x = T := by
  obtain ⟨a, b⟩ := x
  cases a <;> cases b <;> decide

end FOUR

end Bilattice

namespace Trivalent

open Bilattice Product

/-- Kleene's three values inside `FOUR`, sending `false`, `undefined` and `true` to `F`, `U` and
`T`. -/
def toFour : Trivalent → FOUR
  | .false => FOUR.F
  | .undefined => FOUR.U
  | .true => FOUR.T

theorem toFour_injective : Function.Injective toFour := by decide

@[simp] theorem toFour_le_toFour {a b : Trivalent} : toFour a ≤ toFour b ↔ a ≤ b := by
  cases a <;> cases b <;> decide

/-- Kleene's values are exactly the consistent values of `FOUR` ([fitting-1994] §3). -/
theorem range_toFour : Set.range toFour = {x : FOUR | IsConsistent x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    cases a <;> decide
  · intro hx
    obtain ⟨a, b⟩ := x
    cases a <;> cases b
    · exact ⟨.undefined, rfl⟩
    · exact ⟨.false, rfl⟩
    · exact ⟨.true, rfl⟩
    · exact absurd hx (by decide)

/-- `Trivalent` is the consistent part of `FOUR` ([fitting-1994] §3). -/
def orderIsoConsistent : Trivalent ≃o {x : FOUR | IsConsistent x} where
  toFun a := ⟨toFour a, range_toFour ▸ Set.mem_range_self a⟩
  invFun x := if x.1.pro then .true else if x.1.con then .false else .undefined
  left_inv a := by cases a <;> rfl
  right_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    cases a <;> cases b
    · rfl
    · rfl
    · rfl
    · exact absurd h (by decide)
  map_rel_iff' := toFour_le_toFour

/-- The exact values among Kleene's are the defined ones ([fitting-1994] §3). -/
theorem isExact_toFour (a : Trivalent) : IsExact (toFour a) ↔ a ≠ .undefined := by
  cases a <;> decide

/-- Kleene's knowledge order is `FOUR`'s on his values. -/
@[simp] theorem toFour_kLE_toFour {a b : Trivalent} : toFour a ≤ₖ toFour b ↔ a ≤ₖ b := by
  cases a <;> cases b <;> decide

/-- Kleene's negation is `FOUR`'s negation on his values. -/
@[simp] theorem toFour_compl (a : Trivalent) : toFour aᶜ = (toFour a)ᶜ := by
  cases a <;> rfl

/-- Strong Kleene conjunction is `FOUR`'s truth meet on Kleene's values ([fitting-1994] §3). -/
@[simp] theorem toFour_inf (a b : Trivalent) : toFour (a ⊓ b) = toFour a ⊓ toFour b := by
  cases a <;> cases b <;> decide

/-- Strong Kleene disjunction is `FOUR`'s truth join on Kleene's values ([fitting-1994] §3). -/
@[simp] theorem toFour_sup (a b : Trivalent) : toFour (a ⊔ b) = toFour a ⊔ toFour b := by
  cases a <;> cases b <;> decide

/-- Blamey's transplication is Fitting's guard on Kleene's values: `π / φ` is `π : φ`
([blamey-1986], [fitting-1994]). -/
theorem toFour_transplication (a b : Trivalent) :
    toFour (transplication a b) = guard (toFour a) (toFour b) := by
  cases a <;> cases b <;> decide

/-! ### The glut reading -/

/-- Under conflation Kleene's values are the anticonsistent part of `FOUR`, where `undefined`
reads as the glut `I`. -/
theorem range_conf_toFour :
    Set.range (fun a ↦ conf (toFour a)) = {x : FOUR | IsAnticonsistent x} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    cases a <;> decide
  · intro hx
    obtain ⟨a, b⟩ := x
    cases a <;> cases b
    · exact absurd hx (by decide)
    · exact ⟨.false, rfl⟩
    · exact ⟨.true, rfl⟩
    · exact ⟨.undefined, rfl⟩

/-! ### Conditional assertion in the knowledge lattice -/

/-- De Finetti's conditional is the supremum of its consequent over the K3 designation of its
antecedent: the consequent where the antecedent is true, the gap `⊥ₖ` elsewhere. -/
theorem toKnow_toFour_condAssert_k3 (a b : Trivalent) :
    toKnow (toFour (condAssert .k3 a b)) = ⨆ _ : Designation.k3.threshold ≤ a, toKnow (toFour b) := by
  by_cases h : Designation.k3.threshold ≤ a
  · rw [condAssert_of_le h, iSup_pos h]
  · rw [condAssert_of_not_le h, iSup_neg h]; rfl

/-- Cooper's conditional, read with LP's glut, is the infimum of its consequent over the LP
designation of its antecedent: the consequent where the antecedent is not false, the glut `⊤ₖ`
elsewhere. -/
theorem toKnow_conf_toFour_condAssert_lp (a b : Trivalent) :
    toKnow (conf (toFour (condAssert .lp a b))) =
      ⨅ _ : Designation.lp.threshold ≤ a, toKnow (conf (toFour b)) := by
  by_cases h : Designation.lp.threshold ≤ a
  · rw [condAssert_of_le h, iInf_pos h]
  · rw [condAssert_of_not_le h, iInf_neg h]; rfl

end Trivalent
