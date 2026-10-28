module

public import Linglib.Logic.Bilattice.Product
public import Linglib.Logic.Trivalent.Flat

/-!
# Belnap's four values

Belnap's four values are the diagonal product `Bool ⊙ Bool`: a value records whether a
proposition has been told true and whether it has been told false. Arieli and Avron develop their
logic as a bilattice, and `FOUR` is the literature's name for it. The consistent values, those
without a glut, are Kleene's three: `SignType.orderIsoConsistent` identifies `SignType` with them,
carrying Strong Kleene negation, conjunction and disjunction to `FOUR`'s negation and truth meet
and join, and the knowledge order of `SignType.toFlat` to `FOUR`'s.

## Main definitions

* `Bilattice.FOUR`: `Bool ⊙ Bool`, with the values `U` (neither), `T`, `F` and `I` (both).
* `SignType.toFour`: Kleene's values inside `FOUR`.

## Main results

* `Bilattice.FOUR.isConsistent_iff`, `Bilattice.FOUR.isExact_iff`: the consistent values are those
  other than `I`, and the exact values are `F` and `T`.
* `SignType.orderIsoConsistent`: `SignType` is the consistent part of `FOUR`.
* `SignType.toFour_neg`, `SignType.toFour_inf`, `SignType.toFour_sup`,
  `SignType.toFour_kLE_toFour`: the identification respects the connectives and both orders.

## References

* [belnap-1977]
* [arieli-avron-1996]
* [fitting-1994]
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

namespace SignType

open Bilattice Product

/-- Kleene's three values inside `FOUR`, sending `0`, `1` and `-1` to `U`, `T` and `F`. -/
def toFour : SignType → FOUR
  | .zero => FOUR.U
  | .pos => FOUR.T
  | .neg => FOUR.F

theorem toFour_injective : Function.Injective toFour := fun a b ↦ by
  cases a <;> cases b <;> decide

@[simp] theorem toFour_le_toFour {a b : SignType} : toFour a ≤ toFour b ↔ a ≤ b := by
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
    · exact ⟨0, rfl⟩
    · exact ⟨-1, rfl⟩
    · exact ⟨1, rfl⟩
    · exact absurd hx (by decide)

/-- `SignType` is the consistent part of `FOUR` ([fitting-1994] §3). -/
def orderIsoConsistent : SignType ≃o {x : FOUR | IsConsistent x} where
  toFun a := ⟨toFour a, range_toFour ▸ Set.mem_range_self a⟩
  invFun x := if x.1.pro then 1 else if x.1.con then -1 else 0
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
theorem isExact_toFour (a : SignType) : IsExact (toFour a) ↔ a ≠ 0 := by
  cases a <;> decide

/-- The knowledge order of `SignType` is `FOUR`'s on Kleene's values. -/
theorem toFour_kLE_toFour {a b : SignType} : toFour a ≤ₖ toFour b ↔ toFlat a ≤ toFlat b := by
  cases a <;> cases b <;> decide

/-- Strong Kleene negation is `FOUR`'s negation on Kleene's values. -/
@[simp] theorem toFour_neg (a : SignType) : toFour (-a) = (toFour a)ᶜ := by
  cases a <;> rfl

/-- Strong Kleene conjunction is `FOUR`'s truth meet on Kleene's values ([fitting-1994] §3). -/
@[simp] theorem toFour_inf (a b : SignType) : toFour (a ⊓ b) = toFour a ⊓ toFour b := by
  cases a <;> cases b <;> decide

/-- Strong Kleene disjunction is `FOUR`'s truth join on Kleene's values ([fitting-1994] §3). -/
@[simp] theorem toFour_sup (a b : SignType) : toFour (a ⊔ b) = toFour a ⊔ toFour b := by
  cases a <;> cases b <;> decide

end SignType
