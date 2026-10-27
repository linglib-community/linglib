module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Interval.Basic

/-!
# Finitely many intervals

[UPSTREAM] candidate for `Mathlib/Order/Interval/Basic.lean`.

A nonempty interval is a pair of endpoints `a ≤ b`, so the nonempty intervals of a finite order
form a finite type.

## Main definitions

* `NonemptyInterval.equivSubtype`: a nonempty interval is a pair `(a, b)` with `a ≤ b`.
-/

@[expose] public section

namespace NonemptyInterval

variable {α : Type*} [LE α]

/-- A nonempty interval is a pair of endpoints `(a, b)` with `a ≤ b`. -/
def equivSubtype : NonemptyInterval α ≃ {p : α × α // p.1 ≤ p.2} where
  toFun s := ⟨s.toProd, s.fst_le_snd⟩
  invFun p := ⟨p.1, p.2⟩

instance [Fintype α] [DecidableLE α] : Fintype (NonemptyInterval α) :=
  .ofEquiv _ equivSubtype.symm

end NonemptyInterval
