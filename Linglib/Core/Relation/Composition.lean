module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Basic.Rel

/-!
# Relations under composition

`[UPSTREAM]` Composition of relations distributes over union on both sides, so the relations on a
type form an idempotent semiring: the sum is the union, the product is composition `R ○ S`, the
zero is the empty relation and the unit is the identity. An algebra of named relations whose
composition table is exact on some type, such as the point and interval algebras of
`Logic/Temporal`, maps into it by a semiring homomorphism.

## Main results

* `SetRel.comp_union`, `SetRel.union_comp`: composition distributes over union.
* `SetRel.Composition.instIdemSemiring`: the idempotent semiring of relations on a type, in the
  scope `SetRel.Composition`.

## Implementation notes

The instances are scoped, as mathlib's pointwise instances on sets are: `SetRel α α` is
`Set (α × α)`, which also carries the pointwise operations of `α × α`, so a global `Mul` on it
would compete with them.
-/

@[expose] public section

namespace SetRel

variable {α β γ : Type*}

theorem comp_union (R : SetRel α β) (S S' : SetRel β γ) : R ○ (S ∪ S') = (R ○ S) ∪ (R ○ S') := by
  ext ⟨a, c⟩
  simp only [mem_comp, Set.mem_union, and_or_left, exists_or]

theorem union_comp (R R' : SetRel α β) (S : SetRel β γ) : (R ∪ R') ○ S = (R ○ S) ∪ (R' ○ S) := by
  ext ⟨a, c⟩
  simp only [mem_comp, Set.mem_union, or_and_right, exists_or]

namespace Composition

/-- The sum of two relations is their union. -/
scoped instance : Add (SetRel α α) := ⟨(· ∪ ·)⟩

/-- The zero relation is the empty one. -/
scoped instance : Zero (SetRel α α) := ⟨∅⟩

/-- The product of two relations is their composite. -/
scoped instance : Mul (SetRel α α) := ⟨(· ○ ·)⟩

/-- The unit relation is the identity. -/
scoped instance : One (SetRel α α) := ⟨SetRel.id⟩

theorem add_def (R S : SetRel α α) : R + S = R ∪ S := rfl

theorem zero_def : (0 : SetRel α α) = ∅ := rfl

theorem mul_def (R S : SetRel α α) : R * S = R ○ S := rfl

theorem one_def : (1 : SetRel α α) = SetRel.id := rfl

/-- The relations on a type form an idempotent semiring under union and composition. -/
scoped instance instIdemSemiring : IdemSemiring (SetRel α α) where
  __ := (inferInstance : SemilatticeSup (SetRel α α))
  __ := (inferInstance : OrderBot (SetRel α α))
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  add_assoc := Set.union_assoc
  zero_add := Set.empty_union
  add_zero := Set.union_empty
  add_comm := Set.union_comm
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_union
  right_distrib := union_comp
  zero_mul := empty_comp
  mul_zero := comp_empty
  bot_le _ := Set.empty_subset _

end Composition

end SetRel
