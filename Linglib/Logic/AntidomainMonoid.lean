module

public import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Antidomain monoids

An antidomain monoid is a monoid with zero and an operation `∼` sending an element to the test of
where it cannot be executed. The binary relations on a type are the motivating example, with
`∼R` the identity on the states outside the domain of `R`; there composition and `∼` are the
propositional part of dynamic predicate logic, in which `∼` interprets negation,
`∼(x * ∼y)` implication and `∼(∼x * ∼y)` disjunction. The axioms are those of
[hollenberg-1997], which prove every equation true of relations, and they
[determine the operation](##IsAntidomain.unique) from the monoid, as [hollenberg-visser-1999]
show. The name is that of [desharnais-jipsen-struth-2009].

## Implementation notes

The axioms are a predicate `IsAntidomain` on an operation of a monoid with zero, so that two
operations on one monoid can be compared; `AntidomainMonoid` bundles the operation with its
proof. Three of [hollenberg-visser-1999]'s ten axioms are those of a monoid with zero.
[desharnais-jipsen-struth-2009] axiomatize the same operations by six equations, of which one
holds in every monoid with zero; `isAntidomain_iff` is the equivalence, and `IsAntidomain.mk'`
builds an antidomain from the shorter list. [visser-1997] generates the same algebra from
composition and dynamic implication.

## References

* [hollenberg-1997]
* [hollenberg-visser-1999]
* [desharnais-jipsen-struth-2009]
* [visser-1997]

## TODO

The Heyting algebras, with meet as the product and pseudocomplement as `∼`, are antidomain
monoids that are not algebras of relations; the instance is not stated. Nor is the Boolean
algebra that the antidomain elements form.
-/

@[expose] public section

variable {M : Type*}

/-- An operation on a monoid with zero is an antidomain operation, or a dynamic negation, when it
satisfies the axioms of [hollenberg-visser-1999]. -/
structure IsAntidomain [MonoidWithZero M] (a : M → M) : Prop where
  /-- Identity definition. -/
  map_zero : a 0 = 1
  /-- Negation elimination. -/
  mul_self (x : M) : a x * x = 0
  /-- Test permutation. -/
  comm (x y : M) : a x * a y = a y * a x
  /-- Domain test. -/
  map_map_mul_self (x : M) : a (a x) * x = x
  /-- Test composition. -/
  map_map_mul (x y : M) : a (a (a x * a y)) = a x * a y
  /-- Modus ponens. -/
  modusPonens (x y : M) : a (x * y) * x = a (x * y) * x * a y
  /-- Distribution. -/
  distrib (x y z : M) : a (x * a (a y * a z)) = a (a (a (x * y) * a (x * z)))

namespace IsAntidomain

variable [MonoidWithZero M] {a b : M → M}

/-- Triple negation law. -/
theorem map_map_map (h : IsAntidomain a) (x : M) : a (a (a x)) = a x := by
  simpa [h.map_zero] using h.map_map_mul 0 x

/-- Test idempotency. -/
theorem mul_self_eq (h : IsAntidomain a) (x : M) : a x * a x = a x := by
  simpa [h.map_map_map] using h.map_map_mul_self (a x)

/-- Range test. -/
theorem map_mul_map_map (h : IsAntidomain a) (x y : M) : a (x * a (a y)) = a (x * y) := by
  simpa [h.mul_self_eq, h.map_map_map] using h.distrib x y y

theorem map_one (h : IsAntidomain a) : a 1 = 0 := by simpa using h.mul_self 1

theorem map_mul_eq_left (ha : IsAntidomain a) (hb : IsAntidomain b) (x : M) :
    a x * b x = a x := by
  have h := hb.modusPonens (a x) x
  rw [ha.mul_self, hb.map_zero, one_mul] at h
  exact h.symm

theorem map_map_mul_eq_zero (ha : IsAntidomain a) (hb : IsAntidomain b) (x : M) :
    a (a x) * b x = 0 := by
  calc a (a x) * b x = (a (a x) * b (a x)) * (b x * a x) := by
        rw [map_mul_eq_left ha hb, map_mul_eq_left hb ha]
    _ = a (a x) * b x * (b (a x) * a x) := by
        rw [mul_assoc, ← mul_assoc (b (a x)), hb.comm, mul_assoc, mul_assoc]
    _ = 0 := by rw [hb.mul_self, mul_zero]

theorem map_map_eq (ha : IsAntidomain a) (hb : IsAntidomain b) (x : M) : a (b x) = a (a x) := by
  have h : a (a (a (a x)) * a (a x)) = 1 := by rw [ha.mul_self, ha.map_zero]
  calc a (b x) = a (a (a (a (a x)) * a (a x)) * a (a (b x))) := by
        rw [ha.map_mul_map_map, h, one_mul]
    _ = a (a (a (b x)) * a (a (a (a x)) * a (a x))) := by rw [ha.comm]
    _ = a (a (a (a (a (b x)) * a (a x)) * a (a (a (b x)) * a x))) := by rw [ha.distrib]
    _ = a (a (a (a (a x) * a (a (b x))) * a (a x * a (a (b x))))) := by
        rw [ha.comm (a (b x)) (a x), ha.comm (a (b x)) x]
    _ = a (a x) := by
        rw [ha.map_mul_map_map, ha.map_mul_map_map, map_map_mul_eq_zero ha hb,
          map_mul_eq_left ha hb, ha.map_zero, one_mul, ha.map_map_map]

/-- A monoid with zero has at most one antidomain operation. -/
theorem unique (ha : IsAntidomain a) (hb : IsAntidomain b) : a = b := by
  funext x
  calc a x = a x * b x := (map_mul_eq_left ha hb x).symm
    _ = a (a (a x)) * b x := by rw [ha.map_map_map]
    _ = a (a (b x)) * b x := by rw [map_map_eq ha hb]
    _ = b x := ha.map_map_mul_self _

end IsAntidomain

namespace IsAntidomain

variable [MonoidWithZero M] {a : M → M}

/-- The antidomain of `x` is the meet of where `x` cannot be followed by `y` and where it
cannot be followed by the antidomain of `y`. -/
theorem map_eq_mul (h : IsAntidomain a) (x y : M) : a x = a (x * y) * a (x * a y) := by
  have := h.distrib x y (a y)
  rwa [h.comm, h.mul_self, h.map_zero, mul_one, h.map_map_mul] at this

/-- An operation satisfying the five equations of [desharnais-jipsen-struth-2009] is an
antidomain operation. -/
theorem mk' (h₁ : ∀ x, a x * x = 0) (h₃ : ∀ x y, a x * a y = a y * a x)
    (h₄ : ∀ x, a (a x) * x = x) (h₅ : ∀ x y, a x = a (x * y) * a (x * a y))
    (h₆ : ∀ x y, a (x * y) * x = a (x * y) * x * a y) : IsAntidomain a := by
  have one : a 1 = 0 := by simpa using h₁ 1
  have zero : a 0 = 1 := by simpa [one] using h₄ 1
  have anti (x : M) : a x * a (a x) = 0 := by rw [h₃, h₁]
  have triple (x : M) : a (a (a x)) = a x := by
    have := h₅ (a (a x)) x
    rwa [h₄, h₁, zero, mul_one] at this
  -- Test composition: the double antidomain of a product of tests absorbs each factor.
  have absorb (p q : M) : a (a (a p * a q)) = a (a (a p * a q)) * a p := by
    have h0 : a (a p) * a (a (a p * a q)) = 0 :=
      calc a (a p) * a (a (a p * a q))
          = a (a p * a q) * a (a p * a (a q)) * a (a (a p * a q)) := by rw [← h₅ (a p) (a q)]
        _ = a (a p * a q) * a (a (a p * a q)) * a (a p * a (a q)) := by
            rw [mul_assoc, h₃ (a p * a (a q)), ← mul_assoc]
        _ = 0 := by rw [anti, zero_mul]
    have := h₆ (a (a (a p * a q))) (a (a p))
    rwa [h₃ (a (a p * a q)) (a p), h0, zero, one_mul, triple] at this
  have test (x y : M) : a (a (a x * a y)) = a x * a y := by
    have hy := absorb y x
    rw [h₃ y x] at hy
    calc a (a (a x * a y)) = a (a (a x * a y)) * a y := hy
      _ = a (a (a x * a y)) * a x * a y := congrArg (· * a y) (absorb x y)
      _ = a x * a y := by rw [mul_assoc, h₄]
  -- A test annihilating `x` lies below the antidomain of `x`.
  have le (t x : M) (h : a t * x = 0) : a t = a t * a x := by
    have := h₅ (a t) x
    rw [h, zero, one_mul] at this
    rw [← test, ← this, triple]
  -- Locality.
  have loc (x y : M) : a (x * a (a y)) = a (x * y) := by
    have hv : x * a (a y) * y = x * y := by rw [mul_assoc, h₄]
    have h : a (x * a (a y)) * (x * y) = 0 := by rw [← hv, ← mul_assoc, h₁, zero_mul]
    have h' : a (x * y) * (x * a (a y)) = 0 := by
      have := h₆ (x * a (a y)) y
      rw [hv] at this
      rw [this, mul_assoc, mul_assoc, h₁, mul_zero, mul_zero]
    rw [le _ _ h, h₃, ← le _ _ h']
  -- Distribution: each side absorbs the other.
  have dist (x y z : M) : a (x * a (a y * a z)) = a (x * y) * a (x * z) := by
    have hA : a (x * a (a y * a z)) * x = a (x * a (a y * a z)) * x * (a y * a z) := by
      have := h₆ x (a (a y * a z))
      rwa [test] at this
    have hAB : a (x * a (a y * a z)) = a (x * a (a y * a z)) * a (x * y) :=
      le _ _ (by rw [← mul_assoc, hA, h₃ y z]; simp only [mul_assoc, h₁, mul_zero])
    have hAC : a (x * a (a y * a z)) = a (x * a (a y * a z)) * a (x * z) :=
      le _ _ (by rw [← mul_assoc, hA]; simp only [mul_assoc, h₁, mul_zero])
    have hwq : a (x * y) * a (x * z) * x = a (x * y) * a (x * z) * x * a z :=
      calc a (x * y) * a (x * z) * x = a (x * y) * (a (x * z) * x) := mul_assoc ..
        _ = a (x * y) * (a (x * z) * x * a z) := congrArg (a (x * y) * ·) (h₆ x z)
        _ = a (x * y) * a (x * z) * x * a z := by simp only [mul_assoc]
    have hwp : a (x * y) * a (x * z) * x = a (x * y) * a (x * z) * x * a y :=
      calc a (x * y) * a (x * z) * x = a (x * z) * (a (x * y) * x) := by
            rw [h₃ (x * y) (x * z), mul_assoc]
        _ = a (x * z) * (a (x * y) * x * a y) := congrArg (a (x * z) * ·) (h₆ x y)
        _ = a (x * y) * a (x * z) * x * a y := by rw [h₃ (x * y) (x * z)]; simp only [mul_assoc]
    have hw : a (x * y) * a (x * z) * x * a (a y * a z) = 0 :=
      calc a (x * y) * a (x * z) * x * a (a y * a z)
          = a (x * y) * a (x * z) * x * a y * a z * a (a y * a z) := by rw [← hwp, ← hwq]
        _ = a (x * y) * a (x * z) * x * (a (a (a y * a z)) * a (a y * a z)) := by
            rw [test]; simp only [mul_assoc]
        _ = 0 := by rw [h₁, mul_zero]
    have hBC : a (x * y) * a (x * z) = a (x * y) * a (x * z) * a (x * a (a y * a z)) := by
      have := le (a (a (x * y) * a (x * z))) (x * a (a y * a z))
        (by rw [test, ← mul_assoc]; exact hw)
      rwa [test] at this
    calc a (x * a (a y * a z)) = a (x * a (a y * a z)) * a (x * z) := hAC
      _ = a (x * a (a y * a z)) * a (x * y) * a (x * z) := by rw [← hAB]
      _ = a (x * y) * a (x * z) * a (x * a (a y * a z)) := by
          rw [mul_assoc, ← test (x * y) (x * z), h₃]
      _ = a (x * y) * a (x * z) := hBC.symm
  exact ⟨zero, h₁, h₃, h₄, test, h₆, fun x y z ↦ by rw [dist, test]⟩

end IsAntidomain

/-- The six equations by which [desharnais-jipsen-struth-2009] axiomatize the antidomain
monoids; the sixth, that zero is absorbing on the right, holds in every monoid with zero. -/
theorem isAntidomain_iff [MonoidWithZero M] {a : M → M} :
    IsAntidomain a ↔ (∀ x, a x * x = 0) ∧ (∀ x y, a x * a y = a y * a x) ∧
      (∀ x, a (a x) * x = x) ∧ (∀ x y, a x = a (x * y) * a (x * a y)) ∧
      ∀ x y, a (x * y) * x = a (x * y) * x * a y :=
  ⟨fun h ↦ ⟨h.mul_self, h.comm, h.map_map_mul_self, h.map_eq_mul, h.modusPonens⟩,
    fun ⟨h₁, h₃, h₄, h₅, h₆⟩ ↦ .mk' h₁ h₃ h₄ h₅ h₆⟩

/-- An antidomain monoid is a monoid with zero and an antidomain operation `∼`. -/
class AntidomainMonoid (M : Type*) extends MonoidWithZero M where
  /-- The antidomain of `x` is the test of where `x` cannot be executed. -/
  antidomain : M → M
  /-- The antidomain satisfies the axioms. -/
  isAntidomain : IsAntidomain antidomain

namespace AntidomainMonoid

@[inherit_doc] scoped prefix:max "∼" => antidomain

variable [AntidomainMonoid M] (x y z : M)

/-- Dynamic implication holds where every execution of `x` can be followed by one of `y`. -/
def dimp : M := ∼(x * ∼y)

/-- Dynamic disjunction holds where `x` or `y` can be executed. -/
def dor : M := ∼(∼x * ∼y)

theorem dimp_def : dimp x y = ∼(x * ∼y) := rfl

theorem dor_def : dor x y = ∼(∼x * ∼y) := rfl

@[simp] theorem antidomain_zero : ∼(0 : M) = 1 := isAntidomain.map_zero

@[simp] theorem antidomain_one : ∼(1 : M) = 0 := isAntidomain.map_one

@[simp] theorem antidomain_mul_self : ∼x * x = 0 := isAntidomain.mul_self x

theorem antidomain_mul_antidomain_comm : ∼x * ∼y = ∼y * ∼x := isAntidomain.comm x y

@[simp] theorem antidomain_antidomain_mul_self : ∼∼x * x = x := isAntidomain.map_map_mul_self x

@[simp] theorem antidomain_antidomain_antidomain : ∼∼∼x = ∼x := isAntidomain.map_map_map x

@[simp] theorem antidomain_mul_antidomain_self : ∼x * ∼x = ∼x := isAntidomain.mul_self_eq x

@[simp] theorem antidomain_antidomain_mul : ∼∼(∼x * ∼y) = ∼x * ∼y := isAntidomain.map_map_mul x y

@[simp] theorem antidomain_mul_antidomain_antidomain : ∼(x * ∼∼y) = ∼(x * y) :=
  isAntidomain.map_mul_map_map x y

theorem antidomain_mul_mul_self : ∼(x * y) * x = ∼(x * y) * x * ∼y := isAntidomain.modusPonens x y

theorem antidomain_mul_dor : ∼(x * dor y z) = ∼(dor (x * y) (x * z)) :=
  isAntidomain.distrib x y z

/-- The operation of an antidomain monoid is its only antidomain operation. -/
theorem antidomain_unique {a : M → M} (h : IsAntidomain a) : a = antidomain :=
  h.unique isAntidomain

/-! ### Dynamic implication and disjunction -/

theorem antidomain_antidomain_dimp : ∼∼(dimp x y) = dimp x y := antidomain_antidomain_antidomain _

theorem antidomain_antidomain_dor : ∼∼(dor x y) = dor x y := antidomain_antidomain_antidomain _

theorem dor_eq_dimp : dor x y = dimp ∼x y := rfl

theorem antidomain_mul : ∼(x * y) = dimp x ∼y := (antidomain_mul_antidomain_antidomain x y).symm

theorem dimp_antidomain_antidomain : dimp x ∼∼y = dimp x y := by simp [dimp]

/-- Dynamic implication curries over composition. -/
theorem dimp_dimp : dimp x (dimp y z) = dimp (x * y) z := by simp [dimp, mul_assoc]

theorem dimp_antidomain_comm : dimp ∼x y = dimp ∼y x := by
  rw [dimp, dimp, antidomain_mul_antidomain_comm]

theorem dor_comm : dor x y = dor y x := by rw [dor, dor, antidomain_mul_antidomain_comm]

theorem dor_self : dor x x = ∼∼x := by simp [dor]

theorem dor_assoc : dor (dor x y) z = dor x (dor y z) := by simp [dor, mul_assoc]

theorem antidomain_dor : ∼(dor x y) = ∼x * ∼y := antidomain_antidomain_mul x y

theorem antidomain_antidomain_mul_dor : ∼∼(x * dor y z) = dor (x * y) (x * z) := by
  rw [antidomain_mul_dor, antidomain_antidomain_dor]

end AntidomainMonoid
