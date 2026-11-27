module

public import Linglib.Core.Algebra.AntidomainMonoid.Basic
public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# The Boolean algebra of tests of an antidomain monoid

A **test** checks a state and changes nothing. In relational dynamic semantics negations,
implications and disjunctions are tests. In an antidomain monoid the tests are the antidomain
elements, which are the elements that the double antidomain leaves unchanged. With the product as
meet, dynamic disjunction as join and the antidomain as complement they form [a Boolean
algebra](##AntidomainMonoid.Test), as Desharnais, Jipsen and Struth show. Tests thus combine by
classical logic, although the double antidomain of an element is not in general that element.
Dynamic disjunction therefore [distributes over a product of
tests](##AntidomainMonoid.dor_antidomain_antidomain_mul).

## Implementation notes

`Test M` is a type of its own and not a subtype of `M`, as `Heyting.Regular` is in mathlib: the
order of the Boolean algebra is that of the product, and a subtype would also inherit whatever order
`M` carries.

## References

* [desharnais-jipsen-struth-2009]
* [hollenberg-1997]
-/

@[expose] public section

namespace AntidomainMonoid

variable {M : Type*} [AntidomainMonoid M] (x y z : M)

theorem dor_antidomain_antidomain_left : dor ∼∼x y = dor x y := by simp [dor]

theorem dor_antidomain_antidomain_right : dor x ∼∼y = dor x y := by simp [dor]

theorem dor_mul_self : dor x (x * y) = ∼∼x := by
  rw [dor, ← isAntidomain.eq_mul_map_of_mul_eq_zero (by rw [← mul_assoc, antidomain_mul_self,
    zero_mul])]

variable (M) in
/-- The **tests** of an antidomain monoid are the elements that its double antidomain leaves
unchanged. -/
def Test : Type _ :=
  { x : M // ∼∼x = x }

namespace Test

/-- Every test is an element of the monoid, and this map sends a test to that element. -/
@[coe] def val : Test M → M :=
  Subtype.val

instance : CoeOut (Test M) M := ⟨Test.val⟩

variable (p q r : Test M)

@[simp] theorem antidomain_antidomain_coe : ∼∼(p : M) = p := Subtype.prop p

theorem coe_injective : Function.Injective ((↑) : Test M → M) := Subtype.coe_injective

@[simp] theorem coe_inj {p q : Test M} : (p : M) = q ↔ p = q := Subtype.coe_inj

theorem coe_mul_comm : (p : M) * q = q * p := by
  rw [← antidomain_antidomain_coe p, ← antidomain_antidomain_coe q,
    antidomain_mul_antidomain_comm]

@[simp] theorem coe_mul_self : (p : M) * p = p := by
  rw [← antidomain_antidomain_coe p, antidomain_mul_antidomain_self]

instance : Max (Test M) := ⟨fun p q ↦ ⟨dor (p : M) q, antidomain_antidomain_dor ..⟩⟩

instance : Min (Test M) :=
  ⟨fun p q ↦ ⟨(p : M) * q, by
    rw [← antidomain_antidomain_coe p, ← antidomain_antidomain_coe q,
      antidomain_antidomain_mul]⟩⟩

instance : Compl (Test M) := ⟨fun p ↦ ⟨∼(p : M), antidomain_antidomain_antidomain _⟩⟩

instance : Top (Test M) := ⟨⟨1, by simp⟩⟩

instance : Bot (Test M) := ⟨⟨0, by simp⟩⟩

@[simp, norm_cast] theorem coe_sup : ((p ⊔ q : Test M) : M) = dor (p : M) q := rfl

@[simp, norm_cast] theorem coe_inf : ((p ⊓ q : Test M) : M) = p * q := rfl

@[simp, norm_cast] theorem coe_compl : ((pᶜ : Test M) : M) = ∼(p : M) := rfl

@[simp, norm_cast] theorem coe_top : ((⊤ : Test M) : M) = 1 := rfl

@[simp, norm_cast] theorem coe_bot : ((⊥ : Test M) : M) = 0 := rfl

/-- The product of a test with a dynamic disjunction of two tests is the dynamic disjunction of its
products with each of them. -/
theorem coe_mul_dor : (p : M) * dor (q : M) r = dor ((p : M) * q) ((p : M) * r) := by
  rw [← antidomain_antidomain_mul_dor]
  exact (antidomain_antidomain_coe (p ⊓ (q ⊔ r))).symm

instance : Lattice (Test M) :=
  Lattice.mk' (fun p q ↦ coe_injective (dor_comm ..)) (fun p q r ↦ coe_injective (dor_assoc ..))
    (fun p q ↦ coe_injective (coe_mul_comm p q)) (fun p q r ↦ coe_injective (mul_assoc ..))
    (fun p q ↦ coe_injective <| show dor (p : M) (p * q) = p by
      rw [dor_mul_self, antidomain_antidomain_coe])
    (fun p q ↦ coe_injective <| show (p : M) * dor (p : M) q = p by
      rw [coe_mul_dor, coe_mul_self, dor_mul_self, antidomain_antidomain_coe])

/-- The tests of an antidomain monoid form a Boolean algebra, with the product as meet, dynamic
disjunction as join and the antidomain as complement. -/
instance : BooleanAlgebra (Test M) :=
  { DistribLattice.ofInfSupLe fun p q r ↦ le_of_eq (coe_injective (coe_mul_dor p q r)) with
    inf_compl_le_bot := fun p ↦ le_of_eq <| coe_injective <|
      show (p : M) * ∼(p : M) = 0 from
        (congrArg (· * ∼(p : M)) (antidomain_antidomain_coe p).symm).trans
          (antidomain_mul_self _)
    top_le_sup_compl := fun p ↦ le_of_eq <| coe_injective <|
      show (1 : M) = dor (p : M) ∼(p : M) by
        rw [dor, antidomain_mul_antidomain_comm, antidomain_mul_self, antidomain_zero]
    le_top := fun p ↦ sup_eq_right.mp <| coe_injective <| show dor (p : M) 1 = 1 by simp [dor]
    bot_le := fun p ↦ sup_eq_right.mp <| coe_injective <| show dor 0 (p : M) = p by
      simp [dor] }

variable {p q} in
theorem le_iff_mul_eq : p ≤ q ↔ (p : M) * q = p :=
  inf_eq_left.symm.trans coe_inj.symm

end Test

/-- The double antidomain sends each element of the monoid to a test. -/
def toTest (x : M) : Test M := ⟨∼∼x, antidomain_antidomain_antidomain _⟩

@[simp, norm_cast] theorem coe_toTest : (toTest x : M) = ∼∼x := rfl

@[simp] theorem toTest_coe (p : Test M) : toTest (p : M) = p :=
  Test.coe_injective p.antidomain_antidomain_coe

/-- The dynamic disjunction of *x* with a product whose first factor is a test is the product of the
disjunctions of *x* with each factor. -/
theorem dor_antidomain_antidomain_mul : dor x (∼∼y * z) = dor x y * dor x z := by
  have h := congrArg Test.val (sup_inf_left (toTest x) (toTest y) (toTest z))
  simp only [Test.coe_sup, Test.coe_inf, coe_toTest, dor_antidomain_antidomain_left,
    dor_antidomain_antidomain_right] at h
  rw [← h]
  simp only [dor, antidomain_mul_antidomain_antidomain]

end AntidomainMonoid
