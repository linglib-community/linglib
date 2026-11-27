module

public import Linglib.Logic.Bilattice.Product

/-!
# The guard connective

A presupposition lets a sentence speak only where the presupposition is met. Fitting's **guard** *P
: Q* has the value of *Q* when *P* is at least true and says nothing otherwise. On Kleene's three
values it is Blamey's transplication, the binary presupposition operator, *Q* presupposing *P*. On
pairs of evidence for and against, it keeps the evidence of the second pair only as far as there is
evidence for the first. Fitting characterizes the guard in the operations of a bilattice, as the
value of the second argument attenuated by the degree to which the first is believed. That
characterization is the definition here, so the guard exists on any bilattice with negation. It is
monotone in the knowledge order in both arguments.

## Main definitions

* `Bilattice.guard`: the guard on a bilattice with negation.

## Main results

* `Bilattice.guard_kLE_guard`: the guard is knowledge-monotone.
* `Bilattice.guard_of_top_kLE`: a first argument that is at least true passes the second through.
* `Bilattice.Product.pro_guard`, `Bilattice.Product.con_guard`: the guard of a product in
  coordinates.
* The identities of [fitting-1994] Figure 4: `Bilattice.guard_compl`, `Bilattice.guard_kInf` and
  their kin for any bilattice, `Bilattice.Product.guard_kInf_left` and its kin for products.

## Implementation notes

The guard makes Kleene's weak logic and the asymmetric Lisp logic definable over Belnap's `FOUR`,
and its agreement with transplication on Kleene's three values is `Trivalent.toFour_transplication`.
Fitting defines it on the products `L ⊙ L` that represent the distributive bilattices, as `⟨a, b⟩ :
⟨c, d⟩ = ⟨a ⊓ c, a ⊓ d⟩`, and characterizes it as `x : y = [(x ⊓ₖ t) ⊔ₖ ¬(x ⊓ₖ t)] ⊓ₖ y`. It is not
a lattice-theoretic connective.

## References

* [fitting-1994]
* [blamey-1986]
-/

@[expose] public section

namespace Bilattice

variable {B : Type*}

section Defs

variable [Top B] [Compl B] [Lattice (Know B)]

/-- The **guard** of *y* by *x*, written *x : y*, is the value of *y* attenuated by the degree to
which *x* is believed ([fitting-1994] §9). It is the knowledge meet of *y* with a value built from
*x*, the top of the truth order and negation. -/
def guard (x y : B) : B := (x ⊓ₖ ⊤ ⊔ₖ (x ⊓ₖ ⊤)ᶜ) ⊓ₖ y

variable (x y z : B)

/-- The guard *x : y* never carries more information than *y*. -/
theorem guard_kLE_right : guard x y ≤ₖ y := inf_le_right (α := Know B)

/-- The knowledge join of *y* with the guard *x : y* is *y* ([fitting-1994] Figure 4). -/
theorem kSup_guard_self : y ⊔ₖ guard x y = y :=
  congrArg ofKnow (sup_eq_left.2 (guard_kLE_right x y))

/-- The knowledge meet of *y* with the guard *x : y* is the guard *x : y* ([fitting-1994] Figure
4). -/
theorem kInf_guard_self : y ⊓ₖ guard x y = guard x y :=
  congrArg ofKnow (inf_eq_right.2 (guard_kLE_right x y))

/-- The guard by *x* of a knowledge meet is the knowledge meet of the two guards by *x*
([fitting-1994] Figure 4). -/
theorem guard_kInf : guard x (y ⊓ₖ z) = guard x y ⊓ₖ guard x z :=
  congrArg ofKnow (inf_inf_distrib_left (α := Know B) _ _ _)

variable {x y} [Negation B]

/-- The guard is monotone in the knowledge order in both arguments ([fitting-1994] §5). -/
theorem guard_kLE_guard {x' y' : B} (hx : x ≤ₖ x') (hy : y ≤ₖ y') : guard x y ≤ₖ guard x' y' :=
  have h : x ⊓ₖ ⊤ ≤ₖ x' ⊓ₖ ⊤ := inf_le_inf_right (α := Know B) _ hx
  inf_le_inf (α := Know B) (sup_le_sup (α := Know B) h (compl_kLE_compl h)) hy

end Defs

/-- Where the knowledge order is distributive, the guard by *x* of a knowledge join is the knowledge
join of the two guards by *x* ([fitting-1994] Figure 4). -/
theorem guard_kSup [Top B] [Compl B] [DistribLattice (Know B)] (x y z : B) :
    guard x (y ⊔ₖ z) = guard x y ⊔ₖ guard x z :=
  congrArg ofKnow (inf_sup_left (α := Know B) _ _ _)

/-- The guard by *x* of a negation is the negation of the guard by *x* ([fitting-1994] Figure 4). -/
theorem guard_compl [LE B] [Top B] [InvolutiveCompl B] [Lattice (Know B)] [Negation B]
    (x y : B) : guard x yᶜ = (guard x y)ᶜ := by
  have h : (x ⊓ₖ ⊤ ⊔ₖ (x ⊓ₖ ⊤)ᶜ)ᶜ = x ⊓ₖ ⊤ ⊔ₖ (x ⊓ₖ ⊤)ᶜ := by
    rw [compl_kSup, InvolutiveCompl.compl_compl]
    exact congrArg ofKnow (sup_comm _ _)
  rw [guard, guard, compl_kInf _ y, h]

section Interlaced

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B]

/-- In an interlaced bilattice the guard is monotone in the truth order in its second argument
([fitting-1994] §5). -/
theorem guard_le_guard_right [Top B] [Compl B] {x y z : B} (h : y ≤ z) :
    guard x y ≤ guard x z :=
  kInf_le_kInf le_rfl h

/-- If the first argument carries at least the information of true, the guard is its second argument
([fitting-1994] §5). -/
theorem guard_of_top_kLE [BoundedOrder B] [BoundedOrder (Know B)] [InvolutiveCompl B] {x : B}
    (h : (⊤ : B) ≤ₖ x) (y : B) : guard x y = y := by
  have hx : x ⊓ₖ ⊤ = ⊤ := congrArg ofKnow (inf_eq_right.2 h)
  rw [guard, hx, InvolutiveCompl.compl_top, top_kSup_bot]
  exact congrArg ofKnow (top_inf_eq _)

end Interlaced

/-- The guard of a consistent value, by any value, is consistent ([fitting-1994] §9). -/
theorem IsConsistent.guard [Top B] [Compl B] [Lattice (Know B)] [InvolutiveCompl (Know B)]
    {y : B} (hy : IsConsistent y) (x : B) : IsConsistent (Bilattice.guard x y) :=
  hy.anti (guard_kLE_right x y)

/-!
### The guard of a product

On pairs of evidence for and against, the guard keeps as much of the second pair's evidence, for and
against, as there is evidence for the first. With sets of worlds as evidence, it cuts the second
pair down to the worlds where the first is true.
-/

namespace Product

variable {L : Type*}

section Lattice

variable [Lattice L] [BoundedOrder L]

/-- The evidence for a guard of pairs is the meet of the evidence for its two arguments. With the
matching fact for the evidence against, this is Fitting's definition of the guard on pairs
([fitting-1994] Definition 9.4). -/
@[simp] theorem pro_guard (x y : L ⊙ L) : (guard x y).pro = x.pro ⊓ y.pro := by simp [guard]

@[simp] theorem con_guard (x y : L ⊙ L) : (guard x y).con = x.pro ⊓ y.con := by simp [guard]

/-- If there is no evidence for the first argument, the guard is the pair with no evidence either
way ([fitting-1994] §9). -/
theorem guard_of_pro_bot {x : L ⊙ L} (h : x.pro = ⊥) (y : L ⊙ L) : guard x y = mk ⊥ ⊥ := by
  ext <;> simp [h]

/-! The following are the identities of [fitting-1994] Figure 4 in the first argument. -/

variable (x y z : L ⊙ L)

theorem guard_kInf_eq_guard_inf : guard (x ⊓ₖ y) z = guard (x ⊓ y) z := by ext <;> simp

theorem guard_kSup_eq_guard_sup : guard (x ⊔ₖ y) z = guard (x ⊔ y) z := by ext <;> simp

theorem guard_kInf_left : guard (x ⊓ₖ y) z = guard x z ⊓ₖ guard y z := by
  ext <;> simp [inf_inf_distrib_right]

theorem guard_guard_left : guard (guard x y) z = guard (x ⊓ₖ y) z := by ext <;> simp

theorem guard_guard : guard x (guard y z) = guard (x ⊓ₖ y) z := by ext <;> simp [inf_assoc]

variable {x y z}

/-- For pairs, if one first argument is at or below another in the truth order, the guard by the
first carries at most the information of the guard by the second ([fitting-1994] §5). -/
theorem guard_kLE_guard_of_le (h : x ≤ y) : guard x z ≤ₖ guard y z :=
  calc guard x z = guard x z ⊓ₖ guard y z := by
        rw [← guard_kInf_left, guard_kInf_eq_guard_inf, inf_eq_left.2 h]
    _ ≤ₖ guard y z := inf_le_right (α := Know (L ⊙ L))

end Lattice

section DistribLattice

variable [DistribLattice L] [BoundedOrder L] (x y z : L ⊙ L)

theorem guard_kSup_left : guard (x ⊔ₖ y) z = guard x z ⊔ₖ guard y z := by
  ext <;> simp [inf_sup_right]

theorem guard_inf : guard x (y ⊓ z) = guard x y ⊓ guard x z := by
  ext <;> simp [inf_inf_distrib_left, inf_sup_left]

theorem guard_sup : guard x (y ⊔ z) = guard x y ⊔ guard x z := by
  ext <;> simp [inf_inf_distrib_left, inf_sup_left]

end DistribLattice

end Product

end Bilattice
