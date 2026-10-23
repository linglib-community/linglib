module

public import Linglib.Core.Order.Bilattice.Product

/-!
# The guard connective

The guard `P : Q` of [fitting-1994] is `Q` when `P` is at least true and undefined otherwise; it
makes Kleene's weak logic and the asymmetric Lisp logic definable over Belnap's `FOUR`. On a
diagonal product `L ⊙ L` it is `⟨a, b⟩ : ⟨c, d⟩ = ⟨a ⊓ c, a ⊓ d⟩` ([fitting-1994] Definition 9.4),
the second argument attenuated by the evidence for the first. It is knowledge-monotone in both
arguments but not a lattice-theoretic connective ([schoter-1996b] Def 4).

## Main definitions

* `Bilattice.Product.guard`: the guard on `L ⊙ L`.

## Main results

* `Bilattice.Product.guard_kLE_guard`: the guard is knowledge-monotone.
* `Bilattice.Product.guard_of_top_kLE`, `Bilattice.Product.guard_of_pro_bot`: a first argument
  that is at least true passes the second through, and one with no evidence for it gives `⊥ₖ`.
* `Bilattice.Product.guard_eq_kSup_compl`: the guard is definable from the bilattice operations,
  `P : Q = [(P ⊓ₖ t) ⊔ₖ (P ⊓ₖ t)ᶜ] ⊓ₖ Q` ([fitting-1994] §9).

## References

* [fitting-1994]
* [schoter-1996b]
-/

@[expose] public section

namespace Bilattice.Product

variable {L : Type*}

section SemilatticeInf

variable [SemilatticeInf L]

/-- The guard `x : y` ([fitting-1994] Definition 9.4): the value of `y`, attenuated by the
evidence for `x`. -/
def guard (x y : L ⊙ L) : L ⊙ L := mk (x.pro ⊓ y.pro) (x.pro ⊓ y.con)

@[simp] theorem pro_guard (x y : L ⊙ L) : (guard x y).pro = x.pro ⊓ y.pro := rfl
@[simp] theorem con_guard (x y : L ⊙ L) : (guard x y).con = x.pro ⊓ y.con := rfl

/-- The guard is monotone in the knowledge order in both arguments ([schoter-1996b] Def 4). -/
theorem guard_kLE_guard {x x' y y' : L ⊙ L} (hx : x ≤ₖ x') (hy : y ≤ₖ y') :
    guard x y ≤ₖ guard x' y' :=
  ⟨inf_le_inf hx.1 hy.1, inf_le_inf hx.1 hy.2⟩

variable [BoundedOrder L]

/-- A first argument that is at least true passes the second through ([schoter-1996b] Def 4). -/
theorem guard_of_top_kLE {x : L ⊙ L} (h : (⊤ : L ⊙ L) ≤ₖ x) (y : L ⊙ L) : guard x y = y := by
  have hp : x.pro = ⊤ := le_antisymm le_top h.1
  simp [guard, hp]

/-- A first argument with no evidence for it gives `⊥ₖ = ⟨⊥, ⊥⟩` ([schoter-1996b] Def 4). -/
theorem guard_of_pro_bot {x : L ⊙ L} (h : x.pro = ⊥) (y : L ⊙ L) : guard x y = mk ⊥ ⊥ := by
  simp [guard, h]

end SemilatticeInf

/-- The guard is definable from the bilattice operations,
`x : y = [(x ⊓ₖ t) ⊔ₖ (x ⊓ₖ t)ᶜ] ⊓ₖ y` ([fitting-1994] §9). -/
theorem guard_eq_kSup_compl [Lattice L] [BoundedOrder L] (x y : L ⊙ L) :
    guard x y = (x ⊓ₖ ⊤ ⊔ₖ (x ⊓ₖ ⊤)ᶜ) ⊓ₖ y := by
  ext <;> simp [guard]

end Bilattice.Product
