module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Lattice

/-!
# Bilattices

A bilattice ([avron-1996] Def 2.1) is one carrier with two lattice orders, a **truth** order `≤`
and a **knowledge** order `≤ₖ`. It is interlaced when the meet and join of each order are
monotone for the other order, a condition due to [fitting-1990].

The truth lattice is the carrier's own `[Lattice B]`. The knowledge lattice lives on the type
synonym `Know B`, a distinct type head (cf. `OrderDual`), so both can be instances at once. On
`B` itself the knowledge meet and join, Fitting's consensus `⊗` and gullibility `⊕`, are written
`⊓ₖ` and `⊔ₖ`.

## Main definitions

* `Bilattice.Know`, `Bilattice.toKnow`, `Bilattice.ofKnow`: the knowledge-order synonym and its
  casts.
* `Bilattice.kInf`, `Bilattice.kSup`, `Bilattice.kLE`: the knowledge meet `⊓ₖ`, join `⊔ₖ` and
  order `≤ₖ`.
* `Bilattice.IsInterlaced`: the four interlacing laws.

## References

* [avron-1996]
* [fitting-1990]
-/

@[expose] public section

universe u

variable {B : Type u}

namespace Bilattice

/-- The knowledge-order synonym of a bilattice carrier (cf. `OrderDual`). It is
the same underlying type as `B`, but a distinct type head, so it can carry the
*knowledge* lattice as a separate instance from `B`'s *truth* lattice. -/
def Know (B : Type u) : Type u := B

/-- Cast into the knowledge synonym. -/
def toKnow : B ≃ Know B := Equiv.refl B
/-- Cast out of the knowledge synonym. -/
def ofKnow : Know B ≃ B := Equiv.refl B

@[simp] theorem toKnow_ofKnow (x : Know B) : toKnow (ofKnow x) = x := rfl
@[simp] theorem ofKnow_toKnow (x : B) : ofKnow (toKnow x) = x := rfl

instance [DecidableEq B] : DecidableEq (Know B) := inferInstanceAs (DecidableEq B)

section Defs

variable [Lattice (Know B)]

/-- Knowledge meet `⊓ₖ` (consensus): the meet in the knowledge lattice. -/
def kInf (x y : B) : B := ofKnow (toKnow x ⊓ toKnow y)
/-- Knowledge join `⊔ₖ` (gullibility): the join in the knowledge lattice. -/
def kSup (x y : B) : B := ofKnow (toKnow x ⊔ toKnow y)

@[inherit_doc] scoped infixl:70 " ⊓ₖ " => kInf
@[inherit_doc] scoped infixl:65 " ⊔ₖ " => kSup

@[simp] theorem toKnow_kInf (x y : B) : toKnow (x ⊓ₖ y) = toKnow x ⊓ toKnow y := rfl
@[simp] theorem toKnow_kSup (x y : B) : toKnow (x ⊔ₖ y) = toKnow x ⊔ toKnow y := rfl

end Defs

section KLE

variable [Preorder (Know B)]

/-- Knowledge order `≤_k`. -/
def kLE (x y : B) : Prop := toKnow x ≤ toKnow y

@[inherit_doc] scoped infix:50 " ≤ₖ " => kLE

theorem kLE_def {x y : B} : x ≤ₖ y ↔ toKnow x ≤ toKnow y := Iff.rfl

@[refl] theorem kLE_refl (x : B) : x ≤ₖ x := le_rfl
theorem kLE_trans {x y z : B} (h₁ : x ≤ₖ y) (h₂ : y ≤ₖ z) : x ≤ₖ z := le_trans h₁ h₂

instance : Trans (kLE (B := B)) (kLE (B := B)) (kLE (B := B)) := ⟨kLE_trans⟩

instance [DecidableLE (Know B)] : DecidableRel (kLE (B := B)) :=
  fun x y => inferInstanceAs (Decidable (toKnow x ≤ toKnow y))

end KLE

section KLEAntisymm

variable [PartialOrder (Know B)]

theorem kLE_antisymm {x y : B} (h₁ : x ≤ₖ y) (h₂ : y ≤ₖ x) : x = y :=
  toKnow.injective (le_antisymm h₁ h₂)

end KLEAntisymm

/-! ### The interlacing mixin -/

open scoped Bilattice in
/-- The four **interlacing** laws ([avron-1996] Def 2.1(3)): each operation is
monotone w.r.t. the *other* order. The same-order monotonicities are automatic
(an operation is monotone for its own order). -/
class IsInterlaced (B : Type u) [Lattice B] [Lattice (Know B)] : Prop where
  /-- truth meet `∧ = ⊓` is `≤_k`-monotone -/
  inf_kmono : ∀ {x y : B}, x ≤ₖ y → ∀ z, (x ⊓ z) ≤ₖ (y ⊓ z)
  /-- truth join `∨ = ⊔` is `≤_k`-monotone -/
  sup_kmono : ∀ {x y : B}, x ≤ₖ y → ∀ z, (x ⊔ z) ≤ₖ (y ⊔ z)
  /-- knowledge meet `⊓ₖ` is `≤_t`-monotone -/
  kInf_tmono : ∀ {x y : B}, x ≤ y → ∀ z, (x ⊓ₖ z) ≤ y ⊓ₖ z
  /-- knowledge join `⊔ₖ` is `≤_t`-monotone -/
  kSup_tmono : ∀ {x y : B}, x ≤ y → ∀ z, (x ⊔ₖ z) ≤ y ⊔ₖ z

end Bilattice
