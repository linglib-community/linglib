module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Lattice

/-!
# Bilattices

This file defines bilattices. A bilattice is one carrier with two lattice orders, a truth order `≤`
and a knowledge order `≤ₖ`; it is interlaced, in Fitting's sense, when the meet and join of each
order are monotone for the other order. The truth lattice is the carrier's own `[Lattice B]`, and
the knowledge lattice lives on the type synonym `Know B` (cf. `OrderDual`), where the knowledge
meet and join, Fitting's consensus `⊗` and gullibility `⊕`, are `⊓ₖ` and `⊔ₖ`. `Know B` is
itself the bilattice with the two orders exchanged, and `Bᵒᵈ` the one with the truth order
reversed, so a theorem about bilattices read on either is a dual theorem, as
[the bounds](##ofKnow_top_inf_ofKnow_bot) illustrate.

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

/-! ### The dual bilattice

The knowledge order of `Know B` is the truth order of `B`, so `Know B` is the bilattice with the
two orders exchanged. -/

instance [LE B] : LE (Know (Know B)) := inferInstanceAs (LE B)
instance [Preorder B] : Preorder (Know (Know B)) := inferInstanceAs (Preorder B)
instance [PartialOrder B] : PartialOrder (Know (Know B)) := inferInstanceAs (PartialOrder B)
instance [Lattice B] : Lattice (Know (Know B)) := inferInstanceAs (Lattice B)
instance [LE B] [BoundedOrder B] : BoundedOrder (Know (Know B)) := inferInstanceAs (BoundedOrder B)

/-! ### The truth-dual bilattice

Reversing the truth order and keeping the knowledge order gives the bilattice `Bᵒᵈ`. -/

instance [LE (Know B)] : LE (Know Bᵒᵈ) := inferInstanceAs (LE (Know B))
instance [Preorder (Know B)] : Preorder (Know Bᵒᵈ) := inferInstanceAs (Preorder (Know B))
instance [PartialOrder (Know B)] : PartialOrder (Know Bᵒᵈ) :=
  inferInstanceAs (PartialOrder (Know B))
instance [Lattice (Know B)] : Lattice (Know Bᵒᵈ) := inferInstanceAs (Lattice (Know B))
instance [LE (Know B)] [BoundedOrder (Know B)] : BoundedOrder (Know Bᵒᵈ) :=
  inferInstanceAs (BoundedOrder (Know B))

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

/-- Knowledge order `≤_k`. -/
def kLE [LE (Know B)] (x y : B) : Prop := toKnow x ≤ toKnow y

@[inherit_doc] scoped infix:50 " ≤ₖ " => kLE

theorem kLE_def [LE (Know B)] {x y : B} : x ≤ₖ y ↔ toKnow x ≤ toKnow y := Iff.rfl

instance [LE (Know B)] [DecidableLE (Know B)] : DecidableRel (kLE (B := B)) :=
  fun x y => inferInstanceAs (Decidable (toKnow x ≤ toKnow y))

variable [Preorder (Know B)]

@[refl] theorem kLE_refl (x : B) : x ≤ₖ x := le_rfl
theorem kLE_trans {x y z : B} (h₁ : x ≤ₖ y) (h₂ : y ≤ₖ z) : x ≤ₖ z := le_trans h₁ h₂

instance : Trans (kLE (B := B)) (kLE (B := B)) (kLE (B := B)) := ⟨kLE_trans⟩

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

/-- Interlacing is symmetric in the two orders. -/
instance [Lattice B] [Lattice (Know B)] [IsInterlaced B] : IsInterlaced (Know B) where
  inf_kmono h z := IsInterlaced.kInf_tmono (B := B) h (ofKnow z)
  sup_kmono h z := IsInterlaced.kSup_tmono (B := B) h (ofKnow z)
  kInf_tmono h z := IsInterlaced.inf_kmono (B := B) h (ofKnow z)
  kSup_tmono h z := IsInterlaced.sup_kmono (B := B) h (ofKnow z)

/-- Interlacing survives reversing the truth order. -/
instance [Lattice B] [Lattice (Know B)] [IsInterlaced B] : IsInterlaced Bᵒᵈ where
  inf_kmono h z := IsInterlaced.sup_kmono (B := B) h (OrderDual.ofDual z)
  sup_kmono h z := IsInterlaced.inf_kmono (B := B) h (OrderDual.ofDual z)
  kInf_tmono h z := IsInterlaced.kInf_tmono (B := B) h (OrderDual.ofDual z)
  kSup_tmono h z := IsInterlaced.kSup_tmono (B := B) h (OrderDual.ofDual z)

section Interlaced

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B]

/-- The truth meet is knowledge-monotone in both arguments. -/
theorem inf_kLE_inf {a b c d : B} (h₁ : a ≤ₖ b) (h₂ : c ≤ₖ d) : a ⊓ c ≤ₖ b ⊓ d :=
  calc a ⊓ c ≤ₖ b ⊓ c := IsInterlaced.inf_kmono h₁ c
    _ = c ⊓ b := inf_comm ..
    _ ≤ₖ d ⊓ b := IsInterlaced.inf_kmono h₂ b
    _ = b ⊓ d := inf_comm ..

/-- The truth join is knowledge-monotone in both arguments. -/
theorem sup_kLE_sup {a b c d : B} (h₁ : a ≤ₖ b) (h₂ : c ≤ₖ d) : a ⊔ c ≤ₖ b ⊔ d :=
  calc a ⊔ c ≤ₖ b ⊔ c := IsInterlaced.sup_kmono h₁ c
    _ = c ⊔ b := sup_comm ..
    _ ≤ₖ d ⊔ b := IsInterlaced.sup_kmono h₂ b
    _ = b ⊔ d := sup_comm ..

/-- The knowledge meet is truth-monotone in both arguments, the dual of `inf_kLE_inf`. -/
theorem kInf_le_kInf {a b c d : B} (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ₖ c ≤ b ⊓ₖ d :=
  inf_kLE_inf (B := Know B) (a := toKnow a) (b := toKnow b) (c := toKnow c) (d := toKnow d) h₁ h₂

/-- The knowledge join is truth-monotone in both arguments, the dual of `sup_kLE_sup`. -/
theorem kSup_le_kSup {a b c d : B} (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ₖ c ≤ b ⊔ₖ d :=
  sup_kLE_sup (B := Know B) (a := toKnow a) (b := toKnow b) (c := toKnow c) (d := toKnow d) h₁ h₂

/-! #### The four bounds

In an interlaced bilattice each bound is a combination of two others: the consensus and the
gullibility of `t` and `f` are the knowledge bounds, and the truth meet and join of the knowledge
bounds are `f` and `t` ([fitting-1994] §6). -/

variable [BoundedOrder B] [BoundedOrder (Know B)]

theorem top_kInf_bot : (⊤ : B) ⊓ₖ ⊥ = ofKnow ⊥ :=
  le_antisymm
    (calc (⊤ : B) ⊓ₖ ⊥ = ⊥ ⊓ₖ ⊤ := congrArg ofKnow (inf_comm _ _)
      _ ≤ ofKnow ⊥ ⊓ₖ ⊤ := IsInterlaced.kInf_tmono bot_le ⊤
      _ = ofKnow ⊥ := congrArg ofKnow (bot_inf_eq _))
    (calc ofKnow ⊥ = ofKnow ⊥ ⊓ₖ ⊥ := congrArg ofKnow (bot_inf_eq _).symm
      _ ≤ ⊤ ⊓ₖ ⊥ := IsInterlaced.kInf_tmono le_top ⊥)

theorem top_kSup_bot : (⊤ : B) ⊔ₖ ⊥ = ofKnow ⊤ :=
  le_antisymm
    (calc (⊤ : B) ⊔ₖ ⊥ = ⊥ ⊔ₖ ⊤ := congrArg ofKnow (sup_comm _ _)
      _ ≤ ofKnow ⊤ ⊔ₖ ⊤ := IsInterlaced.kSup_tmono bot_le ⊤
      _ = ofKnow ⊤ := congrArg ofKnow (top_sup_eq _))
    (calc ofKnow ⊤ = ofKnow ⊤ ⊔ₖ ⊥ := congrArg ofKnow (top_sup_eq _).symm
      _ ≤ ⊤ ⊔ₖ ⊥ := IsInterlaced.kSup_tmono le_top ⊥)

/-- The dual of `top_kInf_bot`. -/
theorem ofKnow_top_inf_ofKnow_bot : ofKnow ⊤ ⊓ ofKnow ⊥ = (⊥ : B) := top_kInf_bot (B := Know B)

/-- The dual of `top_kSup_bot`. -/
theorem ofKnow_top_sup_ofKnow_bot : ofKnow ⊤ ⊔ ofKnow ⊥ = (⊤ : B) := top_kSup_bot (B := Know B)

end Interlaced

end Bilattice
