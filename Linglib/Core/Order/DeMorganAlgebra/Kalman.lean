/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.DeMorganAlgebra.Basic
public import Mathlib.Order.Disjoint
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Kalman's construction

Over a distributive lattice `L` with a least element, the pairs `(a, b)` with `a ⊓ b = ⊥` form a
distributive lattice `Kalman L` with meet `(a, b) ⊓ (c, d) = (a ⊓ c, b ⊔ d)`, and the swap
`(a, b)ᶜ = (b, a)` is an involution satisfying Kleene's law; when `L` is bounded, `Kalman L` is a
Kleene algebra. `Kalman L` is the subtype of `L × Lᵒᵈ` of the disjoint pairs, ordered by the
first coordinate and against the second, so the meet and join are those of `L × Lᵒᵈ`. A bounded
lattice homomorphism acts on both coordinates (`Kalman.map`), which is the action on morphisms of
Cignoli's functor from bounded distributive lattices to Kleene algebras.

## Main definitions

* `Kalman L`: the pairs of `L × Lᵒᵈ` with disjoint coordinates, with its `DistribLattice`,
  `BoundedOrder`, `InvolutiveCompl` and `IsKleene` instances.
* `Kalman.map`: the construction on bounded lattice homomorphisms.

## Implementation notes

`Kalman L` is a subtype of `L × Lᵒᵈ` in the manner of mathlib's `Complementeds`, rather than a
`Sublattice`, so that its order and involution need only a partial order with a least element.
Reading the first coordinate as evidence for and the second as evidence against a proposition,
`L × Lᵒᵈ` is the carrier of the product bilattice `L ⊙ L` of `Logic/Bilattice/Product.lean` with
its truth order, and the swap is Ginsberg's negation.

## TODO

* Kalman's general `P(a)`: for any element `a` of a distributive lattice, the pairs with
  `x ⊓ y ≤ a ≤ x ⊔ y` form a normal i-lattice with center `(a, a)`; this file is the case `a = ⊥`.
* Kalman's Theorem 6: the normal extensions of `L` are the i-sublattices of `Kalman L` containing
  the pairs `(⊥, y)` and `(x, ⊥)`.

## References

* [cignoli-1986]
* [jansana-san-martin-2017]
* [kalman-1958]
-/

@[expose] public section

open OrderDual

/-- Kalman's construction is the type of pairs `(a, b)` of a lattice with disjoint coordinates,
ordered by `a` and against `b`, written `P(O)` in [kalman-1958] §3. -/
abbrev Kalman (L : Type*) [PartialOrder L] [OrderBot L] : Type _ :=
  {x : L × Lᵒᵈ // Disjoint x.1 (ofDual x.2)}

namespace Kalman

/-! ### The order and the involution -/

section PartialOrder

variable {L : Type*} [PartialOrder L] [OrderBot L]

/-- The Kalman pair `(a, b)`. -/
def mk (a b : L) (h : Disjoint a b) : Kalman L := ⟨(a, toDual b), h⟩

/-- The first coordinate, the evidence for. -/
def pro (x : Kalman L) : L := x.1.1

/-- The second coordinate, the evidence against. -/
def con (x : Kalman L) : L := ofDual x.1.2

theorem disjoint_pro_con (x : Kalman L) : Disjoint x.pro x.con := x.2

@[simp] theorem fst_coe (x : Kalman L) : (x : L × Lᵒᵈ).1 = x.pro := rfl
@[simp] theorem snd_coe (x : Kalman L) : (x : L × Lᵒᵈ).2 = toDual x.con := rfl

@[simp] theorem pro_mk (a b : L) (h : Disjoint a b) : (mk a b h).pro = a := rfl
@[simp] theorem con_mk (a b : L) (h : Disjoint a b) : (mk a b h).con = b := rfl

@[simp] theorem coe_mk (a b : L) (h : Disjoint a b) :
    ((mk a b h : Kalman L) : L × Lᵒᵈ) = (a, toDual b) :=
  rfl

@[simp] theorem mk_pro_con (x : Kalman L) : mk x.pro x.con x.disjoint_pro_con = x := rfl

@[ext] theorem ext {x y : Kalman L} (h₁ : x.pro = y.pro) (h₂ : x.con = y.con) : x = y :=
  Subtype.ext (Prod.ext h₁ (congrArg toDual h₂))

theorem le_def {x y : Kalman L} : x ≤ y ↔ x.pro ≤ y.pro ∧ y.con ≤ x.con := .rfl

@[simp] theorem mk_le_mk {a₁ b₁ a₂ b₂ : L} {h₁ : Disjoint a₁ b₁} {h₂ : Disjoint a₂ b₂} :
    mk a₁ b₁ h₁ ≤ mk a₂ b₂ h₂ ↔ a₁ ≤ a₂ ∧ b₂ ≤ b₁ := .rfl

/-- The pair with no evidence either way, the fixed point of the involution. -/
instance : Inhabited (Kalman L) := ⟨mk ⊥ ⊥ disjoint_bot_left⟩

/-- Swapping the coordinates is an involution reversing the order. -/
instance : InvolutiveCompl (Kalman L) where
  compl x := mk x.con x.pro x.2.symm
  compl_compl _ := rfl
  compl_le_compl h := ⟨h.2, h.1⟩

@[simp] protected theorem compl_compl (x : Kalman L) : xᶜᶜ = x := rfl

@[simp] theorem pro_compl (x : Kalman L) : xᶜ.pro = x.con := rfl
@[simp] theorem con_compl (x : Kalman L) : xᶜ.con = x.pro := rfl
@[simp] theorem mk_compl (a b : L) (h : Disjoint a b) : (mk a b h)ᶜ = mk b a h.symm := rfl

end PartialOrder

section BoundedOrder

variable {L : Type*} [PartialOrder L] [BoundedOrder L]

instance : BoundedOrder (Kalman L) := Subtype.boundedOrder disjoint_bot_left disjoint_bot_right

@[simp, norm_cast] theorem coe_top : ((⊤ : Kalman L) : L × Lᵒᵈ) = ⊤ := rfl
@[simp, norm_cast] theorem coe_bot : ((⊥ : Kalman L) : L × Lᵒᵈ) = ⊥ := rfl

@[simp] theorem pro_top : (⊤ : Kalman L).pro = ⊤ := rfl
@[simp] theorem con_top : (⊤ : Kalman L).con = ⊥ := rfl
@[simp] theorem pro_bot : (⊥ : Kalman L).pro = ⊥ := rfl
@[simp] theorem con_bot : (⊥ : Kalman L).con = ⊤ := rfl

end BoundedOrder

/-! ### The Kleene lattice -/

section DistribLattice

variable {L : Type*} [DistribLattice L] [OrderBot L]

instance : DistribLattice (Kalman L) :=
  Subtype.distribLattice (fun _ _ hx hy ↦ (hx.inf_right _).sup_left (hy.inf_right' _))
    fun _ _ hx hy ↦ (hx.inf_left _).sup_right (hy.inf_left' _)

@[simp, norm_cast] theorem coe_sup (x y : Kalman L) : ↑(x ⊔ y) = (x : L × Lᵒᵈ) ⊔ y := rfl
@[simp, norm_cast] theorem coe_inf (x y : Kalman L) : ↑(x ⊓ y) = (x : L × Lᵒᵈ) ⊓ y := rfl

@[simp] theorem pro_sup (x y : Kalman L) : (x ⊔ y).pro = x.pro ⊔ y.pro := rfl
@[simp] theorem con_sup (x y : Kalman L) : (x ⊔ y).con = x.con ⊓ y.con := rfl
@[simp] theorem pro_inf (x y : Kalman L) : (x ⊓ y).pro = x.pro ⊓ y.pro := rfl
@[simp] theorem con_inf (x y : Kalman L) : (x ⊓ y).con = x.con ⊔ y.con := rfl

@[simp] theorem mk_sup_mk {a₁ b₁ a₂ b₂ : L} (h₁ : Disjoint a₁ b₁) (h₂ : Disjoint a₂ b₂) :
    mk a₁ b₁ h₁ ⊔ mk a₂ b₂ h₂ =
      mk (a₁ ⊔ a₂) (b₁ ⊓ b₂) ((h₁.inf_right _).sup_left (h₂.inf_right' _)) :=
  rfl

@[simp] theorem mk_inf_mk {a₁ b₁ a₂ b₂ : L} (h₁ : Disjoint a₁ b₁) (h₂ : Disjoint a₂ b₂) :
    mk a₁ b₁ h₁ ⊓ mk a₂ b₂ h₂ =
      mk (a₁ ⊓ a₂) (b₁ ⊔ b₂) ((h₁.inf_left _).sup_right (h₂.inf_left' _)) :=
  rfl

/-- The disjoint pairs satisfy the Kleene law, so they form a normal i-lattice in the sense of
[kalman-1958] §3. -/
instance : IsKleene (Kalman L) :=
  ⟨fun x y ↦ ⟨x.2.le_bot.trans bot_le, y.2.symm.le_bot.trans bot_le⟩⟩

end DistribLattice

/-! ### Functoriality -/

section Map

variable {L M N : Type*} [DistribLattice L] [BoundedOrder L] [DistribLattice M] [BoundedOrder M]
  [DistribLattice N] [BoundedOrder N]

/-- Kalman's construction on morphisms applies a bounded lattice homomorphism to both coordinates
([cignoli-1986], as presented by [jansana-san-martin-2017]). -/
def map (f : BoundedLatticeHom L M) : BoundedLatticeHom (Kalman L) (Kalman M) where
  toFun x := mk (f x.pro) (f x.con) (x.disjoint_pro_con.map f)
  map_sup' x y := ext (map_sup f x.pro y.pro) (map_inf f x.con y.con)
  map_inf' x y := ext (map_inf f x.pro y.pro) (map_sup f x.con y.con)
  map_top' := ext (map_top f) (map_bot f)
  map_bot' := ext (map_bot f) (map_top f)

variable (f : BoundedLatticeHom L M) (g : BoundedLatticeHom M N) (x : Kalman L)

@[simp] theorem pro_map : (map f x).pro = f x.pro := rfl
@[simp] theorem con_map : (map f x).con = f x.con := rfl

@[simp] theorem map_mk (a b : L) (h : Disjoint a b) : map f (mk a b h) = mk (f a) (f b) (h.map f) :=
  rfl

@[simp] protected theorem map_compl : map f xᶜ = (map f x)ᶜ := rfl

@[simp] theorem map_id : map (BoundedLatticeHom.id L) = BoundedLatticeHom.id (Kalman L) := rfl

@[simp] theorem map_comp : map (g.comp f) = (map g).comp (map f) := rfl

end Map

end Kalman
