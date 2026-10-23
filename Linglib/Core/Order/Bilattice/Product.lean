/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Bilattice.Involution
public import Linglib.Core.Order.InvolutiveCompl
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.SupClosed

/-!
# The Ginsberg–Fitting product bilattice

The product `L ⊙ R` of two lattices, the fundamental bilattice construction, carries pairs
`(a, b)` recording evidence for (`a ∈ L`) and against (`b ∈ R`) a proposition, ordered two ways.

* The truth order, more for and less against, is the carrier's `≤`. The type is
  `L ⊙ R := L × Rᵒᵈ`, so the `Prod` and `OrderDual` instances provide the truth lattice, its
  bounds `t = (⊤, ⊥)` and `f = (⊥, ⊤)`, and distributivity.
* The knowledge order, more evidence both ways, is the plain `Prod` order, installed on the
  synonym `Know (L ⊙ R)`.

The `IsInterlaced (L ⊙ R)` instance packages the four monotonicity laws, so the product is an
interlaced bilattice. On the diagonal `L ⊙ L`, swapping the coordinates is Ginsberg's negation.
Avron credits the construction to Ginsberg, generalized by Fitting. `[UPSTREAM]` candidate:
mathlib has no bilattices.

## Main definitions

* `Bilattice.Product` (`L ⊙ R`): the carrier, with truth-order instances from `L × Rᵒᵈ` and
  knowledge-order instances on `Know (L ⊙ R)` from `L × R`.
* `Bilattice.Product.mk`, `Bilattice.Product.pro`, `Bilattice.Product.con`: the plain-coordinate
  constructor and projections.
* the `Compl (L ⊙ L)` instance: Ginsberg negation on the diagonal, with the `InvolutiveCompl` and
  `Negation` instances it underlies.
* `Bilattice.Product.conflation`: the conflation induced by an involution of the factor.

## Main results

* `Bilattice.Product.isExact_iff`, `Bilattice.Product.isConsistent_iff`,
  `Bilattice.Product.isAnticonsistent_iff`: the three classes in coordinates.

## References

* [avron-1996]
* [fitting-1994]
* [fitting-2021]
* [ginsberg-1988]
-/

@[expose] public section

namespace Bilattice

/-- The Ginsberg–Fitting product `L ⊙ R` of pairs of evidence for and against ([avron-1996]
Def 2.4). Its order is the truth order of `L × Rᵒᵈ`, more for and less against; the knowledge
order, more evidence both ways, is that of `L × R` on `Know (L ⊙ R)`. -/
def Product (L R : Type*) : Type _ := L × Rᵒᵈ

@[inherit_doc] scoped infixl:70 " ⊙ " => Product

namespace Product

variable {L R : Type*}

/-- The pair with evidence `a` for and `b` against. -/
def mk (a : L) (b : R) : L ⊙ R := (a, OrderDual.toDual b)

/-- The evidence-for coordinate. -/
def pro (x : L ⊙ R) : L := x.1

/-- The evidence-against coordinate. -/
def con (x : L ⊙ R) : R := OrderDual.ofDual x.2

@[simp] theorem pro_mk (a : L) (b : R) : pro (mk a b) = a := rfl
@[simp] theorem con_mk (a : L) (b : R) : con (mk a b) = b := rfl
@[simp] theorem mk_pro_con (x : L ⊙ R) : mk x.pro x.con = x := rfl

@[ext] theorem ext {x y : L ⊙ R} (h₁ : x.pro = y.pro) (h₂ : x.con = y.con) : x = y :=
  Prod.ext h₁ (congrArg OrderDual.toDual h₂)

/-! ### The truth order

The carrier instances are transported from `L × Rᵒᵈ`. Its `≤` is the truth order
([avron-1996] Def 2.4(ii)), `⊓` and `⊔` the truth meet and join (ibid. Def 2.4(iv), (iii)),
`⊤ = t` and `⊥ = f` the truth bounds (ibid. Def 2.4(vii)), and the product of distributive
lattices is distributive (ibid. Thm 2.5). -/

instance [Preorder L] [Preorder R] : Preorder (L ⊙ R) :=
  inferInstanceAs (Preorder (L × Rᵒᵈ))
instance [PartialOrder L] [PartialOrder R] : PartialOrder (L ⊙ R) :=
  inferInstanceAs (PartialOrder (L × Rᵒᵈ))
instance [Lattice L] [Lattice R] : Lattice (L ⊙ R) :=
  inferInstanceAs (Lattice (L × Rᵒᵈ))
instance [DistribLattice L] [DistribLattice R] : DistribLattice (L ⊙ R) :=
  inferInstanceAs (DistribLattice (L × Rᵒᵈ))
instance [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    BoundedOrder (L ⊙ R) :=
  inferInstanceAs (BoundedOrder (L × Rᵒᵈ))
instance [Preorder L] [Preorder R] [DecidableLE L] [DecidableLE R] :
    DecidableLE (L ⊙ R) :=
  inferInstanceAs (DecidableLE (L × Rᵒᵈ))
instance [DecidableEq L] [DecidableEq R] : DecidableEq (L ⊙ R) :=
  inferInstanceAs (DecidableEq (L × Rᵒᵈ))
instance [Fintype L] [Fintype R] : Fintype (L ⊙ R) :=
  inferInstanceAs (Fintype (L × Rᵒᵈ))

@[simp] theorem mk_le_mk [Preorder L] [Preorder R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ≤ mk a₂ b₂ ↔ a₁ ≤ a₂ ∧ b₂ ≤ b₁ := Iff.rfl

@[simp] theorem mk_inf_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊓ mk a₂ b₂ = mk (a₁ ⊓ a₂) (b₁ ⊔ b₂) := rfl

@[simp] theorem mk_sup_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊔ mk a₂ b₂ = mk (a₁ ⊔ a₂) (b₁ ⊓ b₂) := rfl

theorem le_def [Preorder L] [Preorder R] {x y : L ⊙ R} :
    x ≤ y ↔ x.pro ≤ y.pro ∧ y.con ≤ x.con := Iff.rfl

section Proj

variable [Lattice L] [Lattice R] (x y : L ⊙ R)

@[simp] theorem pro_inf : (x ⊓ y).pro = x.pro ⊓ y.pro := rfl
@[simp] theorem con_inf : (x ⊓ y).con = x.con ⊔ y.con := rfl
@[simp] theorem pro_sup : (x ⊔ y).pro = x.pro ⊔ y.pro := rfl
@[simp] theorem con_sup : (x ⊔ y).con = x.con ⊓ y.con := rfl

end Proj

section ProjBounds

variable [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R]

@[simp] theorem pro_top : (⊤ : L ⊙ R).pro = ⊤ := rfl
@[simp] theorem con_top : (⊤ : L ⊙ R).con = ⊥ := rfl
@[simp] theorem pro_bot : (⊥ : L ⊙ R).pro = ⊥ := rfl
@[simp] theorem con_bot : (⊥ : L ⊙ R).con = ⊤ := rfl

end ProjBounds

/-! ### The knowledge order

The instances on the synonym `Know (L ⊙ R)` are transported from the plain `Prod` order on
`L × R`, so `⊓ₖ`, `⊔ₖ` and `≤ₖ` are the generic knowledge operations of
`Core.Order.Bilattice.Defs`. -/

instance [Preorder L] [Preorder R] : Preorder (Know (L ⊙ R)) :=
  inferInstanceAs (Preorder (L × R))
instance [PartialOrder L] [PartialOrder R] : PartialOrder (Know (L ⊙ R)) :=
  inferInstanceAs (PartialOrder (L × R))
instance [Lattice L] [Lattice R] : Lattice (Know (L ⊙ R)) :=
  inferInstanceAs (Lattice (L × R))
instance [DistribLattice L] [DistribLattice R] : DistribLattice (Know (L ⊙ R)) :=
  inferInstanceAs (DistribLattice (L × R))
instance [Preorder L] [Preorder R] [BoundedOrder L] [BoundedOrder R] :
    BoundedOrder (Know (L ⊙ R)) :=
  inferInstanceAs (BoundedOrder (L × R))
instance [Preorder L] [Preorder R] [DecidableLE L] [DecidableLE R] :
    DecidableLE (Know (L ⊙ R)) :=
  inferInstanceAs (DecidableLE (L × R))

@[simp] theorem mk_kLE_mk [Preorder L] [Preorder R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ≤ₖ mk a₂ b₂ ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂ := Iff.rfl

@[simp] theorem mk_kInf_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊓ₖ mk a₂ b₂ = mk (a₁ ⊓ a₂) (b₁ ⊓ b₂) := rfl

@[simp] theorem mk_kSup_mk [Lattice L] [Lattice R] {a₁ a₂ : L} {b₁ b₂ : R} :
    mk a₁ b₁ ⊔ₖ mk a₂ b₂ = mk (a₁ ⊔ a₂) (b₁ ⊔ b₂) := rfl

section KProj

variable [Lattice L] [Lattice R] (x y : L ⊙ R)

@[simp] theorem pro_kInf : (x ⊓ₖ y).pro = x.pro ⊓ y.pro := rfl
@[simp] theorem con_kInf : (x ⊓ₖ y).con = x.con ⊓ y.con := rfl
@[simp] theorem pro_kSup : (x ⊔ₖ y).pro = x.pro ⊔ y.pro := rfl
@[simp] theorem con_kSup : (x ⊔ₖ y).con = x.con ⊔ y.con := rfl

end KProj

/-- The product is an interlaced bilattice, each order's meet and join being monotone for the
other order ([avron-1996] Thm 2.5). -/
instance [Lattice L] [Lattice R] : IsInterlaced (L ⊙ R) where
  inf_kmono h _ := ⟨inf_le_inf h.1 le_rfl, sup_le_sup h.2 le_rfl⟩
  sup_kmono h _ := ⟨sup_le_sup h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kInf_tmono h _ := ⟨inf_le_inf h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kSup_tmono h _ := ⟨sup_le_sup h.1 le_rfl, sup_le_sup h.2 le_rfl⟩

/-! ### Negation

On the diagonal `L ⊙ L`, Ginsberg's negation swaps the coordinates ([ginsberg-1988];
[avron-1996] Thm 2.5(2)). It needs no order on `L`, so it is a bare `Compl` instance. Over a
preorder it is an involution of the truth order (`InvolutiveCompl`) and a bilattice `Negation`, so
over a bounded distributive lattice the truth lattice is a De Morgan algebra ([fitting-2021]
§8.3). -/

section Negation

/-- Ginsberg negation on `L ⊙ L` swaps the evidence for and the evidence against. -/
instance : Compl (L ⊙ L) := ⟨fun x ↦ mk x.con x.pro⟩

@[simp] theorem pro_compl (x : L ⊙ L) : xᶜ.pro = x.con := rfl
@[simp] theorem con_compl (x : L ⊙ L) : xᶜ.con = x.pro := rfl
@[simp] theorem mk_compl (a b : L) : (mk a b)ᶜ = mk b a := rfl
@[simp] protected theorem compl_compl (x : L ⊙ L) : xᶜᶜ = x := rfl

protected theorem compl_le_compl [Preorder L] {x y : L ⊙ L} (h : x ≤ y) : yᶜ ≤ xᶜ := ⟨h.2, h.1⟩

protected theorem compl_kLE_compl [Preorder L] {x y : L ⊙ L} (h : x ≤ₖ y) : xᶜ ≤ₖ yᶜ :=
  ⟨h.2, h.1⟩

instance [Preorder L] : InvolutiveCompl (L ⊙ L) where
  compl_compl := Product.compl_compl
  compl_le_compl := Product.compl_le_compl

/-- Ginsberg's swap is a negation on the diagonal ([avron-1996] Thm 2.5(2)). -/
instance [Preorder L] : Negation (L ⊙ L) := ⟨Product.compl_kLE_compl⟩

end Negation

/-! ### Conflation

Swapping the coordinates and applying an order-reversing involution of the factor to each is a
conflation of `L ⊙ L` ([fitting-1994] §7, [fitting-2021] §8.8). An involutive complement of the
factor gives the conflation instance, which commutes with Ginsberg negation, and the exact,
consistent and anticonsistent values read off the coordinates. -/

section Conflation

/-- The conflation `⟨a, b⟩ ↦ ⟨f b, f a⟩` of `L ⊙ L` induced by an order-reversing involution `f`
of the factor. -/
abbrev conflation [Preorder L] (f : L → L) (hf : Function.Involutive f) (ha : Antitone f) :
    Conflation (L ⊙ L) where
  conf x := mk (f x.con) (f x.pro)
  conf_conf x := ext (hf x.pro) (hf x.con)
  conf_le_conf h := ⟨ha h.2, ha h.1⟩
  conf_kLE_conf h := ⟨ha h.2, ha h.1⟩

variable [Preorder L] [InvolutiveCompl L]

instance : Conflation (L ⊙ L) :=
  conflation (·ᶜ) InvolutiveCompl.compl_compl InvolutiveCompl.compl_anti

instance : NegConfComm (L ⊙ L) := ⟨fun _ ↦ rfl⟩

@[simp] theorem pro_conf (x : L ⊙ L) : (conf x).pro = x.conᶜ := rfl
@[simp] theorem con_conf (x : L ⊙ L) : (conf x).con = x.proᶜ := rfl

theorem isExact_iff (x : L ⊙ L) : IsExact x ↔ x.con = x.proᶜ :=
  ⟨fun h ↦ (congrArg con h.eq).symm,
    fun h ↦ ext (by simp [h, InvolutiveCompl.compl_compl]) h.symm⟩

theorem isConsistent_iff (x : L ⊙ L) : IsConsistent x ↔ x.con ≤ x.proᶜ :=
  ⟨And.right, fun h ↦ ⟨InvolutiveCompl.le_compl_comm.1 h, h⟩⟩

theorem isAnticonsistent_iff (x : L ⊙ L) : IsAnticonsistent x ↔ x.proᶜ ≤ x.con :=
  ⟨And.right, fun h ↦ ⟨(InvolutiveCompl.compl_le_compl h).trans
    (InvolutiveCompl.compl_compl x.pro).le, h⟩⟩

end Conflation

/-! ### Disjoint coordinates

The pairs whose evidence for and against are disjoint are closed under negation by the symmetry
of `Disjoint` and, over a distributive factor, under the truth operations, and negation satisfies
the Kleene law on them: they form Kalman's construction `Kalman L`
(`Core/Order/DeMorganAlgebra/Kalman.lean`). Over a Boolean factor disjointness is Fitting's
consistency. Over a De Morgan factor neither implies the other: `⟨0, 0⟩` in
`SignType ⊙ SignType` is consistent but not disjoint, and the pair of the glut and the gap in
`FOUR ⊙ FOUR` is disjoint but not consistent. Over a Heyting factor, whose pseudocomplement is no
involution, disjointness is the only notion available. -/

section Disjoint

theorem inf_compl_le_sup_compl_of_disjoint [Lattice L] [OrderBot L] {x y : L ⊙ L}
    (hx : Disjoint x.pro x.con) (hy : Disjoint y.pro y.con) : x ⊓ xᶜ ≤ y ⊔ yᶜ :=
  ⟨hx.le_bot.trans bot_le, hy.symm.le_bot.trans bot_le⟩

variable [DistribLattice L] [OrderBot L]

theorem supClosed_disjoint_pro_con : SupClosed {x : L ⊙ L | Disjoint x.pro x.con} :=
  fun _ hx _ hy ↦ (hx.inf_right _).sup_left (hy.inf_right' _)

theorem infClosed_disjoint_pro_con : InfClosed {x : L ⊙ L | Disjoint x.pro x.con} :=
  fun _ hx _ hy ↦ (hx.inf_left _).sup_right (hy.inf_left' _)

end Disjoint

end Product

end Bilattice
