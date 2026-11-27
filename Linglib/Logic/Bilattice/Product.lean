/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Bilattice.Involution
public import Linglib.Core.Order.InvolutiveCompl
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.SupClosed
public import Mathlib.Order.CompleteLattice.Basic

/-!
# The Ginsberg–Fitting product bilattice

The standard way to build a bilattice is from evidence. A value of the **product** of two lattices
is a pair: the evidence for a proposition and the evidence against it. One pair is truer than
another when it has more for and less against, and it says more when it has more of both. With sets
of worlds as evidence, a pair gives the worlds where a proposition is true and the worlds where it
is false, and nothing keeps the two sets from overlapping or from leaving worlds out. When both
coordinates come from one lattice, swapping them is Ginsberg's negation, and swapping them while
complementing each is Fitting's conflation, which [leaves fixed the pairs whose evidence against is
the complement of their evidence for](##Product.isExact_iff). Avron credits the construction to
Ginsberg, generalized by Fitting.

## Implementation notes

`[UPSTREAM]` candidate: mathlib has no bilattices.

The product `L ⊙ R` has as carrier `L × Rᵒᵈ`, whose order is the truth order, and its knowledge
order, that of `L × R`, is on the synonym `Know (L ⊙ R)`.

## References

* [avron-1996]
* [fitting-1994]
* [fitting-2021]
* [ginsberg-1988]
-/

@[expose] public section

namespace Bilattice

/-- The **product** of two lattices is the set of pairs of evidence for and evidence against a
proposition, one from each lattice ([avron-1996] Def 2.4). A pair is truer when it has more for and
less against, and it says more when it has more of both. -/
def Product (L R : Type*) : Type _ := L × Rᵒᵈ

@[inherit_doc] scoped infixl:70 " ⊙ " => Product

namespace Product

variable {L R : Type*}

/-- A piece of evidence for and a piece of evidence against together make a value of the product. -/
def mk (a : L) (b : R) : L ⊙ R := (a, OrderDual.toDual b)

/-- The **evidence for** of a pair is its first coordinate. -/
def pro (x : L ⊙ R) : L := x.1

/-- The **evidence against** of a pair is its second coordinate. -/
def con (x : L ⊙ R) : R := OrderDual.ofDual x.2

@[simp] theorem pro_mk (a : L) (b : R) : pro (mk a b) = a := rfl
@[simp] theorem con_mk (a : L) (b : R) : con (mk a b) = b := rfl
@[simp] theorem mk_pro_con (x : L ⊙ R) : mk x.pro x.con = x := rfl

@[ext] theorem ext {x y : L ⊙ R} (h₁ : x.pro = y.pro) (h₂ : x.con = y.con) : x = y :=
  Prod.ext h₁ (congrArg OrderDual.toDual h₂)

section Map

variable {L' R' : Type*}

/-- A map on evidence for and a map on evidence against act on a pair by acting on each
coordinate. -/
def map (f : L → L') (g : R → R') (x : L ⊙ R) : L' ⊙ R' := mk (f x.pro) (g x.con)

variable (f : L → L') (g : R → R') (x : L ⊙ R)

@[simp] theorem pro_map : (map f g x).pro = f x.pro := rfl
@[simp] theorem con_map : (map f g x).con = g x.con := rfl
@[simp] theorem map_mk (a : L) (b : R) : map f g (mk a b) = mk (f a) (g b) := rfl

end Map

/-!
### The truth order

A pair is at or below another in the truth order when it has no more evidence for and no less
evidence against ([avron-1996] Def 2.4(ii)). The truth meet takes the meet of the evidence for and
the join of the evidence against, and the truth join the reverse (ibid. Def 2.4(iv), (iii)). True is
the pair with all the evidence for and none against, and false the reverse (ibid. Def 2.4(vii)). The
product of distributive lattices is distributive (ibid. Thm 2.5).
-/

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

/-!
### The knowledge order

A pair is at or below another in the knowledge order when it has no more evidence for and no more
evidence against. The knowledge meet and join take the meets and the joins of both coordinates.
-/

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
instance [CompleteLattice L] [CompleteLattice R] : CompleteLattice (Know (L ⊙ R)) :=
  inferInstanceAs (CompleteLattice (L × R))
instance [Preorder L] [Preorder R] [DecidableLE L] [DecidableLE R] :
    DecidableLE (Know (L ⊙ R)) :=
  inferInstanceAs (DecidableLE (L × R))
instance [Fintype L] [Fintype R] : Fintype (Know (L ⊙ R)) :=
  inferInstanceAs (Fintype (L × R))

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

/-- The product of two lattices is an interlaced bilattice, so the meet and join of each order are
monotone in the other order ([avron-1996] Thm 2.5). -/
instance [Lattice L] [Lattice R] : IsInterlaced (L ⊙ R) where
  inf_kmono h _ := ⟨inf_le_inf h.1 le_rfl, sup_le_sup h.2 le_rfl⟩
  sup_kmono h _ := ⟨sup_le_sup h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kInf_tmono h _ := ⟨inf_le_inf h.1 le_rfl, inf_le_inf h.2 le_rfl⟩
  kSup_tmono h _ := ⟨sup_le_sup h.1 le_rfl, sup_le_sup h.2 le_rfl⟩

/-!
### Negation

When the evidence for and the evidence against come from one lattice, Ginsberg's negation swaps them
([ginsberg-1988]; [avron-1996] Thm 2.5(2)). It undoes itself, reverses the truth order and preserves
the knowledge order. Over a bounded distributive lattice the truth order with this negation obeys
the De Morgan laws ([fitting-2021] §8.3).
-/

section Negation

/-- **Ginsberg negation** of a pair, when both coordinates come from one lattice, swaps its evidence
for and its evidence against. -/
instance : Compl (L ⊙ L) := ⟨fun x ↦ mk x.con x.pro⟩

@[simp] theorem pro_compl (x : L ⊙ L) : xᶜ.pro = x.con := rfl
@[simp] theorem con_compl (x : L ⊙ L) : xᶜ.con = x.pro := rfl
@[simp] theorem mk_compl (a b : L) : (mk a b)ᶜ = mk b a := rfl
@[simp] protected theorem compl_compl (x : L ⊙ L) : xᶜᶜ = x := rfl

theorem compl_map {L' : Type*} (f g : L → L') (x : L ⊙ L) : (map f g x)ᶜ = map g f xᶜ := rfl

protected theorem compl_le_compl [Preorder L] {x y : L ⊙ L} (h : x ≤ y) : yᶜ ≤ xᶜ := ⟨h.2, h.1⟩

protected theorem compl_kLE_compl [Preorder L] {x y : L ⊙ L} (h : x ≤ₖ y) : xᶜ ≤ₖ yᶜ :=
  ⟨h.2, h.1⟩

instance [Preorder L] : InvolutiveCompl (L ⊙ L) where
  compl_compl := Product.compl_compl
  compl_le_compl := Product.compl_le_compl

/-- Ginsberg's swap preserves the knowledge order, which makes it a negation of the product
bilattice ([avron-1996] Thm 2.5(2)). -/
instance [Preorder L] : Negation (L ⊙ L) := ⟨Product.compl_kLE_compl⟩

end Negation

/-!
### Conflation

Conflation swaps the two coordinates and complements each ([fitting-1994] §7, [fitting-2021] §8.8).
It undoes itself, reverses the knowledge order, preserves the truth order and commutes with Ginsberg
negation. Whether a pair is exact, consistent or anticonsistent can be read off its coordinates.
-/

section Conflation

variable [Preorder L] [InvolutiveCompl L]

/-- **Fitting's conflation** sends a pair to the pair of the complement of its evidence against and
the complement of its evidence for. It undoes itself and reverses the knowledge order. -/
instance : InvolutiveCompl (Know (L ⊙ L)) where
  compl x := toKnow (mk (ofKnow x).conᶜ (ofKnow x).proᶜ)
  compl_compl _ := ext (InvolutiveCompl.compl_compl _) (InvolutiveCompl.compl_compl _)
  compl_le_compl h := ⟨InvolutiveCompl.compl_le_compl h.2, InvolutiveCompl.compl_le_compl h.1⟩

instance : Conflation (L ⊙ L) where
  compl_kLE_compl h := ⟨InvolutiveCompl.compl_le_compl h.2, InvolutiveCompl.compl_le_compl h.1⟩

instance : NegConfComm (L ⊙ L) := ⟨fun _ ↦ rfl⟩

@[simp] theorem pro_conf (x : L ⊙ L) : (conf x).pro = x.conᶜ := rfl
@[simp] theorem con_conf (x : L ⊙ L) : (conf x).con = x.proᶜ := rfl

/-- A pair is exact, that is, left fixed by conflation, exactly when its evidence against is the
complement of its evidence for. -/
theorem isExact_iff (x : L ⊙ L) : IsExact x ↔ x.con = x.proᶜ :=
  ⟨fun h ↦ (congrArg con h.eq).symm,
    fun h ↦ ext (by simp [h, InvolutiveCompl.compl_compl]) h.symm⟩

/-- A pair is consistent exactly when its evidence against lies at or below the complement of its
evidence for. -/
theorem isConsistent_iff (x : L ⊙ L) : IsConsistent x ↔ x.con ≤ x.proᶜ :=
  ⟨And.right, fun h ↦ ⟨InvolutiveCompl.le_compl_comm.1 h, h⟩⟩

/-- A pair is anticonsistent exactly when the complement of its evidence for lies at or below its
evidence against. -/
theorem isAnticonsistent_iff (x : L ⊙ L) : IsAnticonsistent x ↔ x.proᶜ ≤ x.con :=
  ⟨And.right, fun h ↦ ⟨(InvolutiveCompl.compl_le_compl h).trans
    (InvolutiveCompl.compl_compl x.pro).le, h⟩⟩

end Conflation

/-!
### Disjoint coordinates

The pairs whose evidence for and evidence against are disjoint are closed under negation and, over a
distributive lattice, under the truth meet and join, and among them a contradiction is never truer
than an excluded middle. They form Kalman's construction `Kalman L`
(`Core/Order/DeMorganAlgebra/Kalman.lean`). Over a Boolean lattice the disjoint pairs are Fitting's
consistent pairs. Over a De Morgan lattice neither notion implies the other: the pair of two
undefined values in `Trivalent ⊙ Trivalent` is consistent but not disjoint, and the pair of the glut
and the gap in `FOUR ⊙ FOUR` is disjoint but not consistent. Over a Heyting lattice, whose
complement does not undo itself, disjointness is the only notion available.
-/

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
