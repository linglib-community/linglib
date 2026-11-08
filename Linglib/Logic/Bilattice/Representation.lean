module

public import Linglib.Logic.Bilattice.Product
public import Mathlib.Order.LatticeIntervals

/-!
# The representation of interlaced bilattices

Every interlaced bilattice `B` is a product of two lattices: `L_B` holds the values truth-above
the knowledge bottom `⊥` under the truth order, `R_B` those truth-below it under the reverse
order, and `x ↦ (x ∨ ⊥, x ∧ ⊥)` is [an isomorphism of bilattices](##productIso_kLE_iff) onto
`L_B ⊙ R_B` with inverse `(a, b) ↦ a ⊕ b`. The proof rests on one interval law, that
[a value knowledge-between `a` and `b` lies truth-below `a ∨ b`](##le_sup_of_kLE_of_kLE), whose
readings on `Bᵒᵈ` and `Know B` make the two orders [agree on `L_B`](##kLE_iff_le_of_ofKnow_bot_le)
and inverse on `R_B`. Conversely, [the `L_B` of a product `L ⊙ R` is `L`](##Product.iciIso).

## References

* [avron-1996]
-/

@[expose] public section

namespace Bilattice

open OrderDual

variable {B : Type*}

section Interlaced

variable [Lattice B] [Lattice (Know B)] [IsInterlaced B] {a b x : B}

/-- A value knowledge-between `a` and `b` lies truth-below `a ∨ b` ([avron-1996] Prop 3.2). -/
theorem le_sup_of_kLE_of_kLE (ha : a ≤ₖ x) (hb : x ≤ₖ b) : x ≤ a ⊔ b :=
  sup_eq_right.1 <| kLE_antisymm
    (calc x ⊔ (a ⊔ b) ≤ₖ b ⊔ (a ⊔ b) := IsInterlaced.sup_kmono hb _
      _ = a ⊔ b := sup_eq_right.2 le_sup_right)
    (calc a ⊔ b = a ⊔ (a ⊔ b) := (sup_eq_right.2 le_sup_left).symm
      _ ≤ₖ x ⊔ (a ⊔ b) := IsInterlaced.sup_kmono ha _)

/-- A value knowledge-between `a` and `b` lies truth-above `a ∧ b`, the truth dual of
`le_sup_of_kLE_of_kLE`. -/
theorem inf_le_of_kLE_of_kLE (ha : a ≤ₖ x) (hb : x ≤ₖ b) : a ⊓ b ≤ x :=
  le_sup_of_kLE_of_kLE (B := Bᵒᵈ) (a := toDual a) (b := toDual b) (x := toDual x) ha hb

/-- A value truth-between `a` and `b` lies knowledge-below `a ⊕ b`, the dual of
`le_sup_of_kLE_of_kLE`. -/
theorem kLE_kSup_of_le_of_le (ha : a ≤ x) (hb : x ≤ b) : x ≤ₖ a ⊔ₖ b :=
  le_sup_of_kLE_of_kLE (B := Know B) (a := toKnow a) (b := toKnow b) (x := toKnow x) ha hb

section Bounded

variable [BoundedOrder (Know B)] {u v : B}

/-- On `L_B` the knowledge order is the truth order ([avron-1996] Prop 4.2). -/
theorem kLE_iff_le_of_ofKnow_bot_le (hu : ofKnow ⊥ ≤ u) (hv : ofKnow ⊥ ≤ v) :
    u ≤ₖ v ↔ u ≤ v :=
  ⟨fun h ↦ (le_sup_of_kLE_of_kLE (bot_le (a := toKnow u)) h).trans_eq (sup_eq_right.2 hv),
    fun h ↦ (kLE_kSup_of_le_of_le hu h).trans_eq (bot_sup_eq (toKnow v))⟩

/-- On `R_B` the knowledge order is the reverse of the truth order ([avron-1996] Prop 4.2). -/
theorem kLE_iff_le_of_le_ofKnow_bot (hu : u ≤ ofKnow ⊥) (hv : v ≤ ofKnow ⊥) :
    u ≤ₖ v ↔ v ≤ u :=
  kLE_iff_le_of_ofKnow_bot_le (B := Bᵒᵈ) (u := toDual u) (v := toDual v) hu hv

theorem sup_ofKnow_bot_kLE (x : B) : x ⊔ ofKnow ⊥ ≤ₖ x :=
  (sup_kLE_sup (c := ofKnow ⊥) (kLE_refl x) bot_le).trans_eq (congrArg toKnow (sup_idem x))

theorem inf_ofKnow_bot_kLE (x : B) : x ⊓ ofKnow ⊥ ≤ₖ x :=
  sup_ofKnow_bot_kLE (B := Bᵒᵈ) (toDual x)

theorem kLE_sup_ofKnow_top (x : B) : x ≤ₖ x ⊔ ofKnow ⊤ :=
  (congrArg toKnow (sup_idem x)).symm.trans_le (sup_kLE_sup (d := ofKnow ⊤) (kLE_refl x) le_top)

/-- `x = (x ∨ ⊥) ⊕ (x ∧ ⊥)` ([avron-1996] Cor 3.8). -/
theorem sup_ofKnow_bot_kSup_inf_ofKnow_bot (x : B) :
    (x ⊔ ofKnow ⊥) ⊔ₖ (x ⊓ ofKnow ⊥) = x :=
  kLE_antisymm (sup_le (sup_ofKnow_bot_kLE x) (inf_ofKnow_bot_kLE x))
    ((kLE_kSup_of_le_of_le inf_le_left le_sup_left).trans_eq (sup_comm _ _))

/-- `x = (x ∨ ⊥) ∧ (x ∨ ⊤)` ([avron-1996] Cor 3.8). -/
theorem sup_ofKnow_bot_inf_sup_ofKnow_top (x : B) :
    (x ⊔ ofKnow ⊥) ⊓ (x ⊔ ofKnow ⊤) = x :=
  le_antisymm (inf_le_of_kLE_of_kLE (sup_ofKnow_bot_kLE x) (kLE_sup_ofKnow_top x))
    (le_inf le_sup_left le_sup_left)

/-- The first coordinate of `a ⊕ b` for `(a, b) ∈ L_B × R_B` is `a` ([avron-1996] Thm 4.3). -/
theorem kSup_sup_ofKnow_bot (ha : ofKnow ⊥ ≤ a) (hb : b ≤ ofKnow ⊥) :
    (a ⊔ₖ b) ⊔ ofKnow ⊥ = a :=
  le_antisymm
    (sup_le ((kSup_le_kSup le_rfl (hb.trans ha)).trans_eq (congrArg ofKnow (sup_idem _))) ha)
    ((kLE_iff_le_of_ofKnow_bot_le ha le_sup_right).1 <|
      (congrArg toKnow (sup_eq_left.2 ha)).symm.trans_le
        (sup_kLE_sup (b := a ⊔ₖ b) (c := ofKnow ⊥) le_sup_left (kLE_refl _)))

/-- The second coordinate of `a ⊕ b` for `(a, b) ∈ L_B × R_B` is `b` ([avron-1996] Thm 4.3). -/
theorem kSup_inf_ofKnow_bot (ha : ofKnow ⊥ ≤ a) (hb : b ≤ ofKnow ⊥) :
    (a ⊔ₖ b) ⊓ ofKnow ⊥ = b :=
  (congrArg (fun z ↦ ofKnow z ⊓ (ofKnow ⊥ : B)) (sup_comm (toKnow a) (toKnow b))).trans
    (kSup_sup_ofKnow_bot (B := Bᵒᵈ) (a := toDual b) (b := toDual a) hb ha)

/-- Avron's representation `x ↦ (x ∨ ⊥, x ∧ ⊥)` of an interlaced bilattice as the product of
`L_B = {x | ⊥ ≤ x}` under the truth order and `R_B = {x | x ≤ ⊥}` under its reverse, an
isomorphism of the truth orders ([avron-1996] Thm 4.3). -/
def productIso : B ≃o Set.Ici (ofKnow ⊥ : B) ⊙ (Set.Iic (ofKnow ⊥ : B))ᵒᵈ :=
  Equiv.toOrderIso
    { toFun x := Product.mk ⟨x ⊔ ofKnow ⊥, le_sup_right⟩ (toDual ⟨x ⊓ ofKnow ⊥, inf_le_right⟩)
      invFun p := p.pro.1 ⊔ₖ (ofDual p.con).1
      left_inv := sup_ofKnow_bot_kSup_inf_ofKnow_bot
      right_inv p := Product.ext (Subtype.ext (kSup_sup_ofKnow_bot p.pro.2 (ofDual p.con).2))
        (congrArg toDual (Subtype.ext (kSup_inf_ofKnow_bot p.pro.2 (ofDual p.con).2))) }
    (fun _ _ h ↦ ⟨sup_le_sup_right h _, inf_le_inf_right _ h⟩)
    fun _ _ h ↦ kSup_le_kSup h.1 h.2

/-- The representation is an isomorphism of the knowledge orders too ([avron-1996] Thm 4.3). -/
theorem productIso_kLE_iff {x y : B} : productIso x ≤ₖ productIso y ↔ x ≤ₖ y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨(kLE_iff_le_of_ofKnow_bot_le le_sup_right le_sup_right).1
    (sup_kLE_sup h (kLE_refl _)), (kLE_iff_le_of_le_ofKnow_bot inf_le_right inf_le_right).1
    (inf_kLE_inf h (kLE_refl _))⟩⟩
  rw [← sup_ofKnow_bot_kSup_inf_ofKnow_bot x, ← sup_ofKnow_bot_kSup_inf_ofKnow_bot y]
  exact sup_le_sup (α := Know B)
    ((kLE_iff_le_of_ofKnow_bot_le le_sup_right le_sup_right).2 h.1)
    ((kLE_iff_le_of_le_ofKnow_bot inf_le_right inf_le_right).2 h.2)

/-- Joining with `⊥` distributes over the truth meet, `(x ∧ y) ∨ ⊥ = (x ∨ ⊥) ∧ (y ∨ ⊥)`. -/
theorem inf_sup_ofKnow_bot (x y : B) :
    x ⊓ y ⊔ ofKnow ⊥ = (x ⊔ ofKnow ⊥) ⊓ (y ⊔ ofKnow ⊥) :=
  congrArg (fun p ↦ (p.pro : B)) (productIso.map_inf x y)

end Bounded

end Interlaced

namespace Product

variable {L R : Type*} [Lattice L] [Lattice R] [BoundedOrder L] [BoundedOrder R]

/-- The evidence-for factor of a product is its `L_B`, the pairs `(a, ⊥)`, which makes the factors
of the representation unique ([avron-1996] Thm 4.3). -/
def iciIso : Set.Ici (ofKnow ⊥ : L ⊙ R) ≃o L where
  toFun x := x.1.pro
  invFun a := ⟨mk a ⊥, bot_le, le_rfl⟩
  left_inv x := Subtype.ext (ext rfl (le_bot_iff.1 x.2.2).symm)
  right_inv _ := rfl
  map_rel_iff' {_ y} := ⟨fun h ↦ ⟨h, (le_bot_iff.1 y.2.2).trans_le bot_le⟩, And.left⟩

end Product

end Bilattice
