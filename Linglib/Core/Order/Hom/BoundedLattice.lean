module

public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.PrimeSeparator

/-!
# Bounded lattice homomorphisms from and to the two-element Boolean algebra

The two-element Boolean algebra `Bool` maps into every bounded lattice by
[`BoundedLatticeHom.ofBool`](##BoundedLatticeHom.ofBool), injectively when the lattice is
nontrivial, and every nontrivial bounded distributive lattice [maps back onto
it](##DistribLattice.nonempty_boundedLatticeHom_bool) along a prime ideal. A statement about
finitely many lattice elements that fails in `Bool` therefore fails in every such lattice.
-/

@[expose] public section

variable {F α β : Type*}

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α]

/-- The bounded lattice homomorphism from the two-element Boolean algebra, sending `false` to `⊥`
and `true` to `⊤`. -/
def ofBool : BoundedLatticeHom Bool α where
  toFun b := bif b then ⊤ else ⊥
  map_sup' a b := by cases a <;> cases b <;> simp
  map_inf' a b := by cases a <;> cases b <;> simp
  map_top' := rfl
  map_bot' := rfl

@[simp] theorem ofBool_true : (ofBool true : α) = ⊤ := rfl

@[simp] theorem ofBool_false : (ofBool false : α) = ⊥ := rfl

@[simp] theorem ofBool_apply_bool (b : Bool) : (ofBool : BoundedLatticeHom Bool Bool) b = b := by
  cases b <;> rfl

theorem ofBool_injective [Nontrivial α] :
    Function.Injective (ofBool : BoundedLatticeHom Bool α) := by
  intro a b h
  cases a <;> cases b <;> simp_all

end BoundedLatticeHom

/-- A bounded lattice homomorphism commutes with the maps from `Bool`. -/
@[simp] theorem map_ofBool [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β]
    [FunLike F α β] [BoundedLatticeHomClass F α β] (f : F) (b : Bool) :
    f (BoundedLatticeHom.ofBool b) = BoundedLatticeHom.ofBool b := by
  cases b <;> simp

/-- A nontrivial bounded distributive lattice has a bounded lattice homomorphism to the two-element
Boolean algebra, the map telling whether an element lies outside a prime ideal. -/
theorem DistribLattice.nonempty_boundedLatticeHom_bool [DistribLattice α] [BoundedOrder α]
    [Nontrivial α] : Nonempty (BoundedLatticeHom α Bool) := by
  classical
  obtain ⟨J, hJ, -, hJ'⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal
    (F := Order.PFilter.principal (⊤ : α)) (I := Order.Ideal.principal ⊥)
    (Set.disjoint_left.2 fun x hx hx' ↦ bot_ne_top (α := α) <|
      le_antisymm bot_le
        ((Order.PFilter.mem_principal.1 hx).trans (Order.Ideal.mem_principal.1 hx')))
  have htop : (⊤ : α) ∉ J := fun h ↦
    Set.disjoint_left.1 hJ' (Order.PFilter.mem_principal.2 le_rfl) h
  have hinf (x y : α) : x ⊓ y ∈ J ↔ x ∈ J ∨ y ∈ J :=
    ⟨hJ.mem_or_mem, fun h ↦ h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
  exact ⟨{ toFun := fun x ↦ decide (x ∉ J)
           map_sup' := fun x y ↦ by simp [Order.Ideal.sup_mem_iff]
           map_inf' := fun x y ↦ by simp [hinf, not_or]
           map_top' := by simpa using htop
           map_bot' := by simp }⟩
