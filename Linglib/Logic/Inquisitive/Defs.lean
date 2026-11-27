module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Antichain
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Order.Lattice
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Closure
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Basic.Finite.Prod

/-!
# Inquisitive propositions

An inquisitive proposition over an order of information states `α` is a lower set of states that
contains the least state: the states that resolve it ([roelofsen-2013],
[ciardelli-groenendijk-roelofsen-2018], [ciardelli-2022]). Statements and questions are both
propositions; the questions are the inquisitive ones.

Over the states `Set W` of a set of worlds the least state is the inconsistent state `∅`. The
alternatives `alt P` of a proposition are its maximal resolving states and its informative
content `info P` is the union of its resolving states. A proposition is informative when `info P`
is not every world and inquisitive when `info P` does not itself resolve it. The declarative
`ofSet p` of a set of worlds is resolved by the states included in `p`, the principal ideal
below `p`.

## Main definitions

* `Inquisitive.Proposition α`: the inquisitive propositions over the states `α`.
* `Inquisitive.Proposition.alt`, `Inquisitive.Proposition.info`: alternatives and informative
  content, over sets of worlds.
* `Inquisitive.Proposition.ofSet`: the declarative of a set of worlds.

## Implementation notes

`Proposition α` extends `LowerSet α` and is not a `LowerSet α` because the bottom elements
differ: the least proposition is resolved by the least state alone, while the bottom lower set
is empty.

## References

* [roelofsen-2013]
* [ciardelli-2022]
* [ciardelli-groenendijk-roelofsen-2018]
* [puncochar-2019]
-/

@[expose] public section

universe u

namespace Inquisitive

/-- An inquisitive proposition over states `α` is a lower set of states that contains the least
state: the states that resolve it. -/
structure Proposition (α : Type u) [LE α] [OrderBot α] extends LowerSet α where
  /-- The least state resolves every proposition. -/
  bot_mem' : ⊥ ∈ carrier

namespace Proposition

section Order

variable {α : Type u} [LE α] [OrderBot α]

/-- A proposition coerces to its set of resolving states. -/
instance : SetLike (Proposition α) α where
  coe P := P.carrier
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by congr; exact SetLike.coe_injective h

@[ext]
theorem ext {P Q : Proposition α} (h : ∀ a, a ∈ P ↔ a ∈ Q) : P = Q :=
  SetLike.ext h

theorem bot_mem (P : Proposition α) : ⊥ ∈ P := P.bot_mem'

protected theorem isLowerSet (P : Proposition α) : IsLowerSet (P : Set α) := P.lower'

/-- The proposition resolved by the members of a lower set of states that contains the least
state. -/
def ofLowerSet (s : Set α) (bot_mem : ⊥ ∈ s) (lower : IsLowerSet s) : Proposition α :=
  ⟨⟨s, lower⟩, bot_mem⟩

@[simp, norm_cast] theorem coe_ofLowerSet (s : Set α) (bot_mem : ⊥ ∈ s) (lower : IsLowerSet s) :
    (ofLowerSet s bot_mem lower : Set α) = s := rfl

@[simp] theorem mem_ofLowerSet {s : Set α} {bot_mem : ⊥ ∈ s} {lower : IsLowerSet s} {a : α} :
    a ∈ ofLowerSet s bot_mem lower ↔ a ∈ s := Iff.rfl

end Order

variable {W : Type u}

/-- The inconsistent state resolves every proposition. -/
theorem empty_mem (P : Proposition (Set W)) : ∅ ∈ P := P.bot_mem

/-- The alternatives of a proposition are its maximal resolving states. -/
def alt (P : Proposition (Set W)) : Set (Set W) :=
  {p | p ∈ P ∧ ∀ q ∈ P, p ⊆ q → p = q}

theorem mem_of_mem_alt {P : Proposition (Set W)} {p : Set W} (h : p ∈ alt P) : p ∈ P := h.1

/-- The informative content of a proposition is the union of its resolving states. -/
def info (P : Proposition (Set W)) : Set W :=
  ⋃₀ (P : Set (Set W))

/-- A proposition is informative if its informative content excludes some world. -/
def IsInformative (P : Proposition (Set W)) : Prop :=
  info P ≠ Set.univ

/-- A proposition is inquisitive if its informative content does not resolve it. -/
def IsInquisitive (P : Proposition (Set W)) : Prop :=
  info P ∉ P

/-- The informative content of a proposition resolves it iff the proposition is not inquisitive.
Its resolving states are then a principal ideal ([puncochar-2019]), see
`info_mem_iff_eq_ofSet_info`. -/
theorem info_mem_iff_not_isInquisitive (P : Proposition (Set W)) :
    P.info ∈ P ↔ ¬ P.IsInquisitive :=
  not_not.symm

theorem mem_info_iff_singleton_mem (P : Proposition (Set W)) (w : W) :
    w ∈ P.info ↔ ({w} : Set W) ∈ P :=
  ⟨fun ⟨_, hq, hwq⟩ ↦ P.isLowerSet (Set.singleton_subset_iff.2 hwq) hq, fun h ↦ ⟨{w}, h, rfl⟩⟩

theorem subset_info_of_mem {P : Proposition (Set W)} {q : Set W} (h : q ∈ P) : q ⊆ P.info :=
  Set.subset_sUnion_of_mem h

/-! ### Declaratives -/

/-- The declarative of `p` is resolved by the states included in `p`, the principal ideal below
`p`, as `Filter.principal` is the principal filter. -/
def ofSet (p : Set W) : Proposition (Set W) :=
  ofLowerSet {q | q ⊆ p} (Set.empty_subset p) fun _ _ hba ha ↦ hba.trans ha

@[simp] theorem mem_ofSet {p q : Set W} :
    q ∈ ofSet p ↔ q ⊆ p := Iff.rfl

@[simp] theorem info_ofSet (p : Set W) : (ofSet p).info = p :=
  Set.Subset.antisymm (Set.sUnion_subset fun _ hq ↦ hq) fun _ hw ↦ ⟨p, Set.Subset.refl p, hw⟩

theorem info_mem_ofSet (p : Set W) : (ofSet p).info ∈ ofSet p := by
  rw [info_ofSet]
  exact Set.Subset.refl p

theorem not_isInquisitive_ofSet (p : Set W) : ¬ (ofSet p).IsInquisitive :=
  fun h ↦ h (info_mem_ofSet p)

end Proposition

end Inquisitive
