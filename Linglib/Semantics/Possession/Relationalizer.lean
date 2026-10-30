module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Relational nouns and the relationalizer

A relational noun such as *sister* denotes a family `R : ι → α` of properties indexed by
possessors, and a sortal noun such as *cloud* denotes a single property `P : α`. This file
defines the relationalizer `π`, which makes a sortal noun relational by conjoining it with a
possession relation, and the possessors `dom` of a noun under a relation.

## Main definitions

* `Possession.π`: the relationalizer, `π P R x = P ⊓ R x`.
* `Possession.dom`: the possessors of `P` under `R`.

## Main statements

* `Possession.π_iSup_self`: relationalizing `⨆ x, R x` by `R` gives back `R`.
* `Possession.iSup_π`: `⨆ x, π P R x = P ⊓ ⨆ x, R x`.

## Implementation notes

Properties are taken in a lattice, so the definitions apply both to predicates `κ → Prop` and to
situation-relative predicates `κ → σ → Prop`. The converse shift, from a relational noun to a
sortal one, is the supremum `⨆ x, R x`: Barker's detransitivizer, Adamson's alienator, Partee and
Borschev's first projection and Hanink and Koontz-Garboden's range operator.

## References

* [barker-2011]
* [adamson-2024]
* [partee-borschev-2003]
* [hanink-koontz-garboden-2025]
* [peters-westerstahl-2006]
-/

@[expose] public section

namespace Possession

variable {ι κ α : Type*}

/-! ### The relationalizer -/

/-- The relationalizer `π P R x` holds of the `P`s to which `x` stands in `R`, as *cloud* in *John's
cloud*. -/
def π [Min α] (P : α) (R : ι → α) : ι → α := fun x ↦ P ⊓ R x

theorem π_apply [Min α] (P : α) (R : ι → α) (x : ι) : π P R x = P ⊓ R x := rfl

@[simp] theorem π_top [SemilatticeInf α] [OrderTop α] (R : ι → α) : π ⊤ R = R :=
  funext fun _ ↦ top_inf_eq _

theorem iSup_π [Order.Frame α] (P : α) (R : ι → α) : ⨆ x, π P R x = P ⊓ ⨆ x, R x :=
  (inf_iSup_eq P R).symm

@[simp] theorem π_iSup_self [CompleteLattice α] (R : ι → α) : π (⨆ x, R x) R = R :=
  funext fun x ↦ inf_eq_right.2 (le_iSup R x)

instance {P : κ → Prop} {R : ι → κ → Prop} [DecidablePred P] [∀ x, DecidablePred (R x)]
    (x : ι) : DecidablePred (π P R x) :=
  fun y ↦ inferInstanceAs (Decidable (P y ∧ R x y))

instance {P : Set κ} {R : ι → κ → Prop} [DecidablePred (· ∈ P)] [∀ x, DecidablePred (R x)]
    (x : ι) : DecidablePred (· ∈ π P R x) :=
  fun y ↦ inferInstanceAs (Decidable (y ∈ P ∧ R x y))

/-! ### Possessors -/

/-- The possessors of `P` under `R` are the `x` that stand in `R` to some `P`. -/
def dom (P : κ → Prop) (R : ι → κ → Prop) (x : ι) : Prop := ∃ y, P y ∧ R x y

instance [Fintype κ] {P : κ → Prop} {R : ι → κ → Prop} [DecidablePred P]
    [∀ x, DecidablePred (R x)] : DecidablePred (dom P R) :=
  fun x ↦ inferInstanceAs (Decidable (∃ y, P y ∧ R x y))

instance [Fintype κ] {P : Set κ} {R : ι → κ → Prop} [DecidablePred (· ∈ P)]
    [∀ x, DecidablePred (R x)] : DecidablePred (dom P R) :=
  fun x ↦ inferInstanceAs (Decidable (∃ y, y ∈ P ∧ R x y))

theorem dom_iSup_self (R : ι → κ → Prop) (x : ι) : dom (⨆ x, R x) R x ↔ ∃ y, R x y :=
  iff_of_eq (congrArg (fun S : ι → κ → Prop ↦ ∃ y, S x y) (π_iSup_self R))

end Possession
