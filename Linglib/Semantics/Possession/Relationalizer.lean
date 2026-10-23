module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Relational nouns and the relationalizer

A sortal noun such as *cloud* denotes a property. A relational noun such as *sister* denotes a
property for each possessor: `R x` is the property of being a sister of `x`. Following
[barker-2011], two type shifters convert between the two kinds of noun.

* The relationalizer `π` adds a possessor to a sortal noun through a possession relation `R`,
  often supplied by context: `π cloud R x` is the property of being a cloud that `x` stands in
  `R` to, the meaning of *cloud* in *John's cloud*.
* Barker's detransitivizer `Ex` removes the possessor of a relational noun: `⨆ x, R x` is the
  property of being an `R` of someone, as *sister* in *a sister*. Adamson's alienator, Partee
  and Borschev's first projection (the sortal part of a relational noun) and the range operator
  of Hanink and Koontz-Garboden are this operation.

Properties may live in any lattice, so the same definitions serve plain predicates `κ → Prop`
and situation-relative ones `κ → σ → Prop`: `π` conjoins the noun with the relation, and `Ex`
closes off the possessor existentially.

## Main definitions

* `Possession.π`: the relationalizer, `π P R x = P ⊓ R x`.
* `Possession.dom`: the possessors of a `P`, those who stand in `R` to some `P`.

## Main statements

* `Possession.π_iSup_self`: relationalizing *someone's sister* by the sister relation gives back
  *sister*, so the inherent reading of *John's sister* is the free-relation reading with the
  noun's own relation filled in.
* `Possession.iSup_π`: removing the possessor of `π P R` leaves the `P`s someone stands in `R` to.

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

/-- Barker's relationalizer: `π P R x` is the property of being a `P` that `x` stands in `R`
to. With `P` = *cloud* and `R` a relation supplied by context, it is the meaning of *cloud* in
*John's cloud*. -/
def π [Min α] (P : α) (R : ι → α) : ι → α := fun x ↦ P ⊓ R x

theorem π_apply [Min α] (P : α) (R : ι → α) (x : ι) : π P R x = P ⊓ R x := rfl

/-- Relationalizing the noun true of everything yields the relation itself. -/
@[simp] theorem π_top [SemilatticeInf α] [OrderTop α] (R : ι → α) : π ⊤ R = R :=
  funext fun _ ↦ top_inf_eq _

/-- Removing the possessor of a relationalized noun leaves the `P`s that someone stands in `R`
to. -/
theorem iSup_π [Order.Frame α] (P : α) (R : ι → α) : ⨆ x, π P R x = P ⊓ ⨆ x, R x :=
  (inf_iSup_eq P R).symm

/-- Removing the possessor of a relational noun and then relationalizing the result by the noun's
own relation gives back the noun: a sister of someone who is `x`'s sister is `x`'s sister. -/
@[simp] theorem π_iSup_self [CompleteLattice α] (R : ι → α) : π (⨆ x, R x) R = R :=
  funext fun x ↦ inf_eq_right.2 (le_iSup R x)

instance {P : κ → Prop} {R : ι → κ → Prop} [DecidablePred P] [∀ x, DecidablePred (R x)]
    (x : ι) : DecidablePred (π P R x) :=
  fun y ↦ inferInstanceAs (Decidable (P y ∧ R x y))

/-! ### Possessors -/

/-- The possessors of a `P`: the individuals that stand in `R` to some `P`. *John's dogs bark*
requires John to be among the possessors of a dog. -/
def dom (P : κ → Prop) (R : ι → κ → Prop) (x : ι) : Prop := ∃ y, P y ∧ R x y

instance [Fintype κ] {P : κ → Prop} {R : ι → κ → Prop} [DecidablePred P]
    [∀ x, DecidablePred (R x)] : DecidablePred (dom P R) :=
  fun x ↦ inferInstanceAs (Decidable (∃ y, P y ∧ R x y))

/-- When the possessed noun is `R` with its possessor removed and the possession relation is `R`
itself, `x` possesses one exactly when `x` stands in `R` to something: `x` has *a sister*, in
the sense of someone's sister, exactly when `x` has a sister. -/
theorem dom_iSup_self (R : ι → κ → Prop) (x : ι) : dom (⨆ x, R x) R x ↔ ∃ y, R x y :=
  iff_of_eq (congrArg (fun S : ι → κ → Prop ↦ ∃ y, S x y) (π_iSup_self R))

end Possession
