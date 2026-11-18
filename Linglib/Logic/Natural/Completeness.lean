/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Hom.BoundedLattice
public import Linglib.Logic.Natural.Projection
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Basic.Rel
public import Mathlib.Order.Concept
public import Mathlib.Order.Interval.Set.Basic

/-!
# Completeness of the projectivity calculus

The join, projection and composition tables of natural logic are sound, and this file proves that
they cannot be improved. A relation is [a formal concept](##NaturalLogic.Relation.toConcept) of
the incidence between constraints and pairs of elements, as a signature is [of the
incidence](##NaturalLogic.ProjectivitySignature.toConcept) between properties and functions, and
the join, projection and composition assert [the polar of what the semantics
relates](##NaturalLogic.Relation.coe_constraints_mul). On a Boolean algebra the join [is relational
composition](##NaturalLogic.Relation.toSetRel_mul). The order on relations is
[implication](##NaturalLogic.Relation.le_iff_forall_holds) in every nontrivial bounded lattice, and
the join is [the least sound chaining](##NaturalLogic.Relation.isLeast_join) in every nontrivial
distributive one, [even among denotations other than `⊥` and
`⊤`](##NaturalLogic.Relation.isLeast_join_Ioo). Between nontrivial distributive lattices each
projection is [least](##NaturalLogic.ProjectivitySignature.isLeast_project) for its function class,
refinement of signatures is [inclusion of
classes](##NaturalLogic.ProjectivitySignature.le_iff_forall_holdsFor), and composition is [least for
composites](##NaturalLogic.ProjectivitySignature.isLeast_compose). Two elements stand in a strongest
relation [exactly when neither is `⊥` or `⊤`](##NaturalLogic.Relation.exists_isLeast_holds_iff), and
the constraints such elements can satisfy together are [those of the seven
relations](##NaturalLogic.Relation.mem_range_constraints_iff).

## Implementation notes

* Countermodels are computed on `Bool` and carried to other lattices: `Bool` embeds in a bounded
  lattice as `⊥` and `⊤`, and a nontrivial bounded distributive lattice maps back onto `Bool` along
  a [prime ideal](##DistribLattice.nonempty_boundedLatticeHom_bool). The function-class
  theorems need distributivity for this map, since the five-element modular lattice `M₃` has no
  morphism to `Bool` and its morphism class into `Bool` is empty.
* The nine signatures do not classify the property profiles a function can have: the constant-`⊤`
  function is monotone, antitone, additive and anti-multiplicative at once, which is no signature's
  property set. Each signature is least for its own projection row.

## TODO

* The countermodels for projection and composition use `⊥` and `⊤` as arguments. Arguments other
  than these need functions on the eight-element Boolean algebra, too many to enumerate.
* `Relation.isLeast_join_Ioo` and `Relation.le_iff_forall_holds_Ioo` are stated on `Finset (Fin 3)`
  and hold in any distributive lattice it embeds in.

## References

* [icard-2012]
* [maccartney-manning-2009]
-/

public section

namespace NaturalLogic

variable {α β γ : Type*}

open BoundedLatticeHom (ofBool ofBool_injective)
open scoped SetRel

/-! ### Relations as formal concepts

A constraint holds of some pairs of elements and not of others, and a relation is a set of
constraints together with the pairs they all hold of. Each determines the other: the pairs are the
polar of the constraints, and the constraints the polar of the pairs. -/

namespace Relation

section Lattice

variable [Lattice α] [BoundedOrder α]

variable (α) in
/-- The pairs of elements of a bounded lattice that a constraint holds of. -/
@[expose] def Atom.toSetRel (a : Atom) : SetRel α α := {(x, y) | a.Holds x y}

variable (α) in
/-- The pairs of elements of a bounded lattice that a relation holds of. -/
@[expose] def toSetRel (R : Relation) : SetRel α α := {(x, y) | R.Holds x y}

@[simp] theorem Atom.mem_toSetRel {a : Atom} {x y : α} : x ~[a.toSetRel α] y ↔ a.Holds x y :=
  Iff.rfl

@[simp] theorem mem_toSetRel {R : Relation} {x y : α} : x ~[R.toSetRel α] y ↔ R.Holds x y :=
  Iff.rfl

variable (α) in
/-- The incidence of the atomic constraints on pairs of elements of a bounded lattice. -/
abbrev Atom.incidence : Atom → α × α → Prop := fun a p ↦ p ∈ a.toSetRel α

/-- The pairs a relation holds of are the polar of its constraints. -/
theorem toSetRel_eq_upperPolar (R : Relation) :
    R.toSetRel α = upperPolar (Atom.incidence α) ↑R.constraints :=
  Set.ext fun ⟨_, _⟩ ↦ holds_iff

variable [Nontrivial α]

/-- The constraints of a relation are the polar of the pairs it holds of: a relation asserts every
constraint it guarantees. -/
theorem coe_constraints_eq_lowerPolar (R : Relation) :
    (↑R.constraints : Set Atom) = lowerPolar (Atom.incidence α) (R.toSetRel α) := by
  refine Set.ext fun a ↦ ⟨fun ha ⟨_, _⟩ hp ↦ holds_iff.1 hp a ha, fun h ↦ ?_⟩
  by_contra ha
  have counter : ∀ (R : Relation) (a : Atom), a ∉ R.constraints →
      ∃ x y : Bool, R.Holds x y ∧ ¬ a.Holds x y := by
    decide
  obtain ⟨x, y, hR, ha'⟩ := counter R a ha
  exact ha' ((Atom.holds_map_iff ofBool_injective).1
    (h (b := (ofBool x, ofBool y)) ((holds_map_iff ofBool_injective).2 hR)))

variable (α) in
/-- A relation as a formal concept of the incidence, its constraints and the pairs it holds
of. -/
@[expose, simps]
def toConcept (R : Relation) : Concept Atom (α × α) (Atom.incidence α) where
  extent := ↑R.constraints
  intent := R.toSetRel α
  upperPolar_extent := (toSetRel_eq_upperPolar R).symm
  lowerPolar_intent := (coe_constraints_eq_lowerPolar R).symm

/-- A stronger relation is a larger concept. -/
theorem toConcept_le_toConcept_iff {R S : Relation} : S.toConcept α ≤ R.toConcept α ↔ R ≤ S := by
  rw [← Concept.extent_subset_extent_iff, extent_toConcept, extent_toConcept,
    Finset.coe_subset, le_iff]

/-- The order on relations is implication: `R ≤ S` exactly when `R` entails `S` in a nontrivial
bounded lattice, [icard-2012]'s definition of ≪. -/
theorem le_iff_forall_holds {R S : Relation} :
    R ≤ S ↔ ∀ x y : α, R.Holds x y → S.Holds x y := by
  rw [← toConcept_le_toConcept_iff (α := α), ← Concept.intent_subset_intent_iff]
  exact ⟨fun h x y hR ↦ h (a := (x, y)) hR, fun h ⟨x, y⟩ hp ↦ h x y hp⟩

end Lattice

/-- The constraints of the join are the polar of the pairs that `R` followed by `S` relates, in
every nontrivial bounded distributive lattice: the atom rule derives every constraint that chaining
guarantees (`Relation.mem_constraints_mul`). -/
theorem coe_constraints_mul [DistribLattice α] [BoundedOrder α] [Nontrivial α] (R S : Relation) :
    (↑(R * S).constraints : Set Atom) =
      lowerPolar (Atom.incidence α) (R.toSetRel α ○ S.toSetRel α) := by
  refine Set.ext fun a ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ha ⟨x, z⟩ ⟨y, hR, hS⟩
    exact holds_iff.1 (Holds.join hR hS) a ha
  by_contra ha
  have counter : ∀ (R S : Relation) (a : Atom), a ∉ (R * S).constraints →
      ∃ x y z : Bool, R.Holds x y ∧ S.Holds y z ∧ ¬ a.Holds x z := by
    decide
  obtain ⟨x, y, z, hR, hS, ha'⟩ := counter R S a ha
  exact ha' ((Atom.holds_map_iff ofBool_injective).1 (h (b := (ofBool x, ofBool z))
    ⟨ofBool y, (holds_map_iff ofBool_injective).2 hR, (holds_map_iff ofBool_injective).2 hS⟩))

end Relation

/-! ### The order and the join -/

namespace Relation

section Lattice

variable [Lattice α] [BoundedOrder α]

/-- The order on relations is already implication between elements other than `⊥` and `⊤`, the
denotations [maccartney-manning-2009] admit, on the eight-element Boolean algebra. -/
theorem le_iff_forall_holds_Ioo {R S : Relation} :
    R ≤ S ↔ ∀ x y : Finset (Fin 3), x ∈ Set.Ioo ⊥ ⊤ → y ∈ Set.Ioo ⊥ ⊤ →
      R.Holds x y → S.Holds x y := by
  refine ⟨fun h _ _ _ _ hR ↦ hR.of_le h, fun h ↦ ?_⟩
  by_contra hle
  have counter : ∀ R S : Relation, ¬ R ≤ S → ∃ x y : Finset (Fin 3),
      (x ∈ Set.Ioo ⊥ ⊤ ∧ y ∈ Set.Ioo ⊥ ⊤) ∧ R.Holds x y ∧ ¬ S.Holds x y := by
    decide
  obtain ⟨x, y, ⟨hx, hy⟩, hR, hS⟩ := counter R S hle
  exact hS (h x y hx hy hR)

end Lattice

/-- `R * S` is the strongest relation that `R` followed by `S` guarantees, in every nontrivial
bounded distributive lattice ([icard-2012]'s definition of the join). -/
theorem isLeast_join [DistribLattice α] [BoundedOrder α] [Nontrivial α] (R S : Relation) :
    IsLeast {T : Relation | ∀ x y z : α, R.Holds x y → S.Holds y z → T.Holds x z} (R * S) :=
  ⟨fun _ _ _ hR hS ↦ hR.join hS, fun _ hT ↦ le_iff.2 fun a ha ↦
    Finset.mem_coe.1 <| (coe_constraints_mul (α := α) R S).symm ▸ fun ⟨x, z⟩ ⟨y, hR, hS⟩ ↦
      holds_iff.1 (hT x y z hR hS) a ha⟩

/-- The join stays least when the three denotations are other than `⊥` and `⊤`, as
[maccartney-manning-2009] require of denotations, on the eight-element Boolean algebra. -/
theorem isLeast_join_Ioo (R S : Relation) :
    IsLeast {T : Relation | ∀ x y z : Finset (Fin 3), x ∈ Set.Ioo ⊥ ⊤ → y ∈ Set.Ioo ⊥ ⊤ →
      z ∈ Set.Ioo ⊥ ⊤ → R.Holds x y → S.Holds y z → T.Holds x z} (R * S) := by
  refine ⟨fun _ _ _ _ _ _ hR hS ↦ hR.join hS, fun T hT ↦ ?_⟩
  by_contra hle
  have counter : ∀ R S T : Relation, ¬ R * S ≤ T →
      ∃ x ∈ Set.Ioo (⊥ : Finset (Fin 3)) ⊤, ∃ y ∈ Set.Ioo (⊥ : Finset (Fin 3)) ⊤,
        ∃ z ∈ Set.Ioo (⊥ : Finset (Fin 3)) ⊤, R.Holds x y ∧ S.Holds y z ∧ ¬ T.Holds x z := by
    decide
  obtain ⟨x, hx, y, hy, z, hz, hR, hS, hT'⟩ := counter R S T hle
  exact hT' (hT x y z hx hy hz hR hS)

/-! ### Relations as partial bijections of the polarities -/

/-- The constraints of a relation are a partial bijection of the polarities: no two of them take
the first argument with the same polarity, nor the second. -/
theorem injOn_src_constraints (R : Relation) : Set.InjOn Atom.src R.constraints := by
  have : ∀ R : Relation, ∀ a ∈ R.constraints, ∀ b ∈ R.constraints, a.src = b.src → a = b := by
    decide
  exact fun a ha b hb ↦ this R a ha b hb

theorem injOn_tgt_constraints (R : Relation) : Set.InjOn Atom.tgt R.constraints := by
  have : ∀ R : Relation, ∀ a ∈ R.constraints, ∀ b ∈ R.constraints, a.tgt = b.tgt → a = b := by
    decide
  exact fun a ha b hb ↦ this R a ha b hb

/-- The seven relations are the partial bijections of the two polarities: a set of constraints is
a relation's exactly when no two of its members agree on the polarity of either argument. -/
theorem mem_range_constraints_iff_injOn {s : Finset Atom} :
    s ∈ Set.range constraints ↔ Set.InjOn Atom.src s ∧ Set.InjOn Atom.tgt s := by
  have : ∀ s : Finset Atom, (∃ R : Relation, R.constraints = s) ↔
      (∀ a ∈ s, ∀ b ∈ s, a.src = b.src → a = b) ∧ ∀ a ∈ s, ∀ b ∈ s, a.tgt = b.tgt → a = b := by
    decide
  exact this s

/-! ### The join is relational composition

An atomic constraint is an inequality between `x` or its complement and `y` or its complement, an
arrow from one of the two polarities of `x` to one of `y`. Chained constraints compose when the
polarity of the middle term agrees, which is the atom rule, and the constraints of a relation form
a partial bijection of the two polarities. -/

section BooleanAlgebra

variable [BooleanAlgebra α]

/-- On a Boolean algebra the join is relational composition: `R * S` holds of `x` and `z` exactly
when some `y` has `x R y` and `y S z`. The constraints bound `y` and its complement from both sides,
and the bounds are compatible when `R * S` holds. The middle term may be `⊥` or `⊤`; among other
elements the join is only the least sound relation (`Relation.isLeast_join_Ioo`). -/
theorem toSetRel_mul (R S : Relation) :
    (R * S).toSetRel α = R.toSetRel α ○ S.toSetRel α := by
  ext ⟨x, z⟩
  refine ⟨fun h ↦ ?_, fun ⟨y, hR, hS⟩ ↦ Holds.join hR hS⟩
  have H : ∀ a ∈ R.constraints, ∀ b ∈ S.constraints, a.tgt = b.src →
      Polarity.complHom a.src x ≤ Polarity.complHom b.tgt z := by
    intro a ha b hb hab
    have := holds_iff.1 h _ (mem_constraints_mul.2 ⟨a, ha, b, hb, ite_eq_left hab⟩)
    rwa [Atom.holds_iff_complHom_le, Atom.src_ofPolarities, Atom.tgt_ofPolarities] at this
  let l : Atom → α := fun a ↦ match a.tgt with
    | .positive => Polarity.complHom a.src x
    | .negative => ⊥
  let u : Atom → α := fun b ↦ match b.src with
    | .positive => ⊥
    | .negative => (Polarity.complHom b.tgt z)ᶜ
  refine ⟨R.constraints.sup l ⊔ S.constraints.sup u,
    holds_iff.2 fun a ha ↦ Atom.holds_iff_complHom_le.2 ?_,
    holds_iff.2 fun b hb ↦ Atom.holds_iff_complHom_le.2 ?_⟩
  · cases hat : a.tgt
    · exact le_sup_of_le_left (by simpa [l, hat] using Finset.le_sup (f := l) ha)
    · change _ ≤ (_)ᶜ
      rw [le_compl_comm]
      refine sup_le (Finset.sup_le fun a' ha' ↦ ?_) (Finset.sup_le fun b hb ↦ ?_)
      · cases hat' : a'.tgt
        · have hne : a'.src ≠ a.src := fun h ↦ by
            rw [injOn_src_constraints R ha' ha h, hat] at hat'
            exact Polarity.noConfusion hat'
          simpa [l, hat'] using (Polarity.complHom_of_ne hne x).le
        · simp [l, hat']
      · cases hbs : b.src
        · simp [u, hbs]
        · simpa [u, hbs] using H a ha b hb (hat.trans hbs.symm)
  · cases hbs : b.src
    · refine sup_le (Finset.sup_le fun a ha ↦ ?_) (Finset.sup_le fun b' hb' ↦ ?_)
      · cases hat : a.tgt
        · simpa [l, hat] using H a ha b hb (hat.trans hbs.symm)
        · simp [l, hat]
      · cases hbs' : b'.src
        · simp [u, hbs']
        · have hne : b.tgt ≠ b'.tgt := fun h ↦ by
            rw [injOn_tgt_constraints S hb hb' h, hbs'] at hbs
            exact Polarity.noConfusion hbs
          simpa [u, hbs'] using (Polarity.complHom_of_ne hne z).ge
    · change (_)ᶜ ≤ _
      rw [compl_le_iff_compl_le]
      exact le_sup_of_le_right (by simpa [u, hbs] using Finset.le_sup (f := u) hb)

/-- The identity of the join holds of equal elements. -/
theorem toSetRel_one : (1 : Relation).toSetRel α = SetRel.id := rfl

end BooleanAlgebra

/-! ### Why seven relations -/

section Lattice

variable [Lattice α] [BoundedOrder α]

/-- The constraints that hold of `x` and `y` take `x` with different polarities exactly when `x`
is neither `⊥` nor `⊤`: at `⊥` both `x ≤ y` and disjointness hold, at `⊤` both `y ≤ x` and
codisjointness. -/
theorem injOn_src_setOf_holds_iff {x y : α} :
    Set.InjOn Atom.src {a | a.Holds x y} ↔ x ∈ Set.Ioo ⊥ ⊤ := by
  refine ⟨fun h ↦ ⟨bot_lt_iff_ne_bot.2 ?_, lt_top_iff_ne_top.2 ?_⟩, fun ⟨h0, h1⟩ a ha b hb hab ↦ ?_⟩
  · rintro rfl
    exact absurd (h (show Atom.le ∈ {a | a.Holds ⊥ y} from bot_le)
      (show Atom.disjoint ∈ {a | a.Holds ⊥ y} from disjoint_bot_left) rfl)
      (by decide)
  · rintro rfl
    exact absurd (h (show Atom.ge ∈ {a | a.Holds ⊤ y} from le_top)
      (show Atom.codisjoint ∈ {a | a.Holds ⊤ y} from codisjoint_top_left) rfl)
      (by decide)
  · cases a <;> cases b <;> first
      | rfl
      | exact absurd hab (by decide)
      | exact (h0.ne' (Disjoint.eq_bot_of_le hb ha)).elim
      | exact (h0.ne' (Disjoint.eq_bot_of_le ha hb)).elim
      | exact (h1.ne (Codisjoint.eq_top_of_le hb ha)).elim
      | exact (h1.ne (Codisjoint.eq_top_of_le ha hb)).elim

/-- The constraints that hold of `x` and `y` take `y` with different polarities exactly when `y`
is neither `⊥` nor `⊤`. -/
theorem injOn_tgt_setOf_holds_iff {x y : α} :
    Set.InjOn Atom.tgt {a | a.Holds x y} ↔ y ∈ Set.Ioo ⊥ ⊤ := by
  refine ⟨fun h ↦ ⟨bot_lt_iff_ne_bot.2 ?_, lt_top_iff_ne_top.2 ?_⟩, fun ⟨h0, h1⟩ a ha b hb hab ↦ ?_⟩
  · rintro rfl
    exact absurd (h (show Atom.ge ∈ {a | a.Holds x ⊥} from bot_le)
      (show Atom.disjoint ∈ {a | a.Holds x ⊥} from disjoint_bot_right) rfl)
      (by decide)
  · rintro rfl
    exact absurd (h (show Atom.le ∈ {a | a.Holds x ⊤} from le_top)
      (show Atom.codisjoint ∈ {a | a.Holds x ⊤} from codisjoint_top_right) rfl)
      (by decide)
  · cases a <;> cases b <;> first
      | rfl
      | exact absurd hab (by decide)
      | exact (h0.ne' (Disjoint.eq_bot_of_ge hb ha)).elim
      | exact (h0.ne' (Disjoint.eq_bot_of_ge ha hb)).elim
      | exact (h1.ne (Codisjoint.eq_top_of_ge hb ha)).elim
      | exact (h1.ne (Codisjoint.eq_top_of_ge ha hb)).elim

/-- Constraints that two elements other than `⊥` and `⊤` satisfy together are among those of a
single relation. -/
theorem mem_range_constraints_of_holds {s : Finset Atom} {x y : α}
    (h : ∀ a ∈ s, a.Holds x y) (hx : x ∈ Set.Ioo ⊥ ⊤) (hy : y ∈ Set.Ioo ⊥ ⊤) :
    s ∈ Set.range constraints :=
  mem_range_constraints_iff_injOn.2
    ⟨((injOn_src_setOf_holds_iff (y := y)).2 hx).mono fun a ha ↦ h a ha,
      ((injOn_tgt_setOf_holds_iff (x := x)).2 hy).mono fun a ha ↦ h a ha⟩

/-- Two elements of a bounded lattice stand in a strongest relation exactly when neither is `⊥` or
`⊤` ([icard-2012]'s Lemma 1.3 with the converse remarked under it): the strongest relation asserts
the constraints that hold, and these are a relation's when they form a partial bijection of the
polarities. -/
theorem exists_isLeast_holds_iff {x y : α} :
    (∃ R : Relation, IsLeast {S : Relation | S.Holds x y} R) ↔
      x ∈ Set.Ioo ⊥ ⊤ ∧ y ∈ Set.Ioo ⊥ ⊤ := by
  classical
  rw [← injOn_src_setOf_holds_iff (y := y), ← injOn_tgt_setOf_holds_iff (x := x)]
  refine ⟨fun ⟨R, hR⟩ ↦ ?_, fun h ↦ ?_⟩
  · have : {a : Atom | a.Holds x y} = ↑R.constraints := Set.ext fun a ↦
      ⟨fun ha ↦ mem_constraints_iff_le.2 (hR.2 (holds_toRelation.2 ha)),
        fun ha ↦ holds_iff.1 hR.1 a ha⟩
    rw [this]
    exact ⟨injOn_src_constraints R, injOn_tgt_constraints R⟩
  · obtain ⟨R, hR⟩ := (mem_range_constraints_iff_injOn
      (s := Finset.univ.filter fun a ↦ a.Holds x y)).2 (by simpa using h)
    refine ⟨R, holds_iff.2 fun a ha ↦ ?_, fun S hS ↦ le_iff.2 fun a ha ↦ ?_⟩
    · rw [hR] at ha
      exact (Finset.mem_filter.1 ha).2
    · rw [hR]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, holds_iff.1 hS a ha⟩

end Lattice

section BooleanAlgebra

variable [BooleanAlgebra α]

/-- In a Boolean algebra with an element other than `⊥` and `⊤`, every relation holds of two such
elements: the element and itself, or the element and its complement. -/
theorem exists_mem_Ioo_holds (h : (Set.Ioo (⊥ : α) ⊤).Nonempty) (R : Relation) :
    ∃ x ∈ Set.Ioo (⊥ : α) ⊤, ∃ y ∈ Set.Ioo (⊥ : α) ⊤, R.Holds x y := by
  obtain ⟨z, hz⟩ := h
  have hz' : zᶜ ∈ Set.Ioo (⊥ : α) ⊤ :=
    ⟨bot_lt_iff_ne_bot.2 (compl_eq_bot.not.2 hz.2.ne),
      lt_top_iff_ne_top.2 (compl_eq_top.not.2 hz.1.ne')⟩
  cases R with
  | equiv => exact ⟨z, hz, z, hz, rfl⟩
  | forward | reverse => exact ⟨z, hz, z, hz, le_rfl⟩
  | negation => exact ⟨z, hz, zᶜ, hz', isCompl_compl⟩
  | alternation => exact ⟨z, hz, zᶜ, hz', disjoint_compl_right⟩
  | cover => exact ⟨z, hz, zᶜ, hz', isCompl_compl.codisjoint⟩
  | independent => exact ⟨z, hz, z, hz, trivial⟩

/-- Of the sixteen conjunctions of atomic constraints, the seven relations are those that two
elements other than `⊥` and `⊤` can satisfy, [maccartney-manning-2009]'s proviso on denotations. -/
theorem mem_range_constraints_iff (h : (Set.Ioo (⊥ : α) ⊤).Nonempty) {s : Finset Atom} :
    s ∈ Set.range constraints ↔
      ∃ x ∈ Set.Ioo (⊥ : α) ⊤, ∃ y ∈ Set.Ioo (⊥ : α) ⊤, ∀ a ∈ s, a.Holds x y := by
  constructor
  · rintro ⟨R, rfl⟩
    obtain ⟨x, hx, y, hy, hR⟩ := exists_mem_Ioo_holds h R
    exact ⟨x, hx, y, hy, holds_iff.1 hR⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact mem_range_constraints_of_holds h hx hy

end BooleanAlgebra

end Relation

/-! ### Signatures as formal concepts

A property holds of some functions and not of others, and a signature is a set of properties
together with the functions that have them all. Countermodels on `Bool` are carried between
nontrivial bounded distributive lattices along bounded lattice homomorphisms, which are morphisms
and so keep every property under composition. -/

namespace ProjectivitySignature

section Lattice

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- A morphism after a function with a property has the property. -/
theorem Property.HoldsFor.addMult_comp {p : Property} {f : β → γ} {g : α → β}
    (hf : ProjectivitySignature.HoldsFor .addMult f) (hg : p.HoldsFor g) : p.HoldsFor (f ∘ g) := by
  cases p <;> first
    | exact Property.HoldsFor.compose (by rfl) (hf .monotone (by decide)) hg
    | exact Property.HoldsFor.compose (by rfl) (hf .additive (by decide)) hg
    | exact Property.HoldsFor.compose (by rfl) (hf .multiplicative (by decide)) hg

/-- A function with a property after a morphism has the property. -/
theorem Property.HoldsFor.comp_addMult {p : Property} {f : β → γ} {g : α → β}
    (hf : p.HoldsFor f) (hg : ProjectivitySignature.HoldsFor .addMult g) : p.HoldsFor (f ∘ g) := by
  cases p <;> first
    | exact Property.HoldsFor.compose (by rfl) hf (hg .monotone (by decide))
    | exact Property.HoldsFor.compose (by rfl) hf (hg .additive (by decide))
    | exact Property.HoldsFor.compose (by rfl) hf (hg .multiplicative (by decide))

/-- A morphism after a σ-function is a σ-function. -/
theorem HoldsFor.addMult_comp {σ : ProjectivitySignature} {f : β → γ} {g : α → β}
    (hf : HoldsFor .addMult f) (hg : σ.HoldsFor g) : σ.HoldsFor (f ∘ g) :=
  fun p hp ↦ Property.HoldsFor.addMult_comp hf (hg p hp)

/-- A σ-function after a morphism is a σ-function. -/
theorem HoldsFor.comp_addMult {σ : ProjectivitySignature} {f : β → γ} {g : α → β}
    (hf : σ.HoldsFor f) (hg : HoldsFor .addMult g) : σ.HoldsFor (f ∘ g) :=
  fun p hp ↦ (hf p hp).comp_addMult hg

variable (α β) in
/-- The incidence of the properties on functions between bounded lattices. -/
abbrev Property.incidence : Property → (α → β) → Prop := fun p f ↦ p.HoldsFor f

/-- The function class of a signature is the polar of its properties. -/
theorem setOf_holdsFor_eq_upperPolar (σ : ProjectivitySignature) :
    {f : α → β | σ.HoldsFor f} = upperPolar (Property.incidence α β) ↑σ.properties :=
  rfl

end Lattice

section DistribLattice

variable [DistribLattice α] [BoundedOrder α] [Nontrivial α]

omit [Nontrivial α] in
/-- A function on `Bool`, carried between two lattices along a homomorphism onto `Bool` and the
homomorphism from it, has the properties it has on `Bool`. -/
theorem Property.holdsFor_ofBool_comp_comp_iff [DistribLattice β] [BoundedOrder β] [Nontrivial β]
    (π : BoundedLatticeHom α Bool) {p : Property} {f : Bool → Bool} :
    p.HoldsFor ((ofBool : BoundedLatticeHom Bool β) ∘ f ∘ π) ↔ p.HoldsFor f := by
  refine ⟨fun h ↦ ?_, fun h ↦ Property.HoldsFor.addMult_comp
    (holdsFor_addMult_of_boundedLatticeHomClass (ofBool : BoundedLatticeHom Bool β))
    (h.comp_addMult (holdsFor_addMult_of_boundedLatticeHomClass π))⟩
  obtain ⟨ρ⟩ := DistribLattice.nonempty_boundedLatticeHom_bool (α := β)
  have h' := (Property.HoldsFor.addMult_comp
    (holdsFor_addMult_of_boundedLatticeHomClass ρ) h).comp_addMult
    (holdsFor_addMult_of_boundedLatticeHomClass (ofBool : BoundedLatticeHom Bool α))
  convert h' using 1
  funext b
  simp

/-- A projection asserts the polar of the pairs of values that σ-functions give `R`-related
arguments, for functions from a nontrivial bounded distributive lattice to a nontrivial bounded
lattice: the property rule derives every constraint that projection guarantees
(`ProjectivitySignature.mem_constraints_project`). -/
theorem coe_constraints_project [Lattice β] [BoundedOrder β] [Nontrivial β] (R : Relation)
    (σ : ProjectivitySignature) :
    (↑(project R σ).constraints : Set Relation.Atom) = lowerPolar (Relation.Atom.incidence β)
      (⋃ f ∈ {f : α → β | σ.HoldsFor f}, Prod.map f f '' R.toSetRel α) := by
  refine Set.ext fun b ↦ ⟨?_, fun h ↦ ?_⟩
  · intro hb q hq
    obtain ⟨f, hf, ⟨x, y⟩, hR, rfl⟩ := Set.mem_iUnion₂.1 hq
    exact Relation.holds_iff.1 (σ.soundFor_of_holdsFor hf R x y hR) b hb
  have key : ∀ (R : Relation) (σ : ProjectivitySignature) (b : Relation.Atom),
      (∀ (f : Bool → Bool) (x y : Bool), σ.HoldsFor f → R.Holds x y → b.Holds (f x) (f y)) →
        b ∈ (project R σ).constraints := by
    decide
  obtain ⟨π⟩ := DistribLattice.nonempty_boundedLatticeHom_bool (α := α)
  refine key R σ b fun f x y hf hR ↦ (Relation.Atom.holds_map_iff ofBool_injective).1
    (h (b := (ofBool (f x), ofBool (f y))) (Set.mem_iUnion₂.2
      ⟨(ofBool : BoundedLatticeHom Bool β) ∘ f ∘ π,
        (holdsFor_addMult_of_boundedLatticeHomClass ofBool).addMult_comp
          (hf.comp_addMult (holdsFor_addMult_of_boundedLatticeHomClass π)),
        (ofBool x, ofBool y), (Relation.holds_map_iff ofBool_injective).2 hR, by simp⟩))

/-- `project R σ` is the least relation to which every σ-function sends `R`-related arguments, for
functions from a nontrivial bounded distributive lattice to a nontrivial bounded lattice
([icard-2012]'s definition of projection). -/
theorem isLeast_project [Lattice β] [BoundedOrder β] [Nontrivial β] (R : Relation)
    (σ : ProjectivitySignature) :
    IsLeast {T : Relation | ∀ f : α → β, σ.HoldsFor f → ∀ x y, R.Holds x y → T.Holds (f x) (f y)}
      (project R σ) :=
  ⟨fun _ hf x y hR ↦ σ.soundFor_of_holdsFor hf R x y hR, fun _ hT ↦ Relation.le_iff.2 fun b hb ↦
    Finset.mem_coe.1 <| (coe_constraints_project (α := α) (β := β) R σ).symm ▸
      fun _ hq ↦ by
        obtain ⟨f, hf, ⟨x, y⟩, hR, rfl⟩ := Set.mem_iUnion₂.1 hq
        exact Relation.holds_iff.1 (hT f hf x y hR) b hb⟩

variable [DistribLattice β] [BoundedOrder β] [Nontrivial β]

/-- The properties of a signature are the polar of its function class, between nontrivial bounded
distributive lattices: a signature asserts every property its functions share. -/
theorem coe_properties_eq_lowerPolar (σ : ProjectivitySignature) :
    (↑σ.properties : Set Property) =
      lowerPolar (Property.incidence α β) {f | σ.HoldsFor f} := by
  refine Set.ext fun p ↦ ⟨fun hp f hf ↦ hf p hp, fun h ↦ ?_⟩
  by_contra hp
  have counter : ∀ (σ : ProjectivitySignature) (p : Property), p ∉ σ.properties →
      ∃ f : Bool → Bool, σ.HoldsFor f ∧ ¬ p.HoldsFor f := by
    decide
  obtain ⟨f, hf, hp'⟩ := counter σ p hp
  obtain ⟨π⟩ := DistribLattice.nonempty_boundedLatticeHom_bool (α := α)
  exact hp' ((Property.holdsFor_ofBool_comp_comp_iff (β := β) π).1
    (h (b := (ofBool : BoundedLatticeHom Bool β) ∘ f ∘ π)
      fun q hq ↦ (Property.holdsFor_ofBool_comp_comp_iff π).2 (hf q hq)))

variable (α β) in
/-- A signature as a formal concept of the incidence, its properties and its function class. -/
@[expose, simps]
def toConcept (σ : ProjectivitySignature) : Concept Property (α → β) (Property.incidence α β) where
  extent := ↑σ.properties
  intent := {f | σ.HoldsFor f}
  upperPolar_extent := (setOf_holdsFor_eq_upperPolar σ).symm
  lowerPolar_intent := (coe_properties_eq_lowerPolar σ).symm

/-- A more specific signature is a larger concept. -/
theorem toConcept_le_toConcept_iff {σ τ : ProjectivitySignature} :
    τ.toConcept α β ≤ σ.toConcept α β ↔ σ ≤ τ := by
  rw [← Concept.extent_subset_extent_iff, extent_toConcept, extent_toConcept,
    Finset.coe_subset, le_iff]

/-- Refinement of signatures is inclusion of function classes between nontrivial bounded
distributive lattices, [icard-2012]'s definition of ≼. -/
theorem le_iff_forall_holdsFor {σ τ : ProjectivitySignature} :
    σ ≤ τ ↔ ∀ f : α → β, σ.HoldsFor f → τ.HoldsFor f := by
  rw [← toConcept_le_toConcept_iff (α := α) (β := β), ← Concept.intent_subset_intent_iff]
  rfl

variable [DistribLattice γ] [BoundedOrder γ] [Nontrivial γ]

/-- The properties of a composite signature are the polar of the composites of a ψ-function after
a φ-function, between nontrivial bounded distributive lattices: the property rule derives every
property that composites share (`ProjectivitySignature.mem_properties_mul`). -/
theorem coe_properties_mul (ψ φ : ProjectivitySignature) :
    (↑(ψ * φ).properties : Set Property) = lowerPolar (Property.incidence α γ)
      {h | ∃ (f : β → γ) (g : α → β), ψ.HoldsFor f ∧ φ.HoldsFor g ∧ h = f ∘ g} := by
  refine Set.ext fun r ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro hr _ ⟨f, g, hf, hg, rfl⟩
    exact hf.comp hg r hr
  by_contra hr
  have counter : ∀ (ψ φ : ProjectivitySignature) (r : Property), r ∉ (ψ * φ).properties →
      ∃ f g : Bool → Bool, ψ.HoldsFor f ∧ φ.HoldsFor g ∧ ¬ r.HoldsFor (f ∘ g) := by
    decide
  obtain ⟨f, g, hf, hg, hr'⟩ := counter ψ φ r hr
  obtain ⟨π⟩ := DistribLattice.nonempty_boundedLatticeHom_bool (α := α)
  obtain ⟨π'⟩ := DistribLattice.nonempty_boundedLatticeHom_bool (α := β)
  refine hr' ((Property.holdsFor_ofBool_comp_comp_iff (β := γ) π).1
    (h (b := (ofBool : BoundedLatticeHom Bool γ) ∘ (f ∘ g) ∘ π)
      ⟨(ofBool : BoundedLatticeHom Bool γ) ∘ f ∘ π', (ofBool : BoundedLatticeHom Bool β) ∘ g ∘ π,
        fun q hq ↦ (Property.holdsFor_ofBool_comp_comp_iff π').2 (hf q hq),
        fun q hq ↦ (Property.holdsFor_ofBool_comp_comp_iff π).2 (hg q hq), ?_⟩))
  funext a
  simp

/-- `ψ * φ` is the least signature whose class contains every ψ-function after a φ-function,
between nontrivial bounded distributive lattices ([icard-2012]'s definition of composition). -/
theorem isLeast_compose (ψ φ : ProjectivitySignature) :
    IsLeast {χ : ProjectivitySignature | ∀ (f : β → γ) (g : α → β),
      ψ.HoldsFor f → φ.HoldsFor g → χ.HoldsFor (f ∘ g)} (ψ * φ) :=
  ⟨fun _ _ hf hg ↦ hf.comp hg, fun _ hχ ↦ le_iff.2 fun r hr ↦
    Finset.mem_coe.1 <| (coe_properties_mul (α := α) (β := β) (γ := γ) ψ φ).symm ▸
      fun _ ⟨f, g, hf, hg, hh⟩ ↦ hh ▸ hχ f g hf hg r hr⟩

end DistribLattice

end ProjectivitySignature

end NaturalLogic
