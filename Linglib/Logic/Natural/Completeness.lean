/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Projection
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.PrimeSeparator

/-!
# Completeness of the projectivity calculus

The join, projection and composition tables of natural logic are sound, and this file proves that
they cannot be improved. On a Boolean algebra the join [is relational
composition](##NaturalLogic.Relation.holds_mul). The order on relations is
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
  a [prime ideal](##NaturalLogic.ProjectivitySignature.exists_holdsFor_addMult). The function-class
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

/-! ### The two-element algebra in a bounded lattice -/

/-- The copy of the two-element Boolean algebra in a bounded lattice. -/
private def ofBool [Top α] [Bot α] (b : Bool) : α := bif b then ⊤ else ⊥

private theorem ofBool_eq_self (b : Bool) : ofBool b = b := by cases b <;> rfl

section Lattice

variable [Lattice α] [BoundedOrder α]

private theorem Relation.Atom.holds_ofBool_iff [Nontrivial α] {a : Relation.Atom} {b c : Bool} :
    a.Holds (ofBool b : α) (ofBool c) ↔ a.Holds b c := by
  rcases a with ⟨_ | _, _ | _⟩ <;> cases b <;> cases c <;>
    simp [ofBool, Relation.Atom.Holds, disjoint_iff, codisjoint_iff]

private theorem Relation.holds_ofBool_iff [Nontrivial α] {R : Relation} {b c : Bool} :
    R.Holds (ofBool b : α) (ofBool c) ↔ R.Holds b c := by
  simp only [Relation.holds_iff, Relation.Atom.holds_ofBool_iff]

private theorem ProjectivitySignature.holdsFor_addMult_ofBool :
    ProjectivitySignature.HoldsFor .addMult (ofBool : Bool → α) := by
  intro p hp
  cases p with
  | monotone =>
    exact fun b c h ↦ by
      cases b <;> cases c <;> first | exact le_rfl | exact bot_le | exact absurd h (by decide)
  | additive => exact ⟨fun b c ↦ by cases b <;> cases c <;> simp [ofBool], rfl⟩
  | multiplicative => exact ⟨fun b c ↦ by cases b <;> cases c <;> simp [ofBool], rfl⟩
  | antitone | antiAdditive | antiMultiplicative => exact absurd hp (by decide)

end Lattice

/-! ### The order and the join -/

namespace Relation

section Lattice

variable [Lattice α] [BoundedOrder α]

/-- The order on relations is implication: `R ≤ S` exactly when `R` entails `S` in a nontrivial
bounded lattice, [icard-2012]'s definition of ≪. -/
theorem le_iff_forall_holds [Nontrivial α] {R S : Relation} :
    R ≤ S ↔ ∀ x y : α, R.Holds x y → S.Holds x y := by
  refine ⟨fun h _ _ hR ↦ hR.of_le h, fun h ↦ ?_⟩
  by_contra hle
  have counter : ∀ R S : Relation, ¬ R ≤ S → ∃ x y : Bool, R.Holds x y ∧ ¬ S.Holds x y := by
    decide
  obtain ⟨x, y, hR, hS⟩ := counter R S hle
  exact hS (holds_ofBool_iff.1 (h _ _ (holds_ofBool_iff.2 hR)))

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
    IsLeast {T : Relation | ∀ x y z : α, R.Holds x y → S.Holds y z → T.Holds x z} (R * S) := by
  refine ⟨fun _ _ _ hR hS ↦ hR.join hS, fun T hT ↦ ?_⟩
  by_contra hle
  have counter : ∀ R S T : Relation, ¬ R * S ≤ T →
      ∃ x y z : Bool, R.Holds x y ∧ S.Holds y z ∧ ¬ T.Holds x z := by
    decide
  obtain ⟨x, y, z, hR, hS, hT'⟩ := counter R S T hle
  exact hT' (holds_ofBool_iff.1 (hT _ _ _ (holds_ofBool_iff.2 hR) (holds_ofBool_iff.2 hS)))

/-- Three denotations other than `⊥` and `⊤` that `R` and `S` chain and `T` does not relate. The
definition keeps the instance search of `Relation.isLeast_join_Ioo` within its default size. -/
private def JoinCounter (R S T : Relation) : Prop :=
  ∃ x ∈ Set.Ioo (⊥ : Finset (Fin 3)) ⊤, ∃ y ∈ Set.Ioo (⊥ : Finset (Fin 3)) ⊤,
    ∃ z ∈ Set.Ioo (⊥ : Finset (Fin 3)) ⊤, R.Holds x y ∧ S.Holds y z ∧ ¬ T.Holds x z

/-- The join stays least when the three denotations are other than `⊥` and `⊤`, as
[maccartney-manning-2009] require of denotations, on the eight-element Boolean algebra. -/
theorem isLeast_join_Ioo (R S : Relation) :
    IsLeast {T : Relation | ∀ x y z : Finset (Fin 3), x ∈ Set.Ioo ⊥ ⊤ → y ∈ Set.Ioo ⊥ ⊤ →
      z ∈ Set.Ioo ⊥ ⊤ → R.Holds x y → S.Holds y z → T.Holds x z} (R * S) := by
  refine ⟨fun _ _ _ _ _ _ hR hS ↦ hR.join hS, fun T hT ↦ ?_⟩
  by_contra hle
  have counter : ∀ R S T : Relation, ¬ R * S ≤ T → JoinCounter R S T := by
    unfold JoinCounter
    decide
  obtain ⟨x, hx, y, hy, z, hz, hR, hS, hT'⟩ := counter R S T hle
  exact hT' (hT x y z hx hy hz hR hS)

/-! ### The join is relational composition

An atomic constraint is an inequality between `x` or its complement and `y` or its complement, an
arrow from one of the two polarities of `x` to one of `y`. Chained constraints compose when the
polarity of the middle term agrees, which is the atom rule, and the constraints of a relation form
a partial bijection of the two polarities. -/

section BooleanAlgebra

variable [BooleanAlgebra α]

/-- An element, or its complement when the polarity is negative. -/
private def pol : Polarity → α → α
  | .positive, x => x
  | .negative, x => xᶜ

private theorem pol_of_ne {s t : Polarity} (h : s ≠ t) (x : α) : pol s x = (pol t x)ᶜ := by
  cases s <;> cases t <;> simp_all [pol]

private theorem Atom.holds_iff_pol {a : Atom} {x y : α} : a.Holds x y ↔ pol a.src x ≤ pol a.tgt y := by
  rcases a with ⟨_ | _, _ | _⟩
  · exact Iff.rfl
  · exact le_compl_iff_disjoint_right.symm
  · exact codisjoint_iff_compl_le_right
  · exact compl_le_compl_iff_le.symm

private theorem Atom.exists_join (a b : Atom) (h : a.tgt = b.src) :
    ∃ c, a.join b = some c ∧ c.src = a.src ∧ c.tgt = b.tgt :=
  ⟨⟨a.src, b.tgt⟩, ite_eq_left h, rfl, rfl⟩

private theorem Atom.eq_of_mem_constraints : ∀ R : Relation, ∀ a ∈ R.constraints,
    ∀ b ∈ R.constraints, (a.src = b.src → a = b) ∧ (a.tgt = b.tgt → a = b) := by
  decide

/-- On a Boolean algebra the join is relational composition: `R * S` holds of `x` and `z` exactly
when some `y` has `x R y` and `y S z`. The constraints bound `y` and its complement from both sides,
and the bounds are compatible when `R * S` holds. The middle term may be `⊥` or `⊤`; among other
elements the join is only the least sound relation (`Relation.isLeast_join_Ioo`). -/
theorem holds_mul (R S : Relation) :
    (R * S).Holds (α := α) = _root_.Relation.Comp R.Holds S.Holds := by
  ext x z
  refine ⟨fun h ↦ ?_, fun ⟨y, hR, hS⟩ ↦ hR.join hS⟩
  have H : ∀ a ∈ R.constraints, ∀ b ∈ S.constraints, a.tgt = b.src →
      pol a.src x ≤ pol b.tgt z := by
    intro a ha b hb hab
    obtain ⟨c, hc, hs, ht⟩ := Atom.exists_join a b hab
    have := holds_iff.1 h c (mem_constraints_mul.2 ⟨a, ha, b, hb, hc⟩)
    rwa [Atom.holds_iff_pol, hs, ht] at this
  let l : Atom → α := fun a ↦ match a.tgt with
    | .positive => pol a.src x
    | .negative => ⊥
  let u : Atom → α := fun b ↦ match b.src with
    | .positive => ⊥
    | .negative => (pol b.tgt z)ᶜ
  refine ⟨R.constraints.sup l ⊔ S.constraints.sup u,
    holds_iff.2 fun a ha ↦ Atom.holds_iff_pol.2 ?_, holds_iff.2 fun b hb ↦ Atom.holds_iff_pol.2 ?_⟩
  · cases hat : a.tgt
    · exact le_sup_of_le_left (by simpa [l, hat] using Finset.le_sup (f := l) ha)
    · change _ ≤ (_)ᶜ
      rw [le_compl_comm]
      refine sup_le (Finset.sup_le fun a' ha' ↦ ?_) (Finset.sup_le fun b hb ↦ ?_)
      · cases hat' : a'.tgt
        · have hne : a'.src ≠ a.src := fun h ↦ by
            rw [(Atom.eq_of_mem_constraints R a' ha' a ha).1 h, hat] at hat'
            exact Polarity.noConfusion hat'
          simpa [l, hat'] using (pol_of_ne hne x).le
        · simp [l, hat']
      · cases hbs : b.src
        · simp [u, hbs]
        · simpa [u, hbs] using H a ha b hb (hat.trans hbs.symm)
  · cases hbs : b.src
    · refine sup_le (Finset.sup_le fun a ha ↦ ?_) (Finset.sup_le fun b' hb' ↦ ?_)
      · cases hat : a.tgt
        · simpa [l, hat, pol] using H a ha b hb (hat.trans hbs.symm)
        · simp [l, hat]
      · cases hbs' : b'.src
        · simp [u, hbs']
        · have hne : b.tgt ≠ b'.tgt := fun h ↦ by
            rw [(Atom.eq_of_mem_constraints S b hb b' hb').2 h, hbs'] at hbs
            exact Polarity.noConfusion hbs
          simpa [u, hbs'] using (pol_of_ne hne z).ge
    · change (_)ᶜ ≤ _
      rw [compl_le_iff_compl_le]
      exact le_sup_of_le_right (by simpa [u, hbs] using Finset.le_sup (f := u) hb)

/-- The identity of the join holds of equal elements. -/
theorem holds_one : (1 : Relation).Holds (α := α) = Eq := rfl

end BooleanAlgebra

/-! ### Why seven relations -/

section Lattice

variable [Lattice α] [BoundedOrder α]

/-- Constraints that two elements other than `⊥` and `⊤` satisfy together are among those of a
single relation: an inclusion and an exclusion would force one of the elements to `⊥` or `⊤`. -/
theorem mem_range_constraints_of_holds {s : Finset Atom} {x y : α}
    (h : ∀ a ∈ s, a.Holds x y) (hx : x ∈ Set.Ioo ⊥ ⊤) (hy : y ∈ Set.Ioo ⊥ ⊤) :
    s ∈ Set.range constraints := by
  by_contra hs
  have key : ∀ s : Finset Atom, (¬ ∃ R : Relation, R.constraints = s) →
      ({.le, .disjoint} ⊆ s ∨ {.le, .codisjoint} ⊆ s ∨
       {.ge, .disjoint} ⊆ s ∨ {.ge, .codisjoint} ⊆ s) := by decide
  rcases key s hs with hp | hp | hp | hp
  · exact hx.1.ne' ((h .disjoint (hp (by decide))).eq_bot_of_le (h .le (hp (by decide))))
  · exact hy.2.ne ((h .codisjoint (hp (by decide))).eq_top_of_ge (h .le (hp (by decide))))
  · exact hy.1.ne' ((h .disjoint (hp (by decide))).eq_bot_of_ge (h .ge (hp (by decide))))
  · exact hx.2.ne ((h .codisjoint (hp (by decide))).eq_top_of_le (h .ge (hp (by decide))))

/-- Two elements of a bounded lattice stand in a strongest relation exactly when neither is `⊥` or
`⊤` ([icard-2012]'s Lemma 1.3 with the converse remarked under it). At `⊥` or `⊤` an inclusion and
an exclusion both hold, and no relation entails both. -/
theorem exists_isLeast_holds_iff {x y : α} :
    (∃ R : Relation, IsLeast {S : Relation | S.Holds x y} R) ↔
      x ∈ Set.Ioo ⊥ ⊤ ∧ y ∈ Set.Ioo ⊥ ⊤ := by
  classical
  refine ⟨fun ⟨R, hR⟩ ↦ ?_, fun ⟨hx, hy⟩ ↦ ?_⟩
  · have key : ∀ R : Relation, (R ≤ .forward ∨ R ≤ .reverse) →
        (R ≤ .alternation ∨ R ≤ .cover) → False := by decide
    have hle {S : Relation} (hS : S.Holds x y) : R ≤ S := hR.2 hS
    refine ⟨⟨bot_lt_iff_ne_bot.2 ?_, lt_top_iff_ne_top.2 ?_⟩,
      bot_lt_iff_ne_bot.2 ?_, lt_top_iff_ne_top.2 ?_⟩ <;> rintro rfl
    · exact key R (.inl (hle (S := .forward) bot_le))
        (.inl (hle (S := .alternation) disjoint_bot_left))
    · exact key R (.inr (hle (S := .reverse) le_top))
        (.inr (hle (S := .cover) codisjoint_top_left))
    · exact key R (.inr (hle (S := .reverse) bot_le))
        (.inl (hle (S := .alternation) disjoint_bot_right))
    · exact key R (.inl (hle (S := .forward) le_top))
        (.inr (hle (S := .cover) codisjoint_top_right))
  · obtain ⟨R, hR⟩ := mem_range_constraints_of_holds
      (s := Finset.univ.filter fun a ↦ a.Holds x y) (fun a ha ↦ (Finset.mem_filter.1 ha).2) hx hy
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

/-! ### Function classes -/

namespace ProjectivitySignature

section Lattice

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- A morphism after a σ-function is a σ-function. -/
theorem HoldsFor.addMult_comp {σ : ProjectivitySignature} {f : β → γ} {g : α → β}
    (hf : HoldsFor .addMult f) (hg : σ.HoldsFor g) : σ.HoldsFor (f ∘ g) := by
  have h := hf.comp hg
  rwa [show addMult * σ = σ from one_mul σ] at h

/-- A σ-function after a morphism is a σ-function. -/
theorem HoldsFor.comp_addMult {σ : ProjectivitySignature} {f : β → γ} {g : α → β}
    (hf : σ.HoldsFor f) (hg : HoldsFor .addMult g) : σ.HoldsFor (f ∘ g) := by
  have h := hf.comp hg
  rwa [show σ * addMult = σ from mul_one σ] at h

private theorem HoldsFor.map_ofBool {f : α → β} (hf : HoldsFor .addMult f) (b : Bool) :
    f (ofBool b) = ofBool b := by
  cases b
  · exact (hf .multiplicative (by decide)).2
  · exact (hf .additive (by decide)).2

end Lattice

section DistribLattice

variable [DistribLattice α] [BoundedOrder α] [Nontrivial α]

/-- A nontrivial bounded distributive lattice has a morphism to the two-element Boolean algebra,
the map telling whether an element lies outside a prime ideal. -/
theorem exists_holdsFor_addMult : ∃ f : α → Bool, HoldsFor .addMult f := by
  classical
  obtain ⟨J, hJ, -, hJ'⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal
    (F := Order.PFilter.principal (⊤ : α)) (I := Order.Ideal.principal ⊥)
    (Set.disjoint_left.2 fun x hx hx' ↦ bot_ne_top (α := α) <|
      le_antisymm bot_le
        ((Order.PFilter.mem_principal.1 hx).trans (Order.Ideal.mem_principal.1 hx')))
  have htop : (⊤ : α) ∉ J := fun h ↦
    Set.disjoint_left.1 hJ' (Order.PFilter.mem_principal.2 le_rfl) h
  refine ⟨fun x ↦ decide (x ∉ J), fun p hp ↦ ?_⟩
  cases p with
  | monotone =>
    intro x y hxy
    by_cases hy : y ∈ J
    · have hx : x ∈ J := J.lower hxy hy
      simp [hy, hx]
    · simp [hy]
  | additive =>
    exact ⟨fun x y ↦ by simp [Order.Ideal.sup_mem_iff], by simpa using htop⟩
  | multiplicative =>
    refine ⟨fun x y ↦ ?_, by simp⟩
    have : x ⊓ y ∈ J ↔ x ∈ J ∨ y ∈ J :=
      ⟨hJ.mem_or_mem, fun h ↦ h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
    simp [this, not_or]
  | antitone | antiAdditive | antiMultiplicative => exact absurd hp (by decide)

/-- `project R σ` is the least relation to which every σ-function sends `R`-related arguments, for
functions from a nontrivial bounded distributive lattice to a nontrivial bounded lattice
([icard-2012]'s definition of projection). -/
theorem isLeast_project [Lattice β] [BoundedOrder β] [Nontrivial β] (R : Relation)
    (σ : ProjectivitySignature) :
    IsLeast {T : Relation | ∀ f : α → β, σ.HoldsFor f → ∀ x y, R.Holds x y → T.Holds (f x) (f y)}
      (project R σ) := by
  refine ⟨fun f hf x y hR ↦ σ.soundFor_of_holdsFor hf R x y hR, fun T hT ↦ ?_⟩
  by_contra hle
  have counter : ∀ (R : Relation) (σ : ProjectivitySignature) (T : Relation),
      ¬ project R σ ≤ T → ∃ (f : Bool → Bool) (x y : Bool),
        σ.HoldsFor f ∧ R.Holds x y ∧ ¬ T.Holds (f x) (f y) := by
    decide
  obtain ⟨f, x, y, hf, hR, hT'⟩ := counter R σ T hle
  obtain ⟨π, hπ⟩ := exists_holdsFor_addMult (α := α)
  have h := hT (ofBool ∘ f ∘ π) (holdsFor_addMult_ofBool.addMult_comp (hf.comp_addMult hπ))
    (ofBool x) (ofBool y) (Relation.holds_ofBool_iff.2 hR)
  simp only [Function.comp_apply, hπ.map_ofBool, ofBool_eq_self] at h
  exact hT' (Relation.holds_ofBool_iff.1 h)

variable [DistribLattice β] [BoundedOrder β] [Nontrivial β]

/-- Refinement of signatures is inclusion of function classes between nontrivial bounded
distributive lattices, [icard-2012]'s definition of ≼. -/
theorem le_iff_forall_holdsFor {σ τ : ProjectivitySignature} :
    σ ≤ τ ↔ ∀ f : α → β, σ.HoldsFor f → τ.HoldsFor f := by
  refine ⟨fun h f hf ↦ hf.of_le h, fun h ↦ ?_⟩
  by_contra hle
  have counter : ∀ σ τ : ProjectivitySignature, ¬ σ ≤ τ →
      ∃ f : Bool → Bool, σ.HoldsFor f ∧ ¬ τ.HoldsFor f := by
    decide
  obtain ⟨f, hσ, hτ⟩ := counter σ τ hle
  obtain ⟨π, hπ⟩ := exists_holdsFor_addMult (α := α)
  obtain ⟨ρ, hρ⟩ := exists_holdsFor_addMult (α := β)
  have h := (hρ.addMult_comp
    (h _ (holdsFor_addMult_ofBool.addMult_comp (hσ.comp_addMult hπ)))).comp_addMult
    (holdsFor_addMult_ofBool (α := α))
  refine hτ (by
    convert h using 1
    funext b
    simp [hπ.map_ofBool, hρ.map_ofBool, ofBool_eq_self])

/-- `ψ * φ` is the least signature whose class contains every ψ-function after a φ-function,
between nontrivial bounded distributive lattices ([icard-2012]'s definition of composition). -/
theorem isLeast_compose [DistribLattice γ] [BoundedOrder γ] [Nontrivial γ]
    (ψ φ : ProjectivitySignature) :
    IsLeast {χ : ProjectivitySignature | ∀ (f : β → γ) (g : α → β),
      ψ.HoldsFor f → φ.HoldsFor g → χ.HoldsFor (f ∘ g)} (ψ * φ) := by
  refine ⟨fun f g hf hg ↦ hf.comp hg, fun χ hχ ↦ ?_⟩
  by_contra hle
  have counter : ∀ ψ φ χ : ProjectivitySignature, ¬ ψ * φ ≤ χ →
      ∃ f g : Bool → Bool, ψ.HoldsFor f ∧ φ.HoldsFor g ∧ ¬ χ.HoldsFor (f ∘ g) := by
    decide
  obtain ⟨f, g, hf, hg, hχ'⟩ := counter ψ φ χ hle
  obtain ⟨π, hπ⟩ := exists_holdsFor_addMult (α := α)
  obtain ⟨π', hπ'⟩ := exists_holdsFor_addMult (α := β)
  obtain ⟨ρ, hρ⟩ := exists_holdsFor_addMult (α := γ)
  have h := (hρ.addMult_comp
    (hχ _ _ (holdsFor_addMult_ofBool.addMult_comp (hf.comp_addMult hπ'))
      (holdsFor_addMult_ofBool.addMult_comp (hg.comp_addMult hπ)))).comp_addMult
    (holdsFor_addMult_ofBool (α := α))
  refine hχ' (by
    convert h using 1
    funext b
    simp [hπ.map_ofBool, hπ'.map_ofBool, hρ.map_ofBool, ofBool_eq_self])

end DistribLattice

end ProjectivitySignature

end NaturalLogic
