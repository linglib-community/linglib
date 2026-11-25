module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Defs
public import Linglib.Core.Order.AntiAdditive

/-!
# Quantifiers and determiner denotations

This file defines quantifiers and determiner denotations. A quantifier on a universe `α` is a
property of its subsets, `Quantifier α := Set α → Prop`, the denotation of a noun phrase. A
determiner denotation `Det α := Set α → Quantifier α` maps a restrictor `A` to the quantifier
`d A` of the noun phrase it heads, as in Barwise and Cooper. These are the quantifiers of type ⟨1⟩
that Mostowski introduced and their type ⟨1,1⟩ generalization, and both inherit the Boolean
algebra of the Pi type, whose `ᶜ`, `⊓` and `⊔` are outer negation, conjunction and disjunction.

The properties are stated in the lattice of sets: conservativity `d A B ↔ d A (A ∩ B)`, the
monotonicities as `Monotone` and `Antitone` of the sections and the anti-additivities as
`IsAntiAdditive` of the sections, Peters and Westerståhl's left monotonicities, van Benthem's
relational properties. Invariance under the permutations of the universe is in
`Quantifier/Invariance.lean`, and quantifiers with a value on every finite universe are in
`Quantifier/Global.lean`.

## Main definitions

* `Quantifier`, `Quantifier.Det`: quantifiers and determiner denotations.
* `Det.Conservative`, `Det.ScopeMonotone`, `Det.RestrictorMonotone`, `Det.Intersective`,
  `Det.CoIntersective`, `Det.PositiveStrong`: the properties of determiner denotations.
* `Det.UpSEMon`, `Det.Smooth`, `Det.LeftAntiAdditive`: the left monotonicities.
* `Det.QuasiReflexive`, `Det.Filtrating`: relational properties.
* `Det.SatisfiesUniversals`: Barwise and Cooper's determiner universal and monotonicity
  constraint.
* `Det.innerNeg`, `Det.dual`, `Det.adjRestrict`: inner negation, the dual and restriction.
* `Quantifier.LivesOn`, `Quantifier.individual`: the live-on property and the Montague lift.

## Implementation notes

A quantifier is a function `Set α → Prop`, not a set of sets, and a determiner denotation is the
curried function `Set α → Set α → Prop`, not a set of pairs. A quantifier is applied to its scope
and a determiner denotation to its restrictor and then its scope, as the types of Montague grammar
have it, and the monotonicities are `Monotone` and `Antitone` of these functions directly. As
sets of sets the same properties would be `IsUpperSet` and `IsLowerSet` of the family, and
application would be membership; the set of scopes `{B | Q B}` is written where that view is
wanted, as for right continuity.

`Quantifier` and `Det` are abbreviations, so the Boolean algebra is that of the function type and
needs no instance of its own, and an instance stated on `Quantifier α` is an instance on a
function type. The actions of the polarities in `Quantifier/Negation.lean` are of this kind: they
are mathlib's actions on a function type through its values and through its domain.

## References

* [barwise-cooper-1981]
* [keenan-1987]
* [keenan-stavi-1986]
* [montague-1973]
* [mostowski-1957]
* [partee-1987]
* [peters-westerstahl-2006]
* [van-benthem-1984]
* [zuber-keenan-2019]
* [zwarts-1998]
-/

@[expose] public section

universe u

/-- A quantifier on `α` is a property of subsets of `α`, the denotation of a noun phrase, true of
the sets that are its scopes. It is a quantifier of type ⟨1⟩, the kind Mostowski introduced. -/
abbrev Quantifier (α : Type*) := Set α → Prop

namespace Quantifier

/-- A determiner denotation on `α` is a relation between a restrictor and a scope. Applied to a
restrictor it is the quantifier of the noun phrase the determiner heads. It is a quantifier of
type ⟨1,1⟩. -/
abbrev Det (α : Type*) := Set α → Quantifier α

variable {α : Type*}

theorem isAntiAdditive_iff {q : Quantifier α} :
    IsAntiAdditive q ↔ ∀ A B, q (A ∪ B) ↔ q A ∧ q B := by
  simp only [IsAntiAdditive, inf_Prop_eq, eq_iff_iff]

namespace Det

/-! ### Conservativity and monotonicity -/

/-- A determiner denotation is conservative when `d A B ↔ d A (A ∩ B)`, so that only the part of
the scope inside the restrictor matters. -/
def Conservative (d : Det α) : Prop := ∀ A B, d A B ↔ d A (A ∩ B)

/-- A determiner denotation is scope monotone when every section `d A` is `Monotone`, so that
`d A B` and `B ⊆ B'` give `d A B'`. -/
def ScopeMonotone (d : Det α) : Prop := ∀ A, Monotone (d A)

/-- A determiner denotation is scope antitone when every section `d A` is `Antitone`. -/
def ScopeAntitone (d : Det α) : Prop := ∀ A, Antitone (d A)

/-- A determiner denotation is restrictor monotone, or persistent, when `d · B` is `Monotone`
for every scope `B`. -/
def RestrictorMonotone (d : Det α) : Prop := ∀ B, Monotone (d · B)

/-- A determiner denotation is restrictor antitone, or anti-persistent, when `d · B` is
`Antitone` for every scope `B`. -/
def RestrictorAntitone (d : Det α) : Prop := ∀ B, Antitone (d · B)

/-- A determiner denotation is intersective when `d A B` depends only on `A ∩ B`. Equivalently
`d A B ↔ d (A ∩ B) univ`, [keenan-1987]'s characterization of the determiners that occur in
*there*-sentences, which [keenan-stavi-1986] call existential. -/
def Intersective (d : Det α) : Prop :=
  ∀ A B A' B' : Set α, A ∩ B = A' ∩ B' → (d A B ↔ d A' B')

/-- A determiner denotation is co-intersective when `d A B` depends only on `A \ B`, as for *every*
and *all but n*. -/
def CoIntersective (d : Det α) : Prop :=
  ∀ A B A' B' : Set α, A \ B = A' \ B' → (d A B ↔ d A' B')

/-- A determiner denotation satisfies the intersection condition of [barwise-cooper-1981] when
`d A B ↔ d (A ∩ B) B`. For a conservative determiner denotation this is intersectivity. -/
def IntersectionCondition (d : Det α) : Prop := ∀ A B, d A B ↔ d (A ∩ B) B

/-! ### Strength -/

/-- A determiner denotation is positive strong when `d A A` holds for every `A`, as for
*every*. -/
def PositiveStrong (d : Det α) : Prop := ∀ A, d A A

/-- A determiner denotation is negative strong when `d A A` fails for every `A`, as for
*neither*. -/
def NegativeStrong (d : Det α) : Prop := ∀ A, ¬ d A A

/-! ### Left monotonicity and smoothness

Peters and Westerståhl's four left monotonicities enlarge or shrink the restrictor by elements
inside or outside the scope. On the number triangle, with `k = |A \ B|` and `m = |A ∩ B|`,
`UpSEMon` moves `(k, m)` to `(k, m + 1)`, `UpSWMon` to `(k + 1, m)`, `DownNWMon` moves
`(k, m + 1)` to `(k, m)` and `DownNEMon` moves `(k + 1, m)` to `(k, m)`. -/

/-- A determiner denotation is ↑SE monotone when enlarging the restrictor by elements of the scope
preserves it: `A ⊆ A'`, `A' \ B = A \ B` and `d A B` give `d A' B`. -/
def UpSEMon (d : Det α) : Prop := ∀ A B A', A ⊆ A' → A' \ B ⊆ A → d A B → d A' B

/-- A determiner denotation is ↑SW monotone when enlarging the restrictor by elements outside the
scope preserves it: `A ⊆ A'`, `A' ∩ B = A ∩ B` and `d A B` give `d A' B`. -/
def UpSWMon (d : Det α) : Prop := ∀ A B A', A ⊆ A' → A' ∩ B ⊆ A → d A B → d A' B

/-- A determiner denotation is ↓NW monotone when shrinking the restrictor by elements of the scope
preserves it: `A' ⊆ A`, `A' \ B = A \ B` and `d A B` give `d A' B`. -/
def DownNWMon (d : Det α) : Prop := ∀ A B A', A' ⊆ A → A \ B ⊆ A' → d A B → d A' B

/-- A determiner denotation is ↓NE monotone when shrinking the restrictor by elements outside the
scope preserves it: `A' ⊆ A`, `A' ∩ B = A ∩ B` and `d A B` give `d A' B`. -/
def DownNEMon (d : Det α) : Prop := ∀ A B A', A' ⊆ A → A ∩ B ⊆ A' → d A B → d A' B

/-- A determiner denotation is smooth when it is ↓NE and ↑SE monotone; smooth determiner
denotations are scope monotone. -/
def Smooth (d : Det α) : Prop := DownNEMon d ∧ UpSEMon d

/-- A determiner denotation is co-smooth when its inner negation is smooth, that is, when it is
↓NW and ↑SW monotone. -/
def CoSmooth (d : Det α) : Prop := DownNWMon d ∧ UpSWMon d

/-- A determiner denotation is left anti-additive when every section `d · B` is anti-additive,
`d (A ∪ A') B ↔ d A B ∧ d A' B` ([peters-westerstahl-2006] §5.9). -/
def LeftAntiAdditive (d : Det α) : Prop := ∀ B, IsAntiAdditive (d · B)

/-- A determiner denotation is right anti-additive when every section `d A` is anti-additive,
`d A (B ∪ B') ↔ d A B ∧ d A B'`, so that its scope is an anti-additive context in the sense of
[zwarts-1998]. -/
def RightAntiAdditive (d : Det α) : Prop := ∀ A, IsAntiAdditive (d A)

/-! ### Relational properties

A determiner denotation is a binary relation between sets, so the classical relational
properties are the core relation classes: *all* is `IsTrans` and `Std.Antisymm`, *some* and *no*
are `Std.Symm`, and *not all* is `Std.Trichotomous`. The properties below are the ones the
theory of quantifiers adds. -/

/-- A determiner denotation is quasi-reflexive when `d A B` gives `d A A`, as for *some*. -/
def QuasiReflexive (d : Det α) : Prop := ∀ A B, d A B → d A A

/-- A determiner denotation is quasi-universal when `d A A` gives `d A B` for every `B`, as for
*no*. -/
def QuasiUniversal (d : Det α) : Prop := ∀ A B, d A A → d A B

/-- A determiner denotation is almost connected when `d A B` gives `d A C` or `d C B` for every
`C`, which is the transitivity of its complement. -/
def AlmostConnected (d : Det α) : Prop := ∀ A B C, d A B → d A C ∨ d C B

/-- A determiner denotation is circular when `d A B` and `d B C` give `d C A`. -/
def Circular (d : Det α) : Prop := ∀ A B C, d A B → d B C → d C A

/-- A determiner denotation is right continuous when every set of scopes `{B | d A B}` is
order-connected, so that `d A B₁`, `d A B₂` and `B₁ ⊆ B ⊆ B₂` give `d A B`. -/
def RightContinuous (d : Det α) : Prop := ∀ A, {B | d A B}.OrdConnected

/-- A determiner denotation satisfies Barwise and Cooper's determiner universal and monotonicity
constraint (U3 and U6 of [barwise-cooper-1981]) when it is conservative and each of its noun
phrases `d A` is a monotone quantifier or a conjunction of monotone quantifiers. A monotone `d A`
is its own conjunction with the trivial quantifier `⊤`. -/
structure SatisfiesUniversals (d : Det α) : Prop where
  /-- The determiner denotation is conservative, so that each `d A` lives on `A`. -/
  conservative : d.Conservative
  /-- Each `d A` is the meet of two quantifiers, each monotone or antitone. -/
  exists_eq_inf : ∀ A, ∃ Q₁ Q₂ : Quantifier α, (Monotone Q₁ ∨ Antitone Q₁) ∧
    (Monotone Q₂ ∨ Antitone Q₂) ∧ d A = Q₁ ⊓ Q₂

/-- A determiner denotation is scope-intersective when `d A B` and `d A C` give `d A (B ∩ C)`. -/
def ScopeIntersective (d : Det α) : Prop := ∀ A B C, d A B → d A C → d A (B ∩ C)

/-- A determiner denotation is filtrating when it is scope monotone and scope-intersective, so
that its scopes at a fixed restrictor form a filter. -/
def Filtrating (d : Det α) : Prop := ScopeMonotone d ∧ ScopeIntersective d

/-! ### The Boolean algebra, the negations and the dual

The outer negation of a determiner denotation is its complement `dᶜ`, and determiner conjunction
and disjunction are the meet `d ⊓ d'` and join `d ⊔ d'` of the Boolean algebra `Det α`. -/

@[simp] theorem compl_apply (d : Det α) (A B : Set α) : dᶜ A B = ¬ d A B := rfl

@[simp] theorem inf_apply (d d' : Det α) (A B : Set α) : (d ⊓ d') A B = (d A B ∧ d' A B) := rfl

@[simp] theorem sup_apply (d d' : Det α) (A B : Set α) : (d ⊔ d') A B = (d A B ∨ d' A B) := rfl

/-- The inner negation of a determiner denotation negates the scope, `(d~) A B = d A Bᶜ`. -/
def innerNeg (d : Det α) : Det α := fun A B ↦ d A Bᶜ

/-- The dual of a determiner denotation is the complement of its inner negation, so that the dual
of *every* is *some*. -/
def dual (d : Det α) : Det α := (innerNeg d)ᶜ

/-- The restriction of a determiner denotation by an adjective or relative clause `C` narrows the
restrictor, so that *tall student* is *student* and *tall*. -/
def adjRestrict (d : Det α) (C : Set α) : Det α := fun A B ↦ d (A ∩ C) B

end Det

/-! ### Type ⟨1⟩ quantifiers -/

/-- A quantifier lives on `A` when `Q B ↔ Q (A ∩ B)` for every `B`. -/
def LivesOn (Q : Quantifier α) (A : Set α) : Prop := ∀ B, Q B ↔ Q (A ∩ B)

theorem livesOn_univ (Q : Quantifier α) : Q.LivesOn Set.univ := fun B ↦ by rw [Set.univ_inter]

theorem LivesOn.mono {Q : Quantifier α} {A A' : Set α} (h : Q.LivesOn A) (hA : A ⊆ A') :
    Q.LivesOn A' := fun B ↦ by
  rw [h B, h (A' ∩ B), ← Set.inter_assoc, Set.inter_eq_left.2 hA]

theorem LivesOn.inter {Q : Quantifier α} {A A' : Set α} (h : Q.LivesOn A) (h' : Q.LivesOn A') :
    Q.LivesOn (A ∩ A') := fun B ↦ by rw [h B, h' (A ∩ B), Set.inter_left_comm, Set.inter_assoc]

theorem _root_.Quantifier.Det.Conservative.livesOn {d : Det α} (h : d.Conservative)
    (A : Set α) : (d A).LivesOn A :=
  h A

/-! ### The negations and the dual of a quantifier

The outer negation of a quantifier is its complement `Qᶜ` in the Boolean algebra `Quantifier α`.
The inner negation and the dual of a determiner denotation are those of its quantifiers,
`(d.dual) A = (d A).dual`. -/

/-- The inner negation of a quantifier negates its scope, `Q.innerNeg B = Q Bᶜ`. -/
def innerNeg (Q : Quantifier α) : Quantifier α := fun B ↦ Q Bᶜ

/-- The dual of a quantifier is the complement of its inner negation, `Q.dual B = ¬ Q Bᶜ`. -/
def dual (Q : Quantifier α) : Quantifier α := Q.innerNegᶜ

@[simp] theorem innerNeg_apply (Q : Quantifier α) (B : Set α) : Q.innerNeg B = Q Bᶜ := rfl

@[simp] theorem dual_apply (Q : Quantifier α) (B : Set α) : Q.dual B = ¬ Q Bᶜ := rfl

@[simp] theorem innerNeg_innerNeg (Q : Quantifier α) : Q.innerNeg.innerNeg = Q := by
  funext B
  simp

@[simp] theorem dual_dual (Q : Quantifier α) : Q.dual.dual = Q := by
  funext B
  simp

theorem innerNeg_compl (Q : Quantifier α) : Qᶜ.innerNeg = Q.innerNegᶜ := rfl

theorem dual_eq_innerNeg_compl (Q : Quantifier α) : Q.dual = Qᶜ.innerNeg := rfl

theorem monotone_dual {Q : Quantifier α} (hQ : Monotone Q) : Monotone Q.dual :=
  fun _ _ h hB hB' ↦ hB (hQ (Set.compl_subset_compl.mpr h) hB')

theorem Det.innerNeg_apply' (d : Det α) (A : Set α) : d.innerNeg A = (d A).innerNeg := rfl

theorem Det.dual_apply' (d : Det α) (A : Set α) : d.dual A = (d A).dual := rfl

/-- The Montague lift of an entity is the principal ultrafilter it generates, the quantifier of
the sets it belongs to, as [montague-1973] translates a proper name; it is Partee's LIFT and the
continuation `pure`. -/
def individual (a : α) : Quantifier α := fun B ↦ a ∈ B

/-- An individual is its own dual. -/
@[simp] theorem dual_individual (a : α) : (individual a).dual = individual a := by
  funext B
  simp [individual]

theorem individual_injective : Function.Injective (individual (α := α)) :=
  fun a b h ↦ (show b = a from (congrFun h {a}).mp rfl).symm

theorem individual_livesOn {A : Set α} {a : α} (ha : a ∈ A) : (individual a).LivesOn A :=
  fun _ ↦ ⟨fun h ↦ ⟨ha, h⟩, And.right⟩

end Quantifier
