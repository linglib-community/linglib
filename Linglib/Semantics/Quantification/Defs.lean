module

public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Sublattice
public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Data.Fintype.Defs

/-!
# Generalized quantifiers

This file defines generalized quantifier denotations and the properties of them that the
theory of determiners studies. A generalized quantifier on a type `α` is a relation between two
predicates on `α`, the restrictor and the scope, so `GQ α` is `(α → Prop) → (α → Prop) → Prop`
and inherits the Boolean algebra of the Pi type. The properties are Barwise and Cooper's
conservativity, monotonicity, symmetry and strength, Peters and Westerståhl's left monotonicity,
smoothness and anti-additivity, van Benthem's relational properties and quantity invariance in
the sense of Mostowski. The operations are the negations and the dual, the Boolean operations
named for determiner conjunction and disjunction, and restriction by an adjective. The concrete
denotations are in `Quantification/Basic.lean`, and the individuals and the type shifts they fix
in `Quantification/Individual.lean`.

## Main definitions

* `GQ`, `GQ.Family`, `NP`: quantifier denotations on a type, on every finite type, and of
  type ⟨1⟩.
* `GQ.Conservative`, `GQ.ScopeMonotone`, `GQ.RestrictorMonotone`, `GQ.PositiveStrong`: the
  properties of Barwise and Cooper; symmetry is `Std.Symm`.
* `GQ.UpSEMon`, `GQ.Smooth`, `GQ.LeftAntiAdditive`: the left monotonicities of Peters and
  Westerståhl.
* `GQ.QuasiReflexive`, `GQ.Filtrating`, `GQ.QuantityInvariant`: van Benthem's relational
  properties and quantity invariance.
* `GQ.innerNeg`, `GQ.dual`, `GQ.adjRestrict`: the operations; the outer negation, meet and join
  are the Boolean algebra's `ᶜ`, `⊓` and `⊔`.
* `NP.individual`, `NP.LivesOn`: the Montague lift and the live-on property.

## Implementation notes

Extension, the independence of a quantifier from the ambient universe, holds by construction,
since a denotation is given on one type. A quantifier is a binary relation on predicates, so the
classical relational properties are the core relation classes `Std.Symm`, `IsTrans`,
`Std.Antisymm`, `Std.Asymm` and `Std.Trichotomous` applied to it, and the monotonicities are
`Monotone` and `Antitone` of its sections. Decidability of the concrete denotations is recovered
pointwise from `[Fintype α]` and decidable restrictor and scope.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [mostowski-1957]
* [partee-1987]
* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

namespace Quantifier

/-- A generalized quantifier denotation maps a restrictor and a scope to a proposition. Under
the pointwise ordering of `α → Prop` it is a binary relation between predicates. -/
abbrev GQ (α : Type*) := (α → Prop) → (α → Prop) → Prop

universe u

/-- A determiner denotation given on every finite domain, the object from which a lexicon
entry's available readings are drawn. -/
abbrev GQ.Family : Type (u + 1) := ∀ (α : Type u) [Fintype α], GQ α

/-- A type ⟨1⟩ quantifier, the denotation of a noun phrase, is a property of properties, a
quantifier proper in Barwise and Cooper's sense. It is definitionally `Cont Prop α`, the
scope-taking continuation. -/
abbrev NP (α : Type*) := (α → Prop) → Prop

variable {α : Type*}

namespace GQ

/-! ### Conservativity and monotonicity -/

/-- A quantifier is conservative when `Q(A, B) ↔ Q(A, A ∩ B)`, so that only the elements of the
scope that are in the restrictor matter. Barwise and Cooper's universal says that every simple
determiner denotes a conservative quantifier. -/
def Conservative (q : GQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q R (fun x => R x ∧ S x)

/-- A quantifier is scope monotone when `B ⊆ B'` and `Q(A, B)` give `Q(A, B')`, that is, when
every section `q R` is `Monotone` under the pointwise ordering. -/
def ScopeMonotone (q : GQ α) : Prop := ∀ R, Monotone (q R)

/-- A quantifier is scope antitone when `B ⊆ B'` and `Q(A, B')` give `Q(A, B)`, that is, when
every section `q R` is `Antitone`. -/
def ScopeAntitone (q : GQ α) : Prop := ∀ R, Antitone (q R)

/-- A quantifier satisfies the intersection condition when `Q(A, B)` depends only on `A ∩ B`. -/
def IntersectionCondition (q : GQ α) : Prop :=
  ∀ (R S R' S' : α → Prop),
    (∀ x, (R x ∧ S x) ↔ (R' x ∧ S' x)) →
    (q R S ↔ q R' S')

/-- A quantifier is restrictor monotone, or persistent, when `A ⊆ A'` and `Q(A, B)` give
`Q(A', B)`, that is, when `q · S` is `Monotone` for every scope `S`. -/
def RestrictorMonotone (q : GQ α) : Prop := ∀ S, Monotone (q · S)

/-- A quantifier is restrictor antitone, or anti-persistent, when `A ⊆ A'` and `Q(A', B)` give
`Q(A, B)`, that is, when `q · S` is `Antitone` for every scope `S`. -/
def RestrictorAntitone (q : GQ α) : Prop := ∀ S, Antitone (q · S)

/-! ### Strength -/

/-- A quantifier is positive strong when `Q(A, A)` holds for every `A`, as for *every*. -/
def PositiveStrong (q : GQ α) : Prop :=
  ∀ (R : α → Prop), q R R

/-- A quantifier is negative strong when `Q(A, A)` fails for every `A`, as for *neither*. -/
def NegativeStrong (q : GQ α) : Prop :=
  ∀ (R : α → Prop), ¬ q R R

/-- A quantifier has the existential property when `Q(A, B) ↔ Q(A ∩ B, ⊤)`, the property of the
determiners felicitous in *there*-sentences. -/
def Existential (q : GQ α) : Prop :=
  ∀ (R S : α → Prop), q R S ↔ q (fun x => R x ∧ S x) (fun _ => True)

/-! ### Left monotonicity and smoothness

Peters and Westerståhl's four left monotonicities enlarge or shrink the restrictor by elements
inside or outside the scope. On the number triangle, with `k = |A ∖ B|` and `m = |A ∩ B|`,
`UpSEMon` moves `(k, m)` to `(k, m + 1)`, `UpSWMon` to `(k + 1, m)`, `DownNWMon` moves
`(k, m + 1)` to `(k, m)` and `DownNEMon` moves `(k + 1, m)` to `(k, m)`. -/

/-- A quantifier is ↑SE monotone when enlarging the restrictor by elements of the scope
preserves it, so that `A ⊆ A'`, `A ∖ B = A' ∖ B` and `Q(A, B)` give `Q(A', B)`. -/
def UpSEMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R x → R' x) →
    (∀ x, R' x → ¬ S x → R x) →
    q R S → q R' S

/-- A quantifier is ↑SW monotone when enlarging the restrictor by elements outside the scope
preserves it, so that `A ⊆ A'`, `A ∩ B = A' ∩ B` and `Q(A, B)` give `Q(A', B)`. -/
def UpSWMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R x → R' x) →
    (∀ x, R' x → S x → R x) →
    q R S → q R' S

/-- A quantifier is ↓NW monotone when shrinking the restrictor by elements of the scope
preserves it, so that `A' ⊆ A`, `A ∖ B = A' ∖ B` and `Q(A, B)` give `Q(A', B)`. -/
def DownNWMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R' x → R x) →
    (∀ x, R x → ¬ S x → R' x) →
    q R S → q R' S

/-- A quantifier is ↓NE monotone when shrinking the restrictor by elements outside the scope
preserves it, so that `A' ⊆ A`, `A ∩ B = A' ∩ B` and `Q(A, B)` give `Q(A', B)`. -/
def DownNEMon (q : GQ α) : Prop :=
  ∀ (R S R' : α → Prop),
    (∀ x, R' x → R x) →
    (∀ x, R x → S x → R' x) →
    q R S → q R' S

/-- A quantifier is smooth when it is ↓NE and ↑SE monotone; smooth quantifiers are scope-upward
monotone. -/
def Smooth (q : GQ α) : Prop := DownNEMon q ∧ UpSEMon q

/-- A quantifier is co-smooth when its inner negation is smooth, that is, when it is ↓NW and ↑SW
monotone. -/
def CoSmooth (q : GQ α) : Prop := DownNWMon q ∧ UpSWMon q

/-- A quantifier is left anti-additive when `Q(A ∪ B, C) ↔ Q(A, C) ∧ Q(B, C)`. -/
def LeftAntiAdditive (q : GQ α) : Prop :=
  ∀ (R R' S : α → Prop),
    q (fun x => R x ∨ R' x) S ↔ (q R S ∧ q R' S)

/-- A quantifier is right anti-additive when `Q(A, B ∪ C) ↔ Q(A, B) ∧ Q(A, C)`. -/
def RightAntiAdditive (q : GQ α) : Prop :=
  ∀ (R S S' : α → Prop),
    q R (fun x => S x ∨ S' x) ↔ (q R S ∧ q R S')

/-! ### Relational properties

Van Benthem reads a quantifier as a relation between predicates and asks which relational
properties it has. The classical ones are the core relation classes: *all* is `IsTrans` and
`Std.Antisymm`, *some* and *no* are `Std.Symm`, and *not all* is `Std.Trichotomous`. The
properties below are the ones the theory of quantifiers adds. -/

/-- A quantifier is quasi-reflexive when `Q(A, B)` gives `Q(A, A)`, as for *some*. -/
def QuasiReflexive (q : GQ α) : Prop :=
  ∀ (A B : α → Prop), q A B → q A A

/-- A quantifier is quasi-universal when `Q(A, A)` gives `Q(A, B)` for every `B`, as for *no*. -/
def QuasiUniversal (q : GQ α) : Prop :=
  ∀ (A B : α → Prop), q A A → q A B

/-- A quantifier is almost connected when `Q(A, B)` gives `Q(A, C)` or `Q(C, B)` for every `C`,
which is the transitivity of its complement. -/
def AlmostConnected (q : GQ α) : Prop :=
  ∀ (A B C : α → Prop), q A B → q A C ∨ q C B

/-- A quantifier is circular when `Q(A, B)` and `Q(B, C)` give `Q(C, A)`. -/
def Circular (q : GQ α) : Prop :=
  ∀ (A B C : α → Prop), q A B → q B C → q C A

/-- A quantifier is right continuous when `Q(A, B₁)`, `Q(A, B₂)` and `B₁ ⊆ B ⊆ B₂` give
`Q(A, B)`; every scope-monotone quantifier is right continuous. -/
def RightContinuous (q : GQ α) : Prop :=
  ∀ (A B B₁ B₂ : α → Prop),
    (∀ x, B₁ x → B x) →
    (∀ x, B x → B₂ x) →
    q A B₁ → q A B₂ → q A B

/-- A quantifier is scope-intersective when `Q(A, B)` and `Q(A, C)` give `Q(A, B ∩ C)`. -/
def ScopeIntersective (q : GQ α) : Prop :=
  ∀ (A B C : α → Prop),
    q A B → q A C → q A (fun x => B x ∧ C x)

/-- A quantifier is filtrating when it is scope monotone and scope-intersective, so that its
scopes at a fixed restrictor form a filter. -/
def Filtrating (q : GQ α) : Prop := ScopeMonotone q ∧ ScopeIntersective q

/-! ### Invariance -/

/-- A quantifier is quantity invariant when it is invariant under permutations of the domain,
so that `Q(A, B)` depends only on the pattern of the two predicates and not on which elements
satisfy them. This is Mostowski's permutation invariance for type ⟨1, 1⟩ quantifiers. -/
def QuantityInvariant (q : GQ α) : Prop :=
  ∀ (A B A' B' : α → Prop) (f : α → α),
    Function.Bijective f →
    (∀ x, A (f x) ↔ A' x) → (∀ x, B (f x) ↔ B' x) →
    (q A B ↔ q A' B')

/-! ### The Boolean algebra, the negations and the dual

The outer negation of a quantifier is its complement `qᶜ`, and determiner conjunction and
disjunction are the meet `f ⊓ g` and join `f ⊔ g` of the Boolean algebra `GQ α`; the lemmas
below are their pointwise normal forms. -/

@[simp] theorem compl_apply (q : GQ α) (R S : α → Prop) : qᶜ R S = ¬ q R S := rfl

@[simp] theorem inf_apply (f g : GQ α) (R S : α → Prop) : (f ⊓ g) R S = (f R S ∧ g R S) := rfl

@[simp] theorem sup_apply (f g : GQ α) (R S : α → Prop) : (f ⊔ g) R S = (f R S ∨ g R S) := rfl

/-- The inner negation of a quantifier, `(Q~)(A, B) = Q(A, ¬ B)`. -/
def innerNeg (q : GQ α) : GQ α :=
  fun R S => q R (fun x => ¬ S x)

/-- The dual of a quantifier, `Q̌ = (Q~)ᶜ`, so that the dual of *every* is *some*. -/
def dual (q : GQ α) : GQ α := (innerNeg q)ᶜ

/-! ### Restriction -/

/-- The restriction of a quantifier by an adjective or relative clause narrows the restrictor,
so that *tall student* is *student* and *tall*. -/
def adjRestrict (q : GQ α) (adj : α → Prop) : GQ α :=
  fun R S => q (fun x => R x ∧ adj x) S

end GQ

/-! ### Type ⟨1⟩ quantifiers -/

namespace NP

/-- A type ⟨1⟩ quantifier lives on `A` when `Q(B) ↔ Q(A ∩ B)` for every `B`. -/
def LivesOn (Q : NP α) (A : α → Prop) : Prop :=
  ∀ B, Q B ↔ Q (fun x => A x ∧ B x)

theorem _root_.Quantifier.GQ.Conservative.livesOn {q : GQ α} (h : GQ.Conservative q)
    (A : α → Prop) : LivesOn (q A) A := h A

/-- The Montague lift of an entity is the principal ultrafilter it generates, the type ⟨1⟩
quantifier of the properties it has; it is Partee's LIFT and the continuation `pure`. -/
def individual (a : α) : NP α := fun P => P a

theorem individual_injective : Function.Injective (individual (α := α)) :=
  fun a b h => (show b = a from (congrFun h (· = a)).mp rfl).symm

theorem individual_livesOn {A : α → Prop} {a : α} (ha : A a) : LivesOn (individual a) A :=
  fun _ ↦ ⟨fun h ↦ ⟨ha, h⟩, And.right⟩

end NP

end Quantifier
