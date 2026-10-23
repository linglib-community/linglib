module

public import Linglib.Semantics.Quantification.Counting

/-!
# Polyadic quantifiers

This file defines three ways of building a quantifier over binary relations from generalized
quantifiers over sets. Iteration nests one quantifier in the scope of another, as in
*every student read some book*. Resumption applies one quantifier to pairs, binding both
argument places at once, as in the reading of *men are usually taller than women* that counts
pairs of a man and a woman; since it evaluates the quantifier on the universe of pairs, it takes
a quantifier given on every universe, a `GQ.Family`. Branching evaluates two quantifiers
independently, neither in the scope of the other, as Hintikka proposed for *some relative of
each villager and some friend of each townsman hate each other*. Peters and Westerståhl treat
all three, and de Swart and Sag analyse negative concord as the resumption of *no*.

A sentence with two quantifiers has two linear scope readings, which are the two orders of
iteration.

## Main definitions

* `Quantifier.Polyadic.iterate`: the iteration `Q₁x Q₂y R(x, y)` of two quantifiers.
* `Quantifier.Polyadic.resume`: the binary resumption `Q⟨x, y⟩ R(x, y)` of a quantifier.
* `Quantifier.Polyadic.branch`: the branching of two quantifiers, witnessed by choice functions.
* `Quantifier.Polyadic.surfaceScope`, `Quantifier.Polyadic.inverseScope`: the two linear scope
  readings of a two-quantifier sentence.

## Main results

* `Quantifier.Polyadic.iterate_every_some_of_some_every`: `∃∀` entails `∀∃`, so the two linear
  readings of an *every*/*some* pair are nested.
* `Quantifier.Polyadic.resume_no_iff`, `Quantifier.Polyadic.resume_no_iff_iterate_every_no`: the
  resumption of *no* is the iteration of *no* and *some*, and of *every* and *no*.
* `Quantifier.Polyadic.iterate_mono`, `Quantifier.Polyadic.resume_mono`: iteration and resumption
  of scope-upward-monotone quantifiers are monotone in the relation.

## TODO

`branch` states branching with a pair of choice functions. Barwise's formulation for
upward-monotone quantifiers instead asks for sets `X ⊆ A` and `Y ⊆ B` with `Q₁ A X`, `Q₂ B Y`
and `X × Y ⊆ R`; the two should be compared against the sources.

## References

* [peters-westerstahl-2006]
* [hintikka-1996]
* [de-swart-sag-2002]
-/

@[expose] public section

namespace Quantifier.Polyadic

open Quantifier Quantifier.GQ

universe u

variable {α : Type u} {Q₁ Q₂ : GQ α} {A B : α → Prop} {R R' : α → α → Prop}

/-! ### Iteration and branching -/

/-- The iteration `Q₁x Q₂y R(x, y)` nests `Q₂` in the scope of `Q₁`, so that *every student
read some book* is `iterate every student some book read`. -/
def iterate (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  Q₁ A fun x ↦ Q₂ B fun y ↦ R x y

/-- The branching of `Q₁` and `Q₂` evaluates them independently, neither in the scope of the
other. There are choice functions `f` and `g` such that `Q₁` holds of the `x` related to their
`B`-witness `f x`, and `Q₂` of the `y` related to their `A`-witness `g y`. -/
def branch (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  ∃ f g : α → α,
    Q₁ A (fun x ↦ B (f x) ∧ R x (f x)) ∧
    Q₂ B (fun y ↦ A (g y) ∧ R (g y) y)

theorem iterate_no_no_iff : iterate no no A B R ↔ iterate every GQ.some A B R := by
  simp [iterate, no, every, GQ.some]

/-! ### Resumption -/

section Resumption

variable [Fintype α] {Q : GQ.Family.{u}}

/-- The binary resumption `Q⟨x, y⟩ R(x, y)` evaluates `Q` on the universe of pairs, with the
pairs in `A × B` as its restrictor and `R` as its scope. This is the resumption of Peters and
Westerståhl with a product restrictor, de Swart and Sag's type `⟨1, 1, 2⟩`. -/
def resume (Q : GQ.Family.{u}) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  Q (α × α) (fun p ↦ A p.1 ∧ B p.2) fun p ↦ R p.1 p.2

theorem resume_some_iff : resume GQ.Family.some A B R ↔ iterate GQ.some GQ.some A B R :=
  ⟨fun ⟨p, hp, hr⟩ ↦ ⟨p.1, hp.1, p.2, hp.2, hr⟩, fun ⟨x, hx, y, hy, hr⟩ ↦ ⟨(x, y), ⟨hx, hy⟩, hr⟩⟩

theorem resume_every_iff : resume GQ.Family.every A B R ↔ iterate every every A B R :=
  ⟨fun h x hx y hy ↦ h (x, y) ⟨hx, hy⟩, fun h _ hp ↦ h _ hp.1 _ hp.2⟩

theorem resume_no_iff : resume GQ.Family.no A B R ↔ iterate no GQ.some A B R :=
  ⟨fun h x hx ⟨y, hy, hr⟩ ↦ h (x, y) ⟨hx, hy⟩ hr, fun h _ hp hr ↦ h _ hp.1 ⟨_, hp.2, hr⟩⟩

theorem resume_no_iff_iterate_every_no : resume GQ.Family.no A B R ↔ iterate every no A B R :=
  ⟨fun h x hx y hy ↦ h (x, y) ⟨hx, hy⟩, fun h _ hp ↦ h _ hp.1 _ hp.2⟩

theorem resume_mono (h : ScopeMonotone (Q (α × α))) (hR : ∀ x y, R x y → R' x y) :
    resume Q A B R → resume Q A B R' :=
  h _ fun p ↦ hR p.1 p.2

end Resumption

/-! ### Scope order -/

/-- The surface-scope reading of a two-quantifier sentence, on which the first quantifier
outscopes the second. -/
def surfaceScope (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  iterate Q₁ Q₂ A B R

/-- The inverse-scope reading of a two-quantifier sentence, on which the second quantifier
outscopes the first. -/
def inverseScope (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  iterate Q₂ Q₁ B A fun y x ↦ R x y

theorem iterate_every_some_of_some_every (A B : α → Prop) (R : α → α → Prop)
    (h : iterate GQ.some every A B R) : iterate every GQ.some B A (flip R) :=
  let ⟨x, hx, hall⟩ := h; fun y hy ↦ ⟨x, hx, hall y hy⟩

/-! ### Monotonicity -/

theorem iterate_mono (h₁ : ScopeMonotone Q₁) (h₂ : ScopeMonotone Q₂)
    (hR : ∀ x y, R x y → R' x y) : iterate Q₁ Q₂ A B R → iterate Q₁ Q₂ A B R' :=
  h₁ A fun x ↦ h₂ B (hR x)

end Quantifier.Polyadic
