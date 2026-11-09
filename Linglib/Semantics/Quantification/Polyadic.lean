module

public import Linglib.Semantics.Quantification.Counting
public import Mathlib.Logic.Function.Basic

/-!
# Polyadic quantifiers

This file defines three ways of building a quantifier over binary relations from generalized
quantifiers over sets. Iteration nests one quantifier in the scope of another, as in
*every student read some book*. Resumption applies one quantifier to pairs, binding both
argument places at once, as in the reading of *men are usually taller than women* that counts
pairs of a man and a woman; since it evaluates the quantifier on the universe of pairs, it takes
a quantifier given on every universe, a `Det.Family`. Branching evaluates two quantifiers
independently, neither in the scope of the other, as Hintikka proposed for *some relative of
each villager and some friend of each townsman hate each other*. Peters and Westerståhl treat
all three, and de Swart and Sag analyse negative concord as the resumption of *no*.

A sentence with two quantifiers has two linear scope readings, which are the two orders of
iteration, [the two orders in which one quantifier takes scope over the
other](##Quantifier.Polyadic.iterate_iff_curry).

Iteration is composition with the accusative extension `acc`, which applies a quantifier to the
rows of a relation, so a function from relations to truth values is
[reducible](##Quantifier.Polyadic.Reducible), in the sense of Keenan's Frege boundary, when it is
such a composition. [Reducible functions agreeing on the cross products are
equal](##Quantifier.Polyadic.Reducible.eq_of_forall_prod), and a function is reducible [exactly when
some accusative extension refines
it](##Quantifier.Polyadic.reducible_iff_exists_factorsThrough), which sees each row through a
two-valued test, so that [of any three rows two are
interchangeable](##Quantifier.Polyadic.Reducible.exists_interchangeable).

## Main definitions

* `Quantifier.Polyadic.iterate`: the iteration `Q₁x Q₂y R(x, y)` of two quantifiers.
* `Quantifier.Polyadic.acc`, `Quantifier.Polyadic.Reducible`: the accusative extension of a
  quantifier, and the functions from relations to truth values that are compositions of quantifiers.
* `Quantifier.Polyadic.resume`: the binary resumption `Q⟨x, y⟩ R(x, y)` of a quantifier.
* `Quantifier.Polyadic.branch`: the branching of two quantifiers, witnessed by choice functions.

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
* [keenan-1992]
-/

@[expose] public section

namespace Quantifier.Polyadic

open Quantifier Quantifier.Det

universe u

variable {α : Type u} {Q₁ Q₂ : Det α} {A B : Set α} {R R' : α → α → Prop}

/-! ### Iteration and branching -/

/-- The accusative extension of a quantifier maps a relation to the individuals whose row it holds
of, so that *every student* maps *likes* to the set of those who like every student. -/
def acc (Q : Quantifier α) (R : α → α → Prop) : Set α := {x | Q {y | R x y}}

@[simp] theorem mem_acc {Q : Quantifier α} {x : α} : x ∈ acc Q R ↔ Q {y | R x y} := .rfl

/-- The iteration `Q₁x Q₂y R(x, y)` nests `Q₂` in the scope of `Q₁`, so that *every student
read some book* is `iterate every student some book read`. -/
def iterate (Q₁ Q₂ : Det α) (A B : Set α) (R : α → α → Prop) : Prop := Q₁ A (acc (Q₂ B) R)

/-- Iteration is the first quantifier taking scope over the second. -/
theorem iterate_iff_curry : iterate Q₁ Q₂ A B R ↔ (Q₁ A).curry (Q₂ B) {p | R p.1 p.2} := .rfl

/-- The branching of `Q₁` and `Q₂` evaluates them independently, neither in the scope of the
other. There are choice functions `f` and `g` such that `Q₁` holds of the `x` related to their
`B`-witness `f x`, and `Q₂` of the `y` related to their `A`-witness `g y`. -/
def branch (Q₁ Q₂ : Det α) (A B : Set α) (R : α → α → Prop) : Prop :=
  ∃ f g : α → α, Q₁ A {x | f x ∈ B ∧ R x (f x)} ∧ Q₂ B {y | g y ∈ A ∧ R (g y) y}

theorem iterate_no_no_iff : iterate no no A B R ↔ iterate every Det.some A B R :=
  forall_congr' fun _ ↦ imp_congr_right fun _ ↦ (not_congr no_iff_not_some).trans not_not

/-! ### Resumption -/

section Resumption

variable [Finite α] {Q : Det.Family.{u}}

/-- The binary resumption `Q⟨x, y⟩ R(x, y)` evaluates `Q` on the universe of pairs, with the
pairs in `A ×ˢ B` as its restrictor and `R` as its scope. This is the resumption of Peters and
Westerståhl with a product restrictor, de Swart and Sag's type `⟨1, 1, 2⟩`. -/
def resume (Q : Det.Family.{u}) (A B : Set α) (R : α → α → Prop) : Prop :=
  Q (α × α) (A ×ˢ B) {p | R p.1 p.2}

theorem resume_some_iff : resume Det.Family.some A B R ↔ iterate Det.some Det.some A B R :=
  ⟨fun ⟨p, hp, hr⟩ ↦ ⟨p.1, hp.1, p.2, hp.2, hr⟩, fun ⟨x, hx, y, hy, hr⟩ ↦ ⟨(x, y), ⟨hx, hy⟩, hr⟩⟩

theorem resume_every_iff : resume Det.Family.every A B R ↔ iterate every every A B R :=
  ⟨fun h _ hx _ hy ↦ h (Set.mk_mem_prod hx hy), fun h _ hp ↦ h hp.1 hp.2⟩

/-- The resumption of *no* is the iteration of *no* and *some*, so a negative chain read by
resumption denies every pair. -/
theorem resume_no_iff : resume Det.Family.no A B R ↔ iterate no Det.some A B R :=
  ⟨fun h _ hx ⟨_, hy, hr⟩ ↦ h (Set.mk_mem_prod hx hy) hr, fun h _ hp hr ↦ h hp.1 ⟨_, hp.2, hr⟩⟩

/-- The resumption of *no* is also the iteration of *every* and *no*. -/
theorem resume_no_iff_iterate_every_no : resume Det.Family.no A B R ↔ iterate every no A B R :=
  ⟨fun h _ hx _ hy ↦ h (Set.mk_mem_prod hx hy), fun h _ hp ↦ h hp.1 hp.2⟩

/-- The resumption of a quantifier that is scope-upward-monotone on pairs is monotone in the
relation. -/
theorem resume_mono (h : (Q (α × α)).ScopeMonotone) (hR : ∀ x y, R x y → R' x y) :
    resume Q A B R → resume Q A B R' :=
  h _ fun p ↦ hR p.1 p.2

end Resumption

/-! ### Scope order -/

/-- The two scope orders of a two-quantifier sentence are the two orders of iteration, the second
with the relation's arguments exchanged. -/
theorem iterate_flip_iff_map_swap_curry :
    iterate Q₂ Q₁ B A (flip R) ↔ ((Q₂ B).curry (Q₁ A)).map Prod.swap {p | R p.1 p.2} := .rfl

/-- An existential scoping over a universal entails the universal scoping over the existential,
so the two linear readings of an *every*/*some* pair are nested. -/
theorem iterate_every_some_of_some_every (A B : Set α) (R : α → α → Prop)
    (h : iterate Det.some every A B R) : iterate every Det.some B A (flip R) :=
  let ⟨x, hx, hall⟩ := h; fun _ hy ↦ ⟨x, hx, hall hy⟩

/-! ### Monotonicity -/

/-- The iteration of two scope-upward-monotone quantifiers is monotone in the relation. -/
theorem iterate_mono (h₁ : Q₁.ScopeMonotone) (h₂ : Q₂.ScopeMonotone)
    (hR : ∀ x y, R x y → R' x y) : iterate Q₁ Q₂ A B R → iterate Q₁ Q₂ A B R' :=
  h₁ A fun x ↦ h₂ B (hR x)

/-! ### Accusative extension and reducibility -/

section Reducible

variable {g : Quantifier α} {F G : (α → α → Prop) → Prop}

/-- Conservativity iterates: only the pairs in `A × B` matter to `Q₁x Q₂y R(x, y)`. -/
theorem iterate_inter_prod (h₁ : Q₁.Conservative) (h₂ : Q₂.Conservative) :
    iterate Q₁ Q₂ A B R ↔ iterate Q₁ Q₂ A B fun x y ↦ R x y ∧ x ∈ A ∧ y ∈ B :=
  h₁.congr_scope fun x hx ↦ h₂.congr_scope fun y hy ↦ by simp [hx, hy]

/-- A function from relations to truth values is reducible, or Fregean, when it is a quantifier
composed with the accusative extension of a quantifier. -/
def Reducible (F : (α → α → Prop) → Prop) : Prop := ∃ f g : Quantifier α, ∀ R, F R ↔ f (acc g R)

theorem reducible_iterate : Reducible (iterate Q₁ Q₂ A B) := ⟨Q₁ A, Q₂ B, fun _ ↦ .rfl⟩

/-- [keenan-1992]'s Reducibility Characterization: a function is reducible exactly when the
accusative extension of some quantifier refines it. Keenan asks for a positive quantifier, which
`Reducible.exists_positive` supplies. -/
theorem reducible_iff_exists_factorsThrough :
    Reducible F ↔ ∃ g : Quantifier α, Function.FactorsThrough F (acc g) := by
  refine ⟨fun ⟨f, g, h⟩ ↦ ⟨g, fun R S e ↦ propext ?_⟩, fun ⟨g, h⟩ ↦ ?_⟩
  · rw [h, h, e]
  · obtain ⟨f, hf⟩ := (Function.factorsThrough_iff F).1 h
    exact ⟨f, g, fun R ↦ iff_of_eq (congrFun hf R)⟩

/-- A reducible function has a positive right factor, false of the empty set. -/
theorem Reducible.exists_positive (h : Reducible F) :
    ∃ f g : Quantifier α, ¬ g ∅ ∧ ∀ R, F R ↔ f (acc g R) := by
  obtain ⟨f, g, h⟩ := h
  by_cases hg : g ∅
  · refine ⟨fun S ↦ f Sᶜ, gᶜ, not_not.2 hg, fun R ↦ (h R).trans (iff_of_eq (congrArg f ?_))⟩
    exact (compl_compl _).symm
  · exact ⟨f, g, hg, h⟩

theorem acc_prod_of_pos {P Y : Set α} (h₀ : ¬ g ∅) (hY : g Y) :
    acc g (fun x y ↦ (x, y) ∈ P ×ˢ Y) = P := by
  refine Set.ext fun x ↦ ?_
  by_cases hx : x ∈ P
  · simpa [hx] using hY
  · simpa [hx] using h₀

theorem acc_prod_of_neg {P Y : Set α} (h₀ : ¬ g ∅) (hY : ¬ g Y) :
    acc g (fun x y ↦ (x, y) ∈ P ×ˢ Y) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
  by_cases hx' : x ∈ P <;> simp_all

/-- Under a positive quantifier every relation has the accusative extension of a cross product. -/
theorem exists_acc_prod_eq (h₀ : ¬ g ∅) (R : α → α → Prop) :
    ∃ P Y : Set α, acc g (fun x y ↦ (x, y) ∈ P ×ˢ Y) = acc g R := by
  obtain h | ⟨b, hb⟩ := (acc g R).eq_empty_or_nonempty
  · exact ⟨∅, ∅, by rw [acc_prod_of_neg h₀ h₀, h]⟩
  · exact ⟨acc g R, {y | R b y}, acc_prod_of_pos h₀ hb⟩

/-- [keenan-1992]'s Reducibility Equivalence: reducible functions agreeing on the cross products
are equal. -/
theorem Reducible.eq_of_forall_prod (hF : Reducible F) (hG : Reducible G)
    (h : ∀ P Y : Set α, F (fun x y ↦ (x, y) ∈ P ×ˢ Y) ↔ G fun x y ↦ (x, y) ∈ P ×ˢ Y) : F = G := by
  obtain ⟨f, f', hf₀, hf⟩ := hF.exists_positive
  obtain ⟨g, g', hg₀, hg⟩ := hG.exists_positive
  have main {f f' g g' : Quantifier α} {F G : (α → α → Prop) → Prop} (hf₀ : ¬ f' ∅) (hg₀ : ¬ g' ∅)
      (hf : ∀ R, F R ↔ f (acc f' R)) (hg : ∀ R, G R ↔ g (acc g' R))
      (h : ∀ P Y : Set α, F (fun x y ↦ (x, y) ∈ P ×ˢ Y) ↔ G fun x y ↦ (x, y) ∈ P ×ˢ Y)
      {Y : Set α} (hY : f' Y) (hY' : ¬ g' Y) (R) :
      F R ↔ G R := by
    have hc (P : Set α) : f P ↔ g ∅ := by
      have := h P Y
      rwa [hf, hg, acc_prod_of_pos hf₀ hY, acc_prod_of_neg hg₀ hY'] at this
    obtain ⟨P, Q, e⟩ := exists_acc_prod_eq hg₀ R
    rw [hf, hc, hg, ← e, ← hg, ← h, hf, hc]
  refine funext fun R ↦ propext ?_
  by_cases e : f' = g'
  · subst e
    obtain ⟨P, Q, e⟩ := exists_acc_prod_eq hf₀ R
    rw [hf, hg, ← e, ← hf, ← hg]
    exact h P Q
  · obtain ⟨Y, hY⟩ := Function.ne_iff.1 e
    by_cases hY' : f' Y
    · exact main hf₀ hg₀ hf hg h hY' (fun h' ↦ hY (propext (iff_of_true hY' h'))) R
    · have hg' : g' Y := by_contra fun h' ↦ hY (propext (iff_of_false hY' h'))
      exact (main hg₀ hf₀ hg hf (fun P Y ↦ (h P Y).symm) hg' hY' R).symm

/-- A reducible function sees a row only through a two-valued test, so of any three rows two are
interchangeable at every position of every relation. -/
theorem Reducible.exists_interchangeable [DecidableEq α] (h : Reducible F) (r₀ r₁ r₂ : α → Prop) :
    (∀ R x, F (Function.update R x r₀) ↔ F (Function.update R x r₁)) ∨
      (∀ R x, F (Function.update R x r₀) ↔ F (Function.update R x r₂)) ∨
        ∀ R x, F (Function.update R x r₁) ↔ F (Function.update R x r₂) := by
  obtain ⟨f, g, hF⟩ := h
  have key {r r' : α → Prop} (hg : g {z | r z} ↔ g {z | r' z}) (R : α → α → Prop) (x : α) :
      F (Function.update R x r) ↔ F (Function.update R x r') := by
    rw [hF, hF]
    refine iff_of_eq (congrArg f (Set.ext fun y ↦ ?_))
    by_cases hy : y = x
    · subst hy
      simpa only [mem_acc, Function.update_self] using hg
    · simp only [mem_acc, Function.update_of_ne hy]
  by_cases h₁ : g {z | r₀ z} ↔ g {z | r₁ z}
  · exact .inl (key h₁)
  by_cases h₂ : g {z | r₀ z} ↔ g {z | r₂ z}
  · exact .inr (.inl (key h₂))
  · exact .inr (.inr (key (by tauto)))

end Reducible

end Quantifier.Polyadic
