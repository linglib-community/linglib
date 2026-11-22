module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Relation
public import Linglib.Core.Data.Set.Functor
public import Linglib.Semantics.Mereology.Basic

/-!
# Cumulative predication

This file relates the two forms of the cumulative operator `**` on relations between
individuals. In the coverage form of [beck-sauerland-2000], `**R` holds of two pluralities when
every member of the first is `R`-related to some member of the second and conversely: this is
the relation lifting `Set.LiftRel R` of `Linglib/Core/Data/Set/Functor.lean`, and over a
singleton it is distribution (`Set.liftRel_singleton_right`), the number effect of
[johnston-2023]. In the closure form of [krifka-1986] and [sternefeld-1998], `**R` is the
smallest relation containing `R` and closed under componentwise sum, which is Link's `*` on the
product semilattice. The two agree on nonempty finite sets of individuals.

## Definitions

* `Plurality.Cumulativity.Cumulation R x y`: the closure form, on any pair of
  join-semilattices.

## Main results

* `Plurality.Cumulativity.cumulation_iff_of_cum`: a cumulative relation is its own cumulation.
* `Plurality.Cumulativity.cumulation_map_singleton`: on finite sets, the closure form of a
  relation between individuals is the coverage form, `Set.LiftRel`, of a nonempty pair.

## References

* [M. Krifka, *Nominalreferenz und Zeitkonstitution* (1986)][krifka-1986]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
* [S. Beck and U. Sauerland, *Cumulation is needed: A reply to Winter (2000)*
  (2000)][beck-sauerland-2000]
* [G. Link, *The logical analysis of plurals and mass terms* (1983)][link-1983]
* [W. Johnston, *Pair-list answers to questions with plural definites* (2023)][johnston-2023]
-/

@[expose] public section

namespace Plurality.Cumulativity

/-! ### Closure form

Krifka's `**R` is Link's `*` applied to `R` as a predicate on the product semilattice: the
smallest relation containing `R` and closed under componentwise sum. -/

section Closure

open Mereology

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β] {R S : α → β → Prop}
  {x x' : α} {y y' : β}

/-- The cumulation `**R` of a relation ([krifka-1986]; [sternefeld-1998]): the closure of `R`
under componentwise sum, `supClosure` on the product semilattice. -/
def Cumulation (R : α → β → Prop) (x : α) (y : β) : Prop :=
  (x, y) ∈ supClosure {p : α × β | R p.1 p.2}

theorem Cumulation.of_rel (h : R x y) : Cumulation R x y := subset_supClosure h

theorem Cumulation.sup (h : Cumulation R x y) (h' : Cumulation R x' y') :
    Cumulation R (x ⊔ x') (y ⊔ y') :=
  supClosed_supClosure h h'

theorem Cumulation.mono (hRS : ∀ x y, R x y → S x y) (h : Cumulation R x y) :
    Cumulation S x y :=
  supClosure_mono (fun p hp ↦ hRS p.1 p.2 hp) h

/-- A cumulative relation is its own cumulation. -/
theorem cumulation_iff_of_cum (hR : CUM {p : α × β | R p.1 p.2}) : Cumulation R x y ↔ R x y :=
  Set.ext_iff.1 hR.supClosure_eq (x, y)

end Closure

/-! ### Sets of individuals -/

section Finset

open Mereology

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- On finite sets, `**` of a relation between individuals, taken as singletons, is
bidirectional coverage of a nonempty pair: the closure form of [krifka-1986] and the coverage
form of [beck-sauerland-2000] agree away from the empty pair. -/
theorem cumulation_map_singleton (R : A → B → Prop) (x : Finset A) (y : Finset B) :
    Cumulation (Relation.Map R ({·}) ({·})) x y ↔ x.Nonempty ∧ Set.LiftRel R ↑x ↑y := by
  constructor
  · suffices ∀ p : Finset A × Finset B,
        p ∈ supClosure {p : Finset A × Finset B | Relation.Map R ({·}) ({·}) p.1 p.2} →
          p.1.Nonempty ∧ Set.LiftRel R ↑p.1 ↑p.2 from this (x, y)
    intro p h
    induction h using supClosure_induction with
    | mem p h =>
      obtain ⟨x, y⟩ := p
      change ∃ a b, R a b ∧ ({a} : Finset A) = x ∧ ({b} : Finset B) = y at h
      obtain ⟨a, b, hab, rfl, rfl⟩ := h
      refine ⟨Finset.singleton_nonempty a, ?_⟩
      rw [Finset.coe_singleton, Finset.coe_singleton, Set.liftRel_singleton]
      exact hab
    | sup _ _ _ _ ih ih' =>
      refine ⟨ih.1.mono Finset.subset_union_left, ?_⟩
      rw [Prod.fst_sup, Prod.snd_sup,
        Finset.coe_union, Finset.coe_union]
      exact ih.2.union ih'.2
  · rintro ⟨hx, hl, hr⟩
    have : Nonempty B := hx.elim fun a ha ↦ (hl a ha).elim fun b _ ↦ ⟨b⟩
    have : Nonempty A := hx.elim fun a _ ↦ ⟨a⟩
    choose! f hf hRf using hl
    choose! g hg hRg using hr
    have hy : y.Nonempty := hx.elim fun a ha ↦ ⟨f a, hf a ha⟩
    have key : x.sup' hx (fun a ↦ ({a}, {f a})) ⊔ y.sup' hy (fun b ↦ ({g b}, {b})) = (x, y) := by
      refine le_antisymm (sup_le ((Finset.sup'_le_iff _ _).2 fun a ha ↦ ?_)
        ((Finset.sup'_le_iff _ _).2 fun b hb ↦ ?_))
        (Prod.le_def.2 ⟨Finset.subset_iff.2 fun a ha ↦ ?_, Finset.subset_iff.2 fun b hb ↦ ?_⟩)
      · exact Prod.le_def.2
          ⟨Finset.singleton_subset_iff.2 ha, Finset.singleton_subset_iff.2 (hf a ha)⟩
      · exact Prod.le_def.2
          ⟨Finset.singleton_subset_iff.2 (hg b hb), Finset.singleton_subset_iff.2 hb⟩
      · have hle :=
          Prod.le_def.1 (Finset.le_sup' (fun a ↦ (({a} : Finset A), ({f a} : Finset B))) ha)
        rw [Prod.fst_sup]
        exact Finset.mem_union_left _ (Finset.singleton_subset_iff.1 hle.1)
      · have hle :=
          Prod.le_def.1 (Finset.le_sup' (fun b ↦ (({g b} : Finset A), ({b} : Finset B))) hb)
        rw [Prod.snd_sup]
        exact Finset.mem_union_right _ (Finset.singleton_subset_iff.1 hle.2)
    have hmem (a : A) (b : B) (h : R a b) : (({a} : Finset A), ({b} : Finset B)) ∈
        {p : Finset A × Finset B | Relation.Map R ({·}) ({·}) p.1 p.2} := ⟨a, b, h, rfl, rfl⟩
    show (x, y) ∈ supClosure _
    rw [← key]
    exact supClosed_supClosure (finsetSup'_mem_supClosure hx fun a ha ↦ hmem _ _ (hRf a ha))
      (finsetSup'_mem_supClosure hy fun b hb ↦ hmem _ _ (hRg b hb))

end Finset

end Plurality.Cumulativity
