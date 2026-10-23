/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.StarFree`, after the
syntactic-monoid and variety substrate.
-/
module

public import Mathlib.Order.CompleteLattice.Finset
public import Linglib.Core.Algebra.FreeMonoid.Basic
public import Linglib.Core.Computability.Variety.Langs

/-!
# Star-free languages

This file defines the star-free languages as the regular languages with an aperiodic syntactic
monoid. By Schützenberger's theorem these are the languages of the star-free regular expressions,
built from finite sets by union, concatenation and complement without Kleene star; McNaughton and
Papert show that they are also the counter-free and the first-order definable languages. Star-free
is the instance `Monoid.aperiodicVariety` of the languages of a pseudovariety, so its closure
properties are corollaries of `Monoid.Pseudovariety.langs`.

## Main definitions

* `Language.IsStarFree`: the languages of `Monoid.aperiodicVariety`.

## Main results

* `Language.isStarFree_iff`: a language is star-free exactly when it is regular with an aperiodic
  syntactic monoid.
* `Language.IsStarFree.compl`, `Language.IsStarFree.inter`, `Language.IsStarFree.union`: Boolean
  closure.
* `Language.IsStarFree.of_recognizes`, `Language.IsStarFree.of_factorsThrough`: a language is
  star-free when a finite aperiodic monoid recognizes it, or when membership factors through a
  finite invariant that respects concatenation and stabilizes on powers.
* `Language.IsStarFree.comap`: closure under inverse homomorphisms, with the erasing instance
  `Language.IsStarFree.preimage_filter`.

## References

* [schutzenberger-1965]
* [mcnaughton-papert-1971]
-/

@[expose] public section

namespace Language

variable {α : Type*} {L : Language α}

/-- A language is *star-free* when its syntactic monoid is finite and aperiodic, that is, when it
is a language of the pseudovariety of aperiodic monoids. -/
def IsStarFree (L : Language α) : Prop := Monoid.aperiodicVariety.langs L

theorem isStarFree_iff : L.IsStarFree ↔ L.IsRegular ∧ Monoid.IsAperiodic L.SyntacticMonoid :=
  ⟨fun h ↦ ⟨.of_finite_syntacticMonoid h.1, h.2⟩, fun h ↦ ⟨h.1.finite_syntacticMonoid, h.2⟩⟩

theorem IsStarFree.isRegular (h : L.IsStarFree) : L.IsRegular := .of_finite_syntacticMonoid h.1

theorem IsStarFree.isAperiodic (h : L.IsStarFree) :
    Monoid.IsAperiodic L.SyntacticMonoid := h.2

theorem IsStarFree.compl (h : L.IsStarFree) : Lᶜ.IsStarFree :=
  Monoid.aperiodicVariety.langs_compl h

theorem IsStarFree.inter {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊓ M).IsStarFree :=
  Monoid.aperiodicVariety.langs_inf hL hM

theorem IsStarFree.union {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊔ M).IsStarFree :=
  Monoid.aperiodicVariety.langs_sup hL hM

theorem IsStarFree.of_recognizes {M : Type*} [Monoid M] [Finite M]
    (hM : Monoid.IsAperiodic M) (η : FreeMonoid α →* M) (P : Set M)
    (hL : ∀ w : List α, w ∈ L ↔ η (FreeMonoid.ofList w) ∈ P) : L.IsStarFree := by
  obtain ⟨N, f, hf⟩ := Recognizes.syntacticMonoid_isSubquotient (φ := η) ⟨P, Set.ext hL⟩
  exact ⟨.of_surjective f hf, (hM.of_injective N.subtype_injective).of_surjective hf⟩

theorem IsStarFree.of_factorsThrough {β : Type*} {g : List α → β} {n : ℕ}
    (hL : Function.FactorsThrough (· ∈ L) g)
    (hg : ∀ ⦃u u' v v'⦄, g u = g u' → g v = g v' → g (u ++ v) = g (u' ++ v'))
    (hfin : (Set.range g).Finite)
    (hpow : ∀ w, g (List.replicate (n + 1) w).flatten = g (List.replicate n w).flatten) :
    L.IsStarFree := by
  have hcls : Function.FactorsThrough L.syntacticClass g := fun _ _ e ↦
    syntacticClass_eq_iff.mpr fun _ _ ↦ iff_of_eq (hL (hg (hg rfl e) rfl))
  refine ⟨Set.finite_univ_iff.mp ?_, n, fun x ↦ ?_⟩
  · exact L.syntacticClass_surjective.range_eq ▸ hcls.finite_range hfin
  · obtain ⟨w, rfl⟩ := L.syntacticClass_surjective x
    simpa [syntacticClass_flatten] using hcls (hpow w)

theorem IsStarFree.exists_flatten_replicate_succ_mem_iff (h : L.IsStarFree) :
    ∃ n, ∀ w : List α,
      (List.replicate (n + 1) w).flatten ∈ L ↔ (List.replicate n w).flatten ∈ L := by
  obtain ⟨n, hn⟩ := h.isAperiodic
  exact ⟨n, fun w ↦ mem_iff_of_syntacticClass_eq <| by
    simpa [syntacticClass_flatten] using hn (L.syntacticClass w)⟩

theorem not_isStarFree_setOf_even_length [Nonempty α] :
    ¬ IsStarFree {w : List α | Even w.length} := fun h ↦ by
  obtain ⟨n, hn⟩ := h.exists_flatten_replicate_succ_mem_iff
  have h' := hn [Classical.arbitrary α]
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq] at h'
  simp [Nat.even_add_one, -Nat.not_even_iff_odd] at h'

theorem IsStarFree.comap {α β : Type*} {L : Language β} (h : L.IsStarFree)
    (φ : FreeMonoid α →* FreeMonoid β) :
    Language.IsStarFree {w : List α | φ (FreeMonoid.ofList w) ∈ L} := by
  have := h.1
  obtain ⟨S, hS⟩ := L.recognizes_toSyntacticMonoid.comap φ
  exact .of_recognizes h.2 _ S (Set.ext_iff.mp hS)

theorem IsStarFree.preimage_filter (h : L.IsStarFree) (p : α → Bool) :
    IsStarFree {w | w.filter p ∈ L} :=
  h.comap (FreeMonoid.filter p)

theorem isStarFree_univ : IsStarFree (Set.univ : Language α) :=
  Monoid.aperiodicVariety.langs_univ

theorem IsStarFree.iInter {ι : Type*} [Finite ι] {f : ι → Set (List α)}
    (h : ∀ i, IsStarFree (f i)) : IsStarFree (⋂ i, f i) := by
  have := Fintype.ofFinite ι
  classical
  rw [show (⋂ i, f i) = ⋂ i ∈ (Finset.univ : Finset ι), f i by simp]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using isStarFree_univ
  | insert a s ha ih =>
    rw [Finset.set_biInter_insert]
    exact (h a).inter ih

end Language
