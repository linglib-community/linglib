module

public import Linglib.Semantics.Quantification.Predicative
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Partee (1987): Noun phrase interpretation and type-shifting principles

A noun phrase may denote an entity, a predicate or a generalized quantifier, and the shifts among
the three types pair a total injection with its partial inverse: the lift `Quantifier.individual`
with `Quantifier.lower`, the singleton with `iota`, and Chierchia's ∩ with ∪, which [cannot be
total](##Kind.apply_russell_eq_none) and is [no function of
extensions](##Kind.not_exists_apply_eq_comp). `BE` is [the only complete
homomorphism](##Quantifier.BE_unique) taking each lift to its singleton, `A` is [its only
conservative, symmetric, monotone section](##Quantifier.eq_some_of_leftInverse), and [*exactly
one* fails only by monotonicity](##Quantifier.Det.exactly_one_ne_some). The predicative *the
owner of this land* is [a role that no set represents](##Quantifier.BE_the_not_mem_range_const).

## Implementation notes

* The paper systematically represents properties as sets (fn. 5) in an extensional fragment
  (fn. 2); a property here is a set of individuals at each index, `W → Set E`, and a set is the
  rigid property `Function.const W` of it.
* The general results are stated where their objects live: the lift and `lower` in
  `Quantification/Individual.lean`, `BE` and its sections in `Quantification/Predicative.lean`,
  the counting determiners under `BE` in `Quantification/Counting.lean`, ∩ and ∪ in
  `Reference/Kind.lean`. This file keeps the paper's errata.

## Errata

* Fact 2 is stated for homomorphisms of the Boolean structures. On an infinite domain a Boolean
  homomorphism can [agree with `BE` on the lifts and differ
  elsewhere](##exists_boundedLatticeHom_ne_BE); the argument from Keenan and Faltz's generation
  result needs complete homomorphisms.
* *Most men* is said never to contain a singleton, so that *be most men* is always empty; with
  exactly one man [it is the singleton of that man](##Quantifier.Det.BE_most), the degenerate
  case the paper grants for *every man*.
* *Exactly one* is said to be neither symmetric nor monotone; it is symmetric
  (`Quantifier.Det.symm_exactly`), as every intersective determiner is.

## TODO

* Link's pair of §3.4.2, the sum of a set of atoms and `Mereology.atomsBelow` back, and the
  analysis of the Williams puzzle in §4.
* The *consider* judgments of (10) as `Data/Examples` rows, *every island* and *most islands*
  paired with their degenerate predicative readings once a degenerate predicate is defined.

## References

* [partee-1987]
* [chierchia-1984]
* [keenan-faltz-1985]
-/

@[expose] public section

namespace Partee1987

open Quantifier Quantifier.Det Filter

/-! ### Fact 2 on an infinite domain -/

/-- `x` is in `boolBE Q` when `Q` holds of `{x} ∪ [n, ∞)` for ultrafilter-many `n`. -/
private noncomputable def boolBE : BoundedLatticeHom (Quantifier ℕ) (Set ℕ) where
  toFun Q := {x | ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Q (insert x (Set.Ici n))}
  map_sup' _ _ := Set.ext fun _ ↦ Ultrafilter.eventually_or
  map_inf' _ _ := Set.ext fun _ ↦ eventually_and
  map_top' := Set.ext fun _ ↦ by simp
  map_bot' := Set.ext fun _ ↦ by simpa using (hyperfilter ℕ).neBot.ne

private theorem boolBE_individual (j : ℕ) : boolBE (individual j) = {j} := by
  ext x
  simp only [boolBE, BoundedLatticeHom.coe_mk, LatticeHom.coe_mk, SupHom.coe_mk,
    Set.mem_ofPred_eq, individual, Set.mem_insert_iff, Set.mem_Ici, Set.mem_singleton_iff]
  refine ⟨fun h ↦ by_contra fun hne ↦ ?_, fun h ↦ .of_forall fun _ ↦ .inl h.symm⟩
  have hgt : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), j < n :=
    hyperfilter_le_cofinite (Nat.cofinite_eq_atTop ▸ eventually_gt_atTop j)
  obtain ⟨n, h1, h2⟩ := (h.and hgt).exists
  exact h1.elim (fun e ↦ hne e.symm) fun h ↦ absurd h2 (not_lt.2 h)

/-- Read with Boolean homomorphisms, Fact 2 (§3.3) fails on an infinite domain: a homomorphism can
take each lift to its singleton and still differ from `BE`. -/
theorem exists_boundedLatticeHom_ne_BE :
    ∃ f : BoundedLatticeHom (Quantifier ℕ) (Set ℕ), (∀ j, f (individual j) = {j}) ∧
      f ≠ (BE : CompleteLatticeHom (Quantifier ℕ) (Set ℕ)).toBoundedLatticeHom := by
  refine ⟨boolBE, boolBE_individual, fun h ↦ ?_⟩
  have h0 : (0 : ℕ) ∈ boolBE (fun B ↦ B.Infinite) :=
    .of_forall fun n ↦ (Set.Ici_infinite n).mono (Set.subset_insert _ _)
  rw [h] at h0
  exact (Set.finite_singleton 0).not_infinite h0

end Partee1987
