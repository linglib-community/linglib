module

public import Linglib.Semantics.Quantification.Counting
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
one* fails only by monotonicity](##exactly_one_ne_some). The predicative *the
owner of this land* is [a role that no set represents](##Quantifier.BE_the_not_mem_range_const).

## Implementation notes

* The paper systematically represents properties as sets (fn. 5) in an extensional fragment
  (fn. 2); a property here is a set of individuals at each index, `W → Set E`, and a set is the
  rigid property `Function.const W` of it.
* The general results are stated where their objects live: the lift and `lower` in
  `Quantification/Individual.lean`, `BE` and its sections in `Quantification/Predicative.lean`,
  ∩ and ∪ in `Reference/Kind.lean`. This file keeps the paper's comparison of `A` with *exactly
  one*, *most* under `BE`, and Fact 2 on an infinite domain.

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

variable {E : Type*}

/-! ### §3.3: *exactly one* and *most* under `BE`

`BE` undoes *exactly one* as it undoes *some*, and *exactly one* is conservative and symmetric too,
so only monotonicity tells it from *some* among the sections of `BE`. *Be most `A`*, like *be every
`A`*, holds only of the only `A`. -/

theorem BE_exactly_one (A : Set E) : BE (exactly 1 A) = A :=
  Set.ext fun x ↦ (intersective_exactly 1).mem_BE.trans <| by
    by_cases hx : x ∈ A <;> simp [exactly_apply, Set.inter_singleton_of_mem, hx,
      Set.inter_singleton_eq_empty.2]

/-- *Exactly one* is a conservative, symmetric section of `BE` other than *some*, so monotonicity
is what singles out *some* among them ([partee-1987], §3.3). -/
theorem exactly_one_ne_some [Nontrivial E] : (exactly 1 : Det E) ≠ Det.some := fun h ↦ by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have := congrFun₂ h {a, b} {a, b}
  simp [exactly_apply, Set.ncard_pair hab, Det.some] at this

/-- On a finite restrictor, *be most `A`* is *be the `A`*, as *be every `A`* is
([partee-1987], §3.3). -/
theorem BE_most {A : Set E} (hA : A.Finite) : BE (most A) = BE (the A) := by
  ext x
  rw [mem_BE_the, mem_BE, most_apply]
  by_cases hx : x ∈ A
  · rw [Set.inter_singleton_of_mem hx, Set.ncard_singleton, Nat.lt_one_iff,
      Set.ncard_eq_zero hA.sdiff, Set.sdiff_eq_empty]
    exact ⟨fun h ↦ (Set.subset_singleton_iff_eq.1 h).resolve_left
      (Set.nonempty_of_mem hx).ne_empty, fun h ↦ h.le⟩
  · rw [Set.inter_singleton_eq_empty.2 hx, Set.ncard_empty]
    exact ⟨fun h ↦ absurd h (Nat.not_lt_zero _), fun h ↦ absurd (h ▸ rfl : x ∈ A) hx⟩

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
