module

public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.Intensional
public import Mathlib.Basic.PEquiv
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Partee (1987): Noun phrase interpretation and type-shifting principles

A noun phrase may denote an entity, a predicate or a generalized quantifier, and the shifts among
the three types pair a total injection with its partial inverse: the lift of an entity with
`Quantifier.lower`, the singleton property with `iota`, and nominalization, which [cannot be
total](##nom_russell), with predication. The paper works in the extension at an index of
Montague's intensional types; `BE`, the lift, `A` and *the* are projections of his shifts, while
nominalization [does not factor through the extension](##not_exists_nom_eq_comp) and the
predicative *the owner* is [a role that no set represents](##role_not_rigid). `BE` is [the only
complete homomorphism](##Quantifier.BE_unique) taking each lift to its singleton, and `A` is [its
only conservative, symmetric, monotone section](##Quantifier.eq_some_of_leftInverse), which
*exactly one* [fails only by monotonicity](##exactly_one_ne_some).

## Implementation notes

* The paper systematically represents properties as sets (fn. 5) in an extensional fragment
  (fn. 2); here a property is a set of individuals at each index, and the fragment is
  `Quantifier.Intensional` read at an index.
* Nominalization and predication are a partial equivalence between properties and entities, a
  parameter as Chierchia's property correlates are primitive. His later kind operators, defined
  at each situation from the largest member, are `Kind.down` and `Kind.up`.
* Fact 2, that `BE` is the unique homomorphism making Figure 3 commute, is
  `Quantifier.BE_unique`, for complete homomorphisms; the predictions of §3.3 and §3.4.1 for
  particular noun phrases are the lemmas on `BE` and `Quantifier.lower` beside it.

## Errata

* Fact 2 is stated for homomorphisms of the Boolean structures. On an infinite domain a Boolean
  homomorphism can [agree with `BE` on the lifts and differ
  elsewhere](##exists_boundedLatticeHom_ne_BE); the argument from Keenan and Faltz's generation
  result needs complete homomorphisms.
* *Most men* is said never to contain a singleton, so that *be most men* is always empty; with
  exactly one man [it is the singleton of that man](##BE_most), the degenerate case the paper
  grants for *every man*.
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

variable {W E : Type*}

/-! ### Figure 1: nominalization and predication -/

/-- The Russell property of a nominalization: at each index, being the correlate of a property one
lacks there. -/
def russell (c : (W → Set E) ≃. E) : W → Set E := fun w ↦ {x | ∃ P ∈ c.symm x, x ∉ P w}

/-- Nominalization is only almost total: the Russell property has no entity correlate (§3.1). -/
theorem nom_russell [Nonempty W] (c : (W → Set E) ≃. E) : c (russell c) = none := by
  refine Option.eq_none_iff_forall_ne_some.2 fun r h ↦ ?_
  have hr : c.symm r = some (russell c) := c.eq_some_iff.2 h
  obtain ⟨w⟩ := ‹Nonempty W›
  exact iff_not_self (a := r ∈ russell c w)
    ⟨fun ⟨_, hP, hrP⟩ ↦ (Option.some_injective _ (hr.symm.trans hP)) ▸ hrP, fun h ↦ ⟨_, hr, h⟩⟩

/-- Nominalization is not a function of extensions, the sense in which the paper's `nom` is an
extensional misrepresentation (§3.1): where it is defined on a property, a different property with
the same extension at `w` defeats any factoring through the extension at `w`. -/
theorem not_exists_nom_eq_comp (c : (W → Set E) ≃. E) {w : W} {P P' : W → Set E}
    (hw : P w = P' w) (hne : P ≠ P') {x : E} (hx : c P = some x) :
    ¬ ∃ f : Set E → Option E, ∀ Q, c Q = f (Q w) := fun ⟨f, hf⟩ ↦
  hne <| c.inj hx <| by rw [hf P', ← hw, ← hf P]; exact hx

/-! ### fn. 16: the predicative definite as a property -/

/-- The predicative *the owner of this land* is the role of being the only owner at each index,
which presupposes no owner and is no set once the owner changes from one index to another
(fn. 16). -/
theorem role_not_rigid {P : W → Set E} {w₀ w₁ : W} {a b : E} (h₀ : P w₀ = {a})
    (h₁ : P w₁ = {b}) (hab : a ≠ b) : (fun w ↦ BE (the (P w))) ∉ Set.range (Function.const W) := by
  rintro ⟨B, hB⟩
  have h₀' := congrFun hB w₀
  have h₁' := congrFun hB w₁
  simp only [Function.const_apply, h₀, h₁,
    BE_the_of_subsingleton Set.subsingleton_singleton] at h₀' h₁'
  exact hab (Set.singleton_injective (h₀'.symm.trans h₁'))

/-! ### §3.3: `A`, *exactly one* and *most* under `BE` -/

-- §3.3
theorem BE_exactly_one (A : Set E) : BE (exactly 1 A) = A :=
  Set.ext fun x ↦ (intersective_exactly 1).mem_BE.trans <| by
    by_cases hx : x ∈ A <;> simp [exactly_apply, Set.inter_singleton_of_mem, hx,
      Set.inter_singleton_eq_empty.2]

/-- *Exactly one* is conservative, symmetric and undone by `BE`, yet it is not `A`: monotonicity
is what singles `A` out (§3.3). -/
theorem exactly_one_ne_some [Nontrivial E] : (exactly 1 : Det E) ≠ Det.some := fun h ↦ by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  have := congrFun₂ h {a, b} {a, b}
  simp [exactly_apply, Set.ncard_pair hab, Det.some] at this

-- §3.3
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
noncomputable def boolBE : BoundedLatticeHom (Quantifier ℕ) (Set ℕ) where
  toFun Q := {x | ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), Q (insert x (Set.Ici n))}
  map_sup' _ _ := Set.ext fun _ ↦ Ultrafilter.eventually_or
  map_inf' _ _ := Set.ext fun _ ↦ eventually_and
  map_top' := Set.ext fun _ ↦ by simp
  map_bot' := Set.ext fun _ ↦ by simpa using (hyperfilter ℕ).neBot.ne

theorem boolBE_individual (j : ℕ) : boolBE (individual j) = {j} := by
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
