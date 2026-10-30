module

public import Linglib.Semantics.Quantification.Individual
public import Linglib.Semantics.Reference.Iota

/-!
# Partee (1987): Noun Phrase Interpretation and Type-shifting Principles

This file formalizes the type-shifting principles of [partee-1987]. A noun phrase may denote
an entity, a predicate, or a generalized quantifier as its environment demands, and the
mappings between the three types come in inverse pairs, the paper's Figure 1: `lift`, the
substrate's `Quantifier.individual`, and `lower`, the total injection of an entity into
its principal ultrafilter and its partial inverse; `ident` and `iota`, the singleton property
of an entity and the unique member of a property; and `nom` and `pred`, the correlates of
properties and entities after Chierchia. The first two pairs are an injection and its
`Function.partialInv` (`lower_isPartialInv`, `iota_isPartialInv`). The
definite article has a partial entity meaning, `iota`, and a total quantifier meaning, `THE`,
which is the determiner `Det.the`. Whenever `iota(king')` is defined `THE(king')` is its lift,
and otherwise the empty set of properties, so `lower(THE(king')) = iota(king')` either way. The
predicative reading of *the king* is `BE(THE(king'))`, the singleton of the unique king, which
is `ident(iota(king'))` when the latter is defined and coincides with the common noun when there
is at most one king; this is why the article can be dropped in *John is (the) president*
(`the_eq_individual`, `lower_the`, `BE_the_eq_ident`, `BE_the_eq_self`).

The functor `BE`, Montague's translation of *be* reconceived as a type shifter, is a
homomorphism of the Boolean structures, Fact 1, which the substrate builds into `Quantifier.BE`, and
the unique homomorphism making Figure 3 commute, `BE(lift(j)) = ident(j)`, Fact 2
(`BE_natural`). The indefinite article `A` is `Det.some`, natural as an inverse of `BE`
(`Quantifier.BE_some`), so *be a man* comes out as *man*, and *be no man* as the complement of *be a
man* (`BE_no`), while *be every man* holds only of the only man (`mem_BE_every`). English
*be* itself is then predicate application, the predicative reading having moved into the noun
phrase.

## Implementation notes

* The setting is extensional, so `pred` is `ident` and `nom` and `iota` are both the Russellian
  `iota`.
* Fact 2 is read with complete homomorphisms, the homomorphisms of [keenan-faltz-1985]'s result
  that the individuals generate the quantifiers, which the paper invokes for it; on an infinite
  domain a merely Boolean homomorphism need not preserve the infinite meets the argument uses.
* The mappings to and from kinds of §3.4 onward and the analysis of the Williams counterexample
  are not formalized.

## References

* [partee-1987]
* [chierchia-1984]
* [keenan-faltz-1985]
-/

@[expose] public section

namespace Partee1987

open Quantifier Quantifier.Det

variable {E : Type*} (j : E) (P : Set E)

/-- `lower Q` is the entity whose Montague lift is `Q`, when `Q` is a principal ultrafilter. -/
noncomputable def lower : Quantifier E → Option E := Function.partialInv individual

/-! ### Figure 1: three inverse pairs -/

theorem lower_isPartialInv : Function.IsPartialInv individual (lower (E := E)) :=
  individual_injective.isPartialInv

theorem lower_lift : lower (individual j) = some j :=
  Function.partialInv_left individual_injective j

theorem iota_BE_lift : iota (BE (individual j)) = some j := by
  rw [BE_individual]; exact iota_ident j

/-! ### Figure 2: *the king* in three types (§3.2) -/

theorem the_eq_individual (h : iota (· ∈ P) = some j) : the P = individual j :=
  funext fun _ ↦ propext <| the_iff_exists_mem_iota.trans <| by simp [h, individual]

theorem the_eq_bot (h : iota (· ∈ P) = none) : the P = ⊥ :=
  funext fun _ ↦ propext <| the_iff_exists_mem_iota.trans <| by simp [h]

theorem lower_the : lower (the P) = iota (· ∈ P) := by
  cases h : iota (· ∈ P) with
  | some j => rw [the_eq_individual j P h, lower_lift]
  | none =>
    rw [the_eq_bot P h]
    exact Option.eq_none_iff_forall_ne_some.2 fun j hj ↦
      (congrFun ((lower_isPartialInv j ⊥).1 hj) ⊤).mp trivial

theorem mem_BE_the (x : E) : x ∈ BE (the P) ↔ ∀ y, y ∈ P ↔ y = x :=
  ⟨fun ⟨_, hz, hzx⟩ ↦ hzx ▸ hz, fun h ↦ ⟨x, h, rfl⟩⟩

theorem BE_the_eq_ident (h : iota (· ∈ P) = some j) : BE (the P) = ident j := by
  rw [the_eq_individual j P h, BE_individual]; rfl

/-- With at most one king, the predicative *the king* is the common noun *king*, as in *John is
(the) president* (12). -/
theorem BE_the_eq_self (hP : P.Subsingleton) : BE (the P) = P :=
  Set.ext fun x ↦ (mem_BE_the P x).trans
    ⟨fun h ↦ (h x).2 rfl, fun hx _ ↦ ⟨fun hy ↦ hP hy hx, fun e ↦ e ▸ hx⟩⟩

/-! ### `A` and `BE` as natural functors (§3.3) -/

/-- Fact 2: `BE` is the unique homomorphism making Figure 3 commute, `BE(lift(j)) = ident(j)`. -/
theorem BE_natural (f : CompleteLatticeHom (Quantifier E) (Set E))
    (hcomm : ∀ j : E, f (individual j) = ident j) : f = BE :=
  completeLatticeHom_ext fun j ↦ (hcomm j).trans (BE_individual j).symm

theorem mem_BE_every (x : E) : x ∈ BE (every P) ↔ ∀ y ∈ P, y = x :=
  .rfl

/-- `BE(no man) = not(BE(a man))`, by Fact 1. -/
theorem BE_no : BE (no P) = (BE (Det.some P))ᶜ :=
  (congrArg BE (congrFun compl_some P)).symm.trans (map_compl' BE _)

end Partee1987
