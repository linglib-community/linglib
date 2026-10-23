module

public import Linglib.Semantics.Quantification.Individual
public import Linglib.Semantics.Reference.Iota

/-!
# Partee (1987): Noun Phrase Interpretation and Type-shifting Principles

This file formalizes the type-shifting principles of [partee-1987]. A noun phrase may denote
an entity, a predicate, or a generalized quantifier as its environment demands, and the
mappings between the three types come in inverse pairs, the paper's Figure 1: `lift`, the
substrate's `Quantifier.NP.individual`, and `lower`, the total injection of an entity into
its principal ultrafilter and its partial inverse; `ident` and `iota`, the singleton property
of an entity and the unique member of a property; and `nom` and `pred`, the correlates of
properties and entities after [chierchia-1984] (`lower_lift`, `iota_ident`). The
definite article has a partial entity meaning, `iota`, and a total quantifier meaning, `THE`,
which is the determiner `GQ.the`. Whenever `iota(king')` is defined `THE(king')` is its lift,
and otherwise the empty set of properties, so `lower(THE(king')) = iota(king')` either way. The
predicative reading of *the king* is `BE(THE(king'))`, the singleton of the unique king, which
is `ident(iota(king'))` when the latter is defined and coincides with the common noun when there
is at most one king; this is why the article can be dropped in *John is (the) president*
(`the_eq_individual`, `lower_the`, `BE_the_eq_ident`, `BE_the_eq_self`).

The functor `BE`, Montague's translation of *be* reconceived as a type shifter, is a
homomorphism of the Boolean structures, Fact 1, which the substrate builds into `NP.BE`, and
the unique homomorphism making Figure 3 commute, `BE(lift(j)) = ident(j)`, Fact 2
(`BE_natural`). The indefinite article `A` is `GQ.some`, natural as an inverse of `BE`
(`NP.BE_some`), so *be a man* comes out as *man*, and *be no man* as the complement of *be a
man* (`BE_no`), while *be every man* holds only of the only man (`BE_every_apply`). English
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

open Quantifier Quantifier.GQ Quantifier.NP

variable {E : Type*} (j : E) (P : E → Prop)

/-- `lower Q` is the entity whose Montague lift is `Q`, when `Q` is a principal ultrafilter. -/
noncomputable def lower (Q : NP E) : Option E := iota fun j ↦ Q = individual j

/-! ### Figure 1: three inverse pairs -/

theorem lower_lift : lower (individual j) = some j :=
  (iota_eq_some_iff _).2 ⟨rfl, fun _ h ↦ (individual_injective h).symm⟩

theorem iota_BE_lift : iota (BE (individual j)) = some j := by
  rw [BE_individual]; exact iota_ident j

/-! ### Figure 2: *the king* in three types (§3.2) -/

theorem the_eq_individual (h : iota P = some j) : the P = individual j :=
  funext fun S ↦ propext <| (the_sem_iff_iota P S).trans <| by simp [h, individual]

theorem the_eq_bot (h : iota P = none) : the P = ⊥ :=
  funext fun S ↦ propext <| (the_sem_iff_iota P S).trans <| by simp [h]

theorem lower_the : lower (the P) = iota P := by
  cases h : iota P with
  | some j => rw [the_eq_individual j P h, lower_lift]
  | none =>
    rw [the_eq_bot P h, lower, iota_eq_none_iff]
    exact fun ⟨j, hj, _⟩ ↦ (congrFun hj ⊤).mpr trivial

theorem BE_the_apply (x : E) : BE (the P) x ↔ ∀ y, P y ↔ y = x :=
  ⟨fun ⟨_, hz, hzx⟩ ↦ hzx ▸ hz, fun h ↦ ⟨x, h, rfl⟩⟩

theorem BE_the_eq_ident (h : iota P = some j) : BE (the P) = ident j := by
  rw [the_eq_individual j P h, BE_individual]

/-- With at most one king the predicative *the king* is the common noun *king*, the
equivalence that lets the article drop in *John is (the) president* (12). -/
theorem BE_the_eq_self (hP : {x | P x}.Subsingleton) : BE (the P) = P :=
  funext fun x ↦ propext <| (BE_the_apply P x).trans
    ⟨fun h ↦ (h x).2 rfl, fun hx _ ↦ ⟨fun hy ↦ hP hy hx, fun e ↦ e ▸ hx⟩⟩

/-! ### `A` and `BE` as natural functors (§3.3) -/

/-- Fact 2: `BE` is the unique homomorphism making Figure 3 commute, `BE(lift(j)) = ident(j)`. -/
theorem BE_natural (f : CompleteLatticeHom (NP E) (E → Prop))
    (hcomm : ∀ j : E, f (individual j) = ident j) : f = BE :=
  completeLatticeHom_ext fun j ↦ (hcomm j).trans (BE_individual j).symm

theorem BE_every_apply (x : E) : BE (every P) x ↔ ∀ y, P y → y = x :=
  .rfl

/-- `BE(no man) = not(BE(a man))`, by Fact 1. -/
theorem BE_no : BE (no P) = (BE (GQ.some P))ᶜ :=
  (congrArg BE (congrFun compl_some P)).symm.trans (map_compl' BE _)

end Partee1987
