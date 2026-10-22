/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Factors
public import Linglib.Phonology.Autosegmental.Realization
public import Linglib.Phonology.Subregular.StrictlyLocal

/-!
# Autosegmental strictly local languages

A realization `r` maps strings to autosegmental representations, and a banned-subgraph grammar
`B` describes the strings whose realization contains no factor of `B`, Jardine's `L(B^g)`;
the languages so described are the autosegmental strictly local class `ASL^g`. Such a language
is downward closed under containment of realizations, which is how Jardine separates `ASL`
from other classes. Strings themselves are one-tier representations, and at the string
realization the class contains every strictly local language with finitely many forbidden
factors, the parallel Jardine draws between banned subgraphs and banned substrings. For grammars
without association lines the class is a Boolean combination of tier-projected factor
constraints, hence star-free.

## Main definitions

* `Language.bannedSubgraph r B`: the strings whose realization avoids the grammar `B`.
* `Language.IsAutosegmentalStrictlyLocal r L`: some banned-subgraph grammar describes `L`.

## Main results

* `Language.IsAutosegmentalStrictlyLocal.mem_of_factorEmbeds`: an autosegmental strictly local
  language is downward closed under containment of realizations.
* `Language.bannedSubgraph_ofList_boundary`: a forbidden-factor `SL_k` language is the
  banned-subgraph language of its factors over boundary-padded strings.
* `Language.bannedSubgraph_prod_map_eq_of_link_free`, `Language.isStarFree_bannedSubgraph_prod_map`:
  without lines, a banned-subgraph language is an intersection of unions of tier-avoidance
  preimages, and so star-free.

## Implementation notes

The class is parametrized by the realization itself rather than by a primitive map: Jardine's
`ASL^g` is the class at the merging realization of `g` with border primitives, and the unmerged
realization `fun w ↦ (w.map g).prod` and the string realization are other instances. Jardine bans
only connected factors (`Autosegmental/Factors.lean`), so
the class here contains his and its separation results are the stronger statements.

## References

* [jardine-2016b]
* [jardine-2019]
-/

@[expose] public section

namespace Language

open Autosegmental

variable {S ι : Type*} {τ : ι → Type*} (r : List S → AR τ)

/-- The strings whose realization under `r` avoids every factor of the grammar `B`. -/
def bannedSubgraph (B : List (AR τ)) : Language S := {w | (r w).Free B}

/-- A language is **autosegmental strictly local** over `r` when a banned-subgraph grammar
describes it. -/
def IsAutosegmentalStrictlyLocal (L : Language S) : Prop :=
  ∃ B : List (AR τ), bannedSubgraph r B = L

variable {r} {B : List (AR τ)} {L : Language S} {u v w : List S}

@[simp] theorem mem_bannedSubgraph : w ∈ bannedSubgraph r B ↔ (r w).Free B := Iff.rfl

theorem isAutosegmentalStrictlyLocal_bannedSubgraph :
    IsAutosegmentalStrictlyLocal r (bannedSubgraph r B) :=
  ⟨B, rfl⟩

@[simp] theorem bannedSubgraph_nil : bannedSubgraph r [] = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ AR.free_nil

/-- A grammar's language is the intersection of its factors' avoidance languages. -/
theorem bannedSubgraph_cons (F : AR τ) :
    bannedSubgraph r (F :: B) = {w | F.FactorEmbeds (r w)}ᶜ ⊓ bannedSubgraph r B :=
  Set.ext fun _ ↦ AR.free_cons

/-! ### Downward closure -/

/-- A banned-subgraph language is downward closed under containment of realizations. -/
theorem mem_bannedSubgraph_of_factorEmbeds (h : (r u).FactorEmbeds (r v))
    (hv : v ∈ bannedSubgraph r B) : u ∈ bannedSubgraph r B :=
  fun F hF hFu ↦ hv F hF (hFu.trans h)

theorem IsAutosegmentalStrictlyLocal.mem_of_factorEmbeds
    (hL : IsAutosegmentalStrictlyLocal r L) (h : (r u).FactorEmbeds (r v)) (hv : v ∈ L) :
    u ∈ L := by
  obtain ⟨B, rfl⟩ := hL
  exact mem_bannedSubgraph_of_factorEmbeds h hv

/-- A language that separates two strings whose realizations are contained one in the other
is not autosegmental strictly local. -/
theorem not_isAutosegmentalStrictlyLocal_of_factorEmbeds (h : (r u).FactorEmbeds (r v))
    (hu : u ∉ L) (hv : v ∈ L) : ¬ IsAutosegmentalStrictlyLocal r L :=
  fun hL ↦ hu (hL.mem_of_factorEmbeds h hv)

end Language

/-! ### Strings as one-tier representations -/

namespace Language

open Autosegmental

variable {α : Type*}

/-- A forbidden-factor `SL_k` language is the banned-subgraph language of its forbidden factors
over boundary-padded strings. -/
theorem bannedSubgraph_ofList_boundary {Fs : List (Augmented α)} {k : ℕ}
    (hk : ∀ f ∈ Fs, f.length = k) :
    bannedSubgraph (fun w ↦ AR.ofList (boundary k w)) (Fs.map AR.ofList) =
      (StrictlyLocalGrammar.ofForbidden {f | f ∈ Fs}).language k :=
  Set.ext fun w ↦ by
    rw [mem_bannedSubgraph, StrictlyLocalGrammar.mem_ofForbidden_language]
    simp only [AR.Free, List.forall_mem_map, AR.factorEmbeds_ofList_iff, Set.mem_ofPred_eq,
      List.mem_kFactors]
    grind

/-- At the boundary-padded string realization, every finite forbidden-factor `SL_k` language is
autosegmental strictly local. -/
theorem isAutosegmentalStrictlyLocal_ofForbidden {Fs : List (Augmented α)} {k : ℕ}
    (hk : ∀ f ∈ Fs, f.length = k) :
    IsAutosegmentalStrictlyLocal (fun w ↦ AR.ofList (boundary k w))
      ((StrictlyLocalGrammar.ofForbidden {f | f ∈ Fs}).language k) :=
  ⟨_, bannedSubgraph_ofList_boundary hk⟩

end Language

/-! ### Grammars without association lines -/

namespace Language

open Autosegmental

variable {S ι : Type*} {τ : ι → Type*} (g : S → AR τ)

/-- The strings whose realization contains a link-free factor are those whose tier projections
contain its words. -/
theorem setOf_factorEmbeds_prod_map_eq_of_link_free (F : AR τ) (hF : ∀ i j p q, ¬ F.Link i j p q) :
    {w : List S | F.FactorEmbeds (w.map g).prod} =
      ⋂ i, {w : List S | F.word i <:+: (AR.wordHom i).comp (FreeMonoid.lift g) (.ofList w)} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, AR.factorEmbeds_iff_infix_of_link_free hF,
    MonoidHom.comp_apply, FreeMonoid.lift_ofList, AR.wordHom_apply]
  exact Iff.rfl

/-- Without lines, a banned-subgraph language is an intersection over the factors of unions
over the tiers of tier-avoidance preimages. -/
theorem bannedSubgraph_prod_map_eq_of_link_free (B : List (AR τ))
    (hB : ∀ F ∈ B, ∀ i j p q, ¬ F.Link i j p q) :
    bannedSubgraph (fun w ↦ (w.map g).prod) B =
      ⋂ F ∈ B, ⋃ i, {w : List S | ¬ F.word i <:+:
        (AR.wordHom i).comp (FreeMonoid.lift g) (.ofList w)} :=
  Set.ext fun w ↦ by
    refine Iff.trans (show _ ↔ ∀ F ∈ B, ¬ F.FactorEmbeds (w.map g).prod from Iff.rfl) ?_
    refine Iff.trans ?_ Set.mem_iInter₂.symm
    refine forall₂_congr fun F hF ↦ Iff.trans ?_ Set.mem_iUnion.symm
    rw [AR.factorEmbeds_iff_infix_of_link_free (hB F hF)]
    simp only [not_forall, Set.mem_ofPred_eq, MonoidHom.comp_apply, FreeMonoid.lift_ofList,
      AR.wordHom_apply]
    exact Iff.rfl

variable [Finite ι]

/-- Without lines, a banned-subgraph language over a realization is star-free. -/
theorem isStarFree_bannedSubgraph_prod_map (B : List (AR τ))
    (hB : ∀ F ∈ B, ∀ i j p q, ¬ F.Link i j p q) :
    IsStarFree (bannedSubgraph (fun w ↦ (w.map g).prod) B) := by
  induction B with
  | nil => simpa using isStarFree_univ (α := S)
  | cons F B ih =>
    rw [bannedSubgraph_cons, setOf_factorEmbeds_prod_map_eq_of_link_free g F
      (hB F (List.mem_cons_self ..))]
    exact (IsStarFree.iInter fun i ↦ (isStarFree_setOf_infix (F.word i)).comap
      ((AR.wordHom i).comp (FreeMonoid.lift g))).compl.inter
        (ih fun F' hF' ↦ hB F' (List.mem_cons_of_mem _ hF'))

end Language
