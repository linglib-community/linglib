/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Inquisitive.Declarative
public import Mathlib.Order.Hom.Lattice

/-!
# Modalities over inquisitive propositions

An agent has, at each world `w`, an information state `M w`, the worlds compatible with what she
knows or believes there, and an inquisitive state `S w`, a proposition whose informative content
is `M w` and whose resolving states settle the issues she entertains. A proposition `P` is
resolved by `M` at the worlds `w` where `M w ∈ P`, and entertained by `S` at the worlds where
`S w ≤ P`.

Both take a statement or a question. On the declarative of `p` the first is the box, the worlds
whose state lies within `p`. On a question it holds where the state settles the question, and
since a state resolves a join exactly when it resolves one of the two, to resolve a question is to
resolve one of its answers.

## Main definitions

* `Inquisitive.Proposition.resolvedBy`: the worlds at which an information state resolves a
  proposition.
* `Inquisitive.Proposition.resolvedByHom`: resolution by a state as a lattice homomorphism.
* `Inquisitive.Proposition.entertainedBy`: the worlds at which an inquisitive state lies below a
  proposition.

## Main results

* `Inquisitive.Proposition.resolvedBy_singleton`: the state that knows the world resolves a
  proposition exactly where the proposition's informative content is true.
* `Inquisitive.Proposition.resolvedBy_subset_info`: a state that contains its world resolves only
  what is true.
* `Inquisitive.Proposition.exists_eq_setOf_mem_iff`: the sets of propositions that a consistent
  state resolves are those closed upward, closed under arbitrary meets, and containing a join
  only with one of the joined propositions.
* `Inquisitive.Proposition.entertainedBy_ofSet`: a declarative is entertained exactly where the
  informative content of the inquisitive state lies within it.

## Implementation notes

A modality here sees a proposition only through the states that resolve it. An operator sensitive
to how a question's alternatives are presented, and not only to their downward closure, is not of
this form.

## References

* [ciardelli-roelofsen-2015]
* [theiler-etal-2019]
-/

@[expose] public section

namespace Inquisitive.Proposition

variable {W : Type*} {M : W → Set W} {S : W → Proposition (Set W)} {P Q : Proposition (Set W)}
  {p : Set W} {w : W}

/-! ### Resolution by an information state -/

/-- The worlds at which the information state `M` resolves `P`. -/
def resolvedBy (P : Proposition (Set W)) (M : W → Set W) : Set W := {w | M w ∈ P}

@[simp] theorem mem_resolvedBy : w ∈ P.resolvedBy M ↔ M w ∈ P := Iff.rfl

/-- A declarative is resolved where the state lies within it. -/
@[simp] theorem resolvedBy_ofSet (p : Set W) (M : W → Set W) :
    (ofSet p).resolvedBy M = {w | M w ⊆ p} := rfl

@[simp] theorem resolvedBy_inf (P Q : Proposition (Set W)) (M : W → Set W) :
    (P ⊓ Q).resolvedBy M = P.resolvedBy M ∩ Q.resolvedBy M := rfl

/-- A state resolves a join exactly where it resolves one of the two. -/
@[simp] theorem resolvedBy_sup (P Q : Proposition (Set W)) (M : W → Set W) :
    (P ⊔ Q).resolvedBy M = P.resolvedBy M ∪ Q.resolvedBy M := rfl

@[simp] theorem resolvedBy_top (M : W → Set W) :
    (⊤ : Proposition (Set W)).resolvedBy M = Set.univ := rfl

theorem resolvedBy_sInf (s : Set (Proposition (Set W))) (M : W → Set W) :
    (sInf s).resolvedBy M = ⋂ P ∈ s, P.resolvedBy M := by
  ext w
  simp

/-- Resolution by an information state, as a lattice homomorphism to sets of worlds. -/
def resolvedByHom (M : W → Set W) : LatticeHom (Proposition (Set W)) (Set W) where
  toFun P := P.resolvedBy M
  map_sup' P Q := resolvedBy_sup P Q M
  map_inf' P Q := resolvedBy_inf P Q M

@[simp] theorem resolvedByHom_apply (M : W → Set W) (P : Proposition (Set W)) :
    resolvedByHom M P = P.resolvedBy M := rfl

theorem resolvedBy_mono (M : W → Set W) (h : P ≤ Q) : P.resolvedBy M ⊆ Q.resolvedBy M :=
  OrderHomClass.mono (resolvedByHom M) h

/-- The state that knows which world is actual resolves a proposition exactly where the
proposition's informative content is true. -/
@[simp] theorem resolvedBy_singleton (P : Proposition (Set W)) :
    P.resolvedBy (fun w ↦ {w}) = P.info :=
  Set.ext fun w ↦ (mem_info_iff_singleton_mem P w).symm

/-- A state that contains its world resolves only what is true. -/
theorem resolvedBy_subset_info (hM : ∀ w, w ∈ M w) (P : Proposition (Set W)) :
    P.resolvedBy M ⊆ P.info := fun w hw ↦ ⟨M w, hw, hM w⟩

/-- The polar question of a proposition is resolved where the proposition or its negation is. -/
theorem resolvedBy_query (P : Proposition (Set W)) (M : W → Set W) :
    P.query.resolvedBy M = P.resolvedBy M ∪ Pᶜ.resolvedBy M := by
  rw [query_eq_sup_compl, resolvedBy_sup]

/-- The negation of a proposition with no informative content is resolved only by the
inconsistent state. -/
theorem resolvedBy_compl_of_info_eq_univ (h : P.info = Set.univ) (M : W → Set W) :
    Pᶜ.resolvedBy M = {w | M w = ∅} := by
  ext w
  rw [mem_resolvedBy, compl_eq, h, Set.compl_univ, mem_ofSet, Set.subset_empty_iff]
  rfl

/-- A proposition with no informative content is resolved wherever its polar question is. -/
theorem resolvedBy_query_of_info_eq_univ (h : P.info = Set.univ) (M : W → Set W) :
    P.query.resolvedBy M = P.resolvedBy M := by
  rw [query_eq_self_of_info_eq_univ h]

/-- A set of propositions is the set that some consistent state resolves exactly when it is closed
upward, closed under arbitrary meets, and contains an arbitrary join only with one of the joined
propositions. -/
theorem exists_eq_setOf_mem_iff {F : Set (Proposition (Set W))} :
    (∃ s : Set W, s.Nonempty ∧ F = {P | s ∈ P}) ↔
      IsUpperSet F ∧ (∀ S ⊆ F, sInf S ∈ F) ∧ ∀ S, sSup S ∈ F → ∃ P ∈ S, P ∈ F := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨fun P Q h hP ↦ h hP, fun S hS ↦ mem_sInf.2 fun P hP ↦ hS hP, fun S hS ↦ ?_⟩
    exact (mem_sSup.1 hS).resolve_left hs.ne_empty
  · rintro ⟨hup, hinf, hsup⟩
    have h₀ : sInf F ∈ F := hinf F subset_rfl
    have hgen : sSup (ofSet '' ((sInf F : Proposition (Set W)) : Set (Set W))) = sInf F := by
      rw [sSup_image, ← generate_eq_biSup, generate_coe]
    obtain ⟨_, ⟨q, hq, rfl⟩, hqF⟩ := hsup _ (hgen.symm ▸ h₀)
    have heq : sInf F = ofSet q := le_antisymm (sInf_le hqF) (mem_iff_ofSet_le.1 hq)
    refine ⟨q, Set.nonempty_iff_ne_empty.2 ?_, Set.ext fun P ↦
      ⟨fun hP ↦ mem_iff_ofSet_le.2 (heq ▸ sInf_le hP), fun hP ↦ hup (mem_iff_ofSet_le.1 hP) hqF⟩⟩
    rintro rfl
    obtain ⟨P, hP, -⟩ := hsup ∅ (by rwa [sSup_empty, ← ofSet_empty])
    exact hP

/-! ### Entertaining by an inquisitive state -/

/-- The worlds at which the inquisitive state `S` lies below `P`: every state that settles the
agent's issues resolves `P`. -/
def entertainedBy (P : Proposition (Set W)) (S : W → Proposition (Set W)) : Set W :=
  {w | S w ≤ P}

@[simp] theorem mem_entertainedBy : w ∈ P.entertainedBy S ↔ S w ≤ P := Iff.rfl

theorem entertainedBy_mono (S : W → Proposition (Set W)) (h : P ≤ Q) :
    P.entertainedBy S ⊆ Q.entertainedBy S := fun _ hw ↦ le_trans hw h

/-- A declarative is entertained exactly where the informative content of the inquisitive state
lies within it. -/
theorem entertainedBy_ofSet (p : Set W) (S : W → Proposition (Set W)) :
    (ofSet p).entertainedBy S = {w | (S w).info ⊆ p} :=
  Set.ext fun w ↦ (gc_info_ofSet (S w) p).symm

end Inquisitive.Proposition
