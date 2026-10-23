module

public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Individuals

This file is about the Montagovian individuals, the type ⟨1⟩ quantifiers `NP.individual a` of
the properties of an entity, and the type shifts they fix. The individuals generate `NP E` under
complete Boolean operations: every quantifier is the join of the quantifiers true of one of its
properties alone, and the quantifier true of `R` alone, *every `R` and no non-`R`*, is a meet of
individuals and their complements. A complete homomorphism out of `NP E` is therefore fixed by
its values on the individuals. The individuals are exactly the quantifiers that commute with
negation and with arbitrary conjunction, Keenan and Faltz's characterization of proper-noun
denotations, and an existential is one exactly when its restrictor is a singleton.

Predicative content `BE` is the complete homomorphism sending each individual to its singleton,
and the existential determiner `GQ.some`, Partee's `A`, is a section of it, so `BE ∘ A` is the
identity. On the monotone quantifiers the two form a Galois coinsertion, and a quantifier
survives the round trip `A ∘ BE` exactly when it is existential, as an individual is.

## Main definitions

* `NP.BE`: predicative content, as a complete lattice homomorphism.
* `NP.gciSomeBE`: the Galois coinsertion of `GQ.some` and `BE` on the monotone quantifiers.

## Main statements

* `NP.BE_some`: `BE ∘ A` is the identity.
* `NP.completeLatticeHom_ext`: complete homomorphisms out of `NP E` agreeing on the individuals
  are equal.
* `NP.exists_eq_individual_iff`: the individuals are the quantifiers commuting with negation and
  arbitrary conjunction.

## References

* [keenan-faltz-1985]
* [partee-1987]
-/

@[expose] public section

namespace Quantifier.NP

open Quantifier.GQ

variable {E : Type*}

/-! ### Individuals -/

theorem sInter_individual (a : E) : ⋂₀ (individual a : Set (Set E)) = {a} :=
  Set.ext fun _ ↦ ⟨fun h ↦ h {a} rfl, fun h _ hs ↦ h ▸ hs⟩

@[simp] theorem individual_compl (a : E) (P : E → Prop) : individual a Pᶜ ↔ ¬ individual a P :=
  .rfl

@[simp] theorem individual_sInf (a : E) (S : Set (E → Prop)) :
    individual a (sInf S) ↔ ∀ P ∈ S, individual a P := by
  simp [individual]

/-! ### Generation by the individuals

*Every*, *some* and *no* at a restrictor are the meet, the join and the meet of the complements
of the individuals of the restrictor, and every quantifier is a join of meets of individuals and
their complements. -/

theorem every_eq_iInf_individual (R : E → Prop) : every R = ⨅ (x) (_ : R x), individual x :=
  funext fun _ ↦ by simp [every, individual]

theorem some_eq_iSup_individual (R : E → Prop) : GQ.some R = ⨆ (x) (_ : R x), individual x :=
  funext fun _ ↦ by simp [GQ.some, individual]

theorem no_eq_iInf_compl_individual (R : E → Prop) :
    no R = ⨅ (x) (_ : R x), (individual x)ᶜ :=
  funext fun _ ↦ by simp [no, individual]

theorem every_inf_no_compl_apply {R S : E → Prop} : (every R ⊓ no Rᶜ) S ↔ S = R :=
  ⟨fun ⟨h₁, h₂⟩ ↦ funext fun x ↦ propext ⟨fun hS ↦ by_contra (h₂ x · hS), h₁ x⟩,
    fun h ↦ h ▸ ⟨fun _ ↦ id, fun _ h h' ↦ h h'⟩⟩

theorem eq_iSup_every_inf_no (Q : NP E) : Q = ⨆ (R) (_ : Q R), every R ⊓ no Rᶜ :=
  funext fun _ ↦ by
    simp only [iSup_apply, iSup_Prop_eq, every_inf_no_compl_apply, exists_prop, exists_eq_right']

theorem completeLatticeHom_ext {β : Type*} [CompleteBooleanAlgebra β]
    {f g : CompleteLatticeHom (NP E) β} (h : ∀ x, f (individual x) = g (individual x)) :
    f = g := by
  ext Q
  rw [eq_iSup_every_inf_no Q]
  simp only [map_iSup, map_inf, every_eq_iInf_individual, no_eq_iInf_compl_individual, map_iInf,
    map_compl', h]

/-! ### Predicative content and existential closure -/

/-- `BE Q` is the predicative content of the quantifier `Q`, `BE(Q) = λx. Q(λy. y = x)`, which
preserves arbitrary meets and joins. -/
def BE : CompleteLatticeHom (NP E) (E → Prop) where
  toFun Q x := Q (ident x)
  map_sInf' _ := funext fun _ ↦ by simp
  map_sSup' _ := funext fun _ ↦ by simp

@[simp] theorem BE_apply (Q : NP E) (x : E) : BE Q x = Q (ident x) := rfl

@[simp] theorem BE_individual (j : E) : BE (individual j) = ident j :=
  funext fun _ ↦ propext eq_comm

@[simp] theorem some_ident (j : E) : GQ.some (ident j) = individual j :=
  funext fun _ ↦ propext ⟨fun ⟨_, h, hP⟩ ↦ h ▸ hP, fun hP ↦ ⟨j, rfl, hP⟩⟩

@[simp] theorem BE_some (P : E → Prop) : BE (GQ.some P) = P :=
  funext fun _ ↦ propext ⟨fun ⟨_, hP, h⟩ ↦ h ▸ hP, fun hP ↦ ⟨_, hP, rfl⟩⟩

theorem some_injective : Function.Injective (GQ.some : GQ E) :=
  Function.LeftInverse.injective BE_some

theorem some_eq_individual_iff {N : E → Prop} {a : E} :
    GQ.some N = individual a ↔ N = ident a := by
  rw [← some_ident, some_injective.eq_iff]

theorem some_BE_eq_self_iff {Q : NP E} : GQ.some (BE Q) = Q ↔ ∃ P, GQ.some P = Q :=
  ⟨fun h ↦ ⟨_, h⟩, fun ⟨P, h⟩ ↦ h ▸ congrArg GQ.some (BE_some P)⟩

/-! ### The Galois coinsertion on monotone quantifiers -/

theorem individual_le_iff {Q : NP E} (hQ : Monotone Q) {x : E} : individual x ≤ Q ↔ BE Q x :=
  ⟨fun h ↦ h _ rfl, fun h _ hR ↦ hQ (fun y (hy : y = x) ↦ hy ▸ hR) h⟩

theorem some_le_iff {Q : NP E} (hQ : Monotone Q) {P : E → Prop} :
    GQ.some P ≤ Q ↔ P ≤ BE Q := by
  simp only [some_eq_iSup_individual, iSup₂_le_iff, individual_le_iff hQ]
  rfl

/-- On the monotone quantifiers `GQ.some` and `BE` form a Galois coinsertion. -/
def gciSomeBE :
    GaloisCoinsertion (fun P ↦ (⟨GQ.some P, monotone_some P⟩ : (E → Prop) →o Prop))
      fun Q ↦ BE Q :=
  GaloisConnection.toGaloisCoinsertion (fun _ Q ↦ some_le_iff Q.monotone) fun P ↦ (BE_some P).le

/-! ### Individuals as complete homomorphisms

Keenan and Faltz define a proper-noun denotation as a set of properties satisfying the Meets,
Joins and Complements Conditions and prove that these are exactly the individuals generated by
atoms; the Joins Condition follows from the other two. Read as scope, the Complements Condition
says that the quantifier commutes with negation and the Meets Condition that it commutes with
universal quantification, so the scopeless quantifiers are the Montagovian individuals. -/

/-- The quantifiers that commute with negation and with arbitrary conjunction are the
Montagovian individuals, [keenan-faltz-1985]'s Theorem 9 for the algebra `E → Prop`. -/
theorem exists_eq_individual_iff {Q : NP E} :
    (∃ a, Q = individual a) ↔
      (∀ P, Q Pᶜ ↔ ¬ Q P) ∧ ∀ S : Set (E → Prop), Q (sInf S) ↔ ∀ P ∈ S, Q P := by
  refine ⟨?_, fun ⟨hc, hs⟩ ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨individual_compl a, individual_sInf a⟩
  have hC : Q (sInf {P | Q P}) := (hs _).2 fun _ h ↦ h
  obtain ⟨a, ha⟩ : ∃ a, sInf {P | Q P} a := by
    by_contra! h
    have hbot : sInf {P | Q P} = (sInf ∅ : E → Prop)ᶜ := by
      funext x; simp [h x]
    rw [hbot, hc, hs ∅] at hC
    exact hC fun _ h ↦ h.elim
  simp only [sInf_apply, iInf_Prop_eq, Subtype.forall, Set.mem_ofPred_eq] at ha
  refine ⟨a, funext fun P ↦ propext ⟨ha P, fun h ↦ ?_⟩⟩
  by_contra hP
  exact ha _ ((hc P).2 hP) h

end Quantifier.NP
