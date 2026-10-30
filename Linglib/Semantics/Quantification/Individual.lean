module

public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.Hom.CompleteLattice

/-!
# Individuals

This file is about the Montagovian individuals, the quantifiers `Quantifier.individual a` of the
sets an entity belongs to, and the type shifts they fix. The individuals generate `Quantifier E`
under complete Boolean operations: every quantifier is the join of the quantifiers true of one of
its sets alone, and the quantifier true of `A` alone, *every `A` and no non-`A`*, is a meet of
individuals and their complements. A complete homomorphism out of `Quantifier E` is therefore
fixed by its values on the individuals. The individuals are exactly the quantifiers that commute
with negation and with arbitrary conjunction, Keenan and Faltz's characterization of proper-noun
denotations, and an existential is one exactly when its restrictor is a singleton.

Predicative content `BE` is the complete homomorphism sending each individual to its singleton,
and the existential determiner `Det.some`, Partee's `A`, is a section of it, so `BE ∘ A` is the
identity. On the monotone quantifiers the two form a Galois coinsertion, and a quantifier
survives the round trip `A ∘ BE` exactly when it is existential, as an individual is.

## Main definitions

* `Quantifier.BE`: predicative content, as a complete lattice homomorphism.
* `Quantifier.gciSomeBE`: the Galois coinsertion of `Det.some` and `BE` on the monotone quantifiers.

## Main statements

* `Quantifier.BE_some`: `BE ∘ A` is the identity.
* `Quantifier.completeLatticeHom_ext`: complete homomorphisms out of `Quantifier E` agreeing on the
  individuals are equal.
* `Quantifier.exists_eq_individual_iff`: the individuals are the quantifiers commuting with
  negation and arbitrary conjunction.

## References

* [keenan-faltz-1985]
* [partee-1987]
-/

@[expose] public section

namespace Quantifier

open Quantifier.Det

variable {E : Type*}

/-! ### Individuals -/

theorem sInter_individual (a : E) : ⋂₀ {B | individual a B} = {a} :=
  Set.ext fun _ ↦ ⟨fun h ↦ h {a} rfl, fun h _ hs ↦ h ▸ hs⟩

@[simp] theorem individual_compl (a : E) (B : Set E) : individual a Bᶜ ↔ ¬ individual a B :=
  .rfl

@[simp] theorem individual_sInter (a : E) (S : Set (Set E)) :
    individual a (⋂₀ S) ↔ ∀ B ∈ S, individual a B :=
  .rfl

/-! ### Generation by the individuals

*Every*, *some* and *no* at a restrictor are the meet, the join and the meet of the complements
of the individuals of the restrictor, and every quantifier is a join of meets of individuals and
their complements. -/

theorem every_eq_iInf_individual (A : Set E) : every A = ⨅ x ∈ A, individual x :=
  funext fun _ ↦ by simp [every, individual, Set.subset_def]

theorem some_eq_iSup_individual (A : Set E) : Det.some A = ⨆ x ∈ A, individual x :=
  funext fun _ ↦ by simp [Det.some, individual, Set.Nonempty]

theorem no_eq_iInf_compl_individual (A : Set E) : no A = ⨅ x ∈ A, (individual x)ᶜ :=
  funext fun _ ↦ by simp [no, individual, Set.subset_def]

theorem every_inf_no_compl_apply {A B : Set E} : (every A ⊓ no Aᶜ) B ↔ B = A :=
  ⟨fun ⟨h₁, h₂⟩ ↦ Set.Subset.antisymm (Set.compl_subset_compl.1 h₂) h₁,
    fun h ↦ h ▸ ⟨subset_rfl, subset_rfl⟩⟩

theorem eq_iSup_every_inf_no (Q : Quantifier E) : Q = ⨆ (A) (_ : Q A), every A ⊓ no Aᶜ :=
  funext fun _ ↦ by
    simp only [iSup_apply, iSup_Prop_eq, every_inf_no_compl_apply, exists_prop, exists_eq_right']

/-- Complete homomorphisms out of `Quantifier E` that agree on the individuals are equal, the
individuals being complete generators. -/
theorem completeLatticeHom_ext {β : Type*} [CompleteBooleanAlgebra β]
    {f g : CompleteLatticeHom (Quantifier E) β} (h : ∀ x, f (individual x) = g (individual x)) :
    f = g := by
  ext Q
  rw [eq_iSup_every_inf_no Q]
  simp only [map_iSup, map_inf, every_eq_iInf_individual, no_eq_iInf_compl_individual, map_iInf,
    map_compl', h]

/-! ### Predicative content and existential closure -/

/-- `BE Q` is the predicative content of the quantifier `Q`, `BE(Q) = {x | Q {x}}`, which
preserves arbitrary meets and joins. -/
def BE : CompleteLatticeHom (Quantifier E) (Set E) where
  toFun Q := {x | Q {x}}
  map_sInf' _ := Set.ext fun _ ↦ by simp
  map_sSup' _ := Set.ext fun _ ↦ by simp

@[simp] theorem mem_BE (Q : Quantifier E) (x : E) : x ∈ BE Q ↔ Q {x} := .rfl

@[simp] theorem BE_individual (j : E) : BE (individual j) = {j} :=
  Set.ext fun _ ↦ eq_comm

@[simp] theorem some_singleton (j : E) : Det.some {j} = individual j :=
  funext fun _ ↦ propext Set.singleton_inter_nonempty

/-- `BE ∘ A` is the identity: *be a man* is *man*. -/
@[simp] theorem BE_some (A : Set E) : BE (Det.some A) = A :=
  Set.ext fun _ ↦ Set.inter_singleton_nonempty

theorem some_injective : Function.Injective (Det.some : Det E) :=
  Function.LeftInverse.injective BE_some

theorem some_eq_individual_iff {N : Set E} {a : E} : Det.some N = individual a ↔ N = {a} := by
  rw [← some_singleton, some_injective.eq_iff]

theorem some_BE_eq_self_iff {Q : Quantifier E} : Det.some (BE Q) = Q ↔ ∃ A, Det.some A = Q :=
  ⟨fun h ↦ ⟨_, h⟩, fun ⟨A, h⟩ ↦ h ▸ congrArg Det.some (BE_some A)⟩

/-! ### The Galois coinsertion on monotone quantifiers -/

theorem individual_le_iff {Q : Quantifier E} (hQ : Monotone Q) {x : E} :
    individual x ≤ Q ↔ x ∈ BE Q :=
  ⟨fun h ↦ h _ rfl, fun h _ hB ↦ hQ (Set.singleton_subset_iff.2 hB) h⟩

theorem some_le_iff {Q : Quantifier E} (hQ : Monotone Q) {A : Set E} :
    Det.some A ≤ Q ↔ A ⊆ BE Q := by
  simp only [some_eq_iSup_individual, iSup₂_le_iff, individual_le_iff hQ]
  rfl

/-- On the monotone quantifiers `Det.some` and `BE` form a Galois coinsertion. -/
def gciSomeBE :
    GaloisCoinsertion (fun A ↦ (⟨Det.some A, monotone_some A⟩ : Set E →o Prop)) fun Q ↦ BE Q :=
  GaloisConnection.toGaloisCoinsertion (fun _ Q ↦ some_le_iff Q.monotone) fun A ↦ (BE_some A).le

/-! ### Individuals as complete homomorphisms

Keenan and Faltz define a proper-noun denotation as a set of properties satisfying the Meets,
Joins and Complements Conditions and prove that these are exactly the individuals generated by
atoms; the Joins Condition follows from the other two. Read as scope, the Complements Condition
says that the quantifier commutes with negation and the Meets Condition that it commutes with
universal quantification, so the scopeless quantifiers are the Montagovian individuals. -/

/-- The quantifiers that commute with negation and with arbitrary intersection are the
Montagovian individuals, [keenan-faltz-1985]'s Theorem 9 for the algebra `Set E`. -/
theorem exists_eq_individual_iff {Q : Quantifier E} :
    (∃ a, Q = individual a) ↔
      (∀ B, Q Bᶜ ↔ ¬ Q B) ∧ ∀ S : Set (Set E), Q (⋂₀ S) ↔ ∀ B ∈ S, Q B := by
  refine ⟨?_, fun ⟨hc, hs⟩ ↦ ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨individual_compl a, individual_sInter a⟩
  have hC : Q (⋂₀ {B | Q B}) := (hs _).2 fun _ h ↦ h
  obtain ⟨a, ha⟩ : (⋂₀ {B | Q B}).Nonempty := by
    by_contra! h
    rw [h, ← Set.compl_univ, ← Set.sInter_empty, hc, hs ∅] at hC
    exact hC fun _ h ↦ h.elim
  refine ⟨a, funext fun B ↦ propext ⟨fun h ↦ ha B h, fun h ↦ by_contra fun hB ↦ ?_⟩⟩
  exact ha _ ((hc B).2 hB) h

end Quantifier
