/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticSemigroup`.
-/
module

public import Linglib.Core.Algebra.FreeMonoid.FreeSemigroup
public import Linglib.Core.Computability.SyntacticMonoid
public import Linglib.Core.GroupTheory.Congruence.Hom

/-!
# The syntactic semigroup of a language

The *syntactic semigroup* of a language `L` is the quotient of the free semigroup, whose elements
are the nonempty words, by the syntactic congruence `Con.syntactic` of the nonempty words of `L`.
It is the restriction of the syntactic congruence of the free monoid, so the syntactic semigroup
embeds in the syntactic monoid, which adds to it at most the class of the empty word.

The definite, reverse definite and locally trivial pseudovarieties consist of semigroups, and
their languages are read off the syntactic semigroup. A monoid satisfying the defining condition
of any of the three is trivial, because the condition applies to the idempotent `1`.

## Main definitions

* `Language.syntacticSemigroupCon`: the syntactic congruence of the nonempty words of `L`.
* `Language.SyntacticSemigroup`: the quotient semigroup.
* `Language.toSyntacticSemigroup`: the projection, as a `MulHom`.
* `Language.RecognizesSemigroup`: recognition of a language by a homomorphism to a semigroup.

## Main results

* `Language.syntacticSemigroupToMonoid_injective`: the syntactic semigroup embeds in the syntactic
  monoid.
* `Language.isRegular_iff_finite_syntacticSemigroup`: a language is regular exactly when its
  syntactic semigroup is finite.
* `Language.recognizesSemigroup_iff_ker_le`: a homomorphism recognizes `L` exactly when its kernel
  refines the syntactic congruence.
* `Language.syntacticSemigroupCon_insert_nil`: adjoining the empty word leaves the syntactic
  semigroup unchanged.

## References

* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

namespace Language

open FreeSemigroup

variable {α : Type*} {L : Language α}

/-! ### The syntactic congruence and semigroup -/

/-- The *syntactic congruence* of `L` on the free semigroup is the syntactic congruence of the
nonempty words of `L`. -/
def syntacticSemigroupCon (L : Language α) : Con (FreeSemigroup α) :=
  Con.syntactic {u | u.toFreeMonoid.toList ∈ L}

/-- The *syntactic semigroup* of `L` is the quotient of `FreeSemigroup α` by the syntactic
congruence. -/
abbrev SyntacticSemigroup (L : Language α) := (syntacticSemigroupCon L).Quotient

/-- The *syntactic morphism* of `L` projects `FreeSemigroup α` onto the syntactic semigroup. -/
def toSyntacticSemigroup (L : Language α) : FreeSemigroup α →ₙ* L.SyntacticSemigroup :=
  Con.mkMulHom (syntacticSemigroupCon L)

theorem toSyntacticSemigroup_eq_iff {u v : FreeSemigroup α} :
    L.toSyntacticSemigroup u = L.toSyntacticSemigroup v ↔ L.syntacticSemigroupCon u v :=
  Con.eq _

theorem toSyntacticSemigroup_surjective (L : Language α) :
    Function.Surjective L.toSyntacticSemigroup :=
  Con.mkMulHom_surjective _

theorem ker_toSyntacticSemigroup (L : Language α) :
    Con.ker L.toSyntacticSemigroup = L.syntacticSemigroupCon :=
  Con.ker_mkMulHom_eq _

/-! ### Relation to the syntactic monoid -/

/-- The syntactic congruence of `L` on the free semigroup is the restriction of its syntactic
congruence on the free monoid, since every word is empty or nonempty. -/
theorem syntacticSemigroupCon_eq_comap :
    L.syntacticSemigroupCon = L.syntacticCon.comap toFreeMonoid (map_mul _) :=
  (Con.comap_syntactic eq_one_or_toFreeMonoid _).symm

theorem syntacticSemigroupCon_iff {u v : FreeSemigroup α} :
    L.syntacticSemigroupCon u v ↔ L.syntacticCon u.toFreeMonoid v.toFreeMonoid := by
  rw [syntacticSemigroupCon_eq_comap]; rfl

/-- The embedding of the syntactic semigroup into the syntactic monoid sends the class of a
nonempty word to its class in the monoid. -/
def syntacticSemigroupToMonoid (L : Language α) : L.SyntacticSemigroup →ₙ* L.SyntacticMonoid :=
  L.syntacticSemigroupCon.liftMulHom (L.toSyntacticMonoid.toMulHom.comp toFreeMonoid)
    fun _ _ h ↦ toSyntacticMonoid_eq_iff.mpr (syntacticSemigroupCon_iff.1 h)

@[simp] theorem syntacticSemigroupToMonoid_apply (L : Language α) (u : FreeSemigroup α) :
    L.syntacticSemigroupToMonoid (L.toSyntacticSemigroup u) =
      L.toSyntacticMonoid u.toFreeMonoid := rfl

theorem syntacticSemigroupToMonoid_mk (L : Language α) (a : α) (l : List α) :
    L.syntacticSemigroupToMonoid (L.toSyntacticSemigroup ⟨a, l⟩) = L.syntacticClass (a :: l) := by
  rw [syntacticSemigroupToMonoid_apply, toFreeMonoid_mk_eq_cons]; rfl

theorem syntacticSemigroupToMonoid_injective (L : Language α) :
    Function.Injective L.syntacticSemigroupToMonoid :=
  Con.liftMulHom_injective fun _ _ h ↦ syntacticSemigroupCon_iff.2 (toSyntacticMonoid_eq_iff.mp h)

instance [Finite L.SyntacticMonoid] : Finite L.SyntacticSemigroup :=
  .of_injective _ L.syntacticSemigroupToMonoid_injective

theorem eq_one_or_mem_range_syntacticSemigroupToMonoid (L : Language α) (s : L.SyntacticMonoid) :
    s = 1 ∨ s ∈ Set.range L.syntacticSemigroupToMonoid := by
  obtain ⟨x, rfl⟩ := Con.mk'_surjective s
  rcases eq_one_or_toFreeMonoid x with rfl | ⟨u, rfl⟩
  exacts [.inl (map_one _), .inr ⟨L.toSyntacticSemigroup u, rfl⟩]

theorem finite_syntacticMonoid_of_finite_syntacticSemigroup (L : Language α)
    [Finite L.SyntacticSemigroup] : Finite L.SyntacticMonoid :=
  Set.finite_univ_iff.mp <| ((Set.finite_range L.syntacticSemigroupToMonoid).insert 1).subset
    fun s _ ↦ L.eq_one_or_mem_range_syntacticSemigroupToMonoid s

/-! ### Myhill–Nerode -/

theorem IsRegular.finite_syntacticSemigroup (h : L.IsRegular) : Finite L.SyntacticSemigroup :=
  haveI := IsRegular.finite_syntacticMonoid h
  inferInstance

theorem IsRegular.of_finite_syntacticSemigroup (h : Finite L.SyntacticSemigroup) : L.IsRegular :=
  IsRegular.of_finite_syntacticMonoid L.finite_syntacticMonoid_of_finite_syntacticSemigroup

/-- A language is regular exactly when its syntactic semigroup is finite. -/
theorem isRegular_iff_finite_syntacticSemigroup :
    L.IsRegular ↔ Finite L.SyntacticSemigroup :=
  ⟨IsRegular.finite_syntacticSemigroup, IsRegular.of_finite_syntacticSemigroup⟩

/-! ### Boolean combinations -/

theorem syntacticSemigroupCon_compl : Lᶜ.syntacticSemigroupCon = L.syntacticSemigroupCon :=
  Con.syntactic_compl

theorem inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf {L' : Language α} :
    L.syntacticSemigroupCon ⊓ L'.syntacticSemigroupCon ≤ (L ⊓ L').syntacticSemigroupCon :=
  Con.inf_le_syntactic_inter

theorem inf_syntacticSemigroupCon_le_syntacticSemigroupCon_sup {L' : Language α} :
    L.syntacticSemigroupCon ⊓ L'.syntacticSemigroupCon ≤ (L ⊔ L').syntacticSemigroupCon :=
  Con.inf_le_syntactic_union

/-! ### Quotients -/

theorem syntacticSemigroupCon_le_leftQuotient (L : Language α) (u : List α) :
    L.syntacticSemigroupCon ≤ (L.leftQuotient u).syntacticSemigroupCon := fun {_ _} h ↦
  syntacticSemigroupCon_iff.2 (L.syntacticCon_le_leftQuotient u (syntacticSemigroupCon_iff.1 h))

theorem syntacticSemigroupCon_le_rightQuotient (L : Language α) (u : List α) :
    L.syntacticSemigroupCon ≤ (L.rightQuotient u).syntacticSemigroupCon := fun {_ _} h ↦
  syntacticSemigroupCon_iff.2 (L.syntacticCon_le_rightQuotient u (syntacticSemigroupCon_iff.1 h))

theorem syntacticSemigroupCon_congr {L' : Language α}
    (h : ∀ w : List α, w ≠ [] → (w ∈ L ↔ w ∈ L')) :
    L.syntacticSemigroupCon = L'.syntacticSemigroupCon :=
  congrArg Con.syntactic (Set.ext fun u ↦ h _ u.toList_toFreeMonoid_ne_nil)

/-- Adjoining the empty word leaves the syntactic congruence unchanged, since the congruence
sees only nonempty words. -/
theorem syntacticSemigroupCon_insert_nil :
    (insert [] L).syntacticSemigroupCon = L.syntacticSemigroupCon :=
  syntacticSemigroupCon_congr fun _ hw ↦ Set.mem_insert_iff.trans (or_iff_right hw)

/-! ### Recognition by a semigroup -/

section

variable {T : Type*} [Semigroup T] {η : FreeSemigroup α →ₙ* T}

/-- `η` *recognizes* `L` when the nonempty words of `L` are the preimage of a set under `η`. -/
def RecognizesSemigroup (η : FreeSemigroup α →ₙ* T) (L : Language α) : Prop :=
  ∃ P : Set T, {u | u.toFreeMonoid.toList ∈ L} = η ⁻¹' P

theorem recognizesSemigroup_iff :
    L.RecognizesSemigroup η ↔
      ∃ P : Set T, ∀ w : FreeSemigroup α, w.toFreeMonoid.toList ∈ L ↔ η w ∈ P :=
  exists_congr fun _ ↦ Set.ext_iff

theorem RecognizesSemigroup.comap {β : Type*} (hrec : L.RecognizesSemigroup η)
    (ψ : FreeSemigroup β →ₙ* FreeSemigroup α) :
    RecognizesSemigroup (η.comp ψ) {w : List β | ∃ u : FreeSemigroup β,
      u.toFreeMonoid.toList = w ∧ (ψ u).toFreeMonoid.toList ∈ L} := by
  obtain ⟨P, hP⟩ := recognizesSemigroup_iff.mp hrec
  refine recognizesSemigroup_iff.mpr ⟨P, fun w ↦ ⟨?_, fun hw ↦ ⟨w, rfl, (hP _).mpr hw⟩⟩⟩
  rintro ⟨u, hu, hmem⟩
  obtain rfl : u = w := toFreeMonoid_injective (FreeMonoid.toList.injective hu)
  exact (hP _).mp hmem

theorem recognizesSemigroup_iff_ker_le :
    L.RecognizesSemigroup η ↔ Con.ker η ≤ L.syntacticSemigroupCon :=
  (Con.ker_le_syntactic_iff (S := {u : FreeSemigroup α | u.toFreeMonoid.toList ∈ L})).symm

theorem ker_le_syntacticSemigroupCon_of_recognizes (hrec : L.RecognizesSemigroup η) :
    Con.ker η ≤ L.syntacticSemigroupCon :=
  recognizesSemigroup_iff_ker_le.1 hrec

end

theorem recognizesSemigroup_toSyntacticSemigroup (L : Language α) :
    L.RecognizesSemigroup L.toSyntacticSemigroup :=
  recognizesSemigroup_iff_ker_le.2 L.ker_toSyntacticSemigroup.le

end Language
