/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.Basic`, a new topic directory over
`Mathlib.Algebra.Group.Pseudovariety`.
-/
module

public import Linglib.Core.Computability.SyntacticSemigroup
public import Linglib.Core.Algebra.Group.Pseudovariety
public import Mathlib.Order.BooleanSubalgebra

/-!
# Varieties of languages

A *variety of languages* assigns to each alphabet a Boolean algebra of regular languages, closed
under quotients by words and under inverse images of homomorphisms of free monoids. The languages
of a pseudovariety `V` of finite monoids over `α` are those whose syntactic monoid lies in `V`,
equivalently those
[recognized by a member of `V`](##Monoid.Pseudovariety.mem_languages_iff_exists_recognizes), and
they form [a variety of languages](##Monoid.Pseudovariety.toLanguageVariety). The pseudovariety of
all finite monoids gives the [regular languages](##Monoid.Pseudovariety.mem_languages_top), and the
trivial one [only the empty and the full language](##Monoid.Pseudovariety.languages_bot). A
pseudovariety of finite semigroups gives in the same way, through the syntactic semigroup,
Eilenberg's languages of nonempty words.

## Implementation notes

A language of nonempty words is represented by any language with the same nonempty words, since
the syntactic semigroup
[does not see the empty word](##Semigroup.Pseudovariety.insert_nil_mem_languages_iff). A free
semigroup has no erasing homomorphisms, so the semigroup side is closed only under inverse images
of homomorphisms between free semigroups.

## References

* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

universe u

namespace Monoid.Pseudovariety

open Language

variable {V : Pseudovariety.{u}} {α β : Type u} {L : Language α}

variable (V) in
/-- The *languages* of a pseudovariety `V` over `α` are those whose syntactic monoid lies in `V`.
They form a Boolean subalgebra of `Language α`. -/
def languages (α : Type u) : BooleanSubalgebra (Language α) where
  carrier := {L | V.mem L.SyntacticMonoid}
  supClosed' _ hL _ hM :=
    V.mem_quotient_of_le inf_syntacticCon_le_syntacticCon_sup (V.mem_quotient_inf hL hM)
  infClosed' _ hL _ hM :=
    V.mem_quotient_of_le inf_syntacticCon_le_syntacticCon_inf (V.mem_quotient_inf hL hM)
  compl_mem' h := V.mem_quotient_of_le syntacticCon_compl.ge h
  bot_mem' := V.mem_of_isSubquotient
    (Recognizes.syntacticMonoid_isSubquotient (φ := (1 : FreeMonoid α →* PUnit)) ⟨∅, rfl⟩)
    V.memUnit

@[simp] theorem mem_languages : L ∈ V.languages α ↔ V.mem L.SyntacticMonoid := Iff.rfl

theorem isRegular_of_mem_languages (h : L ∈ V.languages α) : L.IsRegular :=
  .of_finite_syntacticMonoid (V.finite_of_mem h)

/-- A language recognized by a member of `V` is a language of `V`, since its syntactic monoid
divides the recognizer. -/
theorem mem_languages_of_recognizes {N : Type u} [Monoid N] (hN : V.mem N)
    {η : FreeMonoid α →* N} (h : Recognizes η L) : L ∈ V.languages α :=
  V.mem_of_isSubquotient h.syntacticMonoid_isSubquotient hN

/-- The languages of `V` are those recognized by a member of `V`. -/
theorem mem_languages_iff_exists_recognizes : L ∈ V.languages α ↔
    ∃ (N : Type u) (_ : Monoid N) (η : FreeMonoid α →* N), V.mem N ∧ Recognizes η L :=
  ⟨fun h ↦ ⟨_, _, _, h, L.recognizes_toSyntacticMonoid⟩,
    fun ⟨_, _, _, hN, h⟩ ↦ mem_languages_of_recognizes hN h⟩

/-- The languages of the pseudovariety of all finite monoids are the regular languages. -/
@[simp] theorem mem_languages_top : L ∈ (⊤ : Pseudovariety.{u}).languages α ↔ L.IsRegular := by
  rw [mem_languages, mem_top, isRegular_iff_finite_syntacticMonoid]

/-- The languages of the trivial pseudovariety are the empty and the full language. -/
@[simp] theorem languages_bot : (⊥ : Pseudovariety.{u}).languages α = ⊥ :=
  BooleanSubalgebra.ext fun _ ↦ by
    rw [mem_languages, mem_bot, subsingleton_syntacticMonoid_iff, BooleanSubalgebra.mem_bot]

/-- The languages of `V` are closed under inverse images of homomorphisms of free monoids. -/
theorem comap_mem_languages {L : Language β} (h : L ∈ V.languages β)
    (φ : FreeMonoid α →* FreeMonoid β) :
    {w : List α | φ (FreeMonoid.ofList w) ∈ L} ∈ V.languages α :=
  mem_languages_of_recognizes h (L.recognizes_toSyntacticMonoid.comap φ)

theorem leftQuotient_mem_languages (h : L ∈ V.languages α) (u : List α) :
    L.leftQuotient u ∈ V.languages α :=
  V.mem_quotient_of_le (L.syntacticCon_le_leftQuotient u) h

theorem rightQuotient_mem_languages (h : L ∈ V.languages α) (u : List α) :
    L.rightQuotient u ∈ V.languages α :=
  V.mem_quotient_of_le (L.syntacticCon_le_rightQuotient u) h

end Monoid.Pseudovariety

namespace Monoid

open Language

/-- A *variety of languages* assigns to each alphabet a Boolean algebra of regular languages, closed
under inverse images of homomorphisms between free monoids and under left and right quotients by
words. -/
structure LanguageVariety where
  /-- The languages of the variety over each alphabet. -/
  lang : ∀ α : Type u, BooleanSubalgebra (Language α)
  /-- Every member is regular. -/
  isRegular : ∀ {α : Type u} {L : Language α}, L ∈ lang α → L.IsRegular
  /-- The inverse image of a member under a homomorphism of free monoids is a member. -/
  comap_mem : ∀ {α β : Type u} {L : Language β} (φ : FreeMonoid α →* FreeMonoid β),
    L ∈ lang β → {w : List α | φ (FreeMonoid.ofList w) ∈ L} ∈ lang α
  /-- The left quotient of a member by a word is a member. -/
  leftQuotient_mem : ∀ {α : Type u} {L : Language α} (u : List α),
    L ∈ lang α → L.leftQuotient u ∈ lang α
  /-- The right quotient of a member by a word is a member. -/
  rightQuotient_mem : ∀ {α : Type u} {L : Language α} (u : List α),
    L ∈ lang α → L.rightQuotient u ∈ lang α

namespace LanguageVariety

instance : DFunLike LanguageVariety.{u} (Type u) fun α ↦ BooleanSubalgebra (Language α) where
  coe := lang
  coe_injective := by
    rintro ⟨f, _, _, _, _⟩ ⟨g, _, _, _, _⟩ (rfl : f = g); rfl

@[ext] theorem ext {𝒱 𝒲 : LanguageVariety.{u}}
    (h : ∀ (α : Type u) (L : Language α), L ∈ 𝒱 α ↔ L ∈ 𝒲 α) : 𝒱 = 𝒲 :=
  DFunLike.ext _ _ fun α ↦ BooleanSubalgebra.ext (h α)

instance : PartialOrder LanguageVariety.{u} := .lift (⇑) DFunLike.coe_injective

theorem le_def {𝒱 𝒲 : LanguageVariety.{u}} :
    𝒱 ≤ 𝒲 ↔ ∀ (α : Type u) ⦃L : Language α⦄, L ∈ 𝒱 α → L ∈ 𝒲 α := Iff.rfl

end LanguageVariety

/-- The languages of a pseudovariety form a variety of languages. -/
def Pseudovariety.toLanguageVariety (V : Pseudovariety.{u}) : LanguageVariety.{u} where
  lang := V.languages
  isRegular := Pseudovariety.isRegular_of_mem_languages
  comap_mem φ h := Pseudovariety.comap_mem_languages h φ
  leftQuotient_mem u h := Pseudovariety.leftQuotient_mem_languages h u
  rightQuotient_mem u h := Pseudovariety.rightQuotient_mem_languages h u

@[simp] theorem Pseudovariety.toLanguageVariety_apply (V : Pseudovariety.{u}) (α : Type u) :
    V.toLanguageVariety α = V.languages α := rfl

end Monoid

namespace Semigroup.Pseudovariety

open Language

variable {V : Pseudovariety.{u}} {α β : Type u} {L : Language α}

variable (V) in
/-- The *languages* of a pseudovariety `V` of finite semigroups over `α` are those whose syntactic
semigroup lies in `V`. They form a Boolean subalgebra of `Language α`. -/
def languages (α : Type u) : BooleanSubalgebra (Language α) where
  carrier := {L | V.mem L.SyntacticSemigroup}
  supClosed' _ hL _ hM := V.mem_quotient_of_le
    inf_syntacticSemigroupCon_le_syntacticSemigroupCon_sup (V.mem_quotient_inf hL hM)
  infClosed' _ hL _ hM := V.mem_quotient_of_le
    inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf (V.mem_quotient_inf hL hM)
  compl_mem' h := V.mem_quotient_of_le syntacticSemigroupCon_compl.ge h
  bot_mem' := V.mem_quotient_of_le
    (ker_le_syntacticSemigroupCon_of_recognizes (η := (1 : FreeSemigroup α →ₙ* PUnit))
      (recognizesSemigroup_iff.2 ⟨∅, fun _ ↦ Iff.rfl⟩))
    (V.mem_quotient_ker _ V.memUnit)

@[simp] theorem mem_languages : L ∈ V.languages α ↔ V.mem L.SyntacticSemigroup := Iff.rfl

theorem isRegular_of_mem_languages (h : L ∈ V.languages α) : L.IsRegular :=
  .of_finite_syntacticSemigroup (V.finite_of_mem h)

/-- A language recognized by a member of `V` is a language of `V`. -/
theorem mem_languages_of_recognizes {T : Type u} [Semigroup T] (hT : V.mem T)
    {η : FreeSemigroup α →ₙ* T} (h : L.RecognizesSemigroup η) : L ∈ V.languages α :=
  V.mem_quotient_of_le (ker_le_syntacticSemigroupCon_of_recognizes h) (V.mem_quotient_ker η hT)

/-- The languages of `V` are those recognized by a member of `V`. -/
theorem mem_languages_iff_exists_recognizes : L ∈ V.languages α ↔
    ∃ (T : Type u) (_ : Semigroup T) (η : FreeSemigroup α →ₙ* T),
      V.mem T ∧ L.RecognizesSemigroup η :=
  ⟨fun h ↦ ⟨_, _, _, h, L.recognizesSemigroup_toSyntacticSemigroup⟩,
    fun ⟨_, _, _, hT, h⟩ ↦ mem_languages_of_recognizes hT h⟩

/-- Whether a language of `V` contains the empty word is invisible to `V`. -/
@[simp] theorem insert_nil_mem_languages_iff :
    insert [] L ∈ V.languages α ↔ L ∈ V.languages α :=
  .of_eq <| congrArg (fun c : Con (FreeSemigroup α) ↦ V.mem c.Quotient)
    syntacticSemigroupCon_insert_nil

/-- The languages of `V` are closed under inverse images of homomorphisms of free semigroups. -/
theorem comap_mem_languages {L : Language β} (h : L ∈ V.languages β)
    (φ : FreeSemigroup α →ₙ* FreeSemigroup β) :
    {w : List α | ∃ u : FreeSemigroup α,
      u.toFreeMonoid.toList = w ∧ (φ u).toFreeMonoid.toList ∈ L} ∈ V.languages α :=
  mem_languages_of_recognizes h (L.recognizesSemigroup_toSyntacticSemigroup.comap φ)

theorem leftQuotient_mem_languages (h : L ∈ V.languages α) (u : List α) :
    L.leftQuotient u ∈ V.languages α :=
  V.mem_quotient_of_le (L.syntacticSemigroupCon_le_leftQuotient u) h

theorem rightQuotient_mem_languages (h : L ∈ V.languages α) (u : List α) :
    L.rightQuotient u ∈ V.languages α :=
  V.mem_quotient_of_le (L.syntacticSemigroupCon_le_rightQuotient u) h

end Semigroup.Pseudovariety
