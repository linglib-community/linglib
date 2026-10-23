/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic

/-!
# Composition, transitivity, and antisymmetry of `List.Forall₂`

`List.Forall₂ R` relates lists of equal length pointwise. It composes pointwise
(`List.forall₂_comp_iff`), so it inherits transitivity and antisymmetry from `R`, as
`List.SublistForall₂` does in `Mathlib/Data/List/Forall2.lean`; with `R := (· ≤ ·)` this is the
pointwise order on lists of equal length, which the lexicographic order refines
(`List.Forall₂.le`, `List.Forall₂.lt_of_ne`), as `Pi.toLex_monotone` and `Pi.toLex_strictMono`
say of `Pi.Lex`; the pointwise witnesses of `Phonology/Tone/Register.lean` lift to the
lexicographic order this way. [UPSTREAM] candidates for that file, beside
`List.SublistForall₂.is_refl` and `List.SublistForall₂.is_trans`.

## Main results

* `List.forall₂_comp_iff`: `Forall₂ (R ∘r S)` is the pointwise composite of `Forall₂ R` and
  `Forall₂ S`.
* `List.Forall₂.trans`, `List.Forall₂.antisymm`, and the `Std.Refl`, `IsTrans`, `Std.Antisymm`
  instances on `Forall₂ R`.
* `List.Forall₂.le`, `List.Forall₂.lt_of_ne`: lists ordered pointwise are ordered
  lexicographically.
* `List.decidableForall₂`: a `Decidable (Forall₂ R l₁ l₂)` instance that `decide` can evaluate.

## Implementation notes

Batteries decides `Forall₂` through `List.all₂`, whose body it stopped exposing to other modules
in batteries#2006, so `decide` gets stuck on it. `List.decidableForall₂` takes priority over that
instance; remove it once Batteries exposes `List.all₂` again.
-/

@[expose] public section

namespace List

variable {α β γ : Type*} {R : α → α → Prop}

/-- `Forall₂` for a composite relation is the pointwise composite of the two `Forall₂`s. -/
theorem forall₂_comp_iff {R : α → β → Prop} {S : β → γ → Prop} {l₁ : List α} {l₃ : List γ} :
    Forall₂ (Relation.Comp R S) l₁ l₃ ↔ ∃ l₂, Forall₂ R l₁ l₂ ∧ Forall₂ S l₂ l₃ := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons hac _ ih =>
      obtain ⟨b, hab, hbc⟩ := hac
      obtain ⟨l₂, h₁, h₂⟩ := ih
      exact ⟨b :: l₂, .cons hab h₁, .cons hbc h₂⟩
  · rintro ⟨l₂, h₁, h₂⟩
    induction h₁ generalizing l₃ with
    | nil => cases h₂; exact .nil
    | cons hab _ ih =>
      cases h₂ with
      | cons hbc h₂' => exact .cons ⟨_, hab, hbc⟩ (ih h₂')

theorem Forall₂.trans [IsTrans α R] {l₁ l₂ l₃ : List α} (h₁ : Forall₂ R l₁ l₂)
    (h₂ : Forall₂ R l₂ l₃) : Forall₂ R l₁ l₃ :=
  (forall₂_comp_iff.2 ⟨l₂, h₁, h₂⟩).imp fun _ _ ⟨_, hab, hbc⟩ ↦ _root_.trans hab hbc

theorem Forall₂.antisymm [Std.Antisymm R] {l₁ l₂ : List α} :
    Forall₂ R l₁ l₂ → Forall₂ R l₂ l₁ → l₁ = l₂
  | .nil, .nil => rfl
  | .cons h₁ t₁, .cons h₂ t₂ => by rw [_root_.antisymm h₁ h₂, t₁.antisymm t₂]

instance Forall₂.instRefl [Std.Refl R] : Std.Refl (Forall₂ R) := ⟨forall₂_refl⟩

instance Forall₂.instIsTrans [IsTrans α R] : IsTrans (List α) (Forall₂ R) :=
  ⟨fun _ _ _ ↦ Forall₂.trans⟩

instance Forall₂.instAntisymm [Std.Antisymm R] : Std.Antisymm (Forall₂ R) :=
  ⟨fun _ _ ↦ Forall₂.antisymm⟩

/-! ### Decidability -/

/-- `Forall₂ R` decided by structural recursion on both lists, so that `decide` evaluates it
outside this module. -/
instance (priority := high) decidableForall₂ {R : α → β → Prop} [∀ a b, Decidable (R a b)] :
    ∀ l₁ l₂, Decidable (Forall₂ R l₁ l₂)
  | [], [] => isTrue .nil
  | [], _ :: _ | _ :: _, [] => isFalse nofun
  | a :: l₁, b :: l₂ =>
    haveI := decidableForall₂ (R := R) l₁ l₂
    decidable_of_iff (R a b ∧ Forall₂ R l₁ l₂) forall₂_cons.symm

/-! ### The lexicographic order refines the pointwise order -/

/-- Lists ordered pointwise are ordered lexicographically, the list form of
`Pi.toLex_monotone`. -/
theorem Forall₂.le [Preorder α] {l₁ l₂ : List α} (h : Forall₂ (· ≤ ·) l₁ l₂) : l₁ ≤ l₂ := by
  induction h with
  | nil => exact fun h ↦ nomatch h
  | cons hab _ ih =>
    intro hlt
    cases hlt with
    | cons hlt => exact ih hlt
    | rel hlt => exact hab.not_gt hlt

/-- Distinct lists ordered pointwise are strictly ordered lexicographically, the list form of
`Pi.toLex_strictMono`. -/
theorem Forall₂.lt_of_ne [PartialOrder α] {l₁ l₂ : List α} (h : Forall₂ (· ≤ ·) l₁ l₂)
    (hne : l₁ ≠ l₂) : l₁ < l₂ := by
  induction h with
  | nil => exact absurd rfl hne
  | cons hab _ ih =>
    rcases hab.lt_or_eq with hab | rfl
    · exact .rel hab
    · exact .cons (ih fun h ↦ hne (h ▸ rfl))

end List
