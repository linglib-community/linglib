module

public import Linglib.Semantics.Dynamic.Update
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.TFAE

/-!
# Consequence in dynamic semantics

This file defines the three notions of validity of Veltman's update semantics. A sentence is an
update of information states, a state accepts a sentence when it is a fixed point of the update, and
a text updates a state sentence by sentence. An argument is valid₁ (`EntailsFrom ⊤`) when updating
the minimal state with the premises yields a state that accepts the conclusion, valid₂ (`Entails`)
when updating any state does, and valid₃ (`PreservesAcceptance`) when every state that accepts the
premises accepts the conclusion.

Validity₂ [implies validity₃](##Entails.preservesAcceptance) in every update system, and each
converse needs only part of Veltman's four constraints. Together the constraints say [that an
update is additive](##isAdditive_iff), meeting its input with a fixed content, and then [the three
notions coincide](##tfae_entails). Each notion is characterized by its structural rules:
[validity₁](##exists_update_entailsFrom_iff) by Reflexivity, Sequential Monotony and Sequential
Cut, [validity₂](##exists_update_entails_iff) by these and Left Monotony, and
[validity₃](##exists_update_preservesAcceptance_iff) by the rules of a classical consequence
relation.

## Implementation notes

States are ordered by inclusion, as for `DynamicSemantics.CCP`: a more informed state lies lower,
the minimal state is `⊤`, and Strengthening says that an update never adds possibilities. Veltman
orients the order the other way, with the minimal state `0` at the bottom and the sum of two states
their join; on `Set` that orientation would make `⊥` the minimal state rather than the absurd state
`∅`.

Acceptance is `Function.IsFixedPt`. A sentence is identified with its update, except in the
structural characterizations, which relate the sentences of a language `L`. Veltman states the
characterization of validity₁ and refers to van Benthem for a way to prove it; the canonical system
used here has not been compared with that proof, and the characterizations of validity₂ and
validity₃ are not in Veltman's paper.

## References

* [F. Veltman, *Defaults in Update Semantics*][veltman-1996]
* [J. van Benthem, *Language in Action*][van-benthem-1991]
-/

@[expose] public section

namespace DynamicSemantics

open Function

universe u

variable {α : Type*}

/-! ### Texts -/

/-- The update of `σ` with a text, `σ[ψ₁]⋯[ψₙ]`, applying the sentences from the left. -/
def text (ψs : List (α → α)) (σ : α) : α := ψs.foldl (fun σ ψ ↦ ψ σ) σ

@[simp] theorem text_nil (σ : α) : text [] σ = σ := rfl

@[simp] theorem text_cons (ψ : α → α) (ψs : List (α → α)) (σ : α) :
    text (ψ :: ψs) σ = text ψs (ψ σ) := rfl

@[simp] theorem text_append (ψs χs : List (α → α)) (σ : α) :
    text (ψs ++ χs) σ = text χs (text ψs σ) :=
  List.foldl_append ..

/-- A property of updates closed under sequencing holds of a text of sentences that have it. -/
theorem text_induction {ψs : List (α → α)} (P : (α → α) → Prop) (hid : P id)
    (hcomp : ∀ f g, P f → P g → P (g ∘ f)) (h : ∀ ψ ∈ ψs, P ψ) : P (text ψs) := by
  induction ψs with
  | nil => exact hid
  | cons ψ ψs ih =>
    rw [List.forall_mem_cons] at h
    exact hcomp _ _ h.1 (ih h.2)

theorem isFixedPt_text {ψs : List (α → α)} {σ : α} (h : ∀ ψ ∈ ψs, IsFixedPt ψ σ) :
    IsFixedPt (text ψs) σ :=
  text_induction (IsFixedPt · σ) rfl (fun _ _ hf hg ↦ IsFixedPt.comp hg hf) h

/-! ### Consequence -/

section Consequence

/-- `ψs` entails `φ` from `σ` when updating `σ` with `ψs` yields a state that accepts `φ`.
Entailment from the minimal state is Veltman's validity₁. -/
def EntailsFrom (σ : α) (ψs : List (α → α)) (φ : α → α) : Prop := IsFixedPt φ (text ψs σ)

/-- `ψs` entails `φ` when updating any state with `ψs` yields a state that accepts `φ`, Veltman's
validity₂. -/
def Entails (ψs : List (α → α)) (φ : α → α) : Prop := ∀ σ, EntailsFrom σ ψs φ

/-- Every state that accepts each of `ψs` accepts `φ`, Veltman's validity₃. -/
def PreservesAcceptance (ψs : List (α → α)) (φ : α → α) : Prop :=
  ∀ σ, (∀ ψ ∈ ψs, IsFixedPt ψ σ) → IsFixedPt φ σ

@[inherit_doc EntailsFrom]
scoped notation:50 ψs:51 " ⊩₁ " φ:51 => EntailsFrom ⊤ ψs φ

@[inherit_doc Entails]
scoped notation:50 ψs:51 " ⊩₂ " φ:51 => Entails ψs φ

@[inherit_doc PreservesAcceptance]
scoped notation:50 ψs:51 " ⊩₃ " φ:51 => PreservesAcceptance ψs φ

variable {σ : α} {ψs χs : List (α → α)} {φ f g : α → α}

theorem entails_singleton_iff : Entails [f] φ ↔ φ ∘ f = f :=
  ⟨fun h ↦ funext h, fun h σ ↦ congrFun h σ⟩

theorem Entails.trans (h₁ : Entails ψs g) (h₂ : Entails [g] φ) : Entails ψs φ :=
  fun σ ↦ (congrArg (IsFixedPt φ) (h₁ σ)).mp (h₂ _)

/-- A state that accepts every premise is left unchanged by them, so validity₂ implies validity₃ in
every update system. -/
theorem Entails.preservesAcceptance (h : Entails ψs φ) : PreservesAcceptance ψs φ :=
  fun σ hσ ↦ (isFixedPt_text hσ).eq ▸ h σ

theorem PreservesAcceptance.mono (h : PreservesAcceptance ψs φ) (hsub : ψs ⊆ χs) :
    PreservesAcceptance χs φ :=
  fun σ hσ ↦ h σ fun ψ hψ ↦ hσ ψ (hsub hψ)

theorem Entails.append_left (h : Entails ψs φ) (χs : List (α → α)) : Entails (χs ++ ψs) φ :=
  fun σ ↦ by simpa [EntailsFrom] using h (text χs σ)

/-- Inserting a conclusion drawn from `σ` right after its premises changes nothing. From right to
left this is Sequential Monotony, and from left to right Sequential Cut. -/
theorem EntailsFrom.insert_iff (h : EntailsFrom σ ψs φ) {θs : List (α → α)} {χ : α → α} :
    EntailsFrom σ (ψs ++ φ :: θs) χ ↔ EntailsFrom σ (ψs ++ θs) χ := by
  simp only [EntailsFrom, text_append, text_cons, h.eq]

/-- Under Idempotence entailment is reflexive: a sentence follows from any premises ending in it. -/
theorem entailsFrom_append_self (hφ : ∀ σ, IsFixedPt φ (φ σ)) : EntailsFrom σ (ψs ++ [φ]) φ := by
  simpa [EntailsFrom] using hφ _

/-- When the outcome of a text accepts each of its sentences, validity₃ implies validity₂. -/
theorem preservesAcceptance_iff_entails (h : ∀ σ, ∀ ψ ∈ ψs, IsFixedPt ψ (text ψs σ)) :
    PreservesAcceptance ψs φ ↔ Entails ψs φ :=
  ⟨fun hp σ ↦ hp _ (h σ), Entails.preservesAcceptance⟩

end Consequence

/-! ### Veltman's constraints -/

section Constraints

variable [Preorder α] {ψs : List (α → α)} {φ ψ : α → α}

theorem text_le (h : ∀ ψ ∈ ψs, ψ ≤ id) : text ψs ≤ id :=
  text_induction (· ≤ id) le_rfl (fun _ _ hf hg σ ↦ (hg _).trans (hf σ)) h

theorem monotone_text (h : ∀ ψ ∈ ψs, Monotone ψ) : Monotone (text ψs) :=
  text_induction Monotone monotone_id (fun _ _ hf hg ↦ hg.comp hf) h

/-- Validity₁ implies validity₂ when the premises satisfy Monotony and the conclusion Persistence,
whether or not the premises are persistent themselves. -/
theorem entailsFrom_top_iff_entails [OrderTop α] (hψs : ∀ ψ ∈ ψs, Monotone ψ)
    (hφ : IsLowerSet (fixedPoints φ)) : EntailsFrom ⊤ ψs φ ↔ Entails ψs φ :=
  ⟨fun h _ ↦ hφ (monotone_text hψs le_top) h, fun h ↦ h ⊤⟩

/-- Along sentences satisfying Strengthening, the outcome of a text accepts each of its sentences
that satisfies Idempotence and Persistence. -/
theorem isFixedPt_text_of_mem (h : ∀ ψ ∈ ψs, ψ ≤ id) (hψ : ψ ∈ ψs)
    (hidem : ∀ σ, IsFixedPt ψ (ψ σ)) (hpers : IsLowerSet (fixedPoints ψ)) (σ : α) :
    IsFixedPt ψ (text ψs σ) := by
  obtain ⟨xs, ys, rfl⟩ := List.append_of_mem hψ
  simpa using hpers (text_le (fun χ hχ ↦ h χ (by simp [hχ])) _) (hidem _)

end Constraints

/-! ### Additive updates -/

section Additive

variable [SemilatticeInf α] [OrderTop α] {f φ : α → α} {ψs : List (α → α)} {σ : α}

/-- An update is *additive* when it meets its input with the update of the minimal state, so that
a static content determines it. -/
def IsAdditive (f : α → α) : Prop := ∀ σ, f σ = σ ⊓ f ⊤

namespace IsAdditive

theorem le (hf : IsAdditive f) : f ≤ id := fun σ ↦ (hf σ).trans_le inf_le_left

theorem monotone (hf : IsAdditive f) : Monotone f := fun σ τ h ↦ by
  rw [hf σ, hf τ]
  exact inf_le_inf_right _ h

theorem isFixedPt_iff (hf : IsAdditive f) : IsFixedPt f σ ↔ σ ≤ f ⊤ := by
  rw [IsFixedPt, hf σ, inf_eq_left]

theorem isFixedPt_apply (hf : IsAdditive f) (σ : α) : IsFixedPt f (f σ) :=
  hf.isFixedPt_iff.2 ((hf σ).trans_le inf_le_right)

theorem isLowerSet_fixedPoints (hf : IsAdditive f) : IsLowerSet (fixedPoints f) :=
  fun _ _ hτσ hσ ↦ hf.isFixedPt_iff.2 (hτσ.trans (hf.isFixedPt_iff.1 hσ))

end IsAdditive

theorem isAdditive_inf_right (a : α) : IsAdditive (· ⊓ a) := fun _ ↦ by simp

/-- An update is additive exactly when it satisfies Strengthening, never adding possibilities,
Monotony, Idempotence, and Persistence, the states that accept it being closed downward. -/
theorem isAdditive_iff : IsAdditive f ↔
    f ≤ id ∧ Monotone f ∧ (∀ σ, IsFixedPt f (f σ)) ∧ IsLowerSet (fixedPoints f) :=
  ⟨fun h ↦ ⟨h.le, h.monotone, h.isFixedPt_apply, h.isLowerSet_fixedPoints⟩,
    fun ⟨hle, hmono, hidem, hpers⟩ σ ↦ le_antisymm (le_inf (hle σ) (hmono le_top)) <|
      (hpers inf_le_right (hidem ⊤)).symm.le.trans (hmono inf_le_left)⟩

/-- For additive updates the three consequence relations coincide. -/
theorem tfae_entails (hψs : ∀ ψ ∈ ψs, IsAdditive ψ) (hφ : IsAdditive φ) :
    [EntailsFrom ⊤ ψs φ, Entails ψs φ, PreservesAcceptance ψs φ].TFAE := by
  tfae_have 1 ↔ 2 :=
    entailsFrom_top_iff_entails (fun ψ hψ ↦ (hψs ψ hψ).monotone) hφ.isLowerSet_fixedPoints
  tfae_have 3 ↔ 2 := preservesAcceptance_iff_entails fun σ ψ hψ ↦
    isFixedPt_text_of_mem (fun χ hχ ↦ (hψs χ hχ).le) hψ (hψs ψ hψ).isFixedPt_apply
      (hψs ψ hψ).isLowerSet_fixedPoints σ
  tfae_finish

/-- For additive updates an argument is valid when the contents of the premises jointly entail the
content of the conclusion. -/
theorem preservesAcceptance_iff_forall_le (hψs : ∀ ψ ∈ ψs, IsAdditive ψ) (hφ : IsAdditive φ) :
    PreservesAcceptance ψs φ ↔ ∀ σ, (∀ ψ ∈ ψs, σ ≤ ψ ⊤) → σ ≤ φ ⊤ :=
  forall_congr' fun _ ↦ imp_congr
    (forall₂_congr fun ψ hψ ↦ (hψs ψ hψ).isFixedPt_iff) hφ.isFixedPt_iff

end Additive

/-! ### Sets of possibilities -/

section CCP

variable {S : Type*} {u : CCP S} {c s : Set S}

theorem CCP.isAdditive_up (c : Set S) : IsAdditive (CCP.up c) := isAdditive_inf_right c

theorem CCP.isFixedPt_up_iff : IsFixedPt (CCP.up c) s ↔ s ⊆ c := Set.inter_eq_left

/-- On sets of possibilities the additive updates are the classical ones, eliminative and
distributive. -/
theorem CCP.isAdditive_iff_isClassical : IsAdditive u ↔ u.IsClassical := by
  rw [CCP.isClassical_iff_up_down_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ CCP.isAdditive_up _⟩
  rw [show u = CCP.up (u ⊤) from funext h, CCP.down_up]

end CCP

/-! ### Structural rules -/

section StructuralRules

variable {L : Type u} {R : List L → L → Prop}

open Classical in
/-- The canonical update for a relation `R` between texts and sentences. A state is a list of
sentences; a sentence that the state already `R`-entails leaves it unchanged, and any other is
appended to it, so that acceptance in a state is `R` itself. -/
private noncomputable def canonicalUpdate (R : List L → L → Prop) (φ : L) (X : List L) : List L :=
  if R X φ then X else X ++ [φ]

private theorem isFixedPt_canonicalUpdate_iff {φ : L} {X : List L} :
    IsFixedPt (canonicalUpdate R φ) X ↔ R X φ := by
  by_cases h : R X φ <;> simp [IsFixedPt, canonicalUpdate, h]

private theorem isFixedPt_canonicalUpdate_apply (hrefl : ∀ X φ, R (X ++ [φ]) φ) (φ : L)
    (X : List L) : IsFixedPt (canonicalUpdate R φ) (canonicalUpdate R φ X) := by
  rw [isFixedPt_canonicalUpdate_iff, canonicalUpdate]
  split_ifs with h
  exacts [h, hrefl X φ]

/-- Under Sequential Monotony and Sequential Cut, entailment from a canonical state is `R` of the
state followed by the whole text. -/
private theorem entailsFrom_canonicalUpdate_iff
    (hins : ∀ ψs θs φ χ, R ψs φ → (R (ψs ++ φ :: θs) χ ↔ R (ψs ++ θs) χ)) (X ψs : List L) (φ : L) :
    EntailsFrom X (ψs.map (canonicalUpdate R)) (canonicalUpdate R φ) ↔ R (X ++ ψs) φ := by
  rw [EntailsFrom, isFixedPt_canonicalUpdate_iff]
  suffices ∀ Z, R (text (ψs.map (canonicalUpdate R)) X ++ Z) φ ↔ R (X ++ ψs ++ Z) φ by
    simpa using this []
  induction ψs generalizing X with
  | nil => simp
  | cons ψ ψs ih =>
    intro Z
    rw [List.map_cons, text_cons, ih]
    by_cases h : R X ψ
    · simp [canonicalUpdate, h, hins _ _ _ _ h]
    · simp [canonicalUpdate, h]

/-- Reflexivity, Sequential Monotony and Sequential Cut completely characterize validity₁ in update
systems satisfying Idempotence (the last two are the two directions of the second clause): a
relation between texts and sentences satisfies them exactly when it is validity₁ of such a
system. -/
theorem exists_update_entailsFrom_iff :
    (∃ (α : Type u) (σ₀ : α) (u : L → α → α), (∀ φ σ, IsFixedPt (u φ) (u φ σ)) ∧
        ∀ ψs φ, R ψs φ ↔ EntailsFrom σ₀ (ψs.map u) (u φ)) ↔
      (∀ ψs φ, R (ψs ++ [φ]) φ) ∧
        ∀ ψs θs φ χ, R ψs φ → (R (ψs ++ φ :: θs) χ ↔ R (ψs ++ θs) χ) := by
  refine ⟨fun ⟨α, σ₀, u, hidem, hR⟩ ↦ ⟨fun ψs φ ↦ ?_, fun ψs θs φ χ h ↦ ?_⟩, fun ⟨hrefl, hins⟩ ↦
    ⟨List L, [], canonicalUpdate R, isFixedPt_canonicalUpdate_apply hrefl, fun ψs φ ↦ ?_⟩⟩
  · simpa [hR] using entailsFrom_append_self (hidem φ)
  · simpa [hR] using ((hR ψs φ).1 h).insert_iff
  · simpa using (entailsFrom_canonicalUpdate_iff hins [] ψs φ).symm

/-- Validity₂ of the update systems satisfying Idempotence is characterized by the rules of
validity₁ together with Left Monotony. -/
theorem exists_update_entails_iff :
    (∃ (α : Type u) (u : L → α → α), (∀ φ σ, IsFixedPt (u φ) (u φ σ)) ∧
        ∀ ψs φ, R ψs φ ↔ Entails (ψs.map u) (u φ)) ↔
      (∀ ψs φ, R (ψs ++ [φ]) φ) ∧
        (∀ ψs θs φ χ, R ψs φ → (R (ψs ++ φ :: θs) χ ↔ R (ψs ++ θs) χ)) ∧
        ∀ χs ψs φ, R ψs φ → R (χs ++ ψs) φ := by
  refine ⟨fun ⟨α, u, hidem, hR⟩ ↦ ⟨fun ψs φ ↦ ?_, fun ψs θs φ χ h ↦ ?_, fun χs ψs φ h ↦ ?_⟩,
    fun ⟨hrefl, hins, hleft⟩ ↦ ⟨List L, canonicalUpdate R,
      isFixedPt_canonicalUpdate_apply hrefl, fun ψs φ ↦ ⟨fun h X ↦ ?_, fun h ↦ ?_⟩⟩⟩
  · simpa [hR, Entails] using fun σ ↦ entailsFrom_append_self (σ := σ) (hidem φ)
  · simpa [hR, Entails] using forall_congr' fun σ ↦ ((hR ψs φ).1 h σ).insert_iff
  · simpa [hR] using ((hR ψs φ).1 h).append_left (χs.map u)
  · exact (entailsFrom_canonicalUpdate_iff hins X ψs φ).2 (hleft X ψs φ h)
  · simpa using (entailsFrom_canonicalUpdate_iff hins [] ψs φ).1 (h [])

/-- Validity₃ is characterized by the rules of a classical consequence relation: a sentence follows
from any premises that include it, and whatever follows from consequences of the premises follows
from the premises. -/
theorem exists_update_preservesAcceptance_iff :
    (∃ (α : Type u) (u : L → α → α), (∀ φ σ, IsFixedPt (u φ) (u φ σ)) ∧
        ∀ ψs φ, R ψs φ ↔ PreservesAcceptance (ψs.map u) (u φ)) ↔
      (∀ ψs φ, φ ∈ ψs → R ψs φ) ∧ ∀ ψs χs φ, (∀ χ ∈ χs, R ψs χ) → R χs φ → R ψs φ := by
  refine ⟨fun ⟨α, u, _, hR⟩ ↦ ⟨fun ψs φ h ↦ ?_, fun ψs χs φ hχs h ↦ ?_⟩, fun ⟨hrefl, hcut⟩ ↦
    ⟨List L, canonicalUpdate R, isFixedPt_canonicalUpdate_apply fun X φ ↦ hrefl _ _ (by simp),
      fun ψs φ ↦ ⟨fun h X hX ↦ ?_, fun h ↦ ?_⟩⟩⟩
  · exact (hR ψs φ).2 fun σ hσ ↦ hσ _ (List.mem_map_of_mem h)
  · refine (hR ψs φ).2 fun σ hσ ↦ (hR χs φ).1 h σ ?_
    simpa using fun χ hχ ↦ (hR ψs χ).1 (hχs χ hχ) σ hσ
  · rw [isFixedPt_canonicalUpdate_iff]
    exact hcut X ψs φ (fun χ hχ ↦
      isFixedPt_canonicalUpdate_iff.1 (hX _ (List.mem_map_of_mem hχ))) h
  · refine isFixedPt_canonicalUpdate_iff.1 (h ψs ?_)
    simpa [isFixedPt_canonicalUpdate_iff] using hrefl ψs

end StructuralRules

end DynamicSemantics
