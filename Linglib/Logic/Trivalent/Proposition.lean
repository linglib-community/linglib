/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Bilattice.Guard
public import Linglib.Logic.Trivalent.Knowledge
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Trivalent propositions

A trivalent proposition is a function `W → Trivalent`, true, false or undefined at each world,
with the connectives taken pointwise. Its worlds split into a positive extension `posExt p`, a
negative extension `negExt p` and a gap `gapExt p`. Sending a proposition to its two extensions
is the bounded lattice embedding `extensions` into Fitting's product `Set W ⊙ Set W`, natural in
the worlds (`extensions_comp`), whose image is the disjoint pairs (`orderIsoDisjoint`); it carries
Kleene's negation to the swap (`extensions_compl`) and transplication to Fitting's guard
(`extensions_transplication`). Beaver and Krahmer's assertion operator applied pointwise
collapses the gap into the negative extension.

A proposition `p` further presupposing `A` is its restriction `restrict A p`, the value of `p`
where `A` holds and `undefined` elsewhere. The restriction of a two-valued proposition is a
conditional event `condEvent A B` in de Finetti's sense. Every trivalent proposition is the
conditional event of its truth on its definedness (`condEvent_ne_undefined_eq_true`), and two
conditional events coincide exactly when they have the same condition and agree on it
(`condEvent_eq_condEvent_iff`). In the knowledge order a restriction lies below the proposition it
restricts, and the propositions below a two-valued one are the conditional events that assert it
(`forall_kLE_ofProp_iff`).

## References

* [beaver-krahmer-2001]
* [de-finetti-1936]
* [fitting-1994]
-/

@[expose] public section

namespace Trivalent

open Bilattice Product

variable {W : Type*}

/-! ### Extensions -/

/-- The positive extension collects the worlds where the proposition is true. -/
def posExt (p : W → Trivalent) : Set W := {w | p w = .true}

/-- The negative extension collects the worlds where the proposition is false. -/
def negExt (p : W → Trivalent) : Set W := {w | p w = .false}

/-- The extension gap collects the worlds where the proposition is neither true nor false. -/
def gapExt (p : W → Trivalent) : Set W := {w | p w = .undefined}

section Extensions

variable {p q : W → Trivalent} {w : W}

@[simp] theorem mem_posExt : w ∈ posExt p ↔ p w = .true := Iff.rfl
@[simp] theorem mem_negExt : w ∈ negExt p ↔ p w = .false := Iff.rfl
@[simp] theorem mem_gapExt : w ∈ gapExt p ↔ p w = .undefined := Iff.rfl
theorem mem_compl_gapExt : w ∈ (gapExt p)ᶜ ↔ p w ≠ .undefined := Iff.rfl

instance (p : W → Trivalent) : DecidablePred (· ∈ posExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .true))

instance (p : W → Trivalent) : DecidablePred (· ∈ negExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .false))

instance (p : W → Trivalent) : DecidablePred (· ∈ gapExt p) :=
  fun w ↦ inferInstanceAs (Decidable (p w = .undefined))

theorem posExt_union_negExt_union_gapExt (p : W → Trivalent) :
    posExt p ∪ negExt p ∪ gapExt p = Set.univ := by
  ext w
  simp only [Set.mem_union, mem_posExt, mem_negExt, mem_gapExt, Set.mem_univ, iff_true]
  cases p w <;> simp

theorem posExt_union_negExt (p : W → Trivalent) : posExt p ∪ negExt p = (gapExt p)ᶜ := by
  ext w; cases h : p w <;> simp [h]

theorem disjoint_posExt_negExt (p : W → Trivalent) : Disjoint (posExt p) (negExt p) :=
  Set.disjoint_left.2 fun w h₁ h₂ ↦ absurd ((mem_posExt.1 h₁).symm.trans h₂) (by decide)

theorem posExt_subset_compl_gapExt (p : W → Trivalent) : posExt p ⊆ (gapExt p)ᶜ :=
  (posExt_union_negExt p) ▸ Set.subset_union_left

theorem negExt_subset_compl_gapExt (p : W → Trivalent) : negExt p ⊆ (gapExt p)ᶜ :=
  (posExt_union_negExt p) ▸ Set.subset_union_right

theorem compl_gapExt_inter_compl_posExt (p : W → Trivalent) :
    (gapExt p)ᶜ ∩ (posExt p)ᶜ = negExt p := by
  ext w; cases h : p w <;> simp [h]

@[simp] theorem gapExt_ofProp (A : W → Prop) [DecidablePred A] :
    gapExt (fun w ↦ ofProp (A w)) = ∅ := by
  ext w; simp

@[simp] theorem gapExt_undefined : gapExt (fun _ ↦ .undefined : W → Trivalent) = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ rfl

/-- The positive and negative extensions of a trivalent proposition, in Fitting's product of
world-sets: Strong Kleene conjunction and disjunction are its truth meet and join. -/
def extensions : BoundedLatticeHom (W → Trivalent) (Set W ⊙ Set W) where
  toFun p := mk (posExt p) (negExt p)
  map_sup' p q := by ext w <;> simp [posExt, negExt]
  map_inf' p q := by ext w <;> simp [posExt, negExt]
  map_top' := by ext w <;> simp [posExt, negExt]
  map_bot' := by ext w <;> simp [posExt, negExt]

theorem extensions_apply (p : W → Trivalent) : extensions p = mk (posExt p) (negExt p) := rfl

@[simp] theorem pro_extensions (p : W → Trivalent) : (extensions p).pro = posExt p := rfl
@[simp] theorem con_extensions (p : W → Trivalent) : (extensions p).con = negExt p := rfl

/-- `extensions` is natural in the worlds: reindexing a proposition along `f` takes preimages of
its extensions. -/
theorem extensions_comp {W' : Type*} (f : W' → W) (p : W → Trivalent) :
    extensions (p ∘ f) = mk (f ⁻¹' posExt p) (f ⁻¹' negExt p) := rfl

theorem extensions_le_extensions : extensions p ≤ extensions q ↔ p ≤ q := by
  have key : ∀ a b : Trivalent, a ≤ b ↔ (a = .true → b = .true) ∧ (b = .false → a = .false) := by
    decide
  simp only [extensions_apply, mk_le_mk, Set.subset_def, mem_posExt, mem_negExt, Pi.le_def, key]
  exact ⟨fun h w ↦ ⟨h.1 w, h.2 w⟩, fun h ↦ ⟨fun w ↦ (h w).1, fun w ↦ (h w).2⟩⟩

theorem extensions_injective : Function.Injective (extensions (W := W)) := fun _ _ h ↦
  le_antisymm (extensions_le_extensions.1 h.le) (extensions_le_extensions.1 h.ge)

/-- The extensions of a proposition are disjoint, and every disjoint pair is the extensions of a
proposition: over a Boolean factor, Fitting's consistent pairs. -/
theorem range_extensions : Set.range (extensions (W := W)) = {x | Disjoint x.pro x.con} := by
  classical
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rw [Set.mem_ofPred_eq, Set.disjoint_left]
    intro w h₁ h₂
    simp only [pro_extensions, con_extensions, mem_posExt, mem_negExt] at h₁ h₂
    exact absurd (h₁.symm.trans h₂) (by decide)
  · intro hx
    refine ⟨fun w ↦ if w ∈ x.pro then .true else if w ∈ x.con then .false else .undefined, ?_⟩
    ext w <;> simp only [pro_extensions, con_extensions, mem_posExt, mem_negExt]
    · split_ifs <;> simp_all
    · split_ifs with h₁ h₂
      · exact iff_of_false (by decide) (Set.disjoint_left.1 hx h₁)
      · simp_all
      · simp_all

/-- Three-valued propositions are the disjoint pairs of world-sets. -/
noncomputable def orderIsoDisjoint :
    (W → Trivalent) ≃o {x : Set W ⊙ Set W | Disjoint x.pro x.con} :=
  (OrderEmbedding.ofMapLEIff extensions fun _ _ ↦ extensions_le_extensions).orderIso.trans
    (Set.orderIsoOfEq _ _ range_extensions)

/-- Kleene's negation of a proposition swaps its extensions. -/
@[simp] theorem extensions_compl (p : W → Trivalent) : extensions pᶜ = (extensions p)ᶜ := by
  ext w <;> simp [posExt, negExt]

/-- Transplication of propositions is Fitting's guard on their extensions. -/
theorem extensions_transplication (π φ : W → Trivalent) :
    extensions (fun w ↦ transplication (π w) (φ w)) = guard (extensions π) (extensions φ) := by
  ext w <;> simp [posExt, negExt, transplication_eq_true_iff, transplication_eq_false_iff]

end Extensions

/-- A proposition is bivalent if it takes no `undefined` value. -/
def IsBivalent (p : W → Trivalent) : Prop :=
  ∀ w, p w = .true ∨ p w = .false

theorem isBivalent_iff_gapExt_eq_empty (p : W → Trivalent) :
    IsBivalent p ↔ gapExt p = ∅ := by
  simp only [IsBivalent, Set.eq_empty_iff_forall_notMem, mem_gapExt]
  exact forall_congr' fun w => by cases p w <;> simp

theorem isBivalent_iff_forall_ne_undefined (p : W → Trivalent) :
    IsBivalent p ↔ ∀ w, p w ≠ .undefined :=
  forall_congr' fun w => by cases p w <;> simp

theorem IsBivalent.ne_undefined {p : W → Trivalent} (h : IsBivalent p) (w : W) :
    p w ≠ .undefined :=
  (isBivalent_iff_forall_ne_undefined p).1 h w

/-! ### Extensions under assertion

Asserting a proposition pointwise, `fun w ↦ ofProp (p w = .true)`, keeps its positive extension and
moves its gap into the negative extension. Conjoining it with a two-valued `R` keeps its gap only
where `R` holds. -/

@[simp] theorem posExt_ofProp_eq_true (p : W → Trivalent) :
    posExt (fun w ↦ ofProp (p w = .true)) = posExt p := by
  ext w; simp

@[simp] theorem negExt_ofProp_eq_true (p : W → Trivalent) :
    negExt (fun w ↦ ofProp (p w = .true)) = negExt p ∪ gapExt p := by
  ext w; cases h : p w <;> simp [h]

@[simp] theorem posExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → Trivalent) :
    posExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w} ∩ posExt p := by
  ext w; by_cases h : R w <;> simp [h]

@[simp] theorem negExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → Trivalent) :
    negExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w}ᶜ ∪ negExt p := by
  ext w; by_cases h : R w <;> simp [h]

@[simp] theorem gapExt_ofProp_inf (R : W → Prop) [DecidablePred R] (p : W → Trivalent) :
    gapExt (fun w ↦ ofProp (R w) ⊓ p w) = {w | R w} ∩ gapExt p := by
  ext w; simp [and_comm]

/-- Composing with a function undefined exactly at `undefined` preserves the gap. -/
theorem gapExt_comp {f : Trivalent → Trivalent} (hf : ∀ a, f a = .undefined ↔ a = .undefined)
    (p : W → Trivalent) :
    gapExt (f ∘ p) = gapExt p := by
  ext w; simp [hf]

/-- Composing with a function that is never `undefined` leaves no gap. -/
theorem isBivalent_comp {f : Trivalent → Trivalent} (hf : ∀ a, f a ≠ .undefined)
    (p : W → Trivalent) :
    IsBivalent (f ∘ p) :=
  (isBivalent_iff_forall_ne_undefined _).2 fun _ ↦ hf _

theorem isBivalent_ofProp_eq_true (p : W → Trivalent) : IsBivalent fun w ↦ ofProp (p w = .true) :=
  fun w ↦ by by_cases h : p w = .true <;> simp [h]

/-! ### Restriction

A trivalent proposition `p` further presupposing `A` is its restriction to `A`, the pointwise
transplication of `p` on `A`: the value of `p` where `A` holds and `undefined` elsewhere. -/

section Restrict

/-- The restriction of `p` to `A`, `p` further presupposing `A`: the value of `p` where `A` holds
and `undefined` elsewhere. -/
protected def restrict (A : W → Prop) [DecidablePred A] (p : W → Trivalent) : W → Trivalent :=
  fun w ↦ transplication (ofProp (A w)) (p w)

variable {A B : W → Prop} [DecidablePred A] [DecidablePred B] {p : W → Trivalent} {w : W}

theorem restrict_apply : Trivalent.restrict A p w = transplication (ofProp (A w)) (p w) := rfl

@[simp] theorem restrict_eq_true_iff :
    Trivalent.restrict A p w = .true ↔ A w ∧ p w = .true := by
  simp [Trivalent.restrict]

@[simp] theorem restrict_eq_false_iff :
    Trivalent.restrict A p w = .false ↔ A w ∧ p w = .false := by
  simp [Trivalent.restrict]

@[simp] theorem restrict_eq_undefined_iff :
    Trivalent.restrict A p w = .undefined ↔ ¬ A w ∨ p w = .undefined := by
  simp [Trivalent.restrict]

@[simp] theorem posExt_restrict : posExt (Trivalent.restrict A p) = {w | A w} ∩ posExt p := by
  ext w; simp

@[simp] theorem negExt_restrict : negExt (Trivalent.restrict A p) = {w | A w} ∩ negExt p := by
  ext w; simp

@[simp] theorem gapExt_restrict : gapExt (Trivalent.restrict A p) = {w | A w}ᶜ ∪ gapExt p := by
  ext w; simp

/-- Negating a restriction negates the proposition and keeps the condition. -/
theorem compl_restrict : (Trivalent.restrict A p)ᶜ = Trivalent.restrict A pᶜ :=
  funext fun _ ↦ eq_of_eq_undefined_iff_of_eq_true_iff (by simp) (by simp)

/-- Restricting twice restricts to the conjunction of the conditions. -/
theorem restrict_restrict :
    Trivalent.restrict A (Trivalent.restrict B p) = Trivalent.restrict (fun w ↦ A w ∧ B w) p :=
  funext fun _ ↦ eq_of_eq_undefined_iff_of_eq_true_iff
    (by simp only [restrict_eq_undefined_iff]; tauto) (by simp [and_assoc])

/-- A restriction has at most the information of the proposition it restricts. -/
theorem restrict_kLE : Trivalent.restrict A p w ≤ₖ p w := transplication_kLE _ _

end Restrict

/-! ### Conditional events

A proposition defined where `A` holds and asserting `B` there is the transplication of `B` on `A`,
pointwise: the classical value of `B` on `A` and `undefined` elsewhere. A trivalent proposition is
fixed by where it is defined and where it is true, and every such pair arises, so trivalent
propositions are the conditional events `B | A` of [de-finetti-1936], conditional assertions of a
two-valued content on a two-valued condition; two of them coincide exactly when they have the
same condition and agree on it. -/

section ConditionalEvent

/-- The conditional event `B | A` of [de-finetti-1936], `B` presupposing `A`: the classical value
of `B` where `A` holds and `undefined` elsewhere, the pointwise transplication of `B` on `A`. -/
def condEvent (A B : W → Prop) [DecidablePred A] [DecidablePred B] : W → Trivalent :=
  fun w ↦ transplication (ofProp (A w)) (ofProp (B w))

section

variable {A B : W → Prop} [DecidablePred A] [DecidablePred B] {w : W}

theorem condEvent_apply : condEvent A B w = transplication (ofProp (A w)) (ofProp (B w)) := rfl

/-- A conditional event is the restriction of a two-valued proposition. -/
theorem condEvent_eq_restrict : condEvent A B = Trivalent.restrict A fun w ↦ ofProp (B w) := rfl

@[simp] theorem condEvent_eq_true_iff : condEvent A B w = .true ↔ A w ∧ B w := by
  simp [condEvent]

@[simp] theorem condEvent_eq_false_iff : condEvent A B w = .false ↔ A w ∧ ¬ B w := by
  simp [condEvent]

@[simp] theorem condEvent_eq_undefined_iff : condEvent A B w = .undefined ↔ ¬ A w := by
  simp [condEvent]

@[simp] theorem posExt_condEvent : posExt (condEvent A B) = {w | A w ∧ B w} := by
  ext w; simp

@[simp] theorem negExt_condEvent : negExt (condEvent A B) = {w | A w ∧ ¬ B w} := by
  ext w; simp

@[simp] theorem gapExt_condEvent : gapExt (condEvent A B) = {w | ¬ A w} := by
  ext w; simp

/-- Negating a conditional event negates its content and keeps its condition. -/
theorem compl_condEvent : (condEvent A B)ᶜ = condEvent A (fun w ↦ ¬ B w) :=
  funext fun _ ↦ eq_of_eq_undefined_iff_of_eq_true_iff (by simp) (by simp)

theorem isBivalent_condEvent_iff : IsBivalent (condEvent A B) ↔ ∀ w, A w := by
  simp [isBivalent_iff_forall_ne_undefined]

/-- A conditional event has at most the information of what it asserts. -/
theorem condEvent_kLE : condEvent A B w ≤ₖ ofProp (B w) := transplication_kLE _ _

/-- The propositions with at most the information of a two-valued one are the conditional events
that assert it. -/
theorem forall_kLE_ofProp_iff {p : W → Trivalent} :
    (∀ w, p w ≤ₖ ofProp (B w)) ↔ p = condEvent (p · ≠ .undefined) B := by
  refine ⟨fun h ↦ funext fun w ↦ ?_, fun h w ↦ ?_⟩
  · have := kLE_ofProp_iff.1 (h w)
    cases hp : p w <;> simp_all [condEvent]
  · rw [h]; exact condEvent_kLE

end

/-- Every trivalent proposition is the conditional event of its truth on its definedness. -/
theorem condEvent_ne_undefined_eq_true (p : W → Trivalent) :
    condEvent (p · ≠ .undefined) (p · = .true) = p := by
  funext w; cases h : p w <;> simp [condEvent, h]

/-- Two conditional events coincide exactly when they have the same condition and agree on it. -/
theorem condEvent_eq_condEvent_iff {A A' B B' : W → Prop} [DecidablePred A]
    [DecidablePred A'] [DecidablePred B] [DecidablePred B'] :
    condEvent A B = condEvent A' B' ↔
      {w | A w} = {w | A' w} ∧ {w | A w} ∩ {w | B w} = {w | A' w} ∩ {w | B' w} := by
  constructor
  · intro h
    have hgap := congrArg gapExt h
    have hpos := congrArg posExt h
    simp only [gapExt_condEvent, posExt_condEvent, Set.ext_iff, Set.mem_ofPred_eq] at hgap hpos
    exact ⟨Set.ext fun w ↦ not_iff_not.1 (hgap w), Set.ext fun w ↦ hpos w⟩
  · rintro ⟨hA, hAB⟩
    funext w
    have h₁ : A w ↔ A' w := Set.ext_iff.1 hA w
    have h₂ : A w ∧ B w ↔ A' w ∧ B' w := Set.ext_iff.1 hAB w
    exact eq_of_eq_undefined_iff_of_eq_true_iff (by simp [h₁]) (by simp [h₂])

end ConditionalEvent

end Trivalent
